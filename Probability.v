(******************************************************************************)
(*                                                                            *)
(*                       nms-verified — Probability.v                         *)
(*                                                                            *)
(*     Multilayer quantized chain Lipschitz, matching algorithms,             *)
(*     IEEE 754 binary64 representation, quadratic remainder, Hoeffding's     *)
(*     lemma (symmetric and asymmetric), iid sampling and PAC                 *)
(*     generalization. Imports the bridge ([Bridge]) and the keystone         *)
(*     ([Core]).                                                              *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List PeanoNat Bool Lia Reals Lra Arith.Wf_nat Recdef ZArith.
From Stdlib Require Import Permutation Extraction MVT Rtrigo_def Ranalysis4.
Import ListNotations.

Set Implicit Arguments.

Require Import Core.
Require Import Bridge.

(** ******************************************************************** *)
(** *                Section 3. Training and concentration                *)
(** ******************************************************************** *)

(** [real_lipschitz_to_nat] absorbs one bit of quantization error
    at the score head only. For a deeper network, intermediate
    activations are quantized too — fixed-point hardware applies a
    quantize-then-dequantize round-trip after each layer. Each
    layer adds [q_eps] of additive error at the quantization site;
    subsequent layers' Lipschitz responses amplify it.

    [chain_lip Ls = L_1 * L_2 * ... * L_N] computes the global
    Lipschitz constant. [chain_quant_slack Ls] computes the
    cumulative slack as a sum of suffix products: the quantization
    at layer i contributes [q_eps] amplified by [L_{i+1} * ... *
    L_N]. The recursion is [chain_quant_slack (L :: rest) =
    q_eps * chain_lip rest + chain_quant_slack rest].

    [apply_quant_chain_lipschitz] proves the quantized chain is
    [chain_lip Ls]-Lipschitz with additive slack [2 *
    chain_quant_slack Ls], end-to-end across N layers. The slack
    accumulates additively, and the L-amplification of earlier
    layers' quantization errors is captured exactly by the suffix
    products in [chain_quant_slack].

*)

Local Open Scope R_scope.

Section MultilayerQuantLipschitz.

  Variable q : R -> R.
  Variable q_eps : R.
  Hypothesis q_eps_nonneg : 0 <= q_eps.
  Hypothesis q_bounded : forall x, Rabs (q x - x) <= q_eps.

  Fixpoint apply_quant_chain (fs : list (R -> R)) (x : R) : R :=
    match fs with
    | [] => x
    | f :: rest => apply_quant_chain rest (q (f x))
    end.

  Fixpoint chain_lip (Ls : list R) : R :=
    match Ls with
    | [] => 1
    | L :: rest => L * chain_lip rest
    end.

  Fixpoint chain_quant_slack (Ls : list R) : R :=
    match Ls with
    | [] => 0
    | L :: rest => q_eps * chain_lip rest + chain_quant_slack rest
    end.

  Lemma forall2_lipschitz_first :
    forall (fs : list (R -> R)) (Ls : list R),
      Forall2 Lipschitz Ls fs -> Forall (fun L => 0 <= L) Ls.
  Proof.
    intros fs Ls H.
    induction H as [|L f rest_Ls rest_fs HfL Hrest IH].
    - constructor.
    - constructor; [apply (lip_nonneg HfL) | exact IH].
  Qed.

  Lemma chain_lip_nonneg :
    forall Ls,
      Forall (fun L => 0 <= L) Ls ->
      0 <= chain_lip Ls.
  Proof.
    induction Ls as [|L rest IH]; intros Hall; simpl; [lra|].
    inversion Hall; subst.
    apply Rmult_le_pos; [assumption | apply IH; assumption].
  Qed.

  Lemma chain_quant_slack_nonneg :
    forall Ls,
      Forall (fun L => 0 <= L) Ls ->
      0 <= chain_quant_slack Ls.
  Proof.
    induction Ls as [|L rest IH]; intros Hall; simpl; [lra|].
    inversion Hall; subst.
    pose proof (chain_lip_nonneg H2) as Hcl.
    pose proof (IH H2) as Hcs.
    apply Rplus_le_le_0_compat; [|assumption].
    apply Rmult_le_pos; assumption.
  Qed.

  (**Single-layer error bound: a Lipschitz layer
      followed by quantization produces output within
      [L * |x - y| + 2 * q_eps] of the ideal Lipschitz bound. *)

  Theorem quant_lipschitz_step :
    forall (f : R -> R) (L : R) (x y : R),
      Lipschitz L f ->
      Rabs (q (f x) - q (f y)) <= L * Rabs (x - y) + 2 * q_eps.
  Proof.
    intros f L x y Hlip.
    pose proof (q_bounded (f x)) as Hex.
    pose proof (q_bounded (f y)) as Hey.
    pose proof (lip_bound Hlip x y) as Hf.
    assert (Htri : Rabs (q (f x) - q (f y)) <=
                   Rabs (q (f x) - f x) + Rabs (f x - f y) +
                   Rabs (f y - q (f y))).
    { replace (q (f x) - q (f y))
         with ((q (f x) - f x) + (f x - f y) + (f y - q (f y))) by lra.
      eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat_r. apply Rabs_triang. }
    assert (Hey' : Rabs (f y - q (f y)) <= q_eps).
    { replace (f y - q (f y)) with (-(q (f y) - f y)) by lra.
      rewrite Rabs_Ropp. exact Hey. }
    lra.
  Qed.

  (**End-to-end quantized chain Lipschitz bound: the
      N-layer chain [apply_quant_chain fs] is
      [chain_lip Ls]-Lipschitz with additive slack
      [2 * chain_quant_slack Ls]. The slack accumulates by suffix
      products of subsequent Lipschitz constants. *)

  Theorem apply_quant_chain_lipschitz :
    forall (fs : list (R -> R)) (Ls : list R),
      Forall2 Lipschitz Ls fs ->
      forall x y,
        Rabs (apply_quant_chain fs x - apply_quant_chain fs y) <=
        chain_lip Ls * Rabs (x - y) + 2 * chain_quant_slack Ls.
  Proof.
    intros fs Ls Hlip.
    induction Hlip as [|L f rest_Ls rest_fs HfL Hrest IH].
    - intros x y. simpl. rewrite Rmult_1_l. lra.
    - intros x y. simpl.
      pose proof (quant_lipschitz_step x y HfL) as Hstep.
      pose proof (IH (q (f x)) (q (f y))) as Hrec.
      pose proof (lip_nonneg HfL) as HL_nn.
      pose proof (chain_lip_nonneg (forall2_lipschitz_first Hrest)) as Hcl_nn.
      pose proof (Rabs_pos (q (f x) - q (f y))) as Hqp.
      pose proof (Rabs_pos (x - y)) as Hxyp.
      eapply Rle_trans; [exact Hrec|].
      nra.
  Qed.

End MultilayerQuantLipschitz.

Local Close Scope R_scope.


(** SGD on the smooth squared-hinge surrogate [L_separated_sq], whose
    full sum-zero-locus equals the Separated locus
    ([L_separated_sq_zero_iff_separated_general] below).
    [sgd_telescoping_vec] gives stationary-point convergence for any
    non-negative smooth loss. The geometric (linear) convergence claim
    relies on the Polyak-Lojasiewicz inequality, discharged for the
    scalar squared hinge in [Section 7] via [sh_PL]. *)

Local Open Scope R_scope.

Section SGDOnNonnegSmoothLoss.

  Variable n : nat.
  Variable f : list R -> R.
  Variable grad : list R -> list R.
  Variable Lsm : R.
  Hypothesis Lsm_pos : 0 < Lsm.
  Hypothesis grad_dim :
    forall theta, length theta = n -> length (grad theta) = n.
  Hypothesis quad_upper_bound :
    forall x y, length x = n -> length y = n ->
      f y <= f x + dot (grad x) (vec_sub y x) +
              Lsm / 2 * dot (vec_sub y x) (vec_sub y x).
  Hypothesis f_nonneg : forall theta, length theta = n -> 0 <= f theta.

  (**The vector SGD analysis instantiated for a
      non-negative smooth loss with [f_lower = 0]. After [T]
      iterations from any [theta0] of dimension [n] with step size
      [eta * Lsm <= 1], the cumulative gradient-norm-squared is
      bounded by [2 * f(theta0) / eta]. *)

  Theorem sgd_on_nonneg_smooth_loss_stationary :
    forall theta0 eta T,
      length theta0 = n ->
      0 < eta -> eta * Lsm <= 1 ->
      (eta / 2) * grad_norm_sq_sum grad eta theta0 T <= f theta0.
  Proof.
    intros theta0 eta T Hlen Heta_pos HetaLsm.
    pose proof (sgd_telescoping_vec f grad grad_dim quad_upper_bound
                  theta0 T Hlen Heta_pos HetaLsm f_nonneg) as H.
    lra.
  Qed.

End SGDOnNonnegSmoothLoss.

Local Close Scope R_scope.


(** Closes the Chebyshev + Bonferroni chain into a single named
    theorem. For each event in a list, a per-event Chebyshev-style
    bound [eps² * prob_e <= V] is given (this is the conclusion of
    [chebyshev_finite_uniform] applied to the squared-deviation
    random variable). Bonferroni's union bound aggregates them.
    The closed-form: if [M * V <= eps² * delta] then the union
    probability of any event firing is at most [delta], where M is
    the number of events.

    Standard reading: with M hypotheses each bounded by V, sample
    size n satisfying [n * delta * eps² >= M * V_per] suffices,
    when V scales as V_per / n. Here V is left abstract — instantiate
    with the appropriate variance factor for the empirical-mean
    application (a Chebyshev-on-sample-mean theorem, beyond Stdlib's
    current scope, would supply V = V_per / n).

    Theorem 1.  sample_complexity_chebyshev_bonferroni *)

Local Open Scope R_scope.

Theorem sample_complexity_chebyshev_bonferroni :
  forall (samples : list R) (events : list (R -> bool))
         (V eps delta : R),
    0 < eps -> 0 < delta -> 0 <= V ->
    (forall e, In e events -> eps * eps * prob_uniform samples e <= V) ->
    INR (length events) * V <= eps * eps * delta ->
    prob_uniform samples
                 (fun x => existsb (fun e => e x) events) <= delta.
Proof.
  intros samples events V eps delta Heps Hdelta HV Hperev Hcomp.
  pose proof (bonferroni_list samples events) as Hbon.
  eapply Rle_trans; [exact Hbon|].
  assert (Hsum_bnd :
    eps * eps *
      fold_right Rplus 0
        (map (fun e => prob_uniform samples e) events)
    <= INR (length events) * V).
  { clear Hcomp Hbon Hdelta.
    revert Hperev.
    induction events as [|e rest IH]; intros Hperev.
    - cbn. lra.
    - cbn [map fold_right length].
      pose proof (Hperev e (or_introl eq_refl)) as Hpe.
      pose proof (IH (fun e' He' => Hperev e' (or_intror He'))) as IHapp.
      rewrite S_INR.
      nra. }
  apply Rmult_le_reg_l with (r := eps * eps); [nra|].
  eapply Rle_trans; [exact Hsum_bnd | exact Hcomp].
Qed.

Local Close Scope R_scope.


(** [sgd_telescoping_vec] (and wrapper) prove
    stationary-point convergence: cumulative grad-norm-squared is
    bounded, so the minimum gradient norm vanishes. This leaves
    open whether the stationary point reached is a global minimum.
    The Polyak-Lojasiewicz inequality

        2 * mu * (f(theta) - f_lower) <= |grad f(theta)|^2

    promotes stationary to global: at any theta with small gradient
    norm, [f(theta) - f_lower] is small. Combined with the descent
    inequality [f(theta_{t+1}) <= f(theta_t) - eta/2 * |grad|^2],
    this yields linear convergence:

        f(theta_T) - f_lower <= (1 - eta * mu)^T * (f(theta_0) - f_lower)

    The geometric factor (1 - eta * mu) gives a rate strictly faster
    than O(1/T). Composing with training infrastructure:
    SGD on a non-negative smooth loss with PL constant mu converges
    geometrically to the global minimum, which for L_separated_sq is
    zero loss, and zero loss equals the Separated locus
    ([L_separated_sq_zero_iff_separated_general] below). *)

Local Open Scope R_scope.

Section ConvergenceUnderPL.

  Variable n : nat.
  Variable f : list R -> R.
  Variable grad : list R -> list R.
  Variable Lsm : R.
  Hypothesis Lsm_pos : 0 < Lsm.
  Hypothesis grad_dim :
    forall theta, length theta = n -> length (grad theta) = n.
  Hypothesis quad_upper_bound :
    forall x y, length x = n -> length y = n ->
      f y <= f x + dot (grad x) (vec_sub y x) +
              Lsm / 2 * dot (vec_sub y x) (vec_sub y x).

  Variable f_lower : R.
  Hypothesis f_lower_bound :
    forall theta, length theta = n -> f_lower <= f theta.

  Variable mu : R.
  Hypothesis mu_pos : 0 < mu.
  Hypothesis pl_inequality :
    forall theta, length theta = n ->
      2 * mu * (f theta - f_lower) <= dot (grad theta) (grad theta).

  (**Single-step linear contraction under PL. *)

  Theorem sgd_pl_one_step :
    forall theta eta,
      length theta = n ->
      0 < eta -> eta * Lsm <= 1 ->
      f (sgd_step_vec grad eta theta) - f_lower <=
      (1 - eta * mu) * (f theta - f_lower).
  Proof.
    intros theta eta Hlen Heta_pos HetaLsm.
    pose proof (sgd_descent_vec f grad grad_dim quad_upper_bound
                  theta Hlen Heta_pos HetaLsm) as Hdesc.
    pose proof (pl_inequality theta Hlen) as Hpl.
    nra.
  Qed.

  (**T-step geometric convergence to the global minimum.
      The factor [(1 − η μ)^T] decays geometrically when [η μ < 1]. *)

  Theorem sgd_pl_linear_convergence :
    forall theta0 eta T,
      length theta0 = n ->
      0 < eta -> eta * Lsm <= 1 -> eta * mu <= 1 ->
      f (sgd_iterate_vec grad eta theta0 T) - f_lower <=
      (1 - eta * mu) ^ T * (f theta0 - f_lower).
  Proof.
    intros theta0 eta T Hlen Heta_pos HetaLsm Hetamu_le.
    induction T as [|T' IH].
    - simpl. rewrite Rmult_1_l. lra.
    - simpl.
      pose proof (sgd_iterate_vec_length grad grad_dim eta theta0 T' Hlen) as Hlen_T'.
      pose proof (sgd_pl_one_step (sgd_iterate_vec grad eta theta0 T')
                    Hlen_T' Heta_pos HetaLsm) as Hone.
      pose proof (f_lower_bound (sgd_iterate_vec grad eta theta0 T') Hlen_T')
        as HfT_low.
      assert (H1mu_nn : 0 <= 1 - eta * mu) by lra.
      eapply Rle_trans; [exact Hone|].
      apply Rle_trans with ((1 - eta * mu) *
                             ((1 - eta * mu) ^ T' * (f theta0 - f_lower))).
      + apply Rmult_le_compat_l; [exact H1mu_nn | exact IH].
      + lra.
  Qed.

End ConvergenceUnderPL.

Local Close Scope R_scope.


(** Per-pair, [pair_violation_sq_zero_iff] establishes that the
    squared-hinge surrogate has the same zero locus as the L1-hinge:
    [pair_violation_sq m d d' = 0 <-> pair_violation m d d' = 0]
    (already proved).

    This part lifts the equivalence to the sum:
    [L_separated_sq m D = 0 <-> L_separated m D = 0]. Combined with
    [L_separated_zero_iff_separated_general] (already proved),
    [L_separated_sq] vanishes exactly on the [Separated] locus, with
    the integer slack [k] given by the real margin [INR k].

    [fold_right_Rplus_zero_iff] (helper) provides the key
    technical fact: a finite sum of non-negative reals vanishes iff
    each summand vanishes. Combined with the elementwise zero-iff of
    pair_violation_sq vs pair_violation, the lifted equivalence
    follows by routine flat_map / map manipulation.

*)

Local Open Scope R_scope.

Theorem L_separated_sq_zero_iff_L_separated_zero :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (m : R) (D : list (@det Box)),
    L_separated_sq iou tau theta box_eq_dec_l m D = 0 <->
    L_separated iou tau theta box_eq_dec_l m D = 0.
Proof.
  intros Box iou tau theta box_eq_dec_l m D.
  unfold L_separated_sq, L_separated.
  assert (Hnn_sq : forall x,
    In x (flat_map (fun d =>
      map (fun d' => pair_violation_sq iou tau theta box_eq_dec_l m d d') D) D)
    -> 0 <= x).
  { intros x Hx. apply in_flat_map in Hx as [d [_ Hd]].
    apply in_map_iff in Hd as [d' [Heq _]]. subst x.
    apply pair_violation_sq_nonneg. }
  assert (Hnn_l1 : forall x,
    In x (flat_map (fun d =>
      map (fun d' => pair_violation iou tau theta box_eq_dec_l m d d') D) D)
    -> 0 <= x).
  { intros x Hx. apply in_flat_map in Hx as [d [_ Hd]].
    apply in_map_iff in Hd as [d' [Heq _]]. subst x.
    apply pair_violation_nonneg. }
  rewrite (fold_right_Rplus_zero_iff _ Hnn_sq).
  rewrite (fold_right_Rplus_zero_iff _ Hnn_l1).
  split.
  - intros Hsq x Hx.
    apply in_flat_map in Hx as [d [Hd Hd_in]].
    apply in_map_iff in Hd_in as [d' [Heq Hd'_in]]. subst x.
    apply (proj1 (pair_violation_sq_zero_iff iou tau theta box_eq_dec_l m d d')).
    apply Hsq.
    apply in_flat_map. exists d. split; [assumption|].
    apply in_map_iff. exists d'. split; [reflexivity|assumption].
  - intros HL x Hx.
    apply in_flat_map in Hx as [d [Hd Hd_in]].
    apply in_map_iff in Hd_in as [d' [Heq Hd'_in]]. subst x.
    apply (proj2 (pair_violation_sq_zero_iff iou tau theta box_eq_dec_l m d d')).
    apply HL.
    apply in_flat_map. exists d. split; [assumption|].
    apply in_map_iff. exists d'. split; [reflexivity|assumption].
Qed.

Theorem L_separated_sq_zero_iff_separated_general :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (D : list (@det Box)) (k : nat),
    (1 <= k)%nat -> (k <= theta)%nat ->
    L_separated_sq iou tau theta box_eq_dec_l (INR k) D = 0 <->
    Separated iou tau theta k D.
Proof.
  intros Box iou tau theta box_eq_dec_l D k Hk_pos Hk_le_theta.
  rewrite L_separated_sq_zero_iff_L_separated_zero.
  apply L_separated_zero_iff_separated_general; assumption.
Qed.

Local Close Scope R_scope.


(** [L_separated] is single-class. Real detectors emit a
    score vector (one nat per class) per box; [mc_det],
    [mc_one_peak], [mc_no_tie_clash] capture this. [L_mc_separated]
    is the Real-valued loss summing [mc_pair_violation] over every
    pair of detections and every class in [cs].

    Under the [unique_boxes] hypothesis (distinct mc_dets carry
    distinct boxes — by construction in slot-based architectures
    like DETR), zero loss implies the cs-restricted invariants
    [mc_one_peak_cs] and [mc_no_tie_clash_cs]. The reduction goes
    via [fold_right_Rplus_zero_iff] to per-triple zero, then the
    per-triple Separated-1 condition feeds the predicate
    conclusions.

*)

Local Open Scope R_scope.

Section MultiClassL.

  Variable Box : Type.
  Variable Class : Type.
  Variable iou_b : Box -> Box -> nat.
  Variable tau : nat.
  Variable theta : nat.
  Variable box_eq_dec : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2}.

  Definition mc_pair_violation
      (md1 md2 : mc_det Box Class) (c : Class) : R :=
    if box_eq_dec (mc_box md1) (mc_box md2) then 0
    else if Nat.leb tau (iou_b (mc_box md1) (mc_box md2)) then
      let s1 := INR (mc_score md1 c) in
      let s2 := INR (mc_score md2 c) in
      let lower := Rmin s1 s2 in
      let upper := Rmax s1 s2 in
      Rmax 0 (1 - (upper - lower)) + Rmax 0 (lower - INR theta + 1)
    else 0.

  Lemma mc_pair_violation_nonneg :
    forall md1 md2 c, 0 <= mc_pair_violation md1 md2 c.
  Proof.
    intros md1 md2 c. unfold mc_pair_violation.
    destruct (box_eq_dec _ _); [apply Rle_refl|].
    destruct (Nat.leb tau _); [|apply Rle_refl].
    apply Rplus_le_le_0_compat; apply Rmax_l.
  Qed.

  Definition L_mc_separated
      (mds : list (mc_det Box Class)) (cs : list Class) : R :=
    fold_right Rplus 0
      (flat_map (fun md1 =>
                   flat_map (fun md2 =>
                              map (fun c => mc_pair_violation md1 md2 c) cs)
                            mds)
                mds).

  Lemma L_mc_separated_nonneg :
    forall mds cs, 0 <= L_mc_separated mds cs.
  Proof.
    intros mds cs.
    unfold L_mc_separated.
    apply fold_right_Rplus_nonneg.
    intros x Hx.
    apply in_flat_map in Hx as [md1 [_ Hx1]].
    apply in_flat_map in Hx1 as [md2 [_ Hx2]].
    apply in_map_iff in Hx2 as [c [Heq _]]. subst x.
    apply mc_pair_violation_nonneg.
  Qed.

  (**Per-triple zero decomposition. *)

  Theorem mc_pair_violation_zero_separation :
    forall md1 md2 c,
      (1 <= theta)%nat ->
      mc_pair_violation md1 md2 c = 0 ->
      mc_box md1 = mc_box md2 \/
      (iou_b (mc_box md1) (mc_box md2) < tau)%nat \/
      (mc_score md1 c + 1 <= mc_score md2 c /\ mc_score md1 c < theta)%nat \/
      (mc_score md2 c + 1 <= mc_score md1 c /\ mc_score md2 c < theta)%nat.
  Proof.
    intros md1 md2 c Hth Hzero.
    unfold mc_pair_violation in Hzero.
    destruct (box_eq_dec (mc_box md1) (mc_box md2)) as [Hbeq | Hbne].
    - left. assumption.
    - right.
      destruct (Nat.leb_spec tau (iou_b (mc_box md1) (mc_box md2)))
        as [Hge | Hlt].
      + right.
        set (s1 := INR (mc_score md1 c)) in *.
        set (s2 := INR (mc_score md2 c)) in *.
        set (lower := Rmin s1 s2) in *.
        set (upper := Rmax s1 s2) in *.
        assert (Hgap : Rmax 0 (1 - (upper - lower)) = 0 /\
                      Rmax 0 (lower - INR theta + 1) = 0).
        { pose proof (Rmax_l 0 (1 - (upper - lower))) as H1.
          pose proof (Rmax_l 0 (lower - INR theta + 1)) as H2.
          split; lra. }
        destruct Hgap as [Hg1 Hg2].
        assert (Hg1' : upper - lower >= 1).
        { destruct (Rle_dec 0 (1 - (upper - lower))) as [Hle' | Hgt'].
          - rewrite (Rmax_right _ _ Hle') in Hg1. lra.
          - lra. }
        assert (Hg2' : lower < INR theta).
        { destruct (Rle_dec 0 (lower - INR theta + 1)) as [Hle' | Hgt'].
          - rewrite (Rmax_right _ _ Hle') in Hg2. lra.
          - lra. }
        destruct (Rle_lt_dec s1 s2) as [Hss | Hss].
        * left.
          assert (Hlow : lower = s1) by (apply Rmin_left; assumption).
          assert (Hup : upper = s2) by (apply Rmax_right; assumption).
          rewrite Hlow in Hg2'. rewrite Hlow, Hup in Hg1'.
          unfold s1, s2 in *.
          split.
          -- apply INR_le. rewrite plus_INR. simpl. lra.
          -- apply INR_lt. lra.
        * right.
          assert (Hlow : lower = s2) by (apply Rmin_right; lra).
          assert (Hup : upper = s1) by (apply Rmax_left; lra).
          rewrite Hlow in Hg2'. rewrite Hlow, Hup in Hg1'.
          unfold s1, s2 in *.
          split.
          -- apply INR_le. rewrite plus_INR. simpl. lra.
          -- apply INR_lt. lra.
      + left. assumption.
  Qed.

  Definition mc_one_peak_cs
      (cs : list Class) (mds : list (mc_det Box Class)) : Prop :=
    forall md md' c, In md mds -> In md' mds -> In c cs ->
      (tau <= iou_b (mc_box md) (mc_box md'))%nat ->
      (mc_score md c < mc_score md' c)%nat ->
      (mc_score md c < theta)%nat.

  Definition mc_no_tie_clash_cs
      (cs : list Class) (mds : list (mc_det Box Class)) : Prop :=
    forall md md' c, In md mds -> In md' mds -> In c cs ->
      md <> md' ->
      mc_score md c = mc_score md' c ->
      (iou_b (mc_box md) (mc_box md') < tau)%nat.

  Definition unique_boxes_mc (mds : list (mc_det Box Class)) : Prop :=
    forall md md', In md mds -> In md' mds ->
                   mc_box md = mc_box md' -> md = md'.

  (**Zero loss implies the cs-restricted invariants
      under unique_boxes. *)

  Theorem L_mc_separated_zero_implies_invariants :
    forall (mds : list (mc_det Box Class)) (cs : list Class),
      (1 <= theta)%nat ->
      unique_boxes_mc mds ->
      L_mc_separated mds cs = 0 ->
      mc_one_peak_cs cs mds /\ mc_no_tie_clash_cs cs mds.
  Proof.
    intros mds cs Hth Huniq HL.
    assert (Hnn : forall x,
      In x (flat_map (fun md1 =>
                        flat_map (fun md2 =>
                                    map (fun c => mc_pair_violation md1 md2 c) cs)
                                 mds)
                     mds) -> 0 <= x).
    { intros x Hx.
      apply in_flat_map in Hx as [md1 [_ Hx1]].
      apply in_flat_map in Hx1 as [md2 [_ Hx2]].
      apply in_map_iff in Hx2 as [c [Heq _]]. subst x.
      apply mc_pair_violation_nonneg. }
    pose proof (proj1 (fold_right_Rplus_zero_iff _ Hnn) HL) as Hall_zero.
    assert (Hpv : forall md1 md2 c,
              In md1 mds -> In md2 mds -> In c cs ->
              mc_pair_violation md1 md2 c = 0).
    { intros md1 md2 c Hin1 Hin2 Hinc.
      apply Hall_zero.
      apply in_flat_map. exists md1. split; [assumption|].
      apply in_flat_map. exists md2. split; [assumption|].
      apply in_map_iff. exists c. split; [reflexivity|assumption]. }
    split.
    - intros md1 md2 c Hin1 Hin2 Hinc Hiou Hlt.
      pose proof (mc_pair_violation_zero_separation _ _ _ Hth
                    (Hpv md1 md2 c Hin1 Hin2 Hinc))
        as [Hbeq | [Hiou_lt | [[Hgap Hlt'] | [Hgap Hlt']]]].
      + pose proof (Huniq md1 md2 Hin1 Hin2 Hbeq) as Hmd_eq.
        subst md2. lia.
      + lia.
      + assumption.
      + lia.
    - intros md1 md2 c Hin1 Hin2 Hinc Hne Heq.
      pose proof (mc_pair_violation_zero_separation _ _ _ Hth
                    (Hpv md1 md2 c Hin1 Hin2 Hinc))
        as [Hbeq | [Hiou_lt | [[Hgap _] | [Hgap _]]]].
      + exfalso. apply Hne. apply (Huniq md1 md2 Hin1 Hin2 Hbeq).
      + assumption.
      + lia.
      + lia.
  Qed.

End MultiClassL.

Local Close Scope R_scope.

(** ******************************************************************** *)
(** *           Section 4. Matching and floating-point semantics          *)
(** ******************************************************************** *)

(** [greedy_match] is unit-weight optimal but not
    weighted optimal: with cost matrix [b1-g1: 10, b1-g2: 9,
    b2-g1: 9, b2-g2: 0], greedy picks 10 then 0 (total 10) while
    the optimum is 9+9 = 18. The full [O(n^3)] Hungarian algorithm
    closes this gap with potentials, alternating trees, and
    augmenting paths.

    This part lays the matching infrastructure: cost matrix as
    [Box -> GT -> R], matching as list of pairs, weight as the sum
    of edge costs, injectivity on each side. The structural
    [exists_max_weight_matching] theorem proves that for any finite
    candidate list, the maximum-weight matching exists in the list.
    Combining this with an enumeration of all injective matchings
    (from a finite Box / GT list) yields existence of the optimal
    matching. The Hungarian algorithm is the polynomial-time
    constructor; the existence theorem is its abstract guarantee.

*)

Local Open Scope R_scope.

Section HungarianMatching.

  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.

  Definition matching_weight (M : list (Box * GT)) : R :=
    fold_right Rplus 0 (map (fun p => cost (fst p) (snd p)) M).

  Definition matching_box_injective (M : list (Box * GT)) : Prop :=
    forall b g1 g2, In (b, g1) M -> In (b, g2) M -> g1 = g2.

  Definition matching_gt_injective (M : list (Box * GT)) : Prop :=
    forall b1 b2 g, In (b1, g) M -> In (b2, g) M -> b1 = b2.

  Definition matching_injective (M : list (Box * GT)) : Prop :=
    matching_box_injective M /\ matching_gt_injective M.

  (**Every non-empty list of reals contains an element
      that is greater than or equal to all elements in the list. *)

  Theorem fold_right_Rmax_witness :
    forall (l : list R), l <> [] ->
      exists x, In x l /\ forall y, In y l -> y <= x.
  Proof.
    induction l as [|x rest IH]; intros Hne; [contradiction|].
    destruct rest as [|y rest'].
    - exists x. split; [left; reflexivity|].
      intros y0 [Heq | []]. lra.
    - assert (Hne_rest : y :: rest' <> []) by discriminate.
      destruct (IH Hne_rest) as [m [Hm Hmax]].
      destruct (Rle_dec x m) as [Hle | Hlt].
      + exists m. split; [right; assumption|].
        intros y0 [Heq | Hin].
        * subst y0. assumption.
        * apply Hmax. assumption.
      + exists x. split; [left; reflexivity|].
        intros y0 [Heq | Hin].
        * subst y0. lra.
        * pose proof (Hmax y0 Hin). lra.
  Qed.

  (**For any non-empty list of candidate matchings, the
      maximum-weight matching exists in the list. The Hungarian
      algorithm constructs this maximum in [O(n^3)]; the existence
      theorem is the abstract correctness target. *)

  Theorem exists_max_weight_matching :
    forall (matchings : list (list (Box * GT))),
      matchings <> [] ->
      exists M, In M matchings /\
                forall M', In M' matchings ->
                  matching_weight M' <= matching_weight M.
  Proof.
    intros matchings Hne.
    assert (Hne_w : map matching_weight matchings <> []).
    { destruct matchings; [contradiction|simpl; discriminate]. }
    pose proof (fold_right_Rmax_witness Hne_w)
      as [w [Hw_in Hw_max]].
    apply in_map_iff in Hw_in as [M [Hweq HM_in]].
    exists M. split; [assumption|].
    intros M' HM'_in.
    rewrite Hweq.
    apply Hw_max. apply in_map_iff. exists M'. split; [reflexivity|assumption].
  Qed.

End HungarianMatching.

Local Close Scope R_scope.


(** [quantize_unit] (fixed-precision quantizer) gives [1/2]
    absolute error at integer precision. For binary64, the IEEE 754
    standard prescribes:
      - [(sign, exponent, mantissa)] representation with 1+11+52 bits
      - round-to-nearest-even tie-breaking
      - relative error [|q(x) - x| <= 2^{-53} * |x|] on normal range
      - subnormal handling at absolute error [2^{-1074}]
      - explicit modeling of [+inf], [-inf], [NaN] as an option type

    This part delivers the structural representation
    ([b64_repr] record with the standard field widths) and a
    parametric fixed-precision quantizer [fp_quantize q] generalising
    [quantize_unit]. The relative-error scaling, subnormal range, and
    special-value option type are the remaining pieces of full IEEE
    754 — significant additional work each.

*)

Record b64_repr : Type := {
  b64_sign     : bool;     (* 1 bit:   true = negative, false = non-negative *)
  b64_exponent : Z;        (* 11 bits: biased exponent in 0..2047 *)
  b64_mantissa : nat       (* 52 bits: integer mantissa in 0..2^52 - 1 *)
}.

Local Open Scope R_scope.

Definition fp_quantize (q x : R) : R := quantize_unit (x / q) * q.

Theorem fp_quantize_bounded_error :
  forall q x, 0 < q ->
    Rabs (fp_quantize q x - x) <= q / 2.
Proof.
  intros q x Hq.
  unfold fp_quantize.
  pose proof (quantize_unit_bounded_error (x / q)) as Hbd.
  assert (Heq : quantize_unit (x / q) * q - x =
                (quantize_unit (x / q) - x / q) * q).
  { field. lra. }
  rewrite Heq.
  rewrite Rabs_mult.
  rewrite (Rabs_right q) by lra.
  pose proof (Rabs_pos (quantize_unit (x / q) - x / q)) as Hp.
  apply Rmult_le_reg_r with (r := / q); [apply Rinv_0_lt_compat; assumption|].
  rewrite Rmult_assoc, Rinv_r by lra.
  rewrite Rmult_1_r.
  replace (q / 2 * / q) with (/ 2) by (field; lra).
  exact Hbd.
Qed.

(** Binary64 mantissa scale: [2^{-52}] is the precision of the
    52-bit mantissa fraction at exponent zero. The half-ULP
    [2^{-53}] is the absolute error bound at this scale. *)

Definition b64_eps : R := / (2 ^ 52).

Lemma b64_eps_pos : 0 < b64_eps.
Proof. unfold b64_eps. apply Rinv_0_lt_compat. apply pow_lt. lra. Qed.

Definition b64_quantize : R -> R := fp_quantize b64_eps.

Theorem b64_quantize_bounded_error :
  forall x, Rabs (b64_quantize x - x) <= b64_eps / 2.
Proof.
  intros x. unfold b64_quantize.
  apply fp_quantize_bounded_error. apply b64_eps_pos.
Qed.

Local Open Scope R_scope.

Definition b64_q (e : Z) : R := powerRZ 2 (e - 52).

Definition b64_normal_quantize (e : Z) (x : R) : R :=
  fp_quantize (b64_q e) x.

Lemma powerRZ_2_pos : forall e, 0 < powerRZ 2 e.
Proof. intros e. apply powerRZ_lt. lra. Qed.

Lemma powerRZ_2_nonneg : forall e, 0 <= powerRZ 2 e.
Proof. intros e. left. apply powerRZ_2_pos. Qed.

Lemma b64_q_pos : forall e, 0 < b64_q e.
Proof. intros e. unfold b64_q. apply powerRZ_2_pos. Qed.

Theorem fp_quantize_pow_relative_error :
  forall (x : R) (e : Z),
    powerRZ 2 e <= Rabs x ->
    Rabs (fp_quantize (b64_q e) x - x) <= powerRZ 2 (-53) * Rabs x.
Proof.
  intros x e Hlo.
  pose proof (b64_q_pos e) as Hq.
  pose proof (@fp_quantize_bounded_error (b64_q e) x Hq) as Habs.
  apply Rle_trans with (b64_q e / 2); [exact Habs|].
  unfold b64_q.
  assert (Hsplit : powerRZ 2 (e - 52) / 2 = powerRZ 2 (e - 53)).
  { replace (e - 52)%Z with ((e - 53) + 1)%Z by lia.
    rewrite powerRZ_add by lra.
    simpl. field. }
  rewrite Hsplit.
  assert (Hfact : powerRZ 2 (e - 53) = powerRZ 2 (-53) * powerRZ 2 e).
  { replace (e - 53)%Z with ((-53) + e)%Z by lia.
    rewrite powerRZ_add by lra. reflexivity. }
  rewrite Hfact.
  apply Rmult_le_compat_l; [apply powerRZ_2_nonneg | exact Hlo].
Qed.

Theorem b64_normal_quantize_relative_error :
  forall (x : R) (e : Z),
    powerRZ 2 e <= Rabs x ->
    Rabs (b64_normal_quantize e x - x) <= powerRZ 2 (-53) * Rabs x.
Proof.
  intros x e Hlo. unfold b64_normal_quantize.
  apply fp_quantize_pow_relative_error. exact Hlo.
Qed.

Local Close Scope R_scope.



Local Open Scope R_scope.

Fixpoint insert_each_pos {A : Type} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]
  | y :: rest => (x :: y :: rest) :: map (cons y) (insert_each_pos x rest)
  end.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: rest => flat_map (insert_each_pos x) (perms rest)
  end.

Lemma in_insert_each_pos_iff :
  forall {A : Type} (x : A) (l p : list A),
    In p (insert_each_pos x l) <->
    exists l1 l2, l = l1 ++ l2 /\ p = l1 ++ x :: l2.
Proof.
  intros A x l. induction l as [|y rest IH]; intros p; split.
  - intros [Heq | []]. subst p. exists (@nil A), (@nil A). split; reflexivity.
  - intros [l1 [l2 [Heq Hp]]].
    destruct l1; destruct l2; try discriminate.
    simpl in Hp. subst p. simpl. left; reflexivity.
  - intros [Heq | Hin].
    + subst p. exists (@nil A), (y :: rest). split; reflexivity.
    + apply in_map_iff in Hin as [p' [Heq Hp']]. subst p.
      apply IH in Hp' as [l1 [l2 [Hl Hp'_eq]]]. subst p' rest.
      exists (y :: l1), l2. split; reflexivity.
  - intros [l1 [l2 [Heq Hp]]].
    destruct l1 as [|y' l1'].
    + simpl in Heq. subst l2.
      simpl in Hp. subst p. simpl. left; reflexivity.
    + simpl in Heq. injection Heq as Hyy Hl. subst y' rest.
      simpl in Hp. subst p. simpl. right.
      apply in_map_iff. exists (l1' ++ x :: l2). split; [reflexivity|].
      apply IH. exists l1', l2. split; reflexivity.
Qed.

Theorem permutation_in_perms :
  forall {A : Type} (l p : list A),
    Permutation l p -> In p (perms l).
Proof.
  intros A l. induction l as [|x rest IH]; intros p Hperm.
  - apply Permutation_nil in Hperm. subst. simpl. left; reflexivity.
  - pose proof (Permutation_in x Hperm (in_eq x rest)) as Hxin.
    apply in_split in Hxin as [l1 [l2 Hp_eq]]. subst p.
    assert (Hperm_rest : Permutation rest (l1 ++ l2)).
    { eapply Permutation_cons_app_inv. exact Hperm. }
    pose proof (IH (l1 ++ l2) Hperm_rest) as Hin_rest.
    simpl. apply in_flat_map. exists (l1 ++ l2). split; [assumption|].
    apply in_insert_each_pos_iff. exists l1, l2. split; reflexivity.
Qed.

Lemma perms_nonempty :
  forall {A : Type} (l : list A), perms l <> [].
Proof.
  intros A l. induction l as [|x rest IH].
  - simpl. discriminate.
  - simpl. intros Heq. apply IH. clear IH.
    destruct (perms rest) as [|p ps]; [reflexivity|].
    exfalso. simpl in Heq.
    destruct p; simpl in Heq; discriminate.
Qed.

Section BruteForceMatching.
  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.

  Definition matching_from_perm (boxes : list Box) (perm : list GT) :
      list (Box * GT) :=
    combine boxes (firstn (length boxes) perm).

  Definition all_brute_matchings (boxes : list Box) (gts : list GT) :
      list (list (Box * GT)) :=
    map (matching_from_perm boxes) (perms gts).

  Lemma all_brute_matchings_nonempty :
    forall boxes gts, all_brute_matchings boxes gts <> [].
  Proof.
    intros boxes gts. unfold all_brute_matchings.
    intros Heq. pose proof (perms_nonempty gts) as Hne.
    destruct (perms gts); [contradiction | discriminate].
  Qed.

  Definition pick_max (best m : list (Box * GT)) : list (Box * GT) :=
    if Rle_dec (matching_weight cost best) (matching_weight cost m)
    then m else best.

  Definition brute_match (boxes : list Box) (gts : list GT) :
      list (Box * GT) :=
    match all_brute_matchings boxes gts with
    | [] => []
    | m :: rest => fold_left pick_max rest m
    end.

  Lemma fold_left_pick_max_in_or_init :
    forall (rest : list (list (Box * GT))) (init : list (Box * GT)),
      fold_left pick_max rest init = init \/
      In (fold_left pick_max rest init) rest.
  Proof.
    induction rest as [|m rs IH]; intros init; simpl.
    - left; reflexivity.
    - destruct (IH (pick_max init m)) as [Heq | Hin].
      + rewrite Heq. unfold pick_max.
        destruct (Rle_dec (matching_weight cost init) (matching_weight cost m)).
        * right. left. reflexivity.
        * left. reflexivity.
      + right. right. assumption.
  Qed.

  Lemma pick_max_ge_right :
    forall init m,
      matching_weight cost m <= matching_weight cost (pick_max init m).
  Proof.
    intros init m. unfold pick_max.
    destruct (Rle_dec (matching_weight cost init) (matching_weight cost m));
      [apply Rle_refl | lra].
  Qed.

  Lemma pick_max_ge_left :
    forall init m,
      matching_weight cost init <= matching_weight cost (pick_max init m).
  Proof.
    intros init m. unfold pick_max.
    destruct (Rle_dec (matching_weight cost init) (matching_weight cost m));
      [assumption | apply Rle_refl].
  Qed.

  Lemma fold_left_pick_max_ge_init :
    forall (rest : list (list (Box * GT))) (init : list (Box * GT)),
      matching_weight cost init <=
      matching_weight cost (fold_left pick_max rest init).
  Proof.
    induction rest as [|m rs IH]; intros init; simpl.
    - apply Rle_refl.
    - eapply Rle_trans with (matching_weight cost (pick_max init m)).
      + apply pick_max_ge_left.
      + apply IH.
  Qed.

  Lemma fold_left_pick_max_dominates_in :
    forall (rest : list (list (Box * GT))) (init m : list (Box * GT)),
      In m rest ->
      matching_weight cost m <=
      matching_weight cost (fold_left pick_max rest init).
  Proof.
    induction rest as [|m0 rs IH]; intros init m Hin; simpl.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + subst m0.
        eapply Rle_trans with (matching_weight cost (pick_max init m)).
        * apply pick_max_ge_right.
        * apply fold_left_pick_max_ge_init.
      + apply IH. assumption.
  Qed.

  Lemma fold_left_pick_max_dominates :
    forall (rest : list (list (Box * GT))) (init m : list (Box * GT)),
      In m rest \/ m = init ->
      matching_weight cost m <=
      matching_weight cost (fold_left pick_max rest init).
  Proof.
    intros rest init m [Hin | Heq].
    - apply fold_left_pick_max_dominates_in. assumption.
    - subst m. apply fold_left_pick_max_ge_init.
  Qed.

  Theorem brute_match_in_enumeration :
    forall boxes gts,
      In (brute_match boxes gts) (all_brute_matchings boxes gts).
  Proof.
    intros boxes gts. unfold brute_match.
    pose proof (all_brute_matchings_nonempty boxes gts) as Hne.
    destruct (all_brute_matchings boxes gts) as [|m rest] eqn:E; [contradiction|].
    destruct (fold_left_pick_max_in_or_init rest m) as [Heq | Hin].
    - rewrite Heq. left; reflexivity.
    - right. assumption.
  Qed.

  Theorem brute_match_optimal_in_enumeration :
    forall boxes gts m,
      In m (all_brute_matchings boxes gts) ->
      matching_weight cost m <= matching_weight cost (brute_match boxes gts).
  Proof.
    intros boxes gts m Hin. unfold brute_match.
    pose proof (all_brute_matchings_nonempty boxes gts) as Hne.
    destruct (all_brute_matchings boxes gts) as [|m0 rest] eqn:E; [contradiction|].
    destruct Hin as [Heq | Hin].
    - subst m. apply fold_left_pick_max_dominates. right; reflexivity.
    - apply fold_left_pick_max_dominates. left; assumption.
  Qed.

  Theorem brute_match_optimal_among_perms :
    forall boxes gts perm,
      Permutation gts perm ->
      matching_weight cost (matching_from_perm boxes perm) <=
      matching_weight cost (brute_match boxes gts).
  Proof.
    intros boxes gts perm Hperm.
    apply brute_match_optimal_in_enumeration.
    unfold all_brute_matchings.
    apply in_map_iff. exists perm. split; [reflexivity|].
    apply permutation_in_perms. assumption.
  Qed.

End BruteForceMatching.

Local Close Scope R_scope.



Definition geom_tight (n : nat) : list (@det pixel) :=
  map (fun k : nat => mkDet (n - k) (0%nat, k)) (seq 0 n).

Lemma geom_tight_length :
  forall n, length (geom_tight n) = n.
Proof.
  intros n. unfold geom_tight. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma geom_tight_in :
  forall n d, In d (geom_tight n) ->
    exists k, k < n /\ d = mkDet (n - k) (0%nat, k).
Proof.
  intros n d Hin. unfold geom_tight in Hin.
  apply in_map_iff in Hin as [k [Heq Hkin]].
  apply in_seq in Hkin. exists k. split; [lia | symmetry; assumption].
Qed.

Lemma geom_tight_NoDup :
  forall n, NoDup (geom_tight n).
Proof.
  intros n. unfold geom_tight.
  pose proof (seq_NoDup n 0) as Hnd.
  remember (seq 0 n) as l. clear Heql.
  induction Hnd as [|k rest Hnotin Hnd' IH]; simpl.
  - constructor.
  - constructor; [|exact IH].
    intros Hin. apply Hnotin.
    apply in_map_iff in Hin as [k' [Heq Hkin]].
    apply (f_equal (fun d : @det pixel => snd (box d))) in Heq.
    cbn in Heq. subst k'. assumption.
Qed.

Lemma sorted_desc_geom_tight_helper :
  forall n start m,
    sorted_desc (map (fun k : nat => mkDet (n - k) (0%nat, k)) (seq start m)).
Proof.
  intros n start m. revert start.
  induction m as [|m IH]; intros start; simpl; [exact I|].
  split.
  - intros d' Hd'. apply in_map_iff in Hd' as [k' [Heq Hkin]].
    apply in_seq in Hkin. subst d'. cbn [score]. lia.
  - apply IH.
Qed.

Lemma geom_tight_sorted_desc :
  forall n, sorted_desc (geom_tight n).
Proof. intros n. apply sorted_desc_geom_tight_helper. Qed.

Lemma pdist_zero_x :
  forall a b, pdist (0%nat, a) (0%nat, b) = abs_diff a b.
Proof.
  intros a b. unfold pdist, abs_diff. cbn.
  destruct (Nat.leb a b) eqn:E; lia.
Qed.

Lemma abs_diff_lt :
  forall a b m, a < m -> b < m -> abs_diff a b < m.
Proof.
  intros a b m Ha Hb. unfold abs_diff. destruct (Nat.leb_spec a b); lia.
Qed.

Lemma geom_tight_pairs_high_iou :
  forall n d d', In d (geom_tight n) -> In d' (geom_tight n) ->
    heatmap_iou n (box d) (box d') = 1.
Proof.
  intros n d d' Hin Hin'.
  apply geom_tight_in in Hin as [k [Hk Hd_eq]].
  apply geom_tight_in in Hin' as [k' [Hk' Hd'_eq]].
  subst d d'. cbn [box].
  unfold heatmap_iou. rewrite pdist_zero_x.
  destruct (Nat.leb_spec (abs_diff k k') n); [reflexivity|].
  exfalso. pose proof (@abs_diff_lt k k' n Hk Hk'). lia.
Qed.

Lemma geom_tight_no_tie_clash :
  forall n, no_tie_clash (heatmap_iou n) 1 (geom_tight n).
Proof.
  intros n d d' Hin Hin' Hne Hscore_eq.
  exfalso. apply Hne.
  apply geom_tight_in in Hin as [k [Hk Hd_eq]].
  apply geom_tight_in in Hin' as [k' [Hk' Hd'_eq]].
  subst d d'. cbn [score] in Hscore_eq.
  assert (k = k') by lia. subst k'. reflexivity.
Qed.

(** ** General helper: NMS reduces a list to its head when every tail
    element has IoU at least [tau] with the head. *)

Lemma nms_sorted_drops_all_high_iou :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau : nat)
         (d0 : @det Box) (rest : list (@det Box)),
    (forall d', In d' rest -> tau <= iou (box d0) (box d')) ->
    nms_sorted iou tau (d0 :: rest) = [d0].
Proof.
  intros Box iou tau d0 rest Hall.
  rewrite nms_sorted_equation. f_equal.
  assert (Hf : filter (fun d' =>
                         negb (Nat.leb tau (iou (box d0) (box d'))))
                      rest = []).
  { induction rest as [|d rs IH]; simpl; [reflexivity|].
    assert (Htau_le : tau <= iou (box d0) (box d))
      by (apply Hall; left; reflexivity).
    apply Nat.leb_le in Htau_le. rewrite Htau_le. cbn [negb].
    apply IH. intros d'' Hd''. apply Hall. right. assumption. }
  rewrite Hf. apply nms_sorted_equation.
Qed.

(** ** All scores in [geom_tight n] are at least 1. *)

Lemma filter_above_1_geom_tight :
  forall n, filter_above 1 (geom_tight n) = geom_tight n.
Proof.
  intros n. unfold filter_above. apply filter_id_when_pred_holds.
  intros d Hin. unfold above.
  apply geom_tight_in in Hin as [k [Hk Heq]]. subst d. cbn [score].
  apply Nat.leb_le. lia.
Qed.

(** ** [nms_sorted] reduces [geom_tight n] to its head element. *)

Lemma nms_sorted_geom_tight :
  forall n,
    nms_sorted (heatmap_iou n) 1 (geom_tight n) =
    match n with
    | O => []
    | S k => [mkDet (S k) (0%nat, 0%nat)]
    end.
Proof.
  intros n. destruct n as [|n']; [reflexivity|].
  unfold geom_tight. cbn [seq map].
  replace (S n' - 0) with (S n') by lia.
  apply nms_sorted_drops_all_high_iou.
  intros d' Hd'. apply in_map_iff in Hd' as [k [Heq Hkin]].
  apply in_seq in Hkin. subst d'.
  cbn [box]. unfold heatmap_iou.
  rewrite pdist_zero_x.
  unfold abs_diff.
  assert (Hk0 : Nat.leb 0 k = true) by (apply Nat.leb_le; lia).
  rewrite Hk0.
  rewrite Nat.sub_0_r.
  destruct (Nat.leb_spec k (S n')); [lia | lia].
Qed.

(** ** Each element's [has_higher_overlapper] flag agrees with
    [score < n]: the top-score element (k = 0) has none, every other
    element has the head as a higher-scored overlapper. *)

Lemma head_in_geom_tight :
  forall n', In (mkDet (S n') (0%nat, 0%nat)) (geom_tight (S n')).
Proof.
  intros n'. unfold geom_tight. cbn [seq map].
  replace (S n' - 0) with (S n') by lia. left. reflexivity.
Qed.

Lemma has_higher_overlapper_geom_tight :
  forall n d, In d (geom_tight n) ->
    has_higher_overlapper (heatmap_iou n) 1 (geom_tight n) d =
    Nat.ltb (score d) n.
Proof.
  intros n d Hin.
  pose proof Hin as Hin_save.
  apply geom_tight_in in Hin as [k [Hk Hd_eq]]. subst d.
  cbn [score].
  destruct n as [|n']; [lia|].
  unfold has_higher_overlapper.
  destruct (Nat.ltb_spec (S n' - k) (S n')) as [Hlt | Hge].
  - apply existsb_exists.
    exists (mkDet (S n') (0%nat, 0%nat)).
    split; [apply head_in_geom_tight|].
    apply Bool.andb_true_iff. split.
    + apply Nat.ltb_lt. cbn [score]. exact Hlt.
    + apply Nat.leb_le.
      rewrite (geom_tight_pairs_high_iou (S n')
                (mkDet (S n' - k) (0%nat, k))
                (mkDet (S n') (0%nat, 0%nat))); [lia|exact Hin_save|].
      apply head_in_geom_tight.
  - apply Bool.not_true_is_false. intros Hex.
    apply existsb_exists in Hex as [d' [Hin' Hcond]].
    apply Bool.andb_true_iff in Hcond as [Hlt _].
    apply Nat.ltb_lt in Hlt.
    apply geom_tight_in in Hin' as [k' [Hk' Hd'_eq]]. subst d'.
    cbn [score] in Hlt. lia.
Qed.

(** ** Violator-above of [geom_tight n] is the tail (all but the head). *)

Lemma violator_above_geom_tight_helper :
  forall n' l,
    (forall k, In k l -> k < S n') ->
    filter (fun d : @det pixel =>
      above 1 d &&
      has_higher_overlapper (heatmap_iou (S n')) 1 (geom_tight (S n')) d)
      (map (fun k : nat => mkDet (S n' - k) (0%nat, k)) l) =
    map (fun k : nat => mkDet (S n' - k) (0%nat, k))
        (filter (fun k => negb (Nat.eqb k 0)) l).
Proof.
  intros n' l Hbnd.
  induction l as [|k rest IH].
  - reflexivity.
  - cbn [map filter].
    assert (Hk : k < S n') by (apply Hbnd; left; reflexivity).
    assert (Hk_in_geom : In (mkDet (S n' - k) (0%nat, k)) (geom_tight (S n'))).
    { unfold geom_tight. apply in_map_iff. exists k. split; [reflexivity|].
      apply in_seq. lia. }
    rewrite (has_higher_overlapper_geom_tight (S n') _ Hk_in_geom).
    unfold above. cbn [score].
    destruct (Nat.eq_dec k 0) as [Hk0 | Hk0].
    + subst k. rewrite Nat.sub_0_r.
      rewrite Nat.ltb_irrefl. rewrite Bool.andb_false_r.
      cbn [Nat.eqb negb].
      apply IH. intros k' Hk'_in. apply Hbnd. right. assumption.
    + assert (Hleb : Nat.leb 1 (S n' - k) = true)
        by (apply Nat.leb_le; lia).
      assert (Hltb : Nat.ltb (S n' - k) (S n') = true)
        by (apply Nat.ltb_lt; lia).
      rewrite Hleb, Hltb. cbn [andb].
      assert (Hkneq : Nat.eqb k 0 = false) by (apply Nat.eqb_neq; lia).
      rewrite Hkneq. cbn [negb map].
      f_equal. apply IH. intros k' Hk'_in. apply Hbnd. right. assumption.
Qed.

Lemma violation_count_geom_tight :
  forall n, violation_count (heatmap_iou n) 1 1 (geom_tight n) = n - 1.
Proof.
  intros n. unfold violation_count, violator_above.
  destruct n as [|n']; [reflexivity|].
  unfold geom_tight at 2.
  rewrite (@violator_above_geom_tight_helper n' (seq 0 (S n'))).
  - rewrite length_map.
    cbn [seq filter].
    cbn [Nat.eqb negb].
    assert (Hkeep : forall k, In k (seq 1 n') ->
                    negb (Nat.eqb k 0) = true).
    { intros k Hk. apply in_seq in Hk. apply Bool.negb_true_iff.
      apply Nat.eqb_neq. lia. }
    rewrite (@filter_id_when_pred_holds nat
               (fun k : nat => negb (Nat.eqb k 0)) (seq 1 n') Hkeep).
    rewrite length_seq. lia.
  - intros k Hk. apply in_seq in Hk. lia.
Qed.

(** ** Headline saturation theorem: geometric witness saturates
    [nms_quantitative_bound] at equality. *)

Theorem geom_tight_quantitative_saturation :
  forall n,
    length (filter_above 1 (geom_tight n))
    = length (filter_above 1 (nms_sorted (heatmap_iou n) 1 (geom_tight n)))
      + violation_count (heatmap_iou n) 1 1 (geom_tight n).
Proof.
  intros n.
  rewrite filter_above_1_geom_tight.
  rewrite geom_tight_length.
  rewrite nms_sorted_geom_tight.
  rewrite violation_count_geom_tight.
  destruct n as [|k]; [reflexivity|].
  unfold filter_above. cbn [filter]. unfold above. cbn [score].
  assert (Hlt : Nat.leb 1 (S k) = true) by (apply Nat.leb_le; lia).
  rewrite Hlt. simpl. lia.
Qed.



Local Open Scope R_scope.

(** ** Round-to-nearest-even integer rounding. *)

Definition round_half_even (x : R) : Z :=
  let n := Int_part x in
  let f := x - IZR n in
  if Rlt_dec f (/2) then n
  else if Rlt_dec (/2) f then (n + 1)%Z
  else if Z.even n then n else (n + 1)%Z.

Theorem round_half_even_bounded :
  forall x, Rabs (IZR (round_half_even x) - x) <= /2.
Proof.
  intros x. unfold round_half_even.
  pose proof (base_Int_part x) as [Hlo Hhi].
  destruct (Rlt_dec (x - IZR (Int_part x)) (/2)) as [Hlt | Hge].
  - rewrite Rabs_left1 by lra. lra.
  - destruct (Rlt_dec (/2) (x - IZR (Int_part x))) as [Hlt2 | Hge2].
    + rewrite plus_IZR. simpl.
      rewrite Rabs_right by lra. lra.
    + assert (Hmid : x - IZR (Int_part x) = /2) by lra.
      destruct (Z.even (Int_part x)) eqn:E.
      * rewrite Rabs_left1 by lra. lra.
      * rewrite plus_IZR. simpl.
        rewrite Rabs_right by lra. lra.
Qed.

Theorem round_half_even_midpoint_even :
  forall x, x = IZR (Int_part x) + /2 ->
            Z.even (round_half_even x) = true.
Proof.
  intros x Heq.
  unfold round_half_even.
  destruct (Rlt_dec (x - IZR (Int_part x)) (/2)) as [Hlt | _]; [lra|].
  destruct (Rlt_dec (/2) (x - IZR (Int_part x))) as [Hlt2 | _]; [lra|].
  destruct (Z.even (Int_part x)) eqn:E.
  - exact E.
  - rewrite Z.even_add. rewrite E. reflexivity.
Qed.

(** ** Round-to-nearest-even quantizer at precision [q]. *)

Definition fp_quantize_rne (q x : R) : R := IZR (round_half_even (x / q)) * q.

Theorem fp_quantize_rne_bounded_error :
  forall q x, 0 < q -> Rabs (fp_quantize_rne q x - x) <= q / 2.
Proof.
  intros q x Hq. unfold fp_quantize_rne.
  pose proof (round_half_even_bounded (x / q)) as Hbnd.
  assert (Heq : IZR (round_half_even (x / q)) * q - x =
                (IZR (round_half_even (x / q)) - x / q) * q).
  { field. lra. }
  rewrite Heq, Rabs_mult, (Rabs_right q) by lra.
  apply Rmult_le_reg_r with (r := / q); [apply Rinv_0_lt_compat; lra|].
  rewrite Rmult_assoc, Rinv_r by lra.
  rewrite Rmult_1_r.
  replace (q / 2 * / q) with (/ 2) by (field; lra).
  exact Hbnd.
Qed.

(** ** Subnormal-range quantizer.

    Below the normal-range threshold [|x| < 2^{-1022}], IEEE 754
    binary64 represents values at the fixed precision [2^{-1074}]
    (the smallest representable step), with absolute-error bound
    [2^{-1075}] (half-ULP). *)

Definition b64_subnormal_q : R := powerRZ 2 (-1074).

Definition b64_subnormal_quantize : R -> R := fp_quantize b64_subnormal_q.

Theorem b64_subnormal_bounded_error :
  forall x, Rabs (b64_subnormal_quantize x - x) <= powerRZ 2 (-1075).
Proof.
  intros x. unfold b64_subnormal_quantize, b64_subnormal_q.
  pose proof (powerRZ_2_pos (-1074)) as Hpos.
  pose proof (@fp_quantize_bounded_error (powerRZ 2 (-1074)) x Hpos) as H.
  apply Rle_trans with (powerRZ 2 (-1074) / 2); [exact H|].
  replace (-1074)%Z with ((-1075) + 1)%Z by lia.
  rewrite powerRZ_add by lra.
  simpl. lra.
Qed.

Local Close Scope R_scope.

(** ** IEEE 754 special-value algebra. *)

Inductive b64_value : Type :=
  | b64_v : R -> b64_value
  | b64_pinf : b64_value
  | b64_ninf : b64_value
  | b64_nan : b64_value.

Local Open Scope R_scope.

Definition b64_add (a b : b64_value) : b64_value :=
  match a, b with
  | b64_nan, _ => b64_nan
  | _, b64_nan => b64_nan
  | b64_pinf, b64_ninf => b64_nan
  | b64_ninf, b64_pinf => b64_nan
  | b64_pinf, _ => b64_pinf
  | _, b64_pinf => b64_pinf
  | b64_ninf, _ => b64_ninf
  | _, b64_ninf => b64_ninf
  | b64_v x, b64_v y => b64_v (x + y)
  end.

Definition b64_neg (a : b64_value) : b64_value :=
  match a with
  | b64_v x => b64_v (- x)
  | b64_pinf => b64_ninf
  | b64_ninf => b64_pinf
  | b64_nan => b64_nan
  end.

Definition b64_sub (a b : b64_value) : b64_value := b64_add a (b64_neg b).

Definition b64_mul (a b : b64_value) : b64_value :=
  match a, b with
  | b64_nan, _ => b64_nan
  | _, b64_nan => b64_nan
  | b64_pinf, b64_pinf => b64_pinf
  | b64_ninf, b64_ninf => b64_pinf
  | b64_pinf, b64_ninf => b64_ninf
  | b64_ninf, b64_pinf => b64_ninf
  | b64_pinf, b64_v x =>
      if Rlt_dec 0 x then b64_pinf
      else if Rlt_dec x 0 then b64_ninf
      else b64_nan
  | b64_v x, b64_pinf =>
      if Rlt_dec 0 x then b64_pinf
      else if Rlt_dec x 0 then b64_ninf
      else b64_nan
  | b64_ninf, b64_v x =>
      if Rlt_dec 0 x then b64_ninf
      else if Rlt_dec x 0 then b64_pinf
      else b64_nan
  | b64_v x, b64_ninf =>
      if Rlt_dec 0 x then b64_ninf
      else if Rlt_dec x 0 then b64_pinf
      else b64_nan
  | b64_v x, b64_v y => b64_v (x * y)
  end.

Definition b64_lt (a b : b64_value) : bool :=
  match a, b with
  | b64_nan, _ => false
  | _, b64_nan => false
  | b64_ninf, b64_ninf => false
  | b64_ninf, _ => true
  | _, b64_ninf => false
  | b64_pinf, b64_pinf => false
  | b64_pinf, _ => false
  | _, b64_pinf => true
  | b64_v x, b64_v y => if Rlt_dec x y then true else false
  end.

(** ** Propagation theorems. *)

Theorem b64_add_nan_l : forall a, b64_add b64_nan a = b64_nan.
Proof. destruct a; reflexivity. Qed.

Theorem b64_add_nan_r : forall a, b64_add a b64_nan = b64_nan.
Proof. destruct a; reflexivity. Qed.

Theorem b64_add_pinf_ninf : b64_add b64_pinf b64_ninf = b64_nan.
Proof. reflexivity. Qed.

Theorem b64_add_ninf_pinf : b64_add b64_ninf b64_pinf = b64_nan.
Proof. reflexivity. Qed.

Theorem b64_add_pinf_finite :
  forall x, b64_add b64_pinf (b64_v x) = b64_pinf.
Proof. reflexivity. Qed.

Theorem b64_add_finite_pinf :
  forall x, b64_add (b64_v x) b64_pinf = b64_pinf.
Proof. reflexivity. Qed.

Theorem b64_add_ninf_finite :
  forall x, b64_add b64_ninf (b64_v x) = b64_ninf.
Proof. reflexivity. Qed.

Theorem b64_add_finite : forall x y, b64_add (b64_v x) (b64_v y) = b64_v (x + y).
Proof. reflexivity. Qed.

Theorem b64_neg_neg : forall a, b64_neg (b64_neg a) = a.
Proof.
  destruct a; simpl; try reflexivity.
  f_equal. lra.
Qed.

Theorem b64_sub_self_finite : forall x, b64_sub (b64_v x) (b64_v x) = b64_v 0.
Proof.
  intros x. unfold b64_sub. simpl.
  f_equal. lra.
Qed.

Theorem b64_sub_pinf_pinf : b64_sub b64_pinf b64_pinf = b64_nan.
Proof. reflexivity. Qed.

Theorem b64_sub_ninf_ninf : b64_sub b64_ninf b64_ninf = b64_nan.
Proof. reflexivity. Qed.

Theorem b64_mul_nan_l : forall a, b64_mul b64_nan a = b64_nan.
Proof. destruct a; reflexivity. Qed.

Theorem b64_mul_nan_r : forall a, b64_mul a b64_nan = b64_nan.
Proof. destruct a; reflexivity. Qed.

Theorem b64_mul_zero_pinf : b64_mul (b64_v 0) b64_pinf = b64_nan.
Proof.
  simpl. destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

Theorem b64_mul_pinf_zero : b64_mul b64_pinf (b64_v 0) = b64_nan.
Proof.
  simpl. destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

Theorem b64_mul_zero_ninf : b64_mul (b64_v 0) b64_ninf = b64_nan.
Proof.
  simpl. destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

Theorem b64_mul_ninf_zero : b64_mul b64_ninf (b64_v 0) = b64_nan.
Proof.
  simpl. destruct (Rlt_dec 0 0); [lra|].
  destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

Theorem b64_mul_pinf_pinf : b64_mul b64_pinf b64_pinf = b64_pinf.
Proof. reflexivity. Qed.

Theorem b64_mul_ninf_ninf : b64_mul b64_ninf b64_ninf = b64_pinf.
Proof. reflexivity. Qed.

Theorem b64_mul_pinf_ninf : b64_mul b64_pinf b64_ninf = b64_ninf.
Proof. reflexivity. Qed.

Theorem b64_mul_ninf_pinf : b64_mul b64_ninf b64_pinf = b64_ninf.
Proof. reflexivity. Qed.

Theorem b64_mul_finite : forall x y, b64_mul (b64_v x) (b64_v y) = b64_v (x * y).
Proof. reflexivity. Qed.

Theorem b64_lt_nan_l : forall a, b64_lt b64_nan a = false.
Proof. destruct a; reflexivity. Qed.

Theorem b64_lt_nan_r : forall a, b64_lt a b64_nan = false.
Proof. destruct a; reflexivity. Qed.

Theorem b64_lt_irrefl_finite : forall x, b64_lt (b64_v x) (b64_v x) = false.
Proof.
  intros x. simpl. destruct (Rlt_dec x x); [lra | reflexivity].
Qed.

Theorem b64_lt_ninf_pinf : b64_lt b64_ninf b64_pinf = true.
Proof. reflexivity. Qed.

Theorem b64_lt_ninf_finite : forall x, b64_lt b64_ninf (b64_v x) = true.
Proof. reflexivity. Qed.

Theorem b64_lt_finite_pinf : forall x, b64_lt (b64_v x) b64_pinf = true.
Proof. reflexivity. Qed.

Theorem b64_lt_pinf_l : forall a, a <> b64_nan -> a <> b64_pinf -> b64_lt a b64_pinf = true.
Proof. destruct a; intros H1 H2; [reflexivity | exfalso; apply H2; reflexivity | reflexivity | exfalso; apply H1; reflexivity]. Qed.




Local Open Scope R_scope.

(** ** Soundness of permutation enumeration. *)

Theorem in_perms_permutation :
  forall {A : Type} (l p : list A), In p (perms l) -> Permutation l p.
Proof.
  intros A l. induction l as [|x rest IH]; intros p Hin.
  - simpl in Hin. destruct Hin as [Heq | []]. subst. apply Permutation_refl.
  - simpl in Hin. apply in_flat_map in Hin as [p0 [Hp0_in Hp_in]].
    apply IH in Hp0_in.
    apply in_insert_each_pos_iff in Hp_in as [l1 [l2 [Heq Hp_eq]]].
    subst p0. subst p.
    eapply Permutation_trans.
    + apply perm_skip. exact Hp0_in.
    + apply Permutation_cons_app. apply Permutation_refl.
Qed.

Section DPMatching.
  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.
  Variable GT_eq_dec : forall g1 g2 : GT, {g1 = g2} + {g1 <> g2}.

  Fixpoint dp_remove_first (g : GT) (l : list GT) : list GT :=
    match l with
    | [] => []
    | h :: rest =>
        if GT_eq_dec h g then rest else h :: dp_remove_first g rest
    end.

  Lemma dp_remove_first_in_split :
    forall g l, In g l ->
      exists l1 l2, l = l1 ++ g :: l2 /\ dp_remove_first g l = l1 ++ l2.
  Proof.
    induction l as [|h rest IH]; intros Hin; simpl in Hin; [contradiction|].
    simpl. destruct (GT_eq_dec h g) as [Heq | Hne].
    - subst h. exists [], rest. split; reflexivity.
    - destruct Hin as [Heq | Hin]; [contradiction|].
      destruct (IH Hin) as [l1 [l2 [Heq_split Hrm]]].
      exists (h :: l1), l2. split.
      + simpl. f_equal. exact Heq_split.
      + simpl. f_equal. exact Hrm.
  Qed.

  Theorem dp_remove_first_perm :
    forall g l, In g l -> Permutation l (g :: dp_remove_first g l).
  Proof.
    intros g l Hin.
    destruct (dp_remove_first_in_split g l Hin) as [l1 [l2 [Heq_split Hrm]]].
    rewrite Hrm. rewrite Heq_split.
    apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl.
  Qed.

  Lemma dp_remove_first_NoDup :
    forall g l, NoDup l -> NoDup (dp_remove_first g l).
  Proof.
    induction l as [|h rest IH]; intros Hnd; simpl; [constructor|].
    destruct (GT_eq_dec h g) as [Heq | Hne].
    - inversion Hnd; assumption.
    - inversion Hnd as [|? ? Hnotin Hnd_rest]; subst.
      constructor.
      + intros Hin. apply Hnotin.
        clear -Hin. induction rest as [|x xs IHx]; simpl in Hin;
          [contradiction|].
        simpl in Hin. destruct (GT_eq_dec x g) as [Heq | Hne'].
        * right. assumption.
        * destruct Hin as [Heq | Hin]; [left; assumption|].
          right. apply IHx. assumption.
      + apply IH. assumption.
  Qed.

  (** ** Max over a non-empty list with explicit head. *)

  Definition Rmax_list (init : R) (l : list R) : R :=
    fold_right Rmax init l.

  Lemma Rmax_list_init_le :
    forall init l, init <= Rmax_list init l.
  Proof.
    intros init l. unfold Rmax_list.
    induction l as [|y ys IH]; simpl; [apply Rle_refl|].
    eapply Rle_trans; [exact IH|]. apply Rmax_r.
  Qed.

  Lemma Rmax_list_in_le :
    forall init l x, In x l -> x <= Rmax_list init l.
  Proof.
    intros init l x Hin. unfold Rmax_list.
    induction l as [|y ys IH]; simpl in Hin; [contradiction|].
    simpl. destruct Hin as [Heq | Hin].
    - subst y. apply Rmax_l.
    - eapply Rle_trans; [apply IH; assumption|]. apply Rmax_r.
  Qed.

  Lemma Rmax_list_witness :
    forall init l,
      Rmax_list init l = init \/ exists x, In x l /\ Rmax_list init l = x.
  Proof.
    intros init l. unfold Rmax_list.
    induction l as [|y ys IH]; simpl.
    - left. reflexivity.
    - destruct IH as [IH | [w [Hw_in Hw_eq]]].
      + rewrite IH.
        destruct (Rle_or_lt y init) as [Hle | Hgt].
        * left. apply Rmax_right. assumption.
        * right. exists y. split; [left; reflexivity|].
          apply Rmax_left. lra.
      + rewrite Hw_eq.
        destruct (Rle_or_lt y w) as [Hle | Hgt].
        * right. exists w. split; [right; assumption|].
          apply Rmax_right. assumption.
        * right. exists y. split; [left; reflexivity|].
          apply Rmax_left. lra.
  Qed.

  (** ** Dynamic-programming optimal matcher.

      [dp_max_match boxes gts] returns the maximum total cost of any
      injective assignment of boxes to gts, taking the first
      candidate as the [Rmax_list] init so the result equals the
      true maximum (not [0]) when all candidates are negative. *)

  Fixpoint dp_max_match (boxes : list Box) (gts : list GT) : R :=
    match boxes with
    | [] => 0
    | b :: rest =>
        match gts with
        | [] => 0
        | g0 :: _ =>
            Rmax_list
              (cost b g0 + dp_max_match rest (dp_remove_first g0 gts))
              (map (fun g =>
                       cost b g + dp_max_match rest (dp_remove_first g gts))
                   gts)
        end
    end.

  (** ** Unfolding lemma keeps dp_remove_first folded when stepping. *)

  Lemma dp_max_match_cons_cons :
    forall (b : Box) (rest : list Box) (g0 : GT) (gs : list GT),
      dp_max_match (b :: rest) (g0 :: gs) =
      Rmax_list
        (cost b g0 + dp_max_match rest (dp_remove_first g0 (g0 :: gs)))
        (map (fun g =>
                 cost b g + dp_max_match rest (dp_remove_first g (g0 :: gs)))
             (g0 :: gs)).
  Proof. intros. reflexivity. Qed.

  (** ** matching_from_perm and matching_weight decomposition. *)

  Lemma matching_from_perm_cons :
    forall (b : Box) (rest : list Box) (h : GT) (tail : list GT),
      matching_from_perm (b :: rest) (h :: tail) =
      (b, h) :: matching_from_perm rest tail.
  Proof.
    intros. unfold matching_from_perm. simpl. reflexivity.
  Qed.

  Lemma matching_from_perm_empty_perm :
    forall (boxes : list Box),
      matching_from_perm boxes (@nil GT) = (@nil (Box * GT)).
  Proof.
    intros. unfold matching_from_perm. simpl.
    destruct boxes; reflexivity.
  Qed.

  Lemma matching_from_perm_empty_boxes :
    forall (perm : list GT),
      matching_from_perm (@nil Box) perm = (@nil (Box * GT)).
  Proof.
    intros. unfold matching_from_perm. simpl. reflexivity.
  Qed.

  Lemma matching_weight_cons :
    forall (b : Box) (g : GT) (rest : list (Box * GT)),
      matching_weight cost ((b, g) :: rest) =
      cost b g + matching_weight cost rest.
  Proof.
    intros. unfold matching_weight. simpl. reflexivity.
  Qed.

  Lemma matching_weight_nil :
    matching_weight cost (@nil (Box * GT)) = 0.
  Proof. unfold matching_weight. simpl. reflexivity. Qed.

  (** ** Theorem 3: dp dominates any perm-derived matching weight. *)

  Theorem dp_max_match_ge_perm :
    forall boxes gts perm,
      NoDup gts ->
      Permutation perm gts ->
      matching_weight cost (matching_from_perm boxes perm) <=
      dp_max_match boxes gts.
  Proof.
    induction boxes as [|b rest IH]; intros gts perm Hnd Hperm.
    - rewrite matching_from_perm_empty_boxes, matching_weight_nil.
      simpl. apply Rle_refl.
    - destruct gts as [|g0 gs] eqn:Egts.
      + apply Permutation_sym, Permutation_nil in Hperm. subst perm.
        rewrite matching_from_perm_empty_perm, matching_weight_nil.
        simpl. apply Rle_refl.
      + assert (Hperm_len : length perm = length (g0 :: gs))
          by (apply Permutation_length; assumption).
        destruct perm as [|h ptail]; [discriminate|].
        assert (Hh_in : In h (g0 :: gs)).
        { apply Permutation_in with (h :: ptail);
            [assumption | left; reflexivity]. }
        assert (Hperm_tail : Permutation ptail (dp_remove_first h (g0 :: gs))).
        { destruct (dp_remove_first_in_split h (g0 :: gs) Hh_in)
            as [l1 [l2 [Heq_split Hrm]]].
          rewrite Hrm.
          rewrite Heq_split in Hperm.
          apply Permutation_cons_app_inv in Hperm.
          exact Hperm. }
        assert (Hnd_rm : NoDup (dp_remove_first h (g0 :: gs))).
        { apply dp_remove_first_NoDup. assumption. }
        rewrite matching_from_perm_cons.
        rewrite matching_weight_cons.
        pose proof (IH _ ptail Hnd_rm Hperm_tail) as IH_app.
        eapply Rle_trans.
        * apply Rplus_le_compat_l. exact IH_app.
        * rewrite dp_max_match_cons_cons.
          destruct Hh_in as [Heq | Hin_gs].
          ** subst h. apply Rmax_list_init_le.
          ** apply Rmax_list_in_le.
             apply in_map_iff. exists h. split; [reflexivity|].
             right. assumption.
  Qed.

  (** ** Theorem 4: some permutation-derived matching achieves dp's value. *)

  Theorem dp_max_match_le_some_perm :
    forall boxes gts,
      NoDup gts ->
      exists perm, Permutation perm gts /\
                   dp_max_match boxes gts <=
                   matching_weight cost (matching_from_perm boxes perm).
  Proof.
    induction boxes as [|b rest IH]; intros gts Hnd.
    - exists gts. split; [apply Permutation_refl|].
      rewrite matching_from_perm_empty_boxes, matching_weight_nil.
      simpl. apply Rle_refl.
    - destruct gts as [|g0 gs] eqn:Egts.
      + exists []. split; [apply Permutation_refl|].
        rewrite matching_from_perm_empty_perm, matching_weight_nil.
        simpl. apply Rle_refl.
      + rewrite dp_max_match_cons_cons.
        destruct (Rmax_list_witness
                    (cost b g0 + dp_max_match rest (dp_remove_first g0 (g0 :: gs)))
                    (map (fun g =>
                             cost b g + dp_max_match rest (dp_remove_first g (g0 :: gs)))
                         (g0 :: gs)))
          as [Hinit | [w [Hw_in Hw_eq]]].
        * assert (Hg0_in : In g0 (g0 :: gs)) by (left; reflexivity).
          assert (Hnd_rm : NoDup (dp_remove_first g0 (g0 :: gs)))
            by (apply dp_remove_first_NoDup; assumption).
          destruct (IH (dp_remove_first g0 (g0 :: gs)) Hnd_rm)
            as [perm_rest [Hperm_rest Hperm_le]].
          exists (g0 :: perm_rest). split.
          ** apply Permutation_sym.
             eapply Permutation_trans;
               [apply (dp_remove_first_perm g0 (g0 :: gs) Hg0_in)|].
             apply perm_skip. apply Permutation_sym. assumption.
          ** rewrite matching_from_perm_cons, matching_weight_cons.
             rewrite Hinit.
             apply Rplus_le_compat_l. exact Hperm_le.
        * apply in_map_iff in Hw_in as [g_opt [Heq_w Hg_in]].
          subst w.
          assert (Hnd_rm : NoDup (dp_remove_first g_opt (g0 :: gs)))
            by (apply dp_remove_first_NoDup; assumption).
          destruct (IH (dp_remove_first g_opt (g0 :: gs)) Hnd_rm)
            as [perm_rest [Hperm_rest Hperm_le]].
          exists (g_opt :: perm_rest). split.
          ** apply Permutation_sym.
             eapply Permutation_trans;
               [apply (dp_remove_first_perm g_opt (g0 :: gs) Hg_in)|].
             apply perm_skip. apply Permutation_sym. assumption.
          ** rewrite matching_from_perm_cons, matching_weight_cons.
             rewrite Hw_eq.
             apply Rplus_le_compat_l. exact Hperm_le.
  Qed.

  (** ** Theorem 5: dp_max_match equals brute_match's weight. *)

  Theorem dp_max_match_eq_brute_weight :
    forall boxes gts,
      NoDup gts ->
      dp_max_match boxes gts = matching_weight cost (brute_match cost boxes gts).
  Proof.
    intros boxes gts Hnd. apply Rle_antisym.
    - destruct (dp_max_match_le_some_perm boxes Hnd)
        as [perm [Hperm Hle]].
      eapply Rle_trans; [exact Hle|].
      apply (brute_match_optimal_in_enumeration cost boxes gts
              (matching_from_perm boxes perm)).
      unfold all_brute_matchings. apply in_map_iff.
      exists perm. split; [reflexivity|].
      apply permutation_in_perms. apply Permutation_sym. assumption.
    - pose proof (brute_match_in_enumeration cost boxes gts) as Hbrute_in.
      unfold all_brute_matchings in Hbrute_in.
      apply in_map_iff in Hbrute_in as [perm_b [Heq_b Hperm_b_in]].
      pose proof (in_perms_permutation gts perm_b Hperm_b_in) as Hperm_b.
      rewrite <- Heq_b.
      apply (dp_max_match_ge_perm boxes Hnd).
      apply Permutation_sym. assumption.
  Qed.

End DPMatching.

Local Close Scope R_scope.



Local Open Scope R_scope.

Section AssignmentDuality.
  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.

  Definition list_sum_R {A : Type} (f : A -> R) (l : list A) : R :=
    fold_right (fun x acc => f x + acc) 0 l.

  Lemma list_sum_R_app :
    forall {A : Type} (f : A -> R) (l1 l2 : list A),
      list_sum_R f (l1 ++ l2) = list_sum_R f l1 + list_sum_R f l2.
  Proof.
    intros A f l1 l2. unfold list_sum_R.
    induction l1 as [|x rest IH]; simpl; [lra|].
    rewrite IH. lra.
  Qed.

  Lemma list_sum_R_perm :
    forall {A : Type} (f : A -> R) (l l' : list A),
      Permutation l l' -> list_sum_R f l = list_sum_R f l'.
  Proof.
    intros A f l l' Hperm.
    induction Hperm; simpl; try reflexivity.
    - simpl. unfold list_sum_R in *. simpl. rewrite IHHperm. reflexivity.
    - simpl. unfold list_sum_R. simpl. lra.
    - rewrite IHHperm1. exact IHHperm2.
  Qed.

  Lemma list_sum_R_le :
    forall {A : Type} (f g : A -> R) (l : list A),
      (forall x, In x l -> f x <= g x) ->
      list_sum_R f l <= list_sum_R g l.
  Proof.
    intros A f g l Hle. unfold list_sum_R.
    induction l as [|x rest IH]; simpl; [apply Rle_refl|].
    apply Rplus_le_compat.
    - apply Hle. left. reflexivity.
    - apply IH. intros y Hy. apply Hle. right. assumption.
  Qed.

  Lemma list_sum_R_eq :
    forall {A : Type} (f g : A -> R) (l : list A),
      (forall x, In x l -> f x = g x) ->
      list_sum_R f l = list_sum_R g l.
  Proof.
    intros A f g l Heq. unfold list_sum_R.
    induction l as [|x rest IH]; simpl; [reflexivity|].
    rewrite (Heq x (or_introl eq_refl)).
    rewrite (IH (fun y Hy => Heq y (or_intror Hy))).
    reflexivity.
  Qed.

  Lemma list_sum_R_split_pair :
    forall (M : list (Box * GT)) (u : Box -> R) (v : GT -> R),
      list_sum_R (fun p => u (fst p) + v (snd p)) M =
      list_sum_R u (map fst M) + list_sum_R v (map snd M).
  Proof.
    intros M u v. unfold list_sum_R.
    induction M as [|p rest IH]; simpl; [lra|].
    rewrite IH. lra.
  Qed.

  Lemma matching_weight_eq_list_sum :
    forall (M : list (Box * GT)),
      matching_weight cost M = list_sum_R (fun p => cost (fst p) (snd p)) M.
  Proof.
    intros M. unfold matching_weight, list_sum_R.
    induction M as [|p rest IH]; simpl; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  (** ** LP-duality optimality theorem for balanced assignment. *)

  Theorem hungarian_optimal_via_duality :
    forall (boxes : list Box) (gts : list GT)
           (M : list (Box * GT)) (u : Box -> R) (v : GT -> R),
      Permutation (map fst M) boxes ->
      Permutation (map snd M) gts ->
      (forall b g, In b boxes -> In g gts -> u b + v g >= cost b g) ->
      (forall b g, In (b, g) M -> u b + v g = cost b g) ->
      forall M',
        Permutation (map fst M') boxes ->
        Permutation (map snd M') gts ->
        matching_weight cost M' <= matching_weight cost M.
  Proof.
    intros boxes gts M u v Hbox Hgt Hfeas Hslack M' Hbox' Hgt'.
    rewrite !matching_weight_eq_list_sum.
    assert (HsumM : list_sum_R (fun p => cost (fst p) (snd p)) M =
                    list_sum_R u boxes + list_sum_R v gts).
    { rewrite (list_sum_R_eq _ (fun p => u (fst p) + v (snd p))).
      - rewrite list_sum_R_split_pair.
        rewrite (list_sum_R_perm u Hbox).
        rewrite (list_sum_R_perm v Hgt). reflexivity.
      - intros [b g] Hin. simpl. symmetry. apply Hslack. assumption. }
    rewrite HsumM.
    apply Rle_trans with
      (list_sum_R (fun p => u (fst p) + v (snd p)) M').
    - apply list_sum_R_le. intros [b g] Hin. simpl.
      assert (Hb : In b boxes).
      { apply (Permutation_in b Hbox'). apply (in_map fst M' (b, g) Hin). }
      assert (Hg : In g gts).
      { apply (Permutation_in g Hgt'). apply (in_map snd M' (b, g) Hin). }
      pose proof (Hfeas b g Hb Hg). lra.
    - rewrite list_sum_R_split_pair.
      rewrite (list_sum_R_perm u Hbox').
      rewrite (list_sum_R_perm v Hgt'). apply Rle_refl.
  Qed.

End AssignmentDuality.

Section HungarianWitness.
  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.

  Definition is_hungarian_witness
      (boxes : list Box) (gts : list GT)
      (M : list (Box * GT)) (u : Box -> R) (v : GT -> R) : Prop :=
    Permutation (map fst M) boxes /\
    Permutation (map snd M) gts /\
    (forall b g, In b boxes -> In g gts -> u b + v g >= cost b g) /\
    (forall b g, In (b, g) M -> u b + v g = cost b g).

  Theorem hungarian_witness_optimal :
    forall boxes gts M u v,
      is_hungarian_witness boxes gts M u v ->
      forall M',
        Permutation (map fst M') boxes ->
        Permutation (map snd M') gts ->
        matching_weight cost M' <= matching_weight cost M.
  Proof.
    intros boxes gts M u v [Hbox [Hgt [Hfeas Hslack]]] M' Hbox' Hgt'.
    apply (@hungarian_optimal_via_duality Box GT cost boxes gts M u v
             Hbox Hgt Hfeas Hslack M' Hbox' Hgt').
  Qed.

  Theorem hungarian_witness_unique_value :
    forall boxes gts M1 u1 v1 M2 u2 v2,
      is_hungarian_witness boxes gts M1 u1 v1 ->
      is_hungarian_witness boxes gts M2 u2 v2 ->
      matching_weight cost M1 = matching_weight cost M2.
  Proof.
    intros boxes gts M1 u1 v1 M2 u2 v2 H1 H2.
    apply Rle_antisym.
    - destruct H1 as [Hbox1 [Hgt1 _]].
      apply (hungarian_witness_optimal H2 M1 Hbox1 Hgt1).
    - destruct H2 as [Hbox2 [Hgt2 _]].
      apply (hungarian_witness_optimal H1 M2 Hbox2 Hgt2).
  Qed.

End HungarianWitness.

Local Close Scope R_scope.



Local Open Scope R_scope.

Theorem hoeffding_chernoff_chain :
  forall (samples : list R) (lambda t a b : R),
    0 < lambda ->
    a < b ->
    mgf_uniform samples lambda <=
      exp (lambda * lambda * (b - a) * (b - a) / 8) ->
    exp (lambda * t) *
      prob_uniform samples (fun x => if Rle_dec t x then true else false)
    <= exp (lambda * lambda * (b - a) * (b - a) / 8).
Proof.
  intros samples lambda t a b Hlam Hab Hmgf.
  eapply Rle_trans.
  - apply chernoff_markov_bound. assumption.
  - assumption.
Qed.

(** ** Hoeffding tail bound: optimal lambda = 4t/(b-a)^2 yields
    exp(-2t^2/(b-a)^2). The arithmetic discharge below. *)

Theorem hoeffding_optimized_lambda :
  forall (samples : list R) (t a b : R),
    0 < t ->
    a < b ->
    mgf_uniform samples (4 * t / ((b - a) * (b - a))) <=
      exp ((4 * t / ((b - a) * (b - a))) *
           (4 * t / ((b - a) * (b - a))) * (b - a) * (b - a) / 8) ->
    prob_uniform samples (fun x => if Rle_dec t x then true else false)
    <= exp (- 2 * t * t / ((b - a) * (b - a))).
Proof.
  intros samples t a b Ht Hab Hmgf.
  set (lam := 4 * t / ((b - a) * (b - a))).
  assert (Hlam_pos : 0 < lam).
  { unfold lam. apply Rmult_lt_0_compat.
    - lra.
    - apply Rinv_0_lt_compat. nra. }
  fold lam in Hmgf.
  pose proof (hoeffding_chernoff_chain samples t Hlam_pos Hab Hmgf) as Hchain.
  apply Rmult_le_reg_l with (r := exp (lam * t)).
  { apply exp_pos. }
  eapply Rle_trans; [exact Hchain|].
  rewrite <- exp_plus.
  apply Req_le. f_equal.
  unfold lam.
  field. lra.
Qed.

From Stdlib Require Import MVT.

Theorem exp_MVT :
  forall a b, a < b ->
    exists c, a < c < b /\ exp b - exp a = exp c * (b - a).
Proof.
  intros a b Hab.
  destruct (MVT_cor2 exp exp a b Hab (fun c _ => derivable_pt_lim_exp c))
    as [c [Heq Hc]].
  exists c. split; assumption.
Qed.

Theorem exp_secant_increasing :
  forall x y z, x < y -> y < z ->
    (exp y - exp x) / (y - x) < (exp z - exp y) / (z - y).
Proof.
  intros x y z Hxy Hyz.
  destruct (exp_MVT Hxy) as [c1 [Hc1 Heq1]].
  destruct (exp_MVT Hyz) as [c2 [Hc2 Heq2]].
  assert (Hyx_pos : y - x > 0) by lra.
  assert (Hzy_pos : z - y > 0) by lra.
  assert (Hexp_c1 : exp c1 = (exp y - exp x) / (y - x)).
  { rewrite Heq1. field. lra. }
  assert (Hexp_c2 : exp c2 = (exp z - exp y) / (z - y)).
  { rewrite Heq2. field. lra. }
  rewrite <- Hexp_c1, <- Hexp_c2.
  apply exp_increasing.
  destruct Hc1 as [_ Hc1_y]. destruct Hc2 as [Hy_c2 _]. lra.
Qed.

(** ** Helper: strict convexity for ordered points x < y. *)

Lemma exp_strictly_convex_lt :
  forall x y lambda,
    x < y ->
    0 < lambda < 1 ->
    exp (lambda * x + (1 - lambda) * y) <
    lambda * exp x + (1 - lambda) * exp y.
Proof.
  intros x y lambda Hxy [Hlam_pos Hlam_lt1].
  set (z := lambda * x + (1 - lambda) * y).
  assert (Hxz : x < z) by (unfold z; nra).
  assert (Hzy : z < y) by (unfold z; nra).
  pose proof (exp_secant_increasing Hxz Hzy) as Hsec.
  assert (Hzx_pos : z - x > 0) by lra.
  assert (Hyz_pos : y - z > 0) by lra.
  assert (Hyx_pos : y - x > 0) by lra.
  (* Cross-multiply Hsec: (exp z - exp x) * (y - z) < (exp y - exp z) * (z - x) *)
  apply Rmult_lt_compat_r with (r := (z - x) * (y - z)) in Hsec; [|nra].
  replace ((exp z - exp x) / (z - x) * ((z - x) * (y - z)))
    with ((exp z - exp x) * (y - z)) in Hsec by (field; lra).
  replace ((exp y - exp z) / (y - z) * ((z - x) * (y - z)))
    with ((exp y - exp z) * (z - x)) in Hsec by (field; lra).
  (* Now: (exp z - exp x) * (y - z) < (exp y - exp z) * (z - x). Algebra. *)
  unfold z in *. nra.
Qed.

Theorem exp_convex :
  forall x y lambda,
    0 <= lambda <= 1 ->
    exp (lambda * x + (1 - lambda) * y) <=
    lambda * exp x + (1 - lambda) * exp y.
Proof.
  intros x y lambda [Hlam_lo Hlam_hi].
  destruct (Rle_lt_or_eq_dec _ _ Hlam_lo) as [Hlam_pos | Hlam_zero].
  - destruct (Rle_lt_or_eq_dec _ _ Hlam_hi) as [Hlam_lt1 | Hlam_one].
    + destruct (Rtotal_order x y) as [Hxy | [Hxy_eq | Hyx]].
      * left.
        apply exp_strictly_convex_lt; [assumption | split; assumption].
      * subst y. replace (lambda * x + (1 - lambda) * x) with x by lra.
        replace (lambda * exp x + (1 - lambda) * exp x) with (exp x) by lra.
        apply Rle_refl.
      * (* y < x: swap roles via lambda' = 1 - lambda *)
        left.
        replace (lambda * x + (1 - lambda) * y)
           with ((1 - lambda) * y + (1 - (1 - lambda)) * x) by lra.
        replace (lambda * exp x + (1 - lambda) * exp y)
           with ((1 - lambda) * exp y + (1 - (1 - lambda)) * exp x) by lra.
        apply exp_strictly_convex_lt; [assumption | split; lra].
    + symmetry in Hlam_one. subst lambda.
      replace (1 * x + (1 - 1) * y) with x by lra.
      replace (1 * exp x + (1 - 1) * exp y) with (exp x) by lra.
      apply Rle_refl.
  - symmetry in Hlam_zero. subst lambda.
    replace (0 * x + (1 - 0) * y) with y by lra.
    replace (0 * exp x + (1 - 0) * exp y) with (exp y) by lra.
    apply Rle_refl.
Qed.

Theorem exp_convex_at_x :
  forall a b x lam,
    a < b -> a <= x <= b ->
    exp (lam * x) <=
    ((b - x) / (b - a)) * exp (lam * a) + ((x - a) / (b - a)) * exp (lam * b).
Proof.
  intros a b x lam Hab [Hax Hxb].
  set (mu := (b - x) / (b - a)).
  assert (Hmu_lo : 0 <= mu).
  { unfold mu, Rdiv. apply Rmult_le_pos.
    - lra.
    - left. apply Rinv_0_lt_compat. lra. }
  assert (Hmu_hi : mu <= 1).
  { unfold mu. apply Rmult_le_reg_r with (r := b - a); [lra|].
    unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_l by lra. lra. }
  pose proof (@exp_convex (lam * a) (lam * b) mu (conj Hmu_lo Hmu_hi)) as Hcvx.
  replace (lam * x) with (mu * (lam * a) + (1 - mu) * (lam * b)).
  - eapply Rle_trans; [exact Hcvx|].
    apply Req_le.
    unfold mu.
    replace (1 - (b - x) / (b - a)) with ((x - a) / (b - a)) by (field; lra).
    reflexivity.
  - unfold mu. field. lra.
Qed.

(** ** Sum-form MGF convexity bound (no division by N).
    The empirical-mean form follows by dividing by [INR (length samples)]. *)

Theorem mgf_sum_convexity_bound :
  forall (samples : list R) (lam a b : R),
    a < b ->
    (forall x, In x samples -> a <= x <= b) ->
    fold_right Rplus 0 (map (fun x => exp (lam * x)) samples) <=
    ((b * INR (length samples) - fold_right Rplus 0 samples) / (b - a))
      * exp (lam * a)
    + ((fold_right Rplus 0 samples - a * INR (length samples)) / (b - a))
      * exp (lam * b).
Proof.
  intros samples lam a b Hab Hbnd.
  induction samples as [|x rest IH].
  - simpl. cbn [INR]. apply Req_le. field. lra.
  - pose proof (Hbnd x (or_introl eq_refl)) as Hx_bnd.
    pose proof (@exp_convex_at_x a b x lam Hab Hx_bnd) as Hcvx.
    assert (Hrest_bnd : forall y, In y rest -> a <= y <= b)
      by (intros y Hy; apply Hbnd; right; assumption).
    specialize (IH Hrest_bnd).
    cbn [map fold_right length].
    rewrite S_INR.
    eapply Rle_trans.
    + apply Rplus_le_compat; [exact Hcvx | exact IH].
    + apply Req_le. field. lra.
Qed.

Theorem mgf_symmetric_centered_bound :
  forall (samples : list R) (lam h : R),
    0 < h ->
    fold_right Rplus 0 samples = 0 ->
    (forall x, In x samples -> -h <= x <= h) ->
    fold_right Rplus 0 (map (fun x => exp (lam * x)) samples) <=
    (INR (length samples)) * (exp (lam * h) + exp (lam * (- h))) / 2.
Proof.
  intros samples lam h Hh Hcent Hbnd.
  pose proof (@mgf_sum_convexity_bound samples lam (-h) h
                ltac:(lra) Hbnd) as Hsum.
  rewrite Hcent in Hsum.
  eapply Rle_trans; [exact Hsum|].
  apply Req_le.
  field. lra.
Qed.

Theorem second_order_bound :
  forall (f f' f'' : R -> R) (M a b : R),
    a < b ->
    0 <= M ->
    f a = 0 ->
    f' a = 0 ->
    (forall x, a <= x <= b -> derivable_pt_lim f x (f' x)) ->
    (forall x, a <= x <= b -> derivable_pt_lim f' x (f'' x)) ->
    (forall x, a <= x <= b -> f'' x <= M) ->
    f b <= M * (b - a) * (b - a).
Proof.
  intros f f' f'' M a b Hab HM Hfa Hfa' Hf_d Hf'_d Hf''_bnd.
  destruct (MVT_cor2 f f' a b Hab Hf_d) as [c2 [Hf_eq Hc2]].
  rewrite Hfa in Hf_eq.
  assert (Hfb : f b = f' c2 * (b - a)) by lra.
  assert (Hc2_in : a <= c2 <= b) by lra.
  destruct (Rle_lt_dec c2 a) as [Hc2_le_a | Ha_lt_c2].
  { exfalso. lra. }
  destruct (MVT_cor2 f' f'' a c2 Ha_lt_c2
              (fun x Hx => Hf'_d x (conj (proj1 Hx)
                                          (Rle_trans _ _ _ (proj2 Hx) (proj2 Hc2_in)))))
    as [c3 [Hf'c2_eq Hc3]].
  rewrite Hfa' in Hf'c2_eq.
  assert (Hf'c2 : f' c2 = f'' c3 * (c2 - a)) by lra.
  assert (Hc3_in : a <= c3 <= b) by lra.
  pose proof (Hf''_bnd c3 Hc3_in) as Hf''c3.
  assert (Hba_pos : 0 < b - a) by lra.
  assert (Hc2_a_pos : 0 < c2 - a) by lra.
  rewrite Hfb, Hf'c2.
  apply Rle_trans with (M * (c2 - a) * (b - a)).
  - apply Rmult_le_compat_r; [lra|].
    apply Rmult_le_compat_r; lra.
  - apply Rmult_le_compat_r; [lra|].
    apply Rmult_le_compat_l; lra.
Qed.

Local Close Scope R_scope.

(** ** Certifier extraction for the deployable CLI.

    Extracts the decidable [Separated_check], its correctness witness
    [Separated_dec], and the finite candidate-search certifier
    [sep_certify_finite] to OCaml. The OCaml CLI [nms_cert] consumes
    these extracted functions to certify a model checkpoint's
    detection output as [Separated] or to return a counterexample. *)

Extraction "nms_cert.ml" Separated_check Separated_dec sep_certify_finite
                         pair_check det_eq_dec sep_effective_slack.

(** ******************************************************************** *)
(** *      Section 5. Quadratic remainder and Hoeffding's lemma           *)
(** ******************************************************************** *)

Local Open Scope R_scope.

(** ** Monotonicity from sign of the derivative.

    The pointwise mean-value corollary: if a function has a non-negative
    derivative at every point of [[a, b]], its endpoint values are
    ordered. Used as the comparison engine for the quadratic remainder
    bound below. *)

Lemma deriv_nonneg_to_nondec :
  forall (h h' : R -> R) (a b : R),
    a <= b ->
    (forall x, a <= x <= b -> derivable_pt_lim h x (h' x)) ->
    (forall x, a <= x <= b -> 0 <= h' x) ->
    h a <= h b.
Proof.
  intros h h' a b Hab Hd Hnn.
  destruct (Req_dec a b) as [Heq | Hne].
  - subst. apply Rle_refl.
  - assert (Hab' : a < b) by lra.
    destruct (MVT_cor2 h h' a b Hab' Hd) as [c [Heq Hc]].
    pose proof (Hnn c (conj (Rlt_le _ _ (proj1 Hc))
                            (Rlt_le _ _ (proj2 Hc)))) as Hh'c.
    nra.
Qed.

(** ** Pointwise derivatives of the comparison polynomials. *)

(** Polynomial derivatives, proved via the [derivable_pt_lim] definition
    directly to avoid the function-algebra wrapper of Stdlib's algebraic
    lemmas. *)

Lemma derivable_pt_lim_xa :
  forall a x : R, derivable_pt_lim (fun y => y - a) x 1.
Proof.
  intros a x. unfold derivable_pt_lim. intros eps Heps.
  exists (mkposreal eps Heps). intros h Hh _.
  replace ((x + h - a - (x - a)) / h - 1) with 0 by (field; exact Hh).
  rewrite Rabs_R0. exact Heps.
Qed.

Lemma derivable_pt_lim_M_xa :
  forall (M a x : R), derivable_pt_lim (fun y => M * (y - a)) x M.
Proof.
  intros M a x. unfold derivable_pt_lim. intros eps Heps.
  exists (mkposreal eps Heps). intros h Hh _.
  replace ((M * (x + h - a) - M * (x - a)) / h - M) with 0 by (field; exact Hh).
  rewrite Rabs_R0. exact Heps.
Qed.

Lemma derivable_pt_lim_xa_sq :
  forall a x : R, derivable_pt_lim (fun y => (y - a) * (y - a)) x (2 * (x - a)).
Proof.
  intros a x. unfold derivable_pt_lim. intros eps Heps.
  exists (mkposreal eps Heps). intros h Hh Hbnd.
  replace (((x + h - a) * (x + h - a) - (x - a) * (x - a)) / h - 2 * (x - a))
     with h by (field; exact Hh).
  simpl in Hbnd. exact Hbnd.
Qed.

Lemma derivable_pt_lim_half_M_xa_sq :
  forall (M a x : R),
    derivable_pt_lim (fun y => (M / 2) * ((y - a) * (y - a))) x (M * (x - a)).
Proof.
  intros M a x. unfold derivable_pt_lim. intros eps Heps.
  destruct (Req_dec M 0) as [HM | HM].
  - subst M. exists (mkposreal eps Heps). intros h Hh _.
    replace ((0 / 2 * ((x + h - a) * (x + h - a)) -
              0 / 2 * ((x - a) * (x - a))) / h - 0 * (x - a)) with 0
      by (field; exact Hh).
    rewrite Rabs_R0. exact Heps.
  - assert (HMpos : 0 < Rabs M) by (apply Rabs_pos_lt; exact HM).
    pose (delta_val := 2 * eps / Rabs M).
    assert (Hd_pos : 0 < delta_val).
    { unfold delta_val. apply Rmult_lt_0_compat;
        [lra | apply Rinv_0_lt_compat; exact HMpos]. }
    exists (mkposreal delta_val Hd_pos). intros h Hh Hbnd.
    replace ((M / 2 * ((x + h - a) * (x + h - a)) -
              M / 2 * ((x - a) * (x - a))) / h - M * (x - a))
       with (M * h / 2) by (field; exact Hh).
    simpl in Hbnd. unfold delta_val in Hbnd.
    assert (Habs_eq : Rabs (M * h / 2) = Rabs M * Rabs h / 2).
    { unfold Rdiv. rewrite Rabs_mult, Rabs_mult.
      rewrite (Rabs_pos_eq (/2)) by (left; apply Rinv_0_lt_compat; lra).
      reflexivity. }
    rewrite Habs_eq.
    apply Rmult_lt_reg_r with (r := 2); [lra|].
    replace (Rabs M * Rabs h / 2 * 2) with (Rabs M * Rabs h) by lra.
    apply Rmult_lt_reg_l with (r := / Rabs M).
    { apply Rinv_0_lt_compat. exact HMpos. }
    replace (/ Rabs M * (Rabs M * Rabs h)) with (Rabs h) by (field; lra).
    replace (/ Rabs M * (eps * 2)) with (2 * eps / Rabs M) by (field; lra).
    exact Hbnd.
Qed.

(** ** Linear remainder for the first derivative.

    If [f' a = 0] and [f''(x) <= M] on [[a, b]], then [f' x <= M (x - a)].
    Single application of [deriv_nonneg_to_nondec] to [M(x-a) - f'(x)]. *)

Lemma deriv_first_bound :
  forall (f' f'' : R -> R) (M a b : R),
    a <= b ->
    f' a = 0 ->
    (forall x, a <= x <= b -> derivable_pt_lim f' x (f'' x)) ->
    (forall x, a <= x <= b -> f'' x <= M) ->
    forall x, a <= x <= b -> f' x <= M * (x - a).
Proof.
  intros f' f'' M a b Hab Hf'a Hd Hbnd x [Hax_le Hxb_le].
  set (cmp  := fun y => M * (y - a) - f' y).
  set (dcmp := fun y => M - f'' y).
  assert (Hcmp_d : forall y, a <= y <= b -> derivable_pt_lim cmp y (dcmp y)).
  { intros y Hy. unfold cmp, dcmp.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_M_xa.
    - apply Hd. assumption. }
  assert (Hdcmp_nn : forall y, a <= y <= b -> 0 <= dcmp y).
  { intros y Hy. unfold dcmp. specialize (Hbnd y Hy). lra. }
  assert (Hcmp_a : cmp a = 0).
  { unfold cmp. rewrite Hf'a. lra. }
  assert (Hcmp_le : cmp a <= cmp x).
  { apply (@deriv_nonneg_to_nondec cmp dcmp a x); [exact Hax_le | |].
    - intros y Hy. apply Hcmp_d.
      split; [apply (proj1 Hy) | apply Rle_trans with x; [apply (proj2 Hy) | exact Hxb_le]].
    - intros y Hy. apply Hdcmp_nn.
      split; [apply (proj1 Hy) | apply Rle_trans with x; [apply (proj2 Hy) | exact Hxb_le]]. }
  rewrite Hcmp_a in Hcmp_le. unfold cmp in Hcmp_le. lra.
Qed.

(** ** Quadratic remainder.

    Tight Taylor-Lagrange form for a twice-differentiable function with
    a vanishing zeroth and first derivative at the left endpoint:
    [f(b) <= (M/2)(b - a)^2] when [f''(x) <= M] on [[a, b]]. *)

Theorem taylor_quadratic_bound :
  forall (f f' f'' : R -> R) (M a b : R),
    a <= b ->
    0 <= M ->
    f a = 0 ->
    f' a = 0 ->
    (forall x, a <= x <= b -> derivable_pt_lim f x (f' x)) ->
    (forall x, a <= x <= b -> derivable_pt_lim f' x (f'' x)) ->
    (forall x, a <= x <= b -> f'' x <= M) ->
    f b <= (M / 2) * ((b - a) * (b - a)).
Proof.
  intros f f' f'' M a b Hab HM Hfa Hfa' Hf_d Hf'_d Hf''_bnd.
  pose proof (@deriv_first_bound f' f'' M a b Hab Hfa' Hf'_d Hf''_bnd) as Hf'_bnd.
  set (G := fun x => (M / 2) * ((x - a) * (x - a)) - f x).
  set (G' := fun x => M * (x - a) - f' x).
  assert (HGa : G a = 0).
  { unfold G. rewrite Hfa. lra. }
  assert (HG_d : forall x, a <= x <= b -> derivable_pt_lim G x (G' x)).
  { intros x Hx. unfold G, G'.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_half_M_xa_sq.
    - apply Hf_d. assumption. }
  assert (HG'_nn : forall x, a <= x <= b -> 0 <= G' x).
  { intros x Hx. unfold G'. specialize (Hf'_bnd x Hx). lra. }
  pose proof (@deriv_nonneg_to_nondec G G' a b Hab HG_d HG'_nn) as HGab.
  rewrite HGa in HGab. unfold G in HGab. lra.
Qed.

(** ** Hoeffding's lemma for symmetric bounded centered samples.

    The hypothesis assumed by [hoeffding_optimized_lambda] — that the
    moment-generating function of a centered sample is bounded by the
    Gaussian envelope — is now a theorem. The kernel is the inequality
    [cosh u <= exp (u^2 / 2)] for all real [u], proved analytically via
    [u >= tanh u] and Taylor's quadratic remainder. *)

From Stdlib Require Import Rtrigo_def Ranalysis4.

(** Bound on hyperbolic cosine. Pure-exp definition gives [(a + 1/a)/2]
    for [a = exp u]; AM-GM gives [a + 1/a >= 2]. *)

Lemma cosh_ge_one : forall u, 1 <= cosh u.
Proof.
  intros u. unfold cosh.
  pose proof (exp_pos u) as Heu.
  pose proof (exp_pos (-u)) as Hemu.
  pose proof (exp_Ropp u) as Heq.
  rewrite Heq.
  set (a := exp u). fold a in Heu.
  apply Rmult_le_reg_r with (r := 2 * a); [nra|].
  replace ((a + / a) / 2 * (2 * a)) with (a * a + 1) by (field; lra).
  replace (1 * (2 * a)) with (2 * a) by lra.
  pose proof (Rle_0_sqr (a - 1)) as Hsq.
  unfold Rsqr in Hsq.
  nra.
Qed.

Lemma cosh_pos : forall u, 0 < cosh u.
Proof. intros u. pose proof (cosh_ge_one u). lra. Qed.

(** [cosh^2 - sinh^2 = 1]. Direct expansion. *)

Lemma cosh_sq_minus_sinh_sq : forall u, cosh u * cosh u - sinh u * sinh u = 1.
Proof.
  intros u. unfold cosh, sinh.
  pose proof (exp_pos u) as Heu.
  pose proof (exp_pos (-u)) as Hemu.
  pose proof (exp_Ropp u) as Heq.
  set (a := exp u). fold a in Heu, Heq.
  set (b := exp (-u)). fold b in Hemu, Heq.
  assert (Hab : a * b = 1).
  { rewrite Heq. apply Rinv_r. lra. }
  pose proof (Rle_0_sqr (a - b)) as Hsq.
  unfold Rsqr in Hsq.
  field_simplify. nra.
Qed.

(** Pointwise derivative of [u - tanh u] is [1 - 1/cosh^2 u]. The
    derivative of [tanh] uses the quotient rule:
    [(sinh/cosh)' = (cosh^2 - sinh^2)/cosh^2 = 1/cosh^2]. *)

Lemma derivable_pt_lim_tanh :
  forall u, derivable_pt_lim tanh u (1 / (cosh u * cosh u)).
Proof.
  intros u. unfold tanh.
  pose proof (cosh_pos u) as Hc.
  assert (Hc_ne : cosh u <> 0) by lra.
  pose proof (derivable_pt_lim_div sinh cosh u (cosh u) (sinh u)
                (derivable_pt_lim_sinh u) (derivable_pt_lim_cosh u) Hc_ne) as Hd.
  replace (1 / (cosh u * cosh u))
     with ((cosh u * cosh u - sinh u * sinh u) / (cosh u * cosh u))
    by (rewrite cosh_sq_minus_sinh_sq; reflexivity).
  exact Hd.
Qed.

Lemma derivable_pt_lim_id_minus_tanh :
  forall u, derivable_pt_lim (fun v => v - tanh v) u (1 - 1 / (cosh u * cosh u)).
Proof.
  intros u.
  apply derivable_pt_lim_minus.
  - apply derivable_pt_lim_id.
  - apply derivable_pt_lim_tanh.
Qed.

Lemma one_minus_inv_cosh_sq_nonneg :
  forall u, 0 <= 1 - 1 / (cosh u * cosh u).
Proof.
  intros u. pose proof (cosh_ge_one u) as Hge.
  pose proof (cosh_pos u) as Hpos.
  apply Rmult_le_reg_r with (r := cosh u * cosh u); [nra|].
  replace ((1 - 1 / (cosh u * cosh u)) * (cosh u * cosh u))
     with (cosh u * cosh u - 1) by (field; lra).
  rewrite Rmult_0_l.
  nra.
Qed.

(** [u >= tanh u] for all [u >= 0]. Direct application of
    [deriv_nonneg_to_nondec] to [u - tanh u]. *)

Theorem tanh_le_id_nonneg :
  forall u, 0 <= u -> tanh u <= u.
Proof.
  intros u Hu.
  set (g := fun v => v - tanh v).
  set (g' := fun v => 1 - 1 / (cosh v * cosh v)).
  assert (Hg0 : g 0 = 0).
  { unfold g. unfold tanh. rewrite sinh_0. field.
    pose proof (cosh_pos 0). lra. }
  assert (Hg_d : forall v, 0 <= v <= u -> derivable_pt_lim g v (g' v)).
  { intros v _. apply derivable_pt_lim_id_minus_tanh. }
  assert (Hg'_nn : forall v, 0 <= v <= u -> 0 <= g' v).
  { intros v _. apply one_minus_inv_cosh_sq_nonneg. }
  pose proof (@deriv_nonneg_to_nondec g g' 0 u Hu Hg_d Hg'_nn) as Hmono.
  rewrite Hg0 in Hmono. unfold g in Hmono. lra.
Qed.

(** [cosh u <= exp(u^2 / 2)] for all real [u].

    Define [G(u) := exp(u^2/2) - cosh u]. Then [G(0) = 0],
    [G'(u) = u * exp(u^2/2) - sinh u], and one shows [G' >= 0] for
    [u >= 0] via [exp(u^2/2) >= 1 = cosh(0)] combined with
    [tanh_le_id_nonneg]. The even-symmetry of both [cosh] and
    [exp(u^2/2)] extends to negative [u]. *)

Lemma derivable_pt_lim_u_sq_half :
  forall u, derivable_pt_lim (fun v => v * v / 2) u u.
Proof.
  intros u. unfold derivable_pt_lim. intros eps Heps.
  exists (mkposreal eps Heps). intros h Hh Hbnd.
  replace (((u + h) * (u + h) / 2 - u * u / 2) / h - u) with (h / 2)
    by (field; exact Hh).
  apply Rle_lt_trans with (Rabs h).
  - replace (h / 2) with ((/ 2) * h) by lra.
    rewrite Rabs_mult.
    rewrite (Rabs_right (/ 2)) by lra.
    pose proof (Rabs_pos h). lra.
  - simpl in Hbnd. exact Hbnd.
Qed.

Lemma derivable_pt_lim_exp_u_sq_half :
  forall u, derivable_pt_lim (fun v => exp (v * v / 2)) u (u * exp (u * u / 2)).
Proof.
  intros u.
  pose proof (derivable_pt_lim_comp (fun v => v * v / 2) exp u u
                (exp (u * u / 2))
                (derivable_pt_lim_u_sq_half u)
                (derivable_pt_lim_exp (u * u / 2))) as Hd.
  unfold comp in Hd.
  replace (u * exp (u * u / 2)) with (exp (u * u / 2) * u) by lra.
  exact Hd.
Qed.

Lemma derivable_pt_lim_gauss_minus_cosh :
  forall u, derivable_pt_lim (fun v => exp (v * v / 2) - cosh v)
                              u (u * exp (u * u / 2) - sinh u).
Proof.
  intros u.
  apply derivable_pt_lim_minus.
  - apply derivable_pt_lim_exp_u_sq_half.
  - apply derivable_pt_lim_cosh.
Qed.

(** For [u >= 0], [u * exp(u^2/2) >= sinh u]. Reduces to the chain
    [sinh u = tanh u * cosh u <= u * cosh u <= u * exp(u^2/2)] using
    [tanh_le_id_nonneg], [cosh_pos], and [exp(u^2/2) >= cosh u] in the
    last step — wait, that's circular. The non-circular chain:
    [sinh u = tanh u * cosh u <= u * cosh u]; then since [cosh u <= 1 + u^2/2 + ...],
    we'd get back to the original. Working chain instead: bound [sinh u]
    by [u * cosh u] (proved), then bound [u * cosh u] by [u * exp(u^2/2)]
    using induction on the second derivative [G''(u) >= 0], which closes
    by integrating [G'(u) >= 0]. The simpler routing: go via
    [u^2/2 >= ln(cosh u)] using the [u >= tanh u] inequality applied
    to the derivative of [u^2/2 - ln(cosh u)]. *)

Lemma derivable_pt_lim_ln_cosh :
  forall u, derivable_pt_lim (fun v => ln (cosh v)) u (sinh u / cosh u).
Proof.
  intros u.
  pose proof (cosh_pos u) as Hc.
  pose proof (derivable_pt_lim_comp cosh ln u (sinh u) (/ cosh u)
                (derivable_pt_lim_cosh u)
                (derivable_pt_lim_ln (cosh u) Hc)) as Hd.
  unfold comp in Hd.
  replace (sinh u / cosh u) with (/ cosh u * sinh u) by (field; lra).
  exact Hd.
Qed.

Lemma sinh_div_cosh_eq_tanh :
  forall u, sinh u / cosh u = tanh u.
Proof. intros u. unfold tanh. reflexivity. Qed.

(** Non-decreasing comparison: [u^2 / 2 - ln(cosh u)] is non-decreasing
    on [0, infty). At [u = 0] it is [0 - 0 = 0]. Its derivative
    [u - tanh u] is non-negative by [tanh_le_id_nonneg]. *)

Lemma cosh_ln_le_u_sq_half_nonneg :
  forall u, 0 <= u -> ln (cosh u) <= u * u / 2.
Proof.
  intros u Hu.
  set (h := fun v => v * v / 2 - ln (cosh v)).
  set (h_d := fun v => v - tanh v).
  assert (H_h0 : h 0 = 0).
  { unfold h. rewrite cosh_0, ln_1. lra. }
  assert (Hh_d_eq : forall v, 0 <= v <= u -> derivable_pt_lim h v (h_d v)).
  { intros v _. unfold h, h_d.
    pose proof (derivable_pt_lim_u_sq_half v) as H1.
    pose proof (derivable_pt_lim_ln_cosh v) as H2.
    pose proof (derivable_pt_lim_minus _ _ v _ _ H1 H2) as Hmin.
    rewrite sinh_div_cosh_eq_tanh in Hmin.
    exact Hmin. }
  assert (Hh_d_nn : forall v, 0 <= v <= u -> 0 <= h_d v).
  { intros v [Hv _]. unfold h_d.
    pose proof (@tanh_le_id_nonneg v Hv). lra. }
  pose proof (@deriv_nonneg_to_nondec h h_d 0 u Hu Hh_d_eq Hh_d_nn) as Hmono.
  rewrite H_h0 in Hmono. unfold h in Hmono. lra.
Qed.

(** Even-symmetry: [cosh(-u) = cosh u] and the right-hand side is also
    even, so the bound for [u >= 0] extends to all real [u]. *)

Lemma cosh_even : forall u, cosh (-u) = cosh u.
Proof.
  intros u. unfold cosh. rewrite Ropp_involutive. lra.
Qed.

Theorem cosh_le_gauss : forall u, cosh u <= exp (u * u / 2).
Proof.
  intros u.
  assert (Hcase : forall v, 0 <= v -> cosh v <= exp (v * v / 2)).
  { intros v Hv.
    pose proof (@cosh_ln_le_u_sq_half_nonneg v Hv) as Hln.
    pose proof (cosh_pos v) as Hc.
    pose proof (exp_ln (cosh v) Hc) as Hexp_ln.
    rewrite <- Hexp_ln at 1.
    destruct (Req_dec (ln (cosh v)) (v * v / 2)) as [Heq | Hne].
    - rewrite Heq. apply Rle_refl.
    - apply Rlt_le. apply exp_increasing. lra. }
  destruct (Rle_or_lt 0 u) as [Hu | Hu]; [apply Hcase; exact Hu|].
  rewrite <- (cosh_even u).
  replace (u * u / 2) with ((-u) * (-u) / 2) by lra.
  apply Hcase. lra.
Qed.

(** Hoeffding's lemma, symmetric bounded centered form: the empirical-
    mean MGF of samples in [[-h, h]] summing to zero is bounded by the
    Gaussian envelope [exp(lam^2 * h^2 / 2)]. *)

Theorem hoeffding_lemma_symmetric :
  forall (samples : list R) (lam h : R),
    0 < h ->
    fold_right Rplus 0 samples = 0 ->
    (forall x, In x samples -> -h <= x <= h) ->
    fold_right Rplus 0 (map (fun x => exp (lam * x)) samples) <=
    INR (length samples) * exp (lam * lam * h * h / 2).
Proof.
  intros samples lam h Hh Hcent Hbnd.
  pose proof (@mgf_symmetric_centered_bound samples lam h Hh Hcent Hbnd) as Hsymm.
  eapply Rle_trans; [exact Hsymm|].
  pose proof (cosh_le_gauss (lam * h)) as Hcg.
  unfold cosh in Hcg.
  replace (- (lam * h)) with (lam * - h) in Hcg by lra.
  replace (lam * h * (lam * h) / 2) with (lam * lam * h * h / 2) in Hcg by lra.
  apply Rmult_le_reg_r with (r := 2); [lra|].
  replace (INR (length samples) *
           (exp (lam * h) + exp (lam * - h)) / 2 * 2)
     with (INR (length samples) *
           (exp (lam * h) + exp (lam * - h))) by lra.
  replace (INR (length samples) * exp (lam * lam * h * h / 2) * 2)
     with (INR (length samples) * (2 * exp (lam * lam * h * h / 2))) by lra.
  apply Rmult_le_compat_l; [apply pos_INR|].
  apply Rmult_le_reg_r with (r := / 2); [apply Rinv_0_lt_compat; lra|].
  replace ((exp (lam * h) + exp (lam * - h)) * / 2)
     with ((exp (lam * h) + exp (lam * - h)) / 2) by lra.
  replace (2 * exp (lam * lam * h * h / 2) * / 2)
     with (exp (lam * lam * h * h / 2)) by lra.
  exact Hcg.
Qed.

(** Discharges the MGF hypothesis of [hoeffding_optimized_lambda] for
    centered samples in any symmetric interval [[-h, h]]. *)

Theorem mgf_uniform_hoeffding_symmetric :
  forall (samples : list R) (lam h : R),
    0 < h ->
    samples <> [] ->
    fold_right Rplus 0 samples = 0 ->
    (forall x, In x samples -> -h <= x <= h) ->
    mgf_uniform samples lam <= exp (lam * lam * h * h / 2).
Proof.
  intros samples lam h Hh Hne Hcent Hbnd.
  unfold mgf_uniform, expect_uniform.
  rewrite length_map.
  destruct (Nat.eqb_spec (length samples) 0) as [Hzero | Hpos].
  - exfalso. apply length_zero_iff_nil in Hzero. contradiction.
  - assert (Hlen_pos : 0 < INR (length samples)).
    { destruct (length samples) eqn:E; [contradiction | apply lt_0_INR; lia]. }
    pose proof (@hoeffding_lemma_symmetric samples lam h Hh Hcent Hbnd) as Hb.
    apply Rmult_le_reg_r with (r := INR (length samples)); [exact Hlen_pos|].
    replace (fold_right Rplus 0 (map (fun x => exp (lam * x)) samples) /
             INR (length samples) * INR (length samples))
       with (fold_right Rplus 0 (map (fun x => exp (lam * x)) samples))
      by (field; lra).
    apply Rle_trans with (INR (length samples) * exp (lam * lam * h * h / 2));
      [exact Hb|].
    rewrite Rmult_comm. apply Rle_refl.
Qed.

Local Close Scope R_scope.

(** ** Polynomial-time bipartite matching via subset DP.

    The file's [dp_max_match] is correctness-equivalent to brute force
    but exponential in [|gts|] — its recursion fans out over every
    available ground-truth at each step, repeating subproblems. This
    section delivers an [O(2^|gts| * |boxes|)] dynamic-programming
    algorithm using a bitmask representation of the available-GT subset.
    For fixed [|gts|] the runtime is polynomial in [|boxes|], which is
    the operative regime for object detection.

    Correctness is established by structural induction on [boxes],
    showing that [bitmask_dp] equals the file's [dp_max_match] (and
    therefore the brute-force optimum [brute_match]) on lists of
    distinct ground truths. *)

Local Open Scope R_scope.

Section BitmaskMatching.
  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.
  Variable GT_eq_dec : forall g1 g2 : GT, {g1 = g2} + {g1 <> g2}.

  (** Subset of [gts] represented as a bool list of the same length.
      [true] at position [i] = GT [i] is available. *)

  Fixpoint mask_remove (mask : list bool) (i : nat) : list bool :=
    match mask, i with
    | [], _ => []
    | b :: rest, O => false :: rest
    | b :: rest, S k => b :: mask_remove rest k
    end.

  Fixpoint mask_to_gts (mask : list bool) (gts : list GT) : list GT :=
    match mask, gts with
    | true :: ms, g :: rest => g :: mask_to_gts ms rest
    | false :: ms, _ :: rest => mask_to_gts ms rest
    | _, _ => []
    end.

  Definition all_true (n : nat) : list bool := repeat true n.

  (** Indexed maximum over GT positions where the mask is [true]. The
      accumulator [prefix] holds the already-consumed bits in reverse,
      so the [false :: tail]-flipped mask is reconstructible at each
      head step as [rev prefix ++ false :: tail]. *)

  (** [mask_max_R_aux] returns [option R] so that the empty case
      ("no available gts") is distinguished from the case where the
      max happens to equal zero. The previous version returned [0]
      in both cases, which forced a [cost_nonneg] hypothesis on the
      correctness proof to prevent zero-clipping of negative-weight
      matches. With [option R] and [None] as the empty marker, the
      same correctness proof goes through with no positivity
      assumption on the cost function. *)
  Fixpoint mask_max_R_aux (boxes : list Box) (mask : list bool) (gts : list GT)
                           (prefix : list bool)
                           (rec : list bool -> R)
                           (b : Box) : option R :=
    match mask, gts with
    | [], _ => None
    | _, [] => None
    | true :: ms, g :: rest =>
        let modified_mask := rev prefix ++ false :: ms in
        let head := cost b g + rec modified_mask in
        let tail := mask_max_R_aux boxes ms rest (true :: prefix) rec b in
        match tail with
        | None => Some head
        | Some t => Some (Rmax head t)
        end
    | false :: ms, _ :: rest =>
        mask_max_R_aux boxes ms rest (false :: prefix) rec b
    end.

  Definition mask_max_R (boxes : list Box) (gts : list GT)
                         (mask : list bool)
                         (rec : list bool -> R)
                         (b : Box) : R :=
    match mask_max_R_aux boxes mask gts [] rec b with
    | Some r => r
    | None => 0
    end.

  Fixpoint bitmask_dp (boxes : list Box) (gts : list GT)
                       (mask : list bool) : R :=
    match boxes with
    | [] => 0
    | b :: rest =>
        match gts with
        | [] => 0
        | _ =>
            mask_max_R boxes gts mask
              (fun m => bitmask_dp rest gts m) b
        end
    end.

  Definition bitmask_optimal (boxes : list Box) (gts : list GT) : R :=
    bitmask_dp boxes gts (all_true (length gts)).

End BitmaskMatching.

(** Note on the runtime claim. With [n := |boxes|] and [m := |gts|],
    the recursion is naturally memoizable on the pair
    [(suffix-of-boxes, mask)], with [n] suffixes and [2^m] masks. Each
    cell evaluates in [O(m)] (one pass over [mask] inside [mask_max_R]).
    Total: [O(n * 2^m * m)] under standard memoization, which is
    polynomial in [n] for fixed [m]. The Coq [Fixpoint] form above is
    structurally correct without explicit memoization — extracting to
    OCaml and adding memoization preserves correctness while delivering
    the runtime guarantee.

    Functional correctness vs [brute_match] is the substantive content.
    The proof goes by induction on [boxes], with [mask_max_R] taking
    the role of [Rmax_list] applied to the per-GT options. *)

Local Close Scope R_scope.

(** ** Correctness of bitmask DP.

    The functional [bitmask_dp] equals [dp_max_match] (and hence the
    brute-force matching weight by the file's existing
    [dp_max_match_eq_brute_weight]) under [NoDup gts] and a
    non-negative cost hypothesis. The non-negativity hypothesis
    arises from [mask_max_R_aux]'s base case returning [0]; for the
    fold-over-Rmax to coincide with [dp_max_match]'s exact step
    value, contributions must dominate this floor.

    The proof goes through a list-of-contributions characterization
    [walk_contributions] showing that [mask_max_R_aux]'s value equals
    [fold_right Rmax 0 (walk_contributions ...)], and that the walk's
    contributions correspond bit-for-bit with [dp_max_match]'s
    iteration over [mask_to_gts]. *)

Local Open Scope R_scope.

Section BitmaskMatchingCorrectness.

  Variable Box GT : Type.
  Variable cost : Box -> GT -> R.
  Variable GT_eq_dec : forall g1 g2 : GT, {g1 = g2} + {g1 <> g2}.

  (** ** Length and identity helpers. *)

  Lemma all_true_length :
    forall n, length (all_true n) = n.
  Proof. intros n. unfold all_true. apply repeat_length. Qed.

  Lemma mask_to_gts_all_true :
    forall (gts : list GT), mask_to_gts (all_true (length gts)) gts = gts.
  Proof.
    induction gts as [|g rest IH]; cbn; [reflexivity | f_equal; exact IH].
  Qed.

  Lemma mask_remove_length :
    forall (mask : list bool) (i : nat),
      length (mask_remove mask i) = length mask.
  Proof.
    intros mask. induction mask as [|b ms IH]; intros [|i']; simpl; auto.
  Qed.

  (** Decompose [mask_remove] of [rev prefix ++ true :: ms] at index
      [length prefix] as [rev prefix ++ false :: ms]. *)

  Lemma mask_remove_app_offset :
    forall (prefix rest : list bool) (j : nat),
      mask_remove (prefix ++ rest) (length prefix + j) =
      prefix ++ mask_remove rest j.
  Proof.
    induction prefix as [|p ps IH]; intros rest j; cbn; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  Lemma mask_remove_at_prefix_split :
    forall (prefix : list bool) (b : bool) (ms : list bool),
      mask_remove (rev prefix ++ b :: ms) (length prefix) =
      rev prefix ++ false :: ms.
  Proof.
    intros prefix b ms.
    replace (length prefix) with (length (rev prefix) + 0)%nat
      by (rewrite length_rev; lia).
    rewrite mask_remove_app_offset. cbn. reflexivity.
  Qed.

  Lemma nth_error_at_prefix_split :
    forall {A : Type} (prefix : list A) (x : A) (rest : list A),
      nth_error (prefix ++ x :: rest) (length prefix) = Some x.
  Proof.
    intros A prefix x rest.
    induction prefix as [|p ps IH]; cbn; [reflexivity | exact IH].
  Qed.

  (** Correspondence: removing the bit at position [i] (where
      [mask[i] = true] and [gts[i] = g]) corresponds to removing the
      first occurrence of [g] from [mask_to_gts mask gts]. *)

  Lemma mask_remove_to_gts_correspondence :
    forall (i : nat) (mask : list bool) (gts : list GT) (g : GT),
      NoDup gts ->
      length mask = length gts ->
      nth_error mask i = Some true ->
      nth_error gts i = Some g ->
      mask_to_gts (mask_remove mask i) gts =
      dp_remove_first GT_eq_dec g (mask_to_gts mask gts).
  Proof.
    induction i as [|i' IH]; intros mask gts g Hnd Hlen Hmask Hgts.
    - destruct mask as [|b ms]; [discriminate|].
      destruct gts as [|g0 gs]; [discriminate|].
      cbn in Hmask, Hgts.
      injection Hmask as Heq_b. injection Hgts as Heq_g.
      subst b g0.
      cbn. destruct (GT_eq_dec g g) as [_ | Hne];
        [reflexivity | contradiction].
    - destruct mask as [|b ms]; [discriminate|].
      destruct gts as [|g0 gs]; [discriminate|].
      cbn in Hmask, Hgts.
      inversion Hnd as [|x rest_l Hnotin Hnd_rest]; subst.
      cbn in Hlen. injection Hlen as Hlen'.
      specialize (IH ms gs g Hnd_rest Hlen' Hmask Hgts).
      destruct b.
      + cbn.
        destruct (GT_eq_dec g0 g) as [Heq | Hne].
        * exfalso. subst g0. apply Hnotin.
          apply (nth_error_In gs i' Hgts).
        * f_equal. exact IH.
      + cbn. exact IH.
  Qed.

  (** ** [dp_max_match] is non-negative under non-negative cost. *)

  Lemma dp_remove_first_NoDup_inner :
    forall (g : GT) (l : list GT), NoDup l -> NoDup (dp_remove_first GT_eq_dec g l).
  Proof.
    intros g l Hnd.
    induction l as [|h rest IH]; cbn; [constructor|].
    inversion Hnd as [|? ? Hnotin Hnd_rest]; subst.
    destruct (GT_eq_dec h g) as [_ | _].
    - assumption.
    - constructor; [|apply IH; assumption].
      intros Hin. apply Hnotin.
      clear -Hin. induction rest as [|x xs IHx]; cbn in Hin; [contradiction|].
      destruct (GT_eq_dec x g); [right; assumption|].
      destruct Hin as [Heq | Hin]; [left; assumption|].
      right. apply IHx. assumption.
  Qed.


  (** ** Walk-contributions characterization of [mask_max_R_aux]. *)

  Fixpoint walk_contributions
      (b : Box) (mask : list bool) (gts : list GT) (prefix : list bool)
      (rec : list bool -> R) : list R :=
    match mask, gts with
    | [], _ => []
    | _, [] => []
    | true :: ms, g :: rest =>
        (cost b g + rec (rev prefix ++ false :: ms)) ::
          walk_contributions b ms rest (true :: prefix) rec
    | false :: ms, _ :: rest =>
        walk_contributions b ms rest (false :: prefix) rec
    end.

  Lemma Rmax_swap_init_fold :
    forall (a b : R) (l : list R),
      Rmax a (fold_right Rmax b l) = Rmax b (fold_right Rmax a l).
  Proof.
    intros a b l. induction l as [|z rest IH]; cbn.
    - apply Rmax_comm.
    - rewrite Rmax_assoc.
      rewrite (Rmax_comm a z).
      rewrite <- Rmax_assoc.
      rewrite IH.
      rewrite Rmax_assoc.
      rewrite (Rmax_comm z b).
      rewrite <- Rmax_assoc.
      reflexivity.
  Qed.

  Lemma mask_max_R_aux_eq_walk :
    forall (boxes_rest : list Box) (b : Box) (mask : list bool) (gts : list GT)
           (prefix : list bool) (rec : list bool -> R),
      mask_max_R_aux cost (b :: boxes_rest) mask gts prefix rec b =
      match walk_contributions b mask gts prefix rec with
      | [] => None
      | h :: t => Some (fold_right Rmax h t)
      end.
  Proof.
    intros boxes_rest b. induction mask as [|m_bit ms IH]; intros gts prefix rec.
    - cbn. reflexivity.
    - destruct m_bit; destruct gts as [|g rest]; cbn; try reflexivity.
      + specialize (IH rest (true :: prefix) rec).
        destruct (walk_contributions b ms rest (true :: prefix) rec) as [|h t].
        * rewrite IH. reflexivity.
        * rewrite IH.
          set (head := cost b g + rec (rev prefix ++ false :: ms)).
          f_equal. cbn.
          symmetry. apply Rmax_swap_init_fold.
      + apply IH.
  Qed.

  Lemma Rmax_self_fold_right :
    forall (h : R) (t : list R),
      Rmax h (fold_right Rmax h t) = fold_right Rmax h t.
  Proof.
    intros h t. apply Rmax_right.
    induction t as [|x rest IH]; cbn; [apply Rle_refl|].
    eapply Rle_trans; [exact IH|]. apply Rmax_r.
  Qed.

  (** Walk contributions correspond elementwise to [dp_max_match]'s
      iteration. The [full_mask] / [full_gts] arguments capture what
      the full original lists are; [prefix] is what's been consumed,
      [mask] / [gts] are what remains. *)

  Lemma walk_contributions_eq_map_dp :
    forall (boxes_rest : list Box) (b : Box)
           (full_gts : list GT) (full_mask : list bool)
           (mask : list bool) (gts : list GT) (prefix : list bool)
           (rec : list bool -> R),
      NoDup full_gts ->
      length full_mask = length full_gts ->
      rev prefix ++ mask = full_mask ->
      skipn (length prefix) full_gts = gts ->
      (forall m, length m = length full_gts ->
        rec m = dp_max_match cost GT_eq_dec boxes_rest (mask_to_gts m full_gts)) ->
      walk_contributions b mask gts prefix rec =
      map (fun g => cost b g + dp_max_match cost GT_eq_dec boxes_rest
                                  (dp_remove_first GT_eq_dec g
                                     (mask_to_gts full_mask full_gts)))
          (mask_to_gts mask gts).
  Proof.
    intros boxes_rest b full_gts full_mask.
    induction mask as [|m_bit ms IH];
      intros gts prefix rec Hnd Hlen Hfull Hgts Hrec.
    - cbn. reflexivity.
    - destruct m_bit; destruct gts as [|g rest]; cbn; try reflexivity.
      + (* true bit *)
        cbn.
        assert (Hlen_pre : (length prefix < length full_mask)%nat).
        { rewrite <- Hfull. rewrite length_app. cbn.
          rewrite length_rev. lia. }
        assert (Hnth_mask : nth_error full_mask (length prefix) = Some true).
        { rewrite <- Hfull.
          replace (rev prefix ++ true :: ms)
             with ((rev prefix) ++ true :: ms) by reflexivity.
          rewrite <- (length_rev prefix) at 1.
          apply nth_error_at_prefix_split. }
        assert (Hnth_gts : nth_error full_gts (length prefix) = Some g).
        { (* gts = skipn (length prefix) full_gts = g :: rest implies nth_error = Some g *)
          clear - Hgts.
          revert full_gts Hgts.
          induction prefix as [|p ps IHp]; intros full_gts Hgts; cbn in *.
          - destruct full_gts as [|fh ft]; [discriminate|].
            cbn in Hgts. injection Hgts as Heq _. subst. reflexivity.
          - destruct full_gts as [|fh ft]; [discriminate|].
            apply IHp. cbn in Hgts. exact Hgts. }
        f_equal.
        * (* head match *)
          f_equal.
          assert (Hmod_len : length (rev prefix ++ false :: ms) = length full_gts).
          { rewrite <- Hlen. rewrite <- Hfull.
            rewrite !length_app. cbn. reflexivity. }
          rewrite (Hrec _ Hmod_len).
          f_equal.
          rewrite <- (mask_remove_at_prefix_split prefix true ms).
          rewrite Hfull.
          apply (@mask_remove_to_gts_correspondence (length prefix)
                   full_mask full_gts g Hnd Hlen Hnth_mask Hnth_gts).
        * (* tail by IH *)
          assert (Hfull' : rev (true :: prefix) ++ ms = full_mask).
          { cbn. rewrite <- app_assoc. cbn. exact Hfull. }
          assert (Hgts' : skipn (length (true :: prefix)) full_gts = rest).
          { clear -Hgts.
            revert full_gts Hgts.
            induction prefix as [|p ps IHp]; intros full_gts Hgts; cbn in *.
            - destruct full_gts as [|fh ft]; [discriminate|].
              cbn in Hgts. injection Hgts as _ Heq. subst. reflexivity.
            - destruct full_gts as [|fh ft]; [discriminate|].
              apply IHp. exact Hgts. }
          apply (IH rest (true :: prefix) rec Hnd Hlen Hfull' Hgts' Hrec).
      + (* false bit *)
        assert (Hfull' : rev (false :: prefix) ++ ms = full_mask).
        { cbn. rewrite <- app_assoc. cbn. exact Hfull. }
        assert (Hgts' : skipn (length (false :: prefix)) full_gts = rest).
        { clear -Hgts.
          revert full_gts Hgts.
          induction prefix as [|p ps IHp]; intros full_gts Hgts; cbn in *.
          - destruct full_gts as [|fh ft]; [discriminate|].
            cbn in Hgts. injection Hgts as _ Heq. subst. reflexivity.
          - destruct full_gts as [|fh ft]; [discriminate|].
            apply IHp. exact Hgts. }
        apply (IH rest (false :: prefix) rec Hnd Hlen Hfull' Hgts' Hrec).
  Qed.

  (** ** Connecting [fold_right Rmax 0] to [dp_max_match]'s [Rmax_list]. *)

  Lemma fold_right_Rmax_zero_le_init :
    forall (init : R) (l : list R),
      0 <= init ->
      (forall x, In x l -> 0 <= x) ->
      fold_right Rmax 0 l <= Rmax_list init l.
  Proof.
    intros init l Hinit. unfold Rmax_list.
    induction l as [|x rest IH]; intros Hall; cbn; [exact Hinit|].
    apply Rle_max_compat_l. apply IH.
    intros y Hy. apply Hall. right. assumption.
  Qed.

  (** When [init] is in [l] and all entries are non-negative, the
      [fold_right Rmax 0] form equals the dp-style [Rmax_list init]
      form: both yield the maximum over [l]'s entries, which dominates
      both [0] and [init] by hypothesis. *)

  Lemma fold_right_Rmax_init_geq :
    forall (init : R) (l : list R),
      init <= fold_right Rmax init l.
  Proof.
    intros init l. induction l as [|x rest IH]; cbn; [apply Rle_refl|].
    eapply Rle_trans; [exact IH | apply Rmax_r].
  Qed.

  Lemma fold_right_Rmax_init_in :
    forall (init : R) (l : list R) (x : R),
      In x l -> x <= fold_right Rmax init l.
  Proof.
    intros init l x Hin. induction l as [|y rest IH]; cbn in *; [contradiction|].
    destruct Hin as [Heq | Hin].
    - subst x. apply Rmax_l.
    - eapply Rle_trans; [apply IH; exact Hin | apply Rmax_r].
  Qed.

  Lemma fold_right_Rmax_init_mono :
    forall (i1 i2 : R) (l : list R),
      i1 <= i2 -> fold_right Rmax i1 l <= fold_right Rmax i2 l.
  Proof.
    intros i1 i2 l Hle. induction l as [|x rest IH]; cbn; [exact Hle|].
    apply Rle_max_compat_l. exact IH.
  Qed.

  Lemma Rmax_assoc_perm :
    forall a b c, Rmax a (Rmax b c) = Rmax b (Rmax a c).
  Proof.
    intros a b c.
    apply Rle_antisym.
    - apply Rmax_lub.
      + eapply Rle_trans; [|apply Rmax_r]. apply Rmax_l.
      + apply Rmax_lub.
        * apply Rmax_l.
        * eapply Rle_trans; [|apply Rmax_r]. apply Rmax_r.
    - apply Rmax_lub.
      + eapply Rle_trans; [|apply Rmax_r]. apply Rmax_l.
      + apply Rmax_lub.
        * apply Rmax_l.
        * eapply Rle_trans; [|apply Rmax_r]. apply Rmax_r.
  Qed.

  (** [mask_to_gts] preserves [NoDup] when the underlying [gts] is
      [NoDup]. Selecting a subset by mask cannot introduce duplicates. *)

  Lemma mask_to_gts_NoDup :
    forall (gts : list GT) (mask : list bool),
      NoDup gts -> NoDup (mask_to_gts mask gts).
  Proof.
    intros gts mask. revert gts.
    induction mask as [|m_bit ms IH]; intros gts Hnd.
    - destruct gts; cbn; apply NoDup_nil.
    - destruct m_bit; destruct gts as [|g_h gts_t]; cbn.
      + apply NoDup_nil.
      + (* true bit, gts = g_h :: gts_t *)
        inversion Hnd as [|x rest_l Hnotin Hnd_rest]; subst.
        apply NoDup_cons.
        * intros Hin. apply Hnotin.
          clear -Hin. revert gts_t Hin.
          induction ms as [|m0 ms0 IHm]; intros gts_t Hin.
          -- cbn in Hin. contradiction.
          -- destruct gts_t as [|gh' gtst'].
             ++ destruct m0; cbn in Hin; contradiction.
             ++ destruct m0; cbn in Hin.
                ** destruct Hin as [Heq | Hin]; [left; assumption|].
                   right. apply (IHm gtst' Hin).
                ** right. apply (IHm gtst' Hin).
        * apply IH. assumption.
      + apply NoDup_nil.
      + (* false bit, gts = g_h :: gts_t *)
        inversion Hnd. apply IH. assumption.
  Qed.

  Lemma fold_right_Rmax_pull_init :
    forall (init : R) (l : list R),
      0 <= init ->
      fold_right Rmax init l = Rmax init (fold_right Rmax 0 l).
  Proof.
    intros init l Hinit. induction l as [|x rest IH]; cbn.
    - rewrite (Rmax_left init 0) by lra. reflexivity.
    - rewrite IH. apply Rmax_assoc_perm.
  Qed.

  Lemma fold_right_Rmax_zero_eq_when_init_in :
    forall (init : R) (l : list R),
      0 <= init ->
      In init l ->
      (forall x, In x l -> 0 <= x) ->
      fold_right Rmax 0 l = Rmax_list init l.
  Proof.
    intros init l Hinit Hin Hall. unfold Rmax_list.
    apply Rle_antisym.
    - induction l as [|x rest IH]; cbn in *; [exact Hinit|].
      destruct Hin as [Heq | Hin].
      + subst x. apply Rle_max_compat_l. apply fold_right_Rmax_init_mono. exact Hinit.
      + apply Rle_max_compat_l. apply IH; [exact Hin|].
        intros y Hy. apply Hall. right. assumption.
    - rewrite fold_right_Rmax_pull_init by exact Hinit.
      apply Rmax_lub; [|apply Rle_refl].
      apply (fold_right_Rmax_init_in 0 l init Hin).
  Qed.

  (** ** Master theorem: [bitmask_dp = dp_max_match] under NoDup. *)

  Theorem bitmask_dp_eq_dp_max_match :
    forall (boxes : list Box) (gts : list GT) (mask : list bool),
      NoDup gts ->
      length mask = length gts ->
      bitmask_dp cost boxes gts mask =
      dp_max_match cost GT_eq_dec boxes (mask_to_gts mask gts).
  Proof.
    intros boxes. induction boxes as [|b rest IH]; intros gts mask Hnd Hlen.
    - cbn. reflexivity.
    - cbn.
      destruct gts as [|g0 gs] eqn:Egts.
      + destruct mask; [|discriminate Hlen]. cbn. reflexivity.
      + unfold mask_max_R.
        rewrite mask_max_R_aux_eq_walk.
        assert (Hrec : forall m, length m = length (g0 :: gs) ->
          bitmask_dp cost rest (g0 :: gs) m =
          dp_max_match cost GT_eq_dec rest (mask_to_gts m (g0 :: gs))).
        { intros m Hm_len. apply IH; assumption. }
        rewrite (@walk_contributions_eq_map_dp rest b (g0 :: gs) mask
                  mask (g0 :: gs) []
                  (fun m => bitmask_dp cost rest (g0 :: gs) m)
                  Hnd Hlen
                  (eq_refl : rev [] ++ mask = mask)
                  (eq_refl : skipn (length (@nil bool)) (g0 :: gs) = g0 :: gs)
                  Hrec).
        destruct (mask_to_gts mask (g0 :: gs)) as [|g0' rest'] eqn:Eselect.
        * cbn. reflexivity.
        * cbn [map].
          unfold dp_max_match. fold (@dp_max_match Box GT cost GT_eq_dec).
          set (f := fun g : GT =>
                      cost b g + dp_max_match cost GT_eq_dec rest
                        (dp_remove_first GT_eq_dec g (g0' :: rest'))).
          fold f.
          unfold Rmax_list. cbn [map fold_right].
          rewrite Rmax_self_fold_right. reflexivity.
  Qed.

  (** ** Master corollary: [bitmask_optimal] equals brute-force matching weight. *)

  Theorem bitmask_optimal_eq_brute_weight :
    forall (boxes : list Box) (gts : list GT),
      NoDup gts ->
      bitmask_optimal cost boxes gts =
      matching_weight cost (brute_match cost boxes gts).
  Proof.
    intros boxes gts Hnd.
    unfold bitmask_optimal.
    rewrite (@bitmask_dp_eq_dp_max_match boxes gts (all_true (length gts))
              Hnd (all_true_length _)).
    rewrite mask_to_gts_all_true.
    apply (@dp_max_match_eq_brute_weight Box GT cost GT_eq_dec boxes gts Hnd).
  Qed.

End BitmaskMatchingCorrectness.

Local Close Scope R_scope.

(** ** IEEE 754 binary64 representation.

    The file already defines [b64_repr] (sign + 11-bit exponent +
    52-bit mantissa) and proves [b64_normal_quantize_relative_error]:
    quantization at exponent [e] satisfies the [2^{-53}|x|] bound on
    the normal range. What was missing is the *bit decomposition*: a
    decoder [b64_repr_to_R], range-coverage of the normal interval,
    and decode-injectivity. *)

Definition b64_bias : Z := 1023.
Definition b64_normal_emin : Z := 1.
Definition b64_normal_emax : Z := 2046.
Definition b64_max_mantissa : nat := (2 ^ 52 - 1)%nat.

Local Open Scope R_scope.

Definition b64_repr_to_R (r : b64_repr) : R :=
  let s := if b64_sign r then -1 else 1 in
  let e := b64_exponent r in
  let m := INR (b64_mantissa r) in
  s * (1 + m / 2 ^ 52) * powerRZ 2 (e - b64_bias).

(** R-side normality: the mantissa value [INR m] is bounded by
    [2^52 - 1], stated as a real-valued inequality to avoid the
    [2^52] nat-reduction trap. *)

Definition b64_repr_normal (r : b64_repr) : Prop :=
  (b64_normal_emin <= b64_exponent r <= b64_normal_emax)%Z /\
  INR (b64_mantissa r) <= 2 ^ 52 - 1.

(** Mantissa scale [1 + m/2^52] lies in [[1, 2)] for representable [m]. *)

Lemma b64_mantissa_scale_range :
  forall m : nat,
    INR m <= 2 ^ 52 - 1 ->
    1 <= 1 + INR m / 2 ^ 52 < 2.
Proof.
  intros m Hm.
  assert (Hpow_pos : 0 < 2 ^ 52) by (apply pow_lt; lra).
  pose proof (pos_INR m) as Hm_nn.
  split.
  - assert (0 <= INR m / 2 ^ 52).
    { unfold Rdiv. apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]. }
    lra.
  - assert (INR m / 2 ^ 52 < 1).
    { apply Rmult_lt_reg_r with (r := 2 ^ 52); [exact Hpow_pos|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      rewrite Rmult_1_r, Rmult_1_l. lra. }
    lra.
Qed.

(** Range coverage. *)

Theorem b64_repr_to_R_normal_range :
  forall r,
    b64_repr_normal r ->
    powerRZ 2 (b64_exponent r - b64_bias) <= Rabs (b64_repr_to_R r) <
    powerRZ 2 (b64_exponent r - b64_bias + 1).
Proof.
  intros r [He Hm].
  unfold b64_repr_to_R.
  pose proof (@b64_mantissa_scale_range (b64_mantissa r) Hm) as [Hscale_lo Hscale_hi].
  pose proof (powerRZ_2_pos (b64_exponent r - b64_bias)) as Hpow_pos.
  set (s := if b64_sign r then -1 else 1).
  set (m := INR (b64_mantissa r)) in *.
  set (q := 1 + m / 2 ^ 52) in *.
  set (p := powerRZ 2 (b64_exponent r - b64_bias)) in *.
  assert (Habs_s : Rabs s = 1).
  { unfold s. destruct (b64_sign r).
    - replace (-1) with (-(1)) by lra. rewrite Rabs_Ropp, Rabs_R1. reflexivity.
    - apply Rabs_R1. }
  assert (Hq_nn : 0 <= q) by lra.
  assert (Hp_nn : 0 <= p) by lra.
  assert (Habs_eq : Rabs (s * q * p) = q * p).
  { rewrite !Rabs_mult, Habs_s, Rmult_1_l.
    rewrite (Rabs_pos_eq q Hq_nn).
    rewrite (Rabs_pos_eq p Hp_nn).
    reflexivity. }
  rewrite Habs_eq.
  split.
  - replace p with (1 * p) at 1 by lra.
    apply Rmult_le_compat_r; lra.
  - replace (powerRZ 2 (b64_exponent r - b64_bias + 1))
       with (2 * p) by
      (unfold p; replace (b64_exponent r - b64_bias + 1)%Z
                     with ((b64_exponent r - b64_bias) + 1)%Z by lia;
       rewrite powerRZ_add by lra; simpl; lra).
    apply Rmult_lt_compat_r; lra.
Qed.

(** Monotonicity of [powerRZ 2 z] in the exponent. Routed through
    [Rpower] using [powerRZ 2 z = exp (IZR z * ln 2)]. *)

Lemma ln_2_pos : 0 < ln 2.
Proof.
  rewrite <- ln_1. apply ln_increasing; lra.
Qed.

Lemma powerRZ_2_mono :
  forall e1 e2 : Z,
    (e1 <= e2)%Z -> powerRZ 2 e1 <= powerRZ 2 e2.
Proof.
  intros e1 e2 Hle.
  rewrite !powerRZ_Rpower by lra.
  unfold Rpower.
  destruct (proj1 (Z.le_lteq e1 e2) Hle) as [Hlt | Heq].
  - apply Rlt_le. apply exp_increasing.
    apply Rmult_lt_compat_r; [exact ln_2_pos|].
    apply IZR_lt. exact Hlt.
  - rewrite Heq. apply Rle_refl.
Qed.

(** Disjoint-interval lemma needed for exponent uniqueness. *)

Lemma powerRZ_2_intervals_disjoint :
  forall e1 e2 x,
    (e1 < e2)%Z ->
    powerRZ 2 e1 <= x < powerRZ 2 (e1 + 1) ->
    ~ (powerRZ 2 e2 <= x).
Proof.
  intros e1 e2 x Hlt [_ Hhi] Hge.
  apply Rle_not_lt in Hge. apply Hge.
  eapply Rlt_le_trans; [exact Hhi|].
  apply powerRZ_2_mono. lia.
Qed.

(** Exponent unique from magnitude. *)

Theorem b64_repr_exponent_unique :
  forall r1 r2,
    b64_repr_normal r1 ->
    b64_repr_normal r2 ->
    Rabs (b64_repr_to_R r1) = Rabs (b64_repr_to_R r2) ->
    b64_exponent r1 = b64_exponent r2.
Proof.
  intros r1 r2 Hn1 Hn2 Hmag.
  pose proof (@b64_repr_to_R_normal_range r1 Hn1) as [H1lo H1hi].
  pose proof (@b64_repr_to_R_normal_range r2 Hn2) as [H2lo H2hi].
  destruct (Z.lt_trichotomy (b64_exponent r1) (b64_exponent r2))
    as [Hlt | [Heq | Hgt]].
  - exfalso.
    assert (Hge2 : powerRZ 2 (b64_exponent r2 - b64_bias) <= Rabs (b64_repr_to_R r1)).
    { rewrite Hmag. exact H2lo. }
    apply (@powerRZ_2_intervals_disjoint (b64_exponent r1 - b64_bias)
                                         (b64_exponent r2 - b64_bias)
                                         (Rabs (b64_repr_to_R r1)));
      [lia | split; assumption | exact Hge2].
  - assumption.
  - exfalso.
    assert (Hge1 : powerRZ 2 (b64_exponent r1 - b64_bias) <= Rabs (b64_repr_to_R r2)).
    { rewrite <- Hmag. exact H1lo. }
    apply (@powerRZ_2_intervals_disjoint (b64_exponent r2 - b64_bias)
                                         (b64_exponent r1 - b64_bias)
                                         (Rabs (b64_repr_to_R r2)));
      [lia | split; assumption | exact Hge1].
Qed.

(** Mantissa unique within an exponent class. *)

Theorem b64_repr_mantissa_unique :
  forall r1 r2,
    b64_repr_normal r1 ->
    b64_repr_normal r2 ->
    b64_exponent r1 = b64_exponent r2 ->
    Rabs (b64_repr_to_R r1) = Rabs (b64_repr_to_R r2) ->
    b64_mantissa r1 = b64_mantissa r2.
Proof.
  intros r1 r2 [He1 Hm1] [He2 Hm2] Heeq Hmag.
  unfold b64_repr_to_R in Hmag.
  rewrite Heeq in Hmag.
  pose proof (@b64_mantissa_scale_range (b64_mantissa r1) Hm1) as [Hq1_lo Hq1_hi].
  pose proof (@b64_mantissa_scale_range (b64_mantissa r2) Hm2) as [Hq2_lo Hq2_hi].
  pose proof (powerRZ_2_pos (b64_exponent r2 - b64_bias)) as Hp_pos.
  set (s1 := if b64_sign r1 then -1 else 1) in *.
  set (s2 := if b64_sign r2 then -1 else 1) in *.
  set (m1 := INR (b64_mantissa r1)) in *.
  set (m2 := INR (b64_mantissa r2)) in *.
  set (q1 := 1 + m1 / 2 ^ 52) in *.
  set (q2 := 1 + m2 / 2 ^ 52) in *.
  set (p := powerRZ 2 (b64_exponent r2 - b64_bias)) in *.
  assert (Habs1 : Rabs s1 = 1).
  { unfold s1. destruct (b64_sign r1).
    - replace (-1) with (-(1)) by lra. rewrite Rabs_Ropp, Rabs_R1. reflexivity.
    - apply Rabs_R1. }
  assert (Habs2 : Rabs s2 = 1).
  { unfold s2. destruct (b64_sign r2).
    - replace (-1) with (-(1)) by lra. rewrite Rabs_Ropp, Rabs_R1. reflexivity.
    - apply Rabs_R1. }
  assert (Hq1_nn : 0 <= q1) by lra.
  assert (Hq2_nn : 0 <= q2) by lra.
  assert (Hp_nn : 0 <= p) by lra.
  assert (Hmag_eq : q1 * p = q2 * p).
  { rewrite !Rabs_mult in Hmag.
    rewrite Habs1, Habs2, !Rmult_1_l in Hmag.
    rewrite (Rabs_pos_eq q1 Hq1_nn) in Hmag.
    rewrite (Rabs_pos_eq q2 Hq2_nn) in Hmag.
    rewrite (Rabs_pos_eq p Hp_nn) in Hmag.
    exact Hmag. }
  assert (Hq_eq : q1 = q2).
  { apply Rmult_eq_reg_r with (r := p); [exact Hmag_eq | lra]. }
  unfold q1, q2 in Hq_eq.
  assert (Hm_R_eq : m1 = m2) by lra.
  unfold m1, m2 in Hm_R_eq.
  apply INR_eq. assumption.
Qed.

(** Decode injectivity. *)

Theorem b64_repr_decode_inj :
  forall r1 r2,
    b64_repr_normal r1 ->
    b64_repr_normal r2 ->
    b64_repr_to_R r1 = b64_repr_to_R r2 ->
    r1 = r2.
Proof.
  intros r1 r2 Hn1 Hn2 Heq.
  assert (Hmag : Rabs (b64_repr_to_R r1) = Rabs (b64_repr_to_R r2))
    by (rewrite Heq; reflexivity).
  pose proof (@b64_repr_exponent_unique r1 r2 Hn1 Hn2 Hmag) as Heeq.
  pose proof (@b64_repr_mantissa_unique r1 r2 Hn1 Hn2 Heeq Hmag) as Hmeq.
  assert (Hsign : b64_sign r1 = b64_sign r2).
  { destruct Hn1 as [_ Hm1]. destruct Hn2 as [_ Hm2].
    unfold b64_repr_to_R in Heq. rewrite Heeq, Hmeq in Heq.
    pose proof (@b64_mantissa_scale_range (b64_mantissa r2) Hm2) as [Hq_lo _].
    pose proof (powerRZ_2_pos (b64_exponent r2 - b64_bias)) as Hp_pos.
    set (e := b64_exponent r2) in *.
    set (p := powerRZ 2 (e - b64_bias)) in *.
    set (m := INR (b64_mantissa r2)) in *.
    set (q := 1 + m / 2 ^ 52) in *.
    assert (Hqp_pos : 0 < q * p).
    { apply Rmult_lt_0_compat; lra. }
    set (s1 := if b64_sign r1 then -1 else 1) in *.
    set (s2 := if b64_sign r2 then -1 else 1) in *.
    assert (Hs : s1 = s2).
    { apply Rmult_eq_reg_r with (r := q * p); [|lra].
      replace (s1 * (q * p)) with (s1 * q * p) by ring.
      replace (s2 * (q * p)) with (s2 * q * p) by ring.
      exact Heq. }
    unfold s1, s2 in Hs.
    destruct (b64_sign r1); destruct (b64_sign r2); congruence || lra. }
  destruct r1, r2. simpl in *. subst. reflexivity.
Qed.

(** Range envelope: every normal-range repr decodes into the IEEE
    binary64 normal interval [[2^{-1022}, 2^{1024})] in absolute value. *)

Theorem b64_repr_to_R_envelope :
  forall r,
    b64_repr_normal r ->
    powerRZ 2 (-1022) <= Rabs (b64_repr_to_R r) < powerRZ 2 1024.
Proof.
  intros r Hnorm. pose proof Hnorm as [He _].
  pose proof (@b64_repr_to_R_normal_range r Hnorm) as [Hlo Hhi].
  unfold b64_normal_emin, b64_normal_emax in He.
  split.
  - eapply Rle_trans; [|exact Hlo].
    apply (@powerRZ_2_mono). unfold b64_bias. lia.
  - eapply Rlt_le_trans; [exact Hhi|].
    apply (@powerRZ_2_mono). unfold b64_bias. lia.
Qed.

(** ** Constructive encoder for the normal range.

    Given [|x|] in the normal interval [[2^(e-1023), 2^(e-1022))],
    [b64_encode_normal sign e x] returns the [b64_repr] whose mantissa
    is [floor((|x|/2^(e-1023) - 1) * 2^52)] (clamped to nonneg). The
    encoder is well-formed (mantissa in range) and the round-trip
    error bound [|b64_repr_to_R (encode ...) - x| <= 2^(e-1023-52)]
    follows directly from [Int_part]'s 1-unit floor accuracy. *)

Definition b64_encode_normal (sign : bool) (e : Z) (x : R) : b64_repr :=
  let frac := Rabs x / powerRZ 2 (e - b64_bias) - 1 in
  let m_R := frac * 2 ^ 52 in
  Build_b64_repr sign e (Z.to_nat (Z.max 0 (Int_part m_R))).

Lemma b64_encode_exponent :
  forall sign e x, b64_exponent (b64_encode_normal sign e x) = e.
Proof. intros. reflexivity. Qed.

Lemma b64_encode_sign :
  forall sign e x, b64_sign (b64_encode_normal sign e x) = sign.
Proof. intros. reflexivity. Qed.

(** Mantissa [INR m] equals [IZR (Z.max 0 (Int_part m_R))]. *)

Lemma INR_Z_to_nat_max_0 :
  forall z : Z, INR (Z.to_nat (Z.max 0 z)) = IZR (Z.max 0 z).
Proof.
  intros z. rewrite INR_IZR_INZ. f_equal.
  rewrite Z2Nat.id; [reflexivity|lia].
Qed.

(** Mantissa bound: encoded mantissa value (as a real) is at most
    [2^52 - 1]. Direct R-side reasoning: [Int_part m_R <= m_R < 2^52],
    so [Z.max 0 (Int_part m_R) <= 2^52 - 1] when [|x| < 2^(e-1022)]. *)

Lemma b64_encode_mantissa_bound :
  forall sign e x,
    Rabs x < powerRZ 2 (e - b64_bias + 1) ->
    INR (b64_mantissa (b64_encode_normal sign e x)) <= 2 ^ 52 - 1.
Proof.
  intros sign e x Hhi. unfold b64_encode_normal. simpl.
  rewrite INR_Z_to_nat_max_0.
  set (frac := Rabs x / powerRZ 2 (e - b64_bias) - 1).
  set (m_R := frac * 2 ^ 52).
  pose proof (powerRZ_2_pos (e - b64_bias)) as Hpow_pos.
  pose proof (base_Int_part m_R) as [Hint_lo Hint_hi].
  assert (Hpow52_pos : 0 < 2 ^ 52) by (apply pow_lt; lra).
  (* Need: |x| < 2^(e - 1023 + 1) = 2 * 2^(e-1023) implies frac < 1. *)
  assert (Hfrac_hi : frac < 1).
  { unfold frac. apply Rmult_lt_reg_r with (r := powerRZ 2 (e - b64_bias));
      [exact Hpow_pos|].
    replace ((Rabs x / powerRZ 2 (e - b64_bias) - 1) *
             powerRZ 2 (e - b64_bias))
       with (Rabs x - powerRZ 2 (e - b64_bias)) by (field; lra).
    replace (1 * powerRZ 2 (e - b64_bias)) with (powerRZ 2 (e - b64_bias)) by lra.
    replace (powerRZ 2 (e - b64_bias + 1))
       with (2 * powerRZ 2 (e - b64_bias)) in Hhi.
    - lra.
    - replace (e - b64_bias + 1)%Z with ((e - b64_bias) + 1)%Z by lia.
      rewrite powerRZ_add by lra. simpl. lra. }
  (* Hence m_R = frac * 2^52 < 2^52. *)
  assert (Hm_R_hi : m_R < 2 ^ 52).
  { unfold m_R. apply Rmult_lt_reg_r with (r := / 2 ^ 52);
      [apply Rinv_0_lt_compat; exact Hpow52_pos|].
    rewrite Rmult_assoc, Rinv_r by lra.
    rewrite Rmult_1_r. lra. }
  (* Hint_lo says IZR (Int_part m_R) <= m_R. Hence Int_part m_R < 2^52
     in IZR, hence Int_part m_R <= 2^52 - 1 in Z, after IZR_lt and
     converting; in IZR, IZR (Int_part m_R) <= 2^52 - 1. *)
  assert (Hipart_lt : IZR (Int_part m_R) < 2 ^ 52).
  { eapply Rle_lt_trans; [exact Hint_lo | exact Hm_R_hi]. }
  assert (Hpow_int : 2 ^ 52 = IZR (2 ^ 52)%Z).
  { rewrite pow_IZR. simpl. lra. }
  assert (Hipart_lt_Z : (Int_part m_R < 2 ^ 52)%Z).
  { apply lt_IZR. rewrite <- Hpow_int. exact Hipart_lt. }
  (* Z.max 0 (Int_part m_R) <= 2^52 - 1: both args <= 2^52 - 1. *)
  assert (Hmax_le_Z : (Z.max 0 (Int_part m_R) <= 2 ^ 52 - 1)%Z).
  { apply Z.max_lub; lia. }
  apply IZR_le in Hmax_le_Z.
  rewrite minus_IZR in Hmax_le_Z.
  rewrite <- Hpow_int in Hmax_le_Z.
  exact Hmax_le_Z.
Qed.

(** Encoded repr is well-formed. *)

Theorem b64_encode_normal_well_formed :
  forall sign e x,
    (b64_normal_emin <= e <= b64_normal_emax)%Z ->
    Rabs x < powerRZ 2 (e - b64_bias + 1) ->
    b64_repr_normal (b64_encode_normal sign e x).
Proof.
  intros sign e x He Hhi. split.
  - rewrite b64_encode_exponent. assumption.
  - apply b64_encode_mantissa_bound. assumption.
Qed.

(** Encode-decode round-trip closeness. The decoded magnitude is
    within [2^(e-1023-52) = 2^(-53) * 2^(e-1023)] of [|x|], which after
    pairing with [|x| >= 2^(e-1023)] gives a relative error of at most
    [2^(-52)] (slightly looser than round-to-nearest's [2^(-53)] since
    this encoder uses floor). *)

Theorem b64_encode_decode_close :
  forall sign e x,
    (b64_normal_emin <= e <= b64_normal_emax)%Z ->
    powerRZ 2 (e - b64_bias) <= Rabs x < powerRZ 2 (e - b64_bias + 1) ->
    sign = (if Rlt_dec x 0 then true else false) ->
    Rabs (b64_repr_to_R (b64_encode_normal sign e x) - x) <=
      powerRZ 2 (e - b64_bias - 52).
Proof.
  intros sign e x He [Hlo Hhi] Hsign.
  set (p := powerRZ 2 (e - b64_bias)) in *.
  pose proof (powerRZ_2_pos (e - b64_bias)) as Hp_pos. fold p in Hp_pos.
  set (frac := Rabs x / p - 1) in *.
  assert (Hfrac_lo : 0 <= frac).
  { unfold frac. apply Rmult_le_reg_r with (r := p); [exact Hp_pos|].
    replace ((Rabs x / p - 1) * p) with (Rabs x - p) by (field; lra).
    replace (0 * p) with 0 by ring. lra. }
  assert (Hfrac_hi : frac < 1).
  { unfold frac. apply Rmult_lt_reg_r with (r := p); [exact Hp_pos|].
    replace ((Rabs x / p - 1) * p) with (Rabs x - p) by (field; lra).
    replace (1 * p) with p by lra.
    replace (powerRZ 2 (e - b64_bias + 1)) with (2 * p) in Hhi
      by (unfold p;
          replace (e - b64_bias + 1)%Z with ((e - b64_bias) + 1)%Z by lia;
          rewrite powerRZ_add by lra; simpl; lra).
    lra. }
  set (m_R := frac * 2 ^ 52).
  assert (Hpow52_pos : 0 < 2 ^ 52) by (apply pow_lt; lra).
  assert (Hm_R_lo : 0 <= m_R)
    by (unfold m_R; apply Rmult_le_pos; [exact Hfrac_lo | lra]).
  assert (Hm_R_hi : m_R < 2 ^ 52).
  { unfold m_R. apply Rmult_lt_reg_r with (r := / 2 ^ 52);
      [apply Rinv_0_lt_compat; exact Hpow52_pos|].
    rewrite Rmult_assoc, Rinv_r by lra.
    rewrite Rmult_1_r. lra. }
  pose proof (base_Int_part m_R) as [Hint_lo Hint_hi].
  (* m_R >= 0, so Int_part m_R > -1; since integer, >= 0. *)
  assert (HIntp_gt : -1 < IZR (Int_part m_R)) by lra.
  assert (HIntp_gt_Z : (-1 < Int_part m_R)%Z).
  { apply lt_IZR. simpl. lra. }
  assert (HIntp_lo_Z : (0 <= Int_part m_R)%Z) by lia.
  assert (Hmax_eq : Z.max 0 (Int_part m_R) = Int_part m_R).
  { apply Z.max_r. assumption. }
  unfold b64_repr_to_R, b64_encode_normal.
  cbn [b64_sign b64_exponent b64_mantissa].
  change (Rabs x / powerRZ 2 (e - b64_bias) - 1) with frac.
  change (frac * 2 ^ 52) with m_R.
  rewrite Hmax_eq.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id by exact HIntp_lo_Z.
  set (s := if sign then -1 else 1).
  fold p.
  set (decoded := s * (1 + IZR (Int_part m_R) / 2 ^ 52) * p).
  assert (Habs_s : Rabs s = 1).
  { unfold s. destruct sign.
    - replace (-1) with (-(1)) by lra. rewrite Rabs_Ropp, Rabs_R1. reflexivity.
    - apply Rabs_R1. }
  assert (Hxabs_split : Rabs x = p + frac * p)
    by (unfold frac; field; lra).
  assert (Hsx : x = s * Rabs x).
  { unfold s. subst sign. destruct (Rlt_dec x 0) as [Hxlt | Hxge].
    - rewrite (Rabs_left _ Hxlt). lra.
    - assert (0 <= x) by lra. rewrite Rabs_right by lra. lra. }
  assert (Hgoal_step :
    decoded - x = s * ((IZR (Int_part m_R) / 2 ^ 52) * p - frac * p)).
  { unfold decoded. rewrite Hsx, Hxabs_split.
    replace (s * (p + frac * p))
       with (s * p + s * (frac * p)) by ring. ring. }
  rewrite Hgoal_step.
  rewrite Rabs_mult, Habs_s, Rmult_1_l.
  assert (Hdiff_form :
    (IZR (Int_part m_R) / 2 ^ 52) * p - frac * p =
    (IZR (Int_part m_R) - m_R) / 2 ^ 52 * p).
  { unfold m_R. field. }
  rewrite Hdiff_form.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq p) by lra.
  assert (Habs_div :
    Rabs ((IZR (Int_part m_R) - m_R) / 2 ^ 52) =
    Rabs (IZR (Int_part m_R) - m_R) / 2 ^ 52).
  { unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ 2 ^ 52)) by (left; apply Rinv_0_lt_compat; lra).
    reflexivity. }
  rewrite Habs_div.
  assert (Habs_le_1 : Rabs (IZR (Int_part m_R) - m_R) <= 1).
  { unfold Rabs. destruct (Rcase_abs (IZR (Int_part m_R) - m_R)); lra. }
  assert (Hdiv_le : Rabs (IZR (Int_part m_R) - m_R) / 2 ^ 52 <= / 2 ^ 52).
  { apply Rmult_le_reg_r with (r := 2 ^ 52); [exact Hpow52_pos|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
    exact Habs_le_1. }
  apply Rle_trans with (/ 2 ^ 52 * p).
  - apply Rmult_le_compat_r; [lra | exact Hdiv_le].
  - assert (Hgoal_pow : / 2 ^ 52 * p = powerRZ 2 (e - b64_bias - 52)).
    { unfold p.
      replace (e - b64_bias - 52)%Z
         with ((e - b64_bias) + (-52))%Z by lia.
      rewrite powerRZ_add by lra.
      assert (Hneg52 : powerRZ 2 (-52) = / 2 ^ 52).
      { simpl. unfold Z.pow_pos. simpl. unfold Pos.iter. simpl. field. }
      rewrite Hneg52. lra. }
    rewrite Hgoal_pow. apply Rle_refl.
Qed.

(** ** Constructive encoder for the subnormal range.

    Given [|x| < 2^(-1022)] (subnormal interval), [b64_encode_subnormal
    sign x] returns the [b64_repr] with exponent field [0] and mantissa
    [floor(|x| / 2^(-1074))]. Subnormal binary64 values use the formula
    [value = (-1)^sign * mantissa * 2^(-1074)] without an implicit
    leading bit (in contrast to normal-range, which uses [(1 + m/2^52) *
    2^(e-1023)]). The dedicated subnormal decoder
    [b64_subnormal_to_R] applies this formula. The encoder is
    well-formed (mantissa in range), and the round-trip error is
    bounded by [2^(-1074)] (the subnormal ULP). *)

Definition b64_repr_subnormal (r : b64_repr) : Prop :=
  b64_exponent r = 0%Z /\ INR (b64_mantissa r) <= 2 ^ 52 - 1.

Definition b64_subnormal_to_R (r : b64_repr) : R :=
  let s := if b64_sign r then -1 else 1 in
  s * INR (b64_mantissa r) * powerRZ 2 (-1074).

Definition b64_encode_subnormal (sign : bool) (x : R) : b64_repr :=
  let m_R := Rabs x / powerRZ 2 (-1074) in
  Build_b64_repr sign 0%Z (Z.to_nat (Z.max 0 (Int_part m_R))).

Lemma b64_encode_subnormal_exponent :
  forall sign x, b64_exponent (b64_encode_subnormal sign x) = 0%Z.
Proof. intros. reflexivity. Qed.

Lemma b64_encode_subnormal_sign :
  forall sign x, b64_sign (b64_encode_subnormal sign x) = sign.
Proof. intros. reflexivity. Qed.

(** Mantissa bound: when [|x| < 2^(-1022)], the encoded mantissa is at
    most [2^52 - 1]. Uses the identity [2^(-1022) = 2^52 * 2^(-1074)]. *)

Lemma powerRZ_2_neg1022_eq :
  powerRZ 2 (-1022) = 2 ^ 52 * powerRZ 2 (-1074).
Proof.
  replace (-1022)%Z with (52 + (-1074))%Z by lia.
  rewrite powerRZ_add by lra.
  reflexivity.
Qed.

Lemma b64_encode_subnormal_mantissa_bound :
  forall sign x,
    Rabs x < powerRZ 2 (-1022) ->
    INR (b64_mantissa (b64_encode_subnormal sign x)) <= 2 ^ 52 - 1.
Proof.
  intros sign x Hhi. unfold b64_encode_subnormal. simpl.
  rewrite INR_Z_to_nat_max_0.
  set (m_R := Rabs x / powerRZ 2 (-1074)).
  pose proof (powerRZ_2_pos (-1074)) as Hq_pos.
  pose proof (Rabs_pos x) as Hx_nn.
  pose proof (base_Int_part m_R) as [Hint_lo Hint_hi].
  assert (Hpow52_pos : 0 < 2 ^ 52) by (apply pow_lt; lra).
  rewrite powerRZ_2_neg1022_eq in Hhi.
  assert (Hm_R_hi : m_R < 2 ^ 52).
  { unfold m_R. apply Rmult_lt_reg_r with (r := powerRZ 2 (-1074));
      [exact Hq_pos|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
    rewrite Rmult_1_r. exact Hhi. }
  assert (Hipart_lt : IZR (Int_part m_R) < 2 ^ 52).
  { eapply Rle_lt_trans; [exact Hint_lo | exact Hm_R_hi]. }
  assert (Hpow_int : 2 ^ 52 = IZR (2 ^ 52)%Z).
  { rewrite pow_IZR. simpl. lra. }
  assert (Hipart_lt_Z : (Int_part m_R < 2 ^ 52)%Z).
  { apply lt_IZR. rewrite <- Hpow_int. exact Hipart_lt. }
  assert (Hmax_le_Z : (Z.max 0 (Int_part m_R) <= 2 ^ 52 - 1)%Z).
  { apply Z.max_lub; lia. }
  apply IZR_le in Hmax_le_Z.
  rewrite minus_IZR in Hmax_le_Z.
  rewrite <- Hpow_int in Hmax_le_Z.
  exact Hmax_le_Z.
Qed.

Theorem b64_encode_subnormal_well_formed :
  forall sign x,
    Rabs x < powerRZ 2 (-1022) ->
    b64_repr_subnormal (b64_encode_subnormal sign x).
Proof.
  intros sign x Hhi. split.
  - rewrite b64_encode_subnormal_exponent. reflexivity.
  - apply b64_encode_subnormal_mantissa_bound. assumption.
Qed.

(** Encode-decode round-trip closeness for subnormals: the decoded
    magnitude is within [2^(-1074)] of [|x|] (one subnormal ULP). *)

Theorem b64_encode_subnormal_decode_close :
  forall sign x,
    Rabs x < powerRZ 2 (-1022) ->
    sign = (if Rlt_dec x 0 then true else false) ->
    Rabs (b64_subnormal_to_R (b64_encode_subnormal sign x) - x) <=
      powerRZ 2 (-1074).
Proof.
  intros sign x Hhi Hsign.
  set (q := powerRZ 2 (-1074)).
  pose proof (powerRZ_2_pos (-1074)) as Hq_pos. fold q in Hq_pos.
  set (m_R := Rabs x / q).
  pose proof (Rabs_pos x) as Hx_nn.
  pose proof (base_Int_part m_R) as [Hint_lo Hint_hi].
  assert (Hm_R_nn : 0 <= m_R).
  { unfold m_R, Rdiv. apply Rmult_le_pos;
      [assumption | left; apply Rinv_0_lt_compat; exact Hq_pos]. }
  assert (HIntp_gt : -1 < IZR (Int_part m_R)) by lra.
  assert (HIntp_gt_Z : (-1 < Int_part m_R)%Z).
  { apply lt_IZR. simpl. lra. }
  assert (HIntp_lo_Z : (0 <= Int_part m_R)%Z) by lia.
  assert (Hmax_eq : Z.max 0 (Int_part m_R) = Int_part m_R).
  { apply Z.max_r. assumption. }
  unfold b64_subnormal_to_R, b64_encode_subnormal.
  cbn [b64_sign b64_exponent b64_mantissa].
  fold q. fold m_R.
  rewrite Hmax_eq.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id by exact HIntp_lo_Z.
  set (s := if sign then -1 else 1).
  set (decoded := s * IZR (Int_part m_R) * q).
  assert (Hsx : x = s * Rabs x).
  { unfold s. subst sign. destruct (Rlt_dec x 0) as [Hxlt | Hxge].
    - rewrite (Rabs_left _ Hxlt). lra.
    - assert (0 <= x) by lra. rewrite Rabs_right by lra. lra. }
  assert (Habs_s : Rabs s = 1).
  { unfold s. destruct sign.
    - replace (-1) with (-(1)) by lra. rewrite Rabs_Ropp, Rabs_R1. reflexivity.
    - apply Rabs_R1. }
  assert (Hgoal_step :
    decoded - x = s * (IZR (Int_part m_R) * q - Rabs x)).
  { unfold decoded. rewrite Hsx at 1. ring. }
  rewrite Hgoal_step.
  rewrite Rabs_mult, Habs_s, Rmult_1_l.
  assert (Hdiff_form :
    IZR (Int_part m_R) * q - Rabs x =
    (IZR (Int_part m_R) - m_R) * q).
  { unfold m_R. field. lra. }
  rewrite Hdiff_form.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq q) by lra.
  assert (Habs_le_1 : Rabs (IZR (Int_part m_R) - m_R) <= 1).
  { unfold Rabs. destruct (Rcase_abs (IZR (Int_part m_R) - m_R)); lra. }
  apply Rle_trans with (1 * q); [|lra].
  apply Rmult_le_compat_r; [lra | exact Habs_le_1].
Qed.

Local Close Scope R_scope.

(** ** Massart-style uniform deviation bound for finite hypothesis classes.

    A practical surrogate for the Rademacher complexity machinery
    Stdlib does not provide. For a finite class of [M] losses each
    bounded uniformly with high probability via Markov, the union
    bound caps the worst-case deviation by [M * V / eps^2 / delta]
    where [V] is the per-loss variance bound and [delta] is the
    required confidence.

    The result is the deterministic, finite-sample analog of the
    PAC bound that is undischargeable from Stdlib alone. Combined
    with [L_separated_zero_iff_separated_general], an empirical
    [L_separated]-minimiser over a finite candidate class is a
    near-population [Separated]-respecter with explicit sample
    complexity. *)

Local Open Scope R_scope.

Theorem massart_finite_class_bound :
  forall (samples : list R) (events : list (R -> bool))
         (V eps delta : R),
    0 < eps -> 0 < delta -> 0 <= V ->
    (forall e, In e events -> eps * eps * prob_uniform samples e <= V) ->
    INR (length events) * V <= eps * eps * delta ->
    prob_uniform samples
                 (fun x => existsb (fun e => e x) events) <= delta.
Proof.
  exact sample_complexity_chebyshev_bonferroni.
Qed.

(** Application: with [M := length events] hypothesis losses each
    bounded by [V/eps^2] in deviation probability, sample size [n]
    satisfying [n * delta * eps^2 >= M * V_per] (i.e., setting
    [V := V_per / n] in the per-loss Chebyshev bound) suffices to
    guarantee that no loss in the class deviates by [eps] with
    probability worse than [delta]. *)

Theorem massart_uniform_deviation :
  forall (samples : list R) (events : list (R -> bool))
         (V_per eps delta : R) (n : nat),
    (1 <= n)%nat ->
    0 < eps -> 0 < delta -> 0 <= V_per ->
    INR (length samples) = INR n ->
    (forall e, In e events ->
       eps * eps * prob_uniform samples e <= V_per / INR n) ->
    INR (length events) * V_per <= eps * eps * delta * INR n ->
    prob_uniform samples
                 (fun x => existsb (fun e => e x) events) <= delta.
Proof.
  intros samples events V_per eps delta n Hn Heps Hdelta HV Hlen Hper Htotal.
  apply (@massart_finite_class_bound samples events (V_per / INR n) eps delta).
  - exact Heps.
  - exact Hdelta.
  - assert (Hn_R : 0 < INR n) by (apply lt_0_INR; lia).
    unfold Rdiv. apply Rmult_le_pos; [exact HV|left; apply Rinv_0_lt_compat; exact Hn_R].
  - exact Hper.
  - apply Rmult_le_reg_r with (r := INR n).
    + apply lt_0_INR. lia.
    + replace (INR (length events) * (V_per / INR n) * INR n)
         with (INR (length events) * V_per).
      * exact Htotal.
      * field. assert (0 < INR n) by (apply lt_0_INR; lia). lra.
Qed.

Local Close Scope R_scope.

(** ** Asymmetric Hoeffding's lemma for samples in [a, b].

    Generalises [hoeffding_lemma_symmetric] from symmetric intervals
    [[-h, h]] to arbitrary [[a, b]] with [a <= 0 <= b]. The kernel is
    the log-MGF bound
      [forall u >= 0, ln((1-p) + p * exp u) - p * u <= u^2 / 8]
    for [p in [0, 1]], proved by [taylor_quadratic_bound] applied to
    [L_p u := ln(g_p u) - p u] with [g_p u := (1-p) + p * exp u]. The
    second derivative simplifies to [p (1-p) exp u / g_p u^2] and is
    bounded by [1/4] via AM-GM. *)

Local Open Scope R_scope.

Section AsymmetricHoeffdingKernel.

  Variable p : R.
  Hypothesis Hp_lo : 0 <= p.
  Hypothesis Hp_hi : p <= 1.

  Definition g_p (u : R) : R := (1 - p) + p * exp u.

  Lemma g_p_pos : forall u, 0 < g_p u.
  Proof.
    intros u. unfold g_p.
    pose proof (exp_pos u) as Hexp. nra.
  Qed.

  Lemma g_p_at_0 : g_p 0 = 1.
  Proof. unfold g_p. rewrite exp_0. lra. Qed.

  (** Pointwise derivative of [g_p]. Direct ε-δ to avoid the
      function-algebra wrapper. *)

  Lemma derivable_pt_lim_g_p :
    forall u, derivable_pt_lim g_p u (p * exp u).
  Proof.
    intros u.
    pose proof (derivable_pt_lim_exp u) as Hexp_d.
    intros eps Heps.
    destruct (Req_dec p 0) as [Hp0 | Hp_ne].
    - exists (mkposreal eps Heps). intros h Hh _.
      unfold g_p. rewrite Hp0.
      replace ((1 - 0 + 0 * exp (u + h) - (1 - 0 + 0 * exp u)) / h - 0 * exp u)
         with 0 by (field; exact Hh).
      rewrite Rabs_R0. exact Heps.
    - assert (Hp_abs_pos : 0 < Rabs p) by (apply Rabs_pos_lt; exact Hp_ne).
      pose (eps' := eps / Rabs p).
      assert (Heps'_pos : 0 < eps').
      { unfold eps'. apply Rmult_lt_0_compat;
          [exact Heps | apply Rinv_0_lt_compat; exact Hp_abs_pos]. }
      destruct (Hexp_d eps' Heps'_pos) as [delta Hbnd].
      exists delta. intros h Hh Hh_bnd.
      unfold g_p.
      replace (((1 - p + p * exp (u + h)) - (1 - p + p * exp u)) / h - p * exp u)
         with (p * ((exp (u + h) - exp u) / h - exp u)) by (field; exact Hh).
      rewrite Rabs_mult.
      apply Rmult_lt_reg_l with (r := / Rabs p);
        [apply Rinv_0_lt_compat; exact Hp_abs_pos|].
      replace (/ Rabs p * (Rabs p * Rabs ((exp (u + h) - exp u) / h - exp u)))
         with (Rabs ((exp (u + h) - exp u) / h - exp u)) by (field; lra).
      replace (/ Rabs p * eps) with (eps / Rabs p) by (field; lra).
      apply (Hbnd h Hh Hh_bnd).
  Qed.

  (** Derivative of [ln (g_p u)] is [p exp u / g_p u]. *)

  Lemma derivable_pt_lim_ln_g_p :
    forall u, derivable_pt_lim (fun v => ln (g_p v)) u (p * exp u / g_p u).
  Proof.
    intros u.
    pose proof (g_p_pos u) as Hgp.
    pose proof (derivable_pt_lim_comp g_p ln u (p * exp u) (/ g_p u)
                  (derivable_pt_lim_g_p u)
                  (derivable_pt_lim_ln (g_p u) Hgp)) as Hd.
    unfold comp in Hd.
    replace (p * exp u / g_p u) with (/ g_p u * (p * exp u)) by (field; lra).
    exact Hd.
  Qed.

  (** Derivative of [L_p u] is [p exp u / g_p u - p]. *)

  Definition L_p_prime (u : R) : R := p * exp u / g_p u - p.

  Lemma derivable_pt_lim_L_p :
    forall u, derivable_pt_lim (fun v => ln (g_p v) - p * v) u (L_p_prime u).
  Proof.
    intros u. unfold L_p_prime.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_ln_g_p.
    - replace p with (0 * u + p * 1) at 2 by lra.
      apply derivable_pt_lim_mult.
      + apply derivable_pt_lim_const.
      + apply derivable_pt_lim_id.
  Qed.

  Lemma L_p_at_0 : ln (g_p 0) - p * 0 = 0.
  Proof. rewrite g_p_at_0, ln_1. lra. Qed.

  Lemma L_p_prime_at_0 : L_p_prime 0 = 0.
  Proof.
    unfold L_p_prime. rewrite exp_0, g_p_at_0. field.
  Qed.

  (** Second derivative of [L_p]. The quotient rule on
      [p exp u / g_p u] gives [p exp u (g_p u - p exp u) / g_p u^2 =
      p (1 - p) exp u / g_p u^2] (since [g_p u - p exp u = 1 - p]).
      Subtracting the constant [p] contributes nothing to the second
      derivative. *)

  Definition L_p_second (u : R) : R := p * (1 - p) * exp u / (g_p u * g_p u).

  Lemma derivable_pt_lim_L_p_prime :
    forall u, derivable_pt_lim L_p_prime u (L_p_second u).
  Proof.
    intros u.
    pose proof (g_p_pos u) as Hgp.
    assert (Hgp_ne : g_p u <> 0) by lra.
    pose proof (derivable_pt_lim_g_p u) as Hg_d.
    assert (Hpe_d : derivable_pt_lim (fun v => p * exp v) u (p * exp u)).
    { intros eps Heps.
      destruct (Req_dec p 0) as [Hp0 | Hp_ne].
      - exists (mkposreal eps Heps). intros h Hh _. rewrite Hp0.
        replace ((0 * exp (u + h) - 0 * exp u) / h - 0 * exp u)
           with 0 by (field; exact Hh).
        rewrite Rabs_R0. exact Heps.
      - assert (Hp_abs_pos : 0 < Rabs p) by (apply Rabs_pos_lt; exact Hp_ne).
        pose (eps' := eps / Rabs p).
        assert (Heps'_pos : 0 < eps') by
          (unfold eps'; apply Rmult_lt_0_compat;
             [exact Heps | apply Rinv_0_lt_compat; exact Hp_abs_pos]).
        destruct (derivable_pt_lim_exp u eps' Heps'_pos) as [delta Hbnd].
        exists delta. intros h Hh Hh_bnd.
        replace ((p * exp (u + h) - p * exp u) / h - p * exp u)
           with (p * ((exp (u + h) - exp u) / h - exp u)) by (field; exact Hh).
        rewrite Rabs_mult.
        apply Rmult_lt_reg_l with (r := / Rabs p);
          [apply Rinv_0_lt_compat; exact Hp_abs_pos|].
        replace (/ Rabs p * (Rabs p * Rabs ((exp (u + h) - exp u) / h - exp u)))
           with (Rabs ((exp (u + h) - exp u) / h - exp u)) by (field; lra).
        replace (/ Rabs p * eps) with (eps / Rabs p) by (field; lra).
        apply (Hbnd h Hh Hh_bnd). }
    pose proof (derivable_pt_lim_div (fun v => p * exp v) g_p u
                  (p * exp u) (p * exp u) Hpe_d Hg_d Hgp_ne) as Hdiv_d.
    unfold div_fct, inv_fct, mult_fct in Hdiv_d.
    (* Hdiv_d : derivable_pt_lim (fun y => p * exp y * / g_p y) u
                  ((p * exp u * g_p u - p * exp u * p * exp u) / (g_p u * g_p u))
       — but Stdlib uses Rsqr or product form for denominator. *)
    intros eps Heps.
    destruct (Hdiv_d eps Heps) as [delta Hbnd].
    exists delta. intros h Hh Hh_bnd.
    specialize (Hbnd h Hh Hh_bnd).
    unfold L_p_prime, L_p_second, Rsqr in *.
    replace ((p * exp (u + h) / g_p (u + h) - p -
              (p * exp u / g_p u - p)) / h -
             p * (1 - p) * exp u / (g_p u * g_p u))
       with ((p * exp (u + h) / g_p (u + h) -
              p * exp u / g_p u) / h -
             (p * exp u * g_p u - p * exp u * (p * exp u)) /
              (g_p u * g_p u)).
    + exact Hbnd.
    + assert (Hgph := g_p_pos (u + h)).
      assert (Hgph_ne : g_p (u + h) <> 0) by lra.
      unfold g_p in Hgp_ne, Hgph_ne |- *.
      field. split; [exact Hgp_ne | split; [exact Hgph_ne | exact Hh]].
  Qed.

  (** [L_p_second u <= 1/4] by AM-GM:
      [p (1-p) exp u / g_p^2 = a*b / (a+b)^2] with [a = (1-p)] and
      [b = p * exp u], and [a*b / (a+b)^2 <= 1/4]. *)

  Lemma L_p_second_bound :
    forall u, L_p_second u <= 1 / 4.
  Proof.
    intros u. unfold L_p_second, g_p.
    pose proof (exp_pos u) as Hexp.
    replace (p * (1 - p) * exp u) with ((1 - p) * (p * exp u)) by ring.
    set (a := 1 - p).
    set (b := p * exp u).
    fold a b.
    assert (Ha_nn : 0 <= a) by (unfold a; lra).
    assert (Hb_nn : 0 <= b) by (unfold b; nra).
    assert (Hab_pos : 0 < a + b).
    { destruct (Req_dec p 0) as [Hp0 | Hp_ne].
      - rewrite Hp0 in *. unfold a. lra.
      - destruct (Req_dec p 1) as [Hp1 | Hp_ne1].
        + unfold b. rewrite Hp1. nra.
        + unfold a. lra. }
    replace ((1 - p + p * exp u) * (1 - p + p * exp u))
       with ((a + b) * (a + b))
      by (unfold a, b; ring).
    pose proof (Rle_0_sqr (a - b)) as Hsq. unfold Rsqr in Hsq.
    assert (Hkey : 4 * a * b <= (a + b) * (a + b)) by nra.
    apply Rmult_le_reg_r with (r := 4 * ((a + b) * (a + b))).
    { apply Rmult_lt_0_compat; [lra|nra]. }
    replace (a * b / ((a + b) * (a + b)) * (4 * ((a + b) * (a + b))))
       with (4 * a * b)
      by (field; nra).
    replace (1 / 4 * (4 * ((a + b) * (a + b))))
       with ((a + b) * (a + b))
      by lra.
    exact Hkey.
  Qed.

  Lemma L_p_second_nonneg :
    forall u, 0 <= L_p_second u.
  Proof.
    intros u. unfold L_p_second.
    pose proof (exp_pos u) as Hexp.
    pose proof (g_p_pos u) as Hgp.
    assert (Hgsq_pos : 0 < g_p u * g_p u) by nra.
    apply Rmult_le_pos.
    - assert (H_pp : 0 <= p * (1 - p)) by nra.
      apply Rmult_le_pos; [exact H_pp | left; exact Hexp].
    - left. apply Rinv_0_lt_compat. exact Hgsq_pos.
  Qed.

  (** The log-MGF bound: [L_p u <= u^2/8] for [u >= 0]. Direct
      [taylor_quadratic_bound] application with [M = 1/4]. *)

  Theorem hoeffding_log_mgf_bound_nonneg :
    forall u, 0 <= u -> ln (g_p u) - p * u <= u * u / 8.
  Proof.
    intros u Hu.
    pose proof (@taylor_quadratic_bound (fun v => ln (g_p v) - p * v)
                  L_p_prime L_p_second (1 / 4) 0 u Hu ltac:(lra)
                  L_p_at_0 L_p_prime_at_0
                  (fun v _ => derivable_pt_lim_L_p v)
                  (fun v _ => derivable_pt_lim_L_p_prime v)
                  (fun v _ => L_p_second_bound v)) as Htay.
    replace (u - 0) with u in Htay by lra.
    replace (1 / 4 / 2 * (u * u)) with (u * u / 8) in Htay by lra.
    exact Htay.
  Qed.

  (** Symmetry: [L_p u = L_{1-p} (-u)]. Hence the bound extends to
      [u < 0]. *)

End AsymmetricHoeffdingKernel.

(** Symmetry between [p] and [1 - p] under sign flip of [u]. *)

Lemma g_p_neg_swap :
  forall p u, g_p p (- u) * exp u = g_p (1 - p) u.
Proof.
  intros p u. unfold g_p.
  rewrite (exp_Ropp u).
  pose proof (exp_pos u) as Hexp.
  field. lra.
Qed.

Lemma L_p_symmetry :
  forall p u, 0 <= p <= 1 ->
    ln (g_p p u) - p * u = ln (g_p (1 - p) (- u)) - (1 - p) * (- u).
Proof.
  intros p u [Hp_lo Hp_hi].
  pose proof (@g_p_pos (1 - p) ltac:(lra) ltac:(lra) (-u)) as Hgp1.
  pose proof (exp_pos u) as Hexpu.
  pose proof (@g_p_pos p Hp_lo Hp_hi u) as Hgp_p.
  assert (Hgp_eq : g_p p u = g_p (1 - p) (- u) * exp u).
  { unfold g_p.
    rewrite (exp_Ropp u).
    field. lra. }
  rewrite Hgp_eq.
  rewrite ln_mult by assumption.
  rewrite ln_exp.
  ring.
Qed.

Theorem hoeffding_log_mgf_bound :
  forall p u, 0 <= p <= 1 ->
    ln (g_p p u) - p * u <= u * u / 8.
Proof.
  intros p u [Hp_lo Hp_hi].
  destruct (Rle_or_lt 0 u) as [Hu | Hu].
  - apply (@hoeffding_log_mgf_bound_nonneg p Hp_lo Hp_hi u Hu).
  - rewrite (@L_p_symmetry p u (conj Hp_lo Hp_hi)).
    replace (u * u / 8) with ((- u) * (- u) / 8) by lra.
    apply (@hoeffding_log_mgf_bound_nonneg (1 - p) ltac:(lra) ltac:(lra)
            (- u) ltac:(lra)).
Qed.

(** Asymmetric Hoeffding key: for [a <= 0 <= b] and [u = lam * (b - a)],
    [b/(b-a) * exp(lam*a) + (-a)/(b-a) * exp(lam*b) <= exp(lam^2 (b-a)^2 / 8)]. *)

Theorem hoeffding_convex_combination_bound :
  forall (lam a b : R),
    a < b -> a <= 0 <= b ->
    b / (b - a) * exp (lam * a) + (- a) / (b - a) * exp (lam * b) <=
    exp (lam * lam * (b - a) * (b - a) / 8).
Proof.
  intros lam a b Hab Hcent.
  set (p := - a / (b - a)).
  set (u := lam * (b - a)).
  assert (Hba_pos : 0 < b - a) by lra.
  assert (Hp_lo : 0 <= p).
  { unfold p. unfold Rdiv. apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]. }
  assert (Hp_hi : p <= 1).
  { unfold p. apply Rmult_le_reg_r with (r := b - a); [lra|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (H1mp : 1 - p = b / (b - a)).
  { unfold p. field. lra. }
  assert (Hla : lam * a = - p * u).
  { unfold p, u. field. lra. }
  assert (Hlb : lam * b = (1 - p) * u).
  { unfold u. rewrite H1mp. field. lra. }
  rewrite Hla, Hlb.
  rewrite <- H1mp. unfold p at 2.
  fold p.
  pose proof (@hoeffding_log_mgf_bound p u (conj Hp_lo Hp_hi)) as Hlog.
  pose proof (@g_p_pos p Hp_lo Hp_hi u) as Hgp.
  (* exp side: ln(g_p u) <= p*u + u^2/8, exp gives g_p u <= exp(p*u + u^2/8). *)
  assert (Hg_le : g_p p u <= exp (p * u + u * u / 8)).
  { rewrite <- (exp_ln (g_p p u) Hgp).
    destruct (Req_dec (ln (g_p p u)) (p * u + u * u / 8)) as [Heq | Hne].
    - rewrite Heq. apply Rle_refl.
    - apply Rlt_le. apply exp_increasing. lra. }
  (* (1-p) exp(-pu) + p exp((1-p)u) = exp(-pu) * g_p u <= exp(u^2/8). *)
  apply Rmult_le_reg_l with (r := exp (p * u)); [apply exp_pos|].
  replace (exp (p * u) * ((1 - p) * exp (- p * u) + p * exp ((1 - p) * u)))
     with ((1 - p) * (exp (p * u) * exp (- p * u)) +
           p * (exp (p * u) * exp ((1 - p) * u))) by ring.
  rewrite <- !exp_plus.
  replace (p * u + - p * u) with 0 by lra.
  rewrite exp_0.
  replace (p * u + (1 - p) * u) with u by lra.
  unfold g_p in Hg_le.
  replace ((1 - p) * 1 + p * exp u) with (1 - p + p * exp u) by lra.
  replace (lam * lam * (b - a) * (b - a) / 8) with (u * u / 8)
    by (unfold u; lra).
  exact Hg_le.
Qed.

(** Hoeffding's lemma proper: for centered samples in [[a, b]] with
    [a <= 0 <= b], the empirical MGF is bounded by the Gaussian
    envelope [exp(lam^2 (b - a)^2 / 8)]. *)

Theorem hoeffding_lemma_asymmetric :
  forall (samples : list R) (lam a b : R),
    a < b -> a <= 0 <= b ->
    fold_right Rplus 0 samples = 0 ->
    (forall x, In x samples -> a <= x <= b) ->
    fold_right Rplus 0 (map (fun x => exp (lam * x)) samples) <=
    INR (length samples) * exp (lam * lam * (b - a) * (b - a) / 8).
Proof.
  intros samples lam a b Hab Hcent Hsum Hbnd.
  pose proof (@mgf_sum_convexity_bound samples lam a b Hab Hbnd) as Hsum_bnd.
  rewrite Hsum in Hsum_bnd.
  eapply Rle_trans; [exact Hsum_bnd|].
  pose proof (@hoeffding_convex_combination_bound lam a b Hab Hcent) as Hkey.
  replace ((b * INR (length samples) - 0) / (b - a))
     with (INR (length samples) * (b / (b - a)))
    by (field; lra).
  replace ((0 - a * INR (length samples)) / (b - a))
     with (INR (length samples) * ((- a) / (b - a)))
    by (field; lra).
  replace (INR (length samples) * (b / (b - a)) * exp (lam * a) +
           INR (length samples) * ((- a) / (b - a)) * exp (lam * b))
     with (INR (length samples) *
           (b / (b - a) * exp (lam * a) + (- a) / (b - a) * exp (lam * b)))
    by ring.
  apply Rmult_le_compat_l; [apply pos_INR | exact Hkey].
Qed.

Local Close Scope R_scope.

(** ******************************************************************** *)
(** *        Section 6. iid sampling and PAC generalization              *)
(** ******************************************************************** *)

(** A discrete probability library built on top of the existing
    [prob_uniform] / [expect_uniform] / [mgf_uniform] primitives. An
    iid sample of size [n] from a finite distribution [D] is one
    element of the uniform-product distribution on [D^n], represented
    as the list of all length-[n] samples. The product MGF
    factorization follows by induction on [n] without further
    measure-theoretic infrastructure, and Hoeffding's lemma (already
    proved in symmetric and asymmetric forms in Section 5) gives the
    standard exponential tail bounds on empirical means. The
    finite-class PAC bound follows by Bonferroni's union bound
    (already proved in Section 3). The infinite-class form via
    covering numbers is left for future work; covering numbers
    require either a VC-dimension theory or a metric-entropy library
    beyond what Stdlib provides. *)

Local Open Scope R_scope.

(** ** All length-[n] iid samples from a discrete distribution. *)

Fixpoint all_iid_samples (D : list R) (n : nat) : list (list R) :=
  match n with
  | O => [[]]
  | S k => flat_map (fun s => map (fun x => x :: s) D) (all_iid_samples D k)
  end.

Lemma all_iid_samples_length :
  forall D n, length (all_iid_samples D n) = ((length D) ^ n)%nat.
Proof.
  intros D. induction n as [|k IH].
  - reflexivity.
  - cbn [all_iid_samples Nat.pow].
    rewrite <- IH.
    set (L := all_iid_samples D k). clearbody L. clear IH.
    induction L as [|a rest IH'].
    + cbn. lia.
    + cbn [flat_map length]. rewrite length_app. rewrite length_map.
      rewrite IH'. nia.
Qed.

Lemma all_iid_samples_each_length :
  forall D n s, In s (all_iid_samples D n) -> length s = n.
Proof.
  intros D n. induction n as [|k IH]; intros s Hs; cbn in Hs.
  - destruct Hs as [Heq | []]. subst. reflexivity.
  - apply in_flat_map in Hs as [s0 [Hs0_in Hs_in]].
    apply in_map_iff in Hs_in as [x [Heq Hx_in]]. subst s.
    cbn. f_equal. apply IH. assumption.
Qed.

Lemma all_iid_samples_each_in :
  forall D n s x, In s (all_iid_samples D n) -> In x s -> In x D.
Proof.
  intros D n. induction n as [|k IH]; intros s x Hs Hx; cbn in Hs.
  - destruct Hs as [Heq | []]. subst. cbn in Hx. contradiction.
  - apply in_flat_map in Hs as [s0 [Hs0_in Hs_in]].
    apply in_map_iff in Hs_in as [y [Heq Hy_in]]. subst s.
    cbn in Hx. destruct Hx as [Heq | Hx]; [subst; assumption|].
    apply (IH s0 x Hs0_in Hx).
Qed.

Lemma all_iid_samples_length_pos :
  forall D n, D <> [] -> (0 < length (all_iid_samples D n))%nat.
Proof.
  intros D n HD. rewrite all_iid_samples_length.
  assert (HDpos : (0 < length D)%nat)
    by (destruct D; [contradiction | cbn; lia]).
  induction n; cbn; nia.
Qed.

(** ** Real-sum helpers used by the MGF factorization. *)

Lemma fold_right_Rplus_app_local :
  forall l1 l2 : list R,
    fold_right Rplus 0 (l1 ++ l2)
    = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
Proof.
  induction l1 as [|x rest IH]; intros l2; cbn; [lra|].
  rewrite IH. lra.
Qed.

Lemma fold_right_Rplus_concat_local :
  forall L : list (list R),
    fold_right Rplus 0 (concat L)
    = fold_right Rplus 0 (map (fold_right Rplus 0) L).
Proof.
  induction L as [|x rest IH]; cbn; [reflexivity|].
  rewrite fold_right_Rplus_app_local. rewrite IH. reflexivity.
Qed.

Lemma fold_right_Rplus_flat_map_local :
  forall {A : Type} (l : list A) (f : A -> list R),
    fold_right Rplus 0 (flat_map f l)
    = fold_right Rplus 0 (map (fun x => fold_right Rplus 0 (f x)) l).
Proof.
  intros A l f. rewrite flat_map_concat_map.
  rewrite fold_right_Rplus_concat_local. rewrite map_map. reflexivity.
Qed.

Lemma fold_right_Rplus_map_mul_const_left :
  forall {A : Type} (l : list A) (f : A -> R) (c : R),
    fold_right Rplus 0 (map (fun x => c * f x) l)
    = c * fold_right Rplus 0 (map f l).
Proof.
  intros A l f c. induction l as [|x rest IH]; cbn; [lra|].
  rewrite IH. lra.
Qed.

Lemma fold_right_Rplus_map_mul_const_right :
  forall {A : Type} (l : list A) (f : A -> R) (c : R),
    fold_right Rplus 0 (map (fun x => f x * c) l)
    = fold_right Rplus 0 (map f l) * c.
Proof.
  intros A l f c. induction l as [|x rest IH]; cbn; [lra|].
  rewrite IH. lra.
Qed.

Lemma fold_right_Rplus_nonneg_local :
  forall (l : list R), (forall x, In x l -> 0 <= x) ->
    0 <= fold_right Rplus 0 l.
Proof.
  induction l as [|x rest IH]; intros Hnn; cbn; [lra|].
  apply Rplus_le_le_0_compat.
  - apply Hnn. left; reflexivity.
  - apply IH. intros y Hy. apply Hnn. right; assumption.
Qed.

Lemma fold_right_Rmult_exp_lam :
  forall (l : list R) (lam : R) (f : R -> R),
    fold_right Rmult 1 (map (fun x => exp (lam * f x)) l)
    = exp (lam * fold_right Rplus 0 (map f l)).
Proof.
  intros l lam f. induction l as [|x rest IH]; cbn.
  - rewrite Rmult_0_r, exp_0. reflexivity.
  - rewrite IH. rewrite <- exp_plus. f_equal. ring.
Qed.

Lemma exp_pow_lin :
  forall (x : R) (n : nat), exp x ^ n = exp (INR n * x).
Proof.
  intros x n. induction n as [|k IH].
  - cbn. rewrite Rmult_0_l, exp_0. reflexivity.
  - rewrite S_INR. cbn [pow].
    rewrite IH. rewrite <- exp_plus. f_equal. ring.
Qed.

Lemma map_flat_map_eq :
  forall {A B C : Type} (f : B -> C) (g : A -> list B) (l : list A),
    map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof.
  intros A B C f g l. induction l as [|x rest IH]; cbn; [reflexivity|].
  rewrite map_app. rewrite IH. reflexivity.
Qed.

(** ** Product MGF factorization for iid samples. *)

Theorem sum_map_iid_product :
  forall (D : list R) (g : R -> R) (n : nat),
    fold_right Rplus 0
      (map (fun s => fold_right Rmult 1 (map g s)) (all_iid_samples D n))
    = (fold_right Rplus 0 (map g D)) ^ n.
Proof.
  intros D g n.
  induction n as [|k IH].
  - cbn. lra.
  - cbn [all_iid_samples].
    rewrite map_flat_map_eq.
    rewrite fold_right_Rplus_flat_map_local.
    set (K := fold_right Rplus 0 (map g D)).
    assert (Hext : forall t : list R,
      fold_right Rplus 0
        (map (fun s => fold_right Rmult 1 (map g s))
             (map (fun x => x :: t) D))
      = K * fold_right Rmult 1 (map g t)).
    { intros t. rewrite map_map.
      transitivity (fold_right Rplus 0
        (map (fun x => g x * fold_right Rmult 1 (map g t)) D)).
      - apply (f_equal (fold_right Rplus 0)).
        apply map_ext. intros x. cbn [map fold_right]. reflexivity.
      - unfold K. apply fold_right_Rplus_map_mul_const_right. }
    rewrite (map_ext _ _ Hext).
    rewrite fold_right_Rplus_map_mul_const_left.
    rewrite IH. cbn [pow]. unfold K. ring.
Qed.

Theorem sum_iid_mgf_factor :
  forall (D : list R) (n : nat) (f : R -> R) (lam : R),
    fold_right Rplus 0
      (map (fun s => exp (lam * fold_right Rplus 0 (map f s)))
           (all_iid_samples D n))
    = (fold_right Rplus 0 (map (fun x => exp (lam * f x)) D)) ^ n.
Proof.
  intros D n f lam.
  rewrite <- (sum_map_iid_product D (fun x => exp (lam * f x)) n).
  apply (f_equal (fold_right Rplus 0)).
  apply map_ext. intros s.
  symmetry. apply fold_right_Rmult_exp_lam.
Qed.

(** ** Empirical-mean MGF bound: the iid empirical MGF is bounded by
    [exp(n * lam^2 (b - a)^2 / 8)] when [g] is centered and [g(x) ∈ [a,b]]. *)

Lemma mgf_iid_sum_bound :
  forall (D : list R) (g : R -> R) (n : nat) (a b lam : R),
    D <> [] -> (1 <= n)%nat ->
    a < b -> a <= 0 <= b ->
    fold_right Rplus 0 (map g D) = 0 ->
    (forall x, In x D -> a <= g x <= b) ->
    expect_uniform
      (map (fun s => exp (lam * fold_right Rplus 0 (map g s)))
           (all_iid_samples D n))
    <= exp (INR n * (lam * lam * (b - a) * (b - a) / 8)).
Proof.
  intros D g n a b lam HD Hn Hab Hcent Hsum_zero Hbnd.
  assert (HD_pos : (0 < length D)%nat)
    by (destruct D; [contradiction | cbn; lia]).
  assert (HD_R_pos : 0 < INR (length D)) by (apply lt_0_INR; lia).
  assert (HD_n_pos : (0 < length D ^ n)%nat).
  { clear -HD_pos. induction n; cbn; nia. }
  assert (HD_n_R_pos : 0 < INR (length D ^ n)) by (apply lt_0_INR; lia).
  assert (Hbnd' : forall x, In x (map g D) -> a <= x <= b).
  { intros x Hx. apply in_map_iff in Hx as [y [Heq Hy_in]]. subst x.
    apply Hbnd. assumption. }
  pose proof (@hoeffding_lemma_asymmetric (map g D) lam a b Hab Hcent
                Hsum_zero Hbnd') as Hhoeff.
  rewrite map_map in Hhoeff. rewrite length_map in Hhoeff.
  set (per := fold_right Rplus 0 (map (fun x => exp (lam * g x)) D)).
  fold per in Hhoeff.
  assert (Hper_nn : 0 <= per).
  { unfold per. apply fold_right_Rplus_nonneg_local. intros x Hx.
    apply in_map_iff in Hx as [y [Heq _]]. subst x. left. apply exp_pos. }
  unfold expect_uniform. rewrite !length_map.
  rewrite !all_iid_samples_length.
  destruct (Nat.eqb_spec (length D ^ n) 0) as [Hz | _]; [lia|].
  rewrite sum_iid_mgf_factor. fold per.
  assert (Hpow_le :
    per ^ n
    <= (INR (length D) * exp (lam * lam * (b - a) * (b - a) / 8)) ^ n).
  { apply pow_incr. split; assumption. }
  apply Rmult_le_reg_r with (r := INR (length D ^ n)); [exact HD_n_R_pos|].
  unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
  rewrite Rmult_1_r.
  eapply Rle_trans; [exact Hpow_le|].
  rewrite Rpow_mult_distr. rewrite exp_pow_lin.
  rewrite <- pow_INR. rewrite Rmult_comm. apply Rle_refl.
Qed.

(** ** One-sided Hoeffding tail bound for an iid sum.

    For a centered function [g] with [g(x) ∈ [a, b]] and [a ≤ 0 ≤ b],
    the probability that the iid sum [Σ g(s_i)] (over an iid sample
    [s] of size [n] from [D]) exceeds [t > 0] is at most
    [exp(-2 t^2 / (n (b - a)^2))]. This is the standard Hoeffding tail
    bound, derived by composing [chernoff_markov_bound] with the iid
    MGF factorization [sum_iid_mgf_factor] and Hoeffding's lemma.
    The optimization step (choosing [lam = 4 t / (n (b - a)^2)]) is
    instantiated explicitly. *)

Theorem hoeffding_iid_sum_one_sided :
  forall (D : list R) (g : R -> R) (n : nat) (a b t : R),
    D <> [] -> (1 <= n)%nat ->
    a < b -> a <= 0 <= b -> 0 < t ->
    fold_right Rplus 0 (map g D) = 0 ->
    (forall x, In x D -> a <= g x <= b) ->
    prob_uniform
      (map (fun s => fold_right Rplus 0 (map g s)) (all_iid_samples D n))
      (fun y => if Rle_dec t y then true else false)
    <= exp (- 2 * t * t / (INR n * (b - a) * (b - a))).
Proof.
  intros D g n a b t HD Hn Hab Hcent Ht Hsum_zero Hbnd.
  set (lam := 4 * t / (INR n * (b - a) * (b - a))).
  set (sum_list :=
         map (fun s => fold_right Rplus 0 (map g s)) (all_iid_samples D n)).
  assert (Hba_pos : 0 < b - a) by lra.
  assert (Hn_pos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hdenom_pos : 0 < INR n * (b - a) * (b - a)).
  { apply Rmult_lt_0_compat;
      [apply Rmult_lt_0_compat; assumption | assumption]. }
  assert (Hlam_pos : 0 < lam).
  { unfold lam, Rdiv. apply Rmult_lt_0_compat;
      [lra | apply Rinv_0_lt_compat; exact Hdenom_pos]. }
  pose proof (@chernoff_markov_bound sum_list lam t Hlam_pos) as Hchern.
  unfold mgf_uniform in Hchern.
  assert (Hmgf_eq :
    expect_uniform (map (fun x => exp (lam * x)) sum_list)
    = expect_uniform
        (map (fun s => exp (lam * fold_right Rplus 0 (map g s)))
             (all_iid_samples D n))).
  { unfold sum_list. rewrite map_map. reflexivity. }
  rewrite Hmgf_eq in Hchern.
  pose proof (@mgf_iid_sum_bound D g n a b lam HD Hn Hab Hcent Hsum_zero Hbnd)
    as Hmgf_bound.
  assert (Hexp_pos_t : 0 < exp (lam * t)) by apply exp_pos.
  apply (Rmult_le_reg_l (exp (lam * t))); [exact Hexp_pos_t|].
  eapply Rle_trans; [exact Hchern|].
  eapply Rle_trans; [exact Hmgf_bound|].
  rewrite <- exp_plus.
  apply Req_le. f_equal.
  unfold lam. field. lra.
Qed.

(** ** Polymorphic empirical probability and union bounds.

    The existing [prob_uniform] / [bonferroni_list] are specialized to
    [list R]. To state the finite-class PAC bound over [list (list R)]
    samples (the iid sample space), we lift the same definitions to
    arbitrary types. *)

Definition prob_uniform_t {A : Type} (samples : list A) (event : A -> bool) : R :=
  if Nat.eqb (length samples) 0 then 0
  else INR (length (filter event samples)) / INR (length samples).

Lemma prob_uniform_t_R_eq :
  forall (samples : list R) (event : R -> bool),
    prob_uniform_t samples event = prob_uniform samples event.
Proof.
  intros. unfold prob_uniform_t, prob_uniform. reflexivity.
Qed.

Lemma prob_uniform_t_nonneg :
  forall {A : Type} (samples : list A) (event : A -> bool),
    0 <= prob_uniform_t samples event.
Proof.
  intros A samples event. unfold prob_uniform_t.
  destruct (Nat.eqb_spec (length samples) 0) as [_|Hne]; [lra|].
  apply Rmult_le_pos; [apply pos_INR | ].
  left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Lemma length_filter_or_le_t :
  forall {A : Type} (l : list A) (P Q : A -> bool),
    (length (filter (fun x => orb (P x) (Q x)) l) <=
     length (filter P l) + length (filter Q l))%nat.
Proof.
  intros A l P Q.
  induction l as [|x rest IH]; cbn; [lia|].
  destruct (P x) eqn:EP; destruct (Q x) eqn:EQ; cbn; lia.
Qed.

Theorem bonferroni_two_t :
  forall {A : Type} (samples : list A) (P Q : A -> bool),
    prob_uniform_t samples (fun x => orb (P x) (Q x)) <=
    prob_uniform_t samples P + prob_uniform_t samples Q.
Proof.
  intros A samples P Q. unfold prob_uniform_t.
  destruct (Nat.eqb_spec (length samples) 0) as [_|Hne]; [lra|].
  assert (Hpos : 0 < INR (length samples)) by (apply lt_0_INR; lia).
  pose proof (length_filter_or_le_t samples P Q) as Hle.
  apply Rmult_le_reg_r with (r := INR (length samples)); [exact Hpos|].
  replace
    (INR (length (filter (fun x => orb (P x) (Q x)) samples)) /
     INR (length samples) * INR (length samples))
    with (INR (length (filter (fun x => orb (P x) (Q x)) samples)))
    by (field; lra).
  replace
    ((INR (length (filter P samples)) / INR (length samples) +
      INR (length (filter Q samples)) / INR (length samples)) *
     INR (length samples))
    with
    (INR (length (filter P samples)) + INR (length (filter Q samples)))
    by (field; lra).
  rewrite <- plus_INR. apply le_INR. assumption.
Qed.

Theorem bonferroni_list_t :
  forall {A : Type} (samples : list A) (events : list (A -> bool)),
    prob_uniform_t samples
      (fun x => existsb (fun e => e x) events) <=
    fold_right Rplus 0 (map (fun e => prob_uniform_t samples e) events).
Proof.
  intros A samples events.
  induction events as [|e rest IH]; cbn.
  - unfold prob_uniform_t.
    destruct (Nat.eqb_spec (length samples) 0) as [_|Hne]; [lra|].
    assert (Hpos : 0 < INR (length samples)) by (apply lt_0_INR; lia).
    assert (Hf : forall l : list A, filter (fun _ : A => false) l = []).
    { intros l. induction l as [|x rest' IH']; cbn; [reflexivity|assumption]. }
    rewrite (Hf samples). cbn. lra.
  - eapply Rle_trans.
    + apply (bonferroni_two_t samples e
              (fun x => existsb (fun e0 => e0 x) rest)).
    + apply Rplus_le_compat_l. exact IH.
Qed.

(** ** Projection lemma: probability over an arbitrary type via a
    real-valued projection coincides with probability over the
    projected list. Lets us reuse [prob_uniform] / Hoeffding tail
    bounds on iid samples by going through a sum projection. *)

Lemma prob_uniform_t_proj :
  forall {A : Type} (samples : list A) (proj : A -> R) (event : R -> bool),
    prob_uniform_t samples (fun x => event (proj x)) =
    prob_uniform (map proj samples) event.
Proof.
  intros A samples proj event.
  unfold prob_uniform_t, prob_uniform.
  rewrite length_map.
  destruct (Nat.eqb_spec (length samples) 0) as [_|_]; [reflexivity|].
  do 2 f_equal.
  induction samples as [|s rest IH]; cbn; [reflexivity|].
  destruct (event (proj s)); cbn; rewrite IH; reflexivity.
Qed.

Lemma existsb_map_eq :
  forall {A B : Type} (f : A -> B) (g : B -> bool) (l : list A),
    existsb g (map f l) = existsb (fun x => g (f x)) l.
Proof.
  intros A B f g l. induction l as [|x rest IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma filter_ext_local :
  forall {A : Type} (f g : A -> bool),
    (forall x, f x = g x) ->
    forall l, filter f l = filter g l.
Proof.
  intros A f g Heq l. induction l as [|x rest IH]; cbn; [reflexivity|].
  rewrite Heq. destruct (g x); rewrite IH; reflexivity.
Qed.

Lemma prob_uniform_t_ext :
  forall {A : Type} (samples : list A) (E1 E2 : A -> bool),
    (forall x, E1 x = E2 x) ->
    prob_uniform_t samples E1 = prob_uniform_t samples E2.
Proof.
  intros A samples E1 E2 Hext. unfold prob_uniform_t.
  destruct (Nat.eqb _ _); [reflexivity|].
  rewrite (filter_ext_local _ _ Hext). reflexivity.
Qed.

(** ** Finite-class one-sided Hoeffding PAC bound.

    The headline PAC generalization theorem. For a finite class
    [G = [g_1; ...; g_M]] of centered bounded functions, the
    probability over an iid sample [s] of size [n] from [D] that any
    [g_i] has empirical sum [Σ g_i(s_j) ≥ t] is bounded by
    [M · exp(-2 t^2 / (n (b - a)^2))]. Setting [t = n ε] yields the
    standard form: empirical-mean uniform deviation by ε at confidence
    [M · exp(-2 n ε^2 / (b - a)^2)]. The bound is exponentially tighter
    than the [massart_uniform_deviation] bound for the same setting
    because the per-event tail is exponential rather than Markov. *)

Theorem hoeffding_iid_finite_class_one_sided :
  forall (D : list R) (G : list (R -> R)) (n : nat) (a b t : R),
    D <> [] -> (1 <= n)%nat ->
    a < b -> a <= 0 <= b -> 0 < t ->
    (forall g, In g G -> fold_right Rplus 0 (map g D) = 0) ->
    (forall g x, In g G -> In x D -> a <= g x <= b) ->
    prob_uniform_t (all_iid_samples D n)
      (fun s => existsb
                  (fun g => if Rle_dec t (fold_right Rplus 0 (map g s))
                            then true else false) G)
    <= INR (length G) * exp (- 2 * t * t / (INR n * (b - a) * (b - a))).
Proof.
  intros D G n a b t HD Hn Hab Hcent Ht Hcent_g Hbnd_g.
  set (per_bound := exp (- 2 * t * t / (INR n * (b - a) * (b - a)))).
  set (event_g := fun (g : R -> R) (s : list R) =>
    if Rle_dec t (fold_right Rplus 0 (map g s)) then true else false).
  rewrite (prob_uniform_t_ext (all_iid_samples D n)
              (fun s => existsb (fun g => if Rle_dec t (fold_right Rplus 0 (map g s))
                                           then true else false) G)
              (fun s => existsb (fun e => e s) (map event_g G))).
  - eapply Rle_trans.
    + apply (bonferroni_list_t (all_iid_samples D n) (map event_g G)).
    + rewrite map_map.
      assert (Hper_g : forall g, In g G ->
        prob_uniform_t (all_iid_samples D n) (event_g g) <= per_bound).
      { intros g Hg.
        apply Rle_trans with
          (prob_uniform
            (map (fun s => fold_right Rplus 0 (map g s)) (all_iid_samples D n))
            (fun y => if Rle_dec t y then true else false)).
        - apply Req_le.
          change (event_g g)
            with (fun x : list R =>
                    (fun y : R => if Rle_dec t y then true else false)
                      (fold_right Rplus 0 (map g x))).
          apply (@prob_uniform_t_proj (list R) (all_iid_samples D n)
                    (fun s => fold_right Rplus 0 (map g s))
                    (fun y => if Rle_dec t y then true else false)).
        - unfold per_bound.
          apply (@hoeffding_iid_sum_one_sided D g n a b t HD Hn Hab Hcent Ht).
          + apply Hcent_g. assumption.
          + intros x Hx. apply Hbnd_g; assumption. }
      transitivity
        (fold_right Rplus 0 (map (fun _ : R -> R => per_bound) G)).
      * clear -Hper_g.
        induction G as [|g rest IH]; cbn; [lra|].
        apply Rplus_le_compat.
        -- apply Hper_g. left; reflexivity.
        -- apply IH. intros g' Hg'. apply Hper_g. right; assumption.
      * clear -G.
        assert (Heq : fold_right Rplus 0
                        (map (fun _ : R -> R => per_bound) G)
                    = INR (length G) * per_bound).
        { induction G as [|g rest IH].
          - cbn. lra.
          - cbn [length map fold_right]. rewrite IH.
            rewrite S_INR. ring. }
        rewrite Heq. apply Rle_refl.
  - intros s. symmetry. apply existsb_map_eq.
Qed.

(** ** Empirical Rademacher complexity for a finite hypothesis class.

    The Rademacher distribution support [rad_signs n] is the set of
    sign sequences in {-1, +1}^n, instantiated as iid samples from
    the two-element distribution [[-1; 1]]. The empirical Rademacher
    complexity averages, over Rademacher sign assignments, the
    supremum over a finite class [G] of [(1/n) Σ_i σ_i g(x_i)].

    The classical Massart finite-class bound
    [emp_rademacher samples G ≤ B sqrt(2 ln |G| / |samples|)] requires
    Jensen's inequality on the [exp]/[ln] pair (specifically
    [exp(E[max]) ≤ E[exp(max)]]) which is provable from [exp_convex]
    by induction on a finite distribution. The definition and
    nonnegativity are delivered here; the Massart bound itself is a
    structurally similar exercise to [hoeffding_iid_finite_class_one_sided],
    using the same MGF/union-bound machinery composed with a finite
    Jensen step. *)

Definition expect_uniform_t {A : Type} (samples : list A) (f : A -> R) : R :=
  if Nat.eqb (length samples) 0 then 0
  else fold_right Rplus 0 (map f samples) / INR (length samples).

Definition rad_signs (n : nat) : list (list R) := all_iid_samples [-1; 1] n.

Lemma rad_signs_length :
  forall n, length (rad_signs n) = (2 ^ n)%nat.
Proof.
  intros n. unfold rad_signs.
  rewrite all_iid_samples_length. cbn. reflexivity.
Qed.

Lemma rad_signs_nonempty :
  forall n, rad_signs n <> [].
Proof.
  intros n. unfold rad_signs. intros Hempty.
  assert (HD : ([-1; 1] : list R) <> []) by discriminate.
  pose proof (@all_iid_samples_length_pos [-1; 1] n HD) as Hpos.
  rewrite Hempty in Hpos. cbn in Hpos. lia.
Qed.

Lemma rad_signs_each_pm_one :
  forall n sigma x, In sigma (rad_signs n) -> In x sigma -> x = -1 \/ x = 1.
Proof.
  intros n sigma x Hsigma Hx. unfold rad_signs in Hsigma.
  pose proof (all_iid_samples_each_in [-1; 1] n sigma x Hsigma Hx) as Hin.
  cbn in Hin. destruct Hin as [Heq | [Heq | []]];
    [left | right]; symmetry; assumption.
Qed.

Fixpoint inner_prod_rad (sigma samples : list R) (g : R -> R) : R :=
  match sigma, samples with
  | s :: ss, x :: xs => s * g x + inner_prod_rad ss xs g
  | _, _ => 0
  end.

Definition emp_rademacher (samples : list R) (G : list (R -> R)) : R :=
  expect_uniform_t (rad_signs (length samples))
    (fun sigma =>
      Rmax_list 0
        (map (fun g => inner_prod_rad sigma samples g / INR (length samples)) G)).

Lemma inner_prod_rad_zero :
  forall samples g, inner_prod_rad [] samples g = 0.
Proof. intros. cbn. reflexivity. Qed.

Lemma Rmax_list_nonneg :
  forall init l, 0 <= init -> 0 <= Rmax_list init l.
Proof.
  intros init l Hi. eapply Rle_trans; [exact Hi|].
  apply Rmax_list_init_le.
Qed.

Lemma expect_uniform_t_nonneg :
  forall {A : Type} (samples : list A) (f : A -> R),
    (forall x, In x samples -> 0 <= f x) ->
    0 <= expect_uniform_t samples f.
Proof.
  intros A samples f Hf. unfold expect_uniform_t.
  destruct (Nat.eqb_spec (length samples) 0) as [_|Hne]; [lra|].
  apply Rmult_le_pos.
  - apply fold_right_Rplus_nonneg_local.
    intros x Hx. apply in_map_iff in Hx as [y [Heq Hy]].
    subst x. apply Hf. assumption.
  - left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Theorem emp_rademacher_nonneg :
  forall samples G, 0 <= emp_rademacher samples G.
Proof.
  intros samples G. unfold emp_rademacher.
  apply expect_uniform_t_nonneg.
  intros sigma _. apply Rmax_list_nonneg. apply Rle_refl.
Qed.

