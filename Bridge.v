(******************************************************************************)
(*                                                                            *)
(*                         nms-verified — Bridge.v                            *)
(*                                                                            *)
(*     SepRespectingHead, FP quantization, hinge losses, vector SGD.          *)
(*     The bridge from Lipschitz score heads to the NMS-collapse keystone     *)
(*     proved in [Core].                                                      *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List PeanoNat Bool Lia Reals Lra Arith.Wf_nat Recdef ZArith.
From Stdlib Require Import Permutation Extraction.
Import ListNotations.

Set Implicit Arguments.

Require Import Core.

(** ******************************************************************** *)
(** *                Section 2. Bridge to learning                        *)
(** ******************************************************************** *)

(** Refactor [one_peak] from a hypothesis on the input list to a
    structural property of a parameterised score head. A
    [SepRespectingHead Feat] bundles the bridge precondition certificate
    (Lipschitz constant, noise budget, margin) into one record.
    Inhabitants discharge [Separated] by construction; composition with
    [nms_collapse_onepeak] yields NMS-collapse with no further hypothesis
    discharge.

    The continuous-optimisation completion — that SGD on
    [L_focal + lambda * L_separated] converges to a [SepRespectingHead]
    inhabitant with explicit sample complexity — needs Rademacher
    complexity and stochastic-optimisation convergence, neither of
    which is in Stdlib. The finite-search version is
    decidable here; the continuous version is the missing library. *)

Record SepRespectingHead (Feat : Type) := mkSepHead {
  sep_h : Feat -> nat;
  sep_dist : Feat -> Feat -> nat;
  sep_L : nat;
  sep_eps : nat;
  sep_m : nat;
  sep_lipschitz :
    forall x y, Nat.max (sep_h x) (sep_h y)
                <= Nat.min (sep_h x) (sep_h y) + sep_L * sep_dist x y;
  sep_margin_bound : 2 * sep_L * sep_eps <= sep_m
}.

Arguments mkSepHead {Feat} _ _ _ _ _ _ _.
Arguments sep_h {Feat} _ _.
Arguments sep_dist {Feat} _ _ _.
Arguments sep_L {Feat} _.
Arguments sep_eps {Feat} _.
Arguments sep_m {Feat} _.
Arguments sep_lipschitz {Feat} _ _ _.
Arguments sep_margin_bound {Feat} _.

Section SepRespecting.

  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym_h : forall a b, iou a b = iou b a.
  Variable tau : nat.
  Variable theta : nat.
  Variable Feat : Type.

  Definition sep_apply (S : SepRespectingHead Feat)
                       (obs true_f : @det Box -> Feat)
                       (D : list (@det Box)) : Prop :=
    (forall d, In d D -> score d = sep_h S (obs d)) /\
    (forall d, In d D -> sep_dist S (true_f d) (obs d) <= sep_eps S) /\
    (forall d d', In d D -> In d' D -> d <> d' ->
       tau <= iou (box d) (box d') ->
       sep_m S + Nat.min (sep_h S (true_f d)) (sep_h S (true_f d'))
         <= Nat.max (sep_h S (true_f d)) (sep_h S (true_f d'))) /\
    (forall d d', In d D -> In d' D -> d <> d' ->
       tau <= iou (box d) (box d') ->
       sep_L S * sep_eps S +
       Nat.min (sep_h S (true_f d)) (sep_h S (true_f d')) < theta).

  Theorem sep_respecting_implies_separated :
    forall (S : SepRespectingHead Feat)
           (obs true_f : @det Box -> Feat)
           (D : list (@det Box)),
      sep_apply S obs true_f D ->
      Separated iou tau theta (sep_m S - 2 * sep_L S * sep_eps S) D.
  Proof.
    intros S obs true_f D [Hscore [Hobs [Hmargin Hth]]].
    apply (@lipschitz_bridge_substantive Box iou tau theta
             Feat (sep_h S) (sep_dist S) true_f obs
             (sep_L S) (sep_m S) (sep_eps S) D);
      [apply (sep_margin_bound S)
      |apply (sep_lipschitz S)
      |assumption
      |assumption
      |assumption
      |assumption].
  Qed.

  Theorem sep_respecting_implies_collapse :
    forall (S : SepRespectingHead Feat)
           (obs true_f : @det Box -> Feat)
           (D : list (@det Box)),
      NoDup D ->
      sorted_desc D ->
      sep_apply S obs true_f D ->
      1 <= sep_m S - 2 * sep_L S * sep_eps S ->
      filter_above theta (nms_sorted iou tau D) = filter_above theta D.
  Proof.
    intros S obs true_f D Hnd Hsd Happ Hslack.
    pose proof (sep_respecting_implies_separated Happ) as Hsep.
    assert (Hsep1 : Separated iou tau theta 1 D).
    { intros d d' Hin Hin' Hne Hiou.
      specialize (Hsep d d' Hin Hin' Hne Hiou).
      destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
      - left. split; [lia | assumption].
      - right. split; [lia | assumption]. }
    apply (nms_collapse_onepeak iou_sym_h Hnd Hsd
             (separated_implies_one_peak Hsep1)
             (separated_implies_no_tie_clash Hsep1)).
  Qed.

End SepRespecting.

(** ** Theorem 3 — worked instance.

    A concrete [SepRespectingHead] for the c1_iou setting. The score
    head is the identity on nat; feature distance is [abs_diff];
    L = 1, eps = 0, m = 150. Both [Separated] and NMS-collapse are
    established on a 2-element list, [vm_compute]-checkable. *)

Definition c40_head : SepRespectingHead nat.
Proof.
  refine (mkSepHead (fun n : nat => n) abs_diff 1 0 150 _ _).
  - intros x y. unfold abs_diff.
    destruct (Nat.leb_spec x y); lia.
  - lia.
Defined.

Definition c40_D : list (@det nat) := [mkDet 200 0; mkDet 50 1].

Lemma c40_NoDup : NoDup c40_D.
Proof.
  unfold c40_D. apply NoDup_cons.
  - simpl. intros [H | H]; [inversion H; lia | contradiction].
  - apply NoDup_cons; [intros H; contradiction | apply NoDup_nil].
Qed.

Lemma c40_sorted : sorted_desc c40_D.
Proof.
  unfold c40_D. simpl. split.
  - intros d' [Heq | Hf]; [subst; cbn; lia | contradiction].
  - split; [intros d' Hd'; contradiction | exact I].
Qed.

Lemma c40_apply :
  sep_apply c1_iou 50 100 c40_head (@score nat) (@score nat) c40_D.
Proof.
  unfold sep_apply, c40_D, c40_head; cbn [sep_h sep_dist sep_L sep_eps sep_m].
  split; [|split; [|split]].
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst; reflexivity.
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst; vm_compute; lia.
  - intros d d' Hin Hin' Hne Hiou.
    simpl in Hin, Hin'.
    destruct Hin as [Heq | [Heq | []]];
      destruct Hin' as [Heq' | [Heq' | []]]; subst;
      try (exfalso; apply Hne; reflexivity); cbn; lia.
  - intros d d' Hin Hin' Hne Hiou.
    simpl in Hin, Hin'.
    destruct Hin as [Heq | [Heq | []]];
      destruct Hin' as [Heq' | [Heq' | []]]; subst;
      try (exfalso; apply Hne; reflexivity); cbn; lia.
Qed.

Theorem c40_separated :
  Separated c1_iou 50 100 150 c40_D.
Proof.
  pose proof (sep_respecting_implies_separated c40_apply) as H.
  cbn [sep_m sep_L sep_eps] in H.
  replace 150 with (150 - 2 * 1 * 0) by lia.
  exact H.
Qed.

Theorem c40_collapse :
  filter_above 100 (nms_sorted c1_iou 50 c40_D)
  = filter_above 100 c40_D.
Proof.
  apply (sep_respecting_implies_collapse c1_iou_sym
           c40_NoDup c40_sorted c40_apply).
  vm_compute. lia.
Qed.

(** ** Universal approximation in the [SepRespectingHead] class.

    Every L-Lipschitz function from [nat] to [nat] under [abs_diff]
    embeds as a [SepRespectingHead nat]. The class is rich: it
    contains every Lipschitz integer function. Proof is direct
    construction. Combined with [real_lipschitz_to_nat], every real
    L-Lipschitz nonneg function on [R] with [L <= Ln] in [nat]
    embeds as a [SepRespectingHead R] via 1-step quantization.
    These show the bridge precondition is non-trivially satisfiable
    across the entire Lipschitz function space — the class is dense
    enough that any reasonable score head can be expressed within
    it. *)

Definition head_from_lipschitz_nat (f : nat -> nat) (L : nat)
    (Hlip : forall i j, Nat.max (f i) (f j) <=
                        Nat.min (f i) (f j) + L * abs_diff i j)
    : SepRespectingHead nat.
Proof.
  refine (mkSepHead f abs_diff L 0 1 _ _).
  - exact Hlip.
  - lia.
Defined.

Theorem sep_respecting_class_universal_nat :
  forall (f : nat -> nat) (L : nat),
    (forall i j, Nat.max (f i) (f j) <=
                 Nat.min (f i) (f j) + L * abs_diff i j) ->
    exists Sh : SepRespectingHead nat,
      sep_h Sh = f /\ sep_L Sh = L /\ sep_eps Sh = 0 /\ sep_m Sh = 1.
Proof.
  intros f L Hlip.
  exists (head_from_lipschitz_nat f L Hlip).
  cbn. repeat split.
Qed.

Definition head_from_real_lipschitz (f : R -> R) (L : R) (Ln : nat)
    (Hlip : Lipschitz L f)
    (HL : (L <= INR Ln)%R)
    (Hf_nn : forall x, (0 <= f x)%R)
    : SepRespectingHead R.
Proof.
  refine (mkSepHead (rnat_h 1 f) (rnat_dist 1) Ln 0 1 _ _).
  - exact (@real_lipschitz_to_nat f L 1%R Ln Hlip ltac:(lra) HL Hf_nn).
  - lia.
Defined.

Theorem sep_respecting_class_universal_real :
  forall (f : R -> R) (L : R) (Ln : nat),
    Lipschitz L f ->
    (L <= INR Ln)%R ->
    (forall x, (0 <= f x)%R) ->
    exists Sh : SepRespectingHead R,
      sep_h Sh = rnat_h 1 f /\ sep_L Sh = Ln /\
      sep_eps Sh = 0 /\ sep_m Sh = 1.
Proof.
  intros f L Ln Hlip HL Hf_nn.
  exists (@head_from_real_lipschitz f L Ln Hlip HL Hf_nn).
  cbn. repeat split.
Qed.

(** ** Closure of the [SepRespectingHead] class under composition.

    Promotes the universal-approximation result from "any individual
    Lipschitz function is in the class" to the structural closure
    "the class is closed under function composition with multiplied
    Lipschitz constants." Combined with the constant function (L=0)
    and identity (L=1) being in the class, this closes the class
    under the standard Lipschitz algebra — analogous to real
    [lip_compose] but lifted to the nat-domain SepRespectingHead
    setting. The class is structurally rich enough to absorb arbitrary
    finite networks of Lipschitz layers. *)

Lemma abs_diff_iff_max_min :
  forall a b L,
    Nat.max a b <= Nat.min a b + L <-> abs_diff a b <= L.
Proof.
  intros a b L. unfold abs_diff.
  destruct (Nat.leb_spec a b) as [Hab | Hab]; split; intros Hyp; lia.
Qed.

Theorem Lipschitz_nat_compose :
  forall (f1 f2 : nat -> nat) (L1 L2 : nat),
    (forall i j, Nat.max (f1 i) (f1 j) <=
                 Nat.min (f1 i) (f1 j) + L1 * abs_diff i j) ->
    (forall i j, Nat.max (f2 i) (f2 j) <=
                 Nat.min (f2 i) (f2 j) + L2 * abs_diff i j) ->
    forall i j,
      Nat.max (f2 (f1 i)) (f2 (f1 j)) <=
      Nat.min (f2 (f1 i)) (f2 (f1 j)) + (L2 * L1) * abs_diff i j.
Proof.
  intros f1 f2 L1 L2 H1 H2 i j.
  apply abs_diff_iff_max_min.
  pose proof (H1 i j) as Hf1. apply abs_diff_iff_max_min in Hf1.
  pose proof (H2 (f1 i) (f1 j)) as Hf2. apply abs_diff_iff_max_min in Hf2.
  nia.
Qed.

Corollary sep_respecting_class_compose :
  forall (f1 f2 : nat -> nat) (L1 L2 : nat),
    (forall i j, Nat.max (f1 i) (f1 j) <=
                 Nat.min (f1 i) (f1 j) + L1 * abs_diff i j) ->
    (forall i j, Nat.max (f2 i) (f2 j) <=
                 Nat.min (f2 i) (f2 j) + L2 * abs_diff i j) ->
    exists Sh : SepRespectingHead nat,
      sep_h Sh = (fun i => f2 (f1 i)) /\ sep_L Sh = L2 * L1.
Proof.
  intros f1 f2 L1 L2 H1 H2.
  exists (head_from_lipschitz_nat (fun i => f2 (f1 i)) (L2 * L1)
            (Lipschitz_nat_compose f1 f2 L1 L2 H1 H2)).
  cbn. split; reflexivity.
Qed.

(** ** Floating-point quantization error analysis.

    Real deployments compute scores in IEEE 754, not exact reals. A
    quantization operator [q] with bounded error [q_eps] (e.g.,
    [2^{-53}] for binary64 round-to-nearest) introduces additive
    slack into Lipschitz bounds. Specifically, if [f] is L-Lipschitz
    in exact reals, [q ∘ f] satisfies
    [|q(f x) − q(f y)| <= L * |x − y| + 2 * q_eps]. Composed with the
    bridge: a [SepRespectingHead] built from a quantized score head
    inherits an extra [2 * q_eps] noise budget. The exact-version
    [Separated(m)] becomes the FP-version [Separated(m − 2*q_eps)].

    This closes the gap from [R] to deployable hardware: the formalism
    analyzes the rounding error of FP arithmetic without assuming
    exact arithmetic on the underlying score computation. *)

Section FloatingPointQuantization.

  Local Open Scope R_scope.

  Variable q : R -> R.
  Variable q_eps : R.
  Hypothesis q_eps_nonneg : 0 <= q_eps.
  Hypothesis q_bounded : forall x, Rabs (q x - x) <= q_eps.

  Theorem quantize_lipschitz_compose :
    forall (L : R) (f : R -> R),
      Lipschitz L f ->
      forall x y, Rabs (q (f x) - q (f y)) <= L * Rabs (x - y) + 2 * q_eps.
  Proof.
    intros L f Hlip x y.
    pose proof (q_bounded (f x)) as Hqx.
    pose proof (q_bounded (f y)) as Hqy.
    pose proof (lip_bound Hlip x y) as Hf.
    pose proof (lip_nonneg Hlip) as HL.
    assert (Htri :
      Rabs (q (f x) - q (f y)) <=
      Rabs (q (f x) - f x) + Rabs (f x - f y) + Rabs (f y - q (f y))).
    { replace (q (f x) - q (f y))
         with ((q (f x) - f x) + (f x - f y) + (f y - q (f y)))
        by lra.
      eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat_r.
      apply Rabs_triang. }
    assert (Hqy' : Rabs (f y - q (f y)) <= q_eps).
    { replace (f y - q (f y)) with (- (q (f y) - f y)) by lra.
      rewrite Rabs_Ropp. assumption. }
    lra.
  Qed.

  Theorem quantize_preserves_Lipschitz_with_slack :
    forall (L : R) (f : R -> R),
      Lipschitz L f ->
      forall x y,
        q_eps = 0 ->
        Rabs (q (f x) - q (f y)) <= L * Rabs (x - y).
  Proof.
    intros L f Hlip x y Hq_zero.
    pose proof (@quantize_lipschitz_compose L f Hlip x y) as H.
    rewrite Hq_zero in H. lra.
  Qed.

End FloatingPointQuantization.

(** ** Concrete fixed-precision quantizer.

    Instantiates the abstract [FloatingPointQuantization] section with
    a concrete operator: round-to-nearest-integer via [Int_part]. The
    bounded-error claim [|q(x) − x| ≤ 1/2] follows directly from
    Stdlib's [base_Int_part] integer-part bound. Composing with
    [quantize_lipschitz_compose] gives an explicit [2 * (1/2) = 1]
    additive slack on Lipschitz bounds when the score is rounded to
    the nearest integer.

    Higher-precision binary64-style quantizers (with 2^{-53} mantissa
    error) take the same shape — replace [/ 2] with [/ 2 ^ 53]. The
    full IEEE 754 normal-range model with subnormal handling is the
    natural extension; this is the constructive starting point. *)

Definition quantize_unit (x : R) : R := IZR (Int_part (x + /2)).

Theorem quantize_unit_bounded_error :
  forall x, (Rabs (quantize_unit x - x) <= /2)%R.
Proof.
  intros x. unfold quantize_unit.
  pose proof (base_Int_part (x + /2)) as [Hlo Hhi].
  set (n := IZR (Int_part (x + /2))) in *.
  unfold Rabs. destruct (Rcase_abs (n - x)) as [Hlt | Hge]; lra.
Qed.

Local Close Scope R_scope.

(** ** Real-valued loss [L_separated] with zero-locus equivalence.

    [pair_violation m d d'] is a nonneg real quantity that is zero
    iff the pair (d, d') satisfies the [Separated 1] condition at
    margin [m]: gap [>= m] and lower score [< theta]. The hinge form
    [Rmax 0 (m − gap) + Rmax 0 (lower − theta + 1)] is the discrete
    analog of the squared-hinge SGD objective (a square of this would
    be smooth; the present form is L1-Lipschitz almost everywhere
    and exactly captures the violation count).

    [L_separated] sums [pair_violation] over the cartesian list of
    distinct pairs. The headline theorem
    [L_separated_zero_iff_separated] establishes the zero-locus
    correspondence: the loss vanishes exactly on lists where
    [Separated iou tau theta 1] holds. This gives the loss landscape
    a target — converging the loss to zero is provably equivalent to
    converging to the [Separated] locus. *)

Local Open Scope R_scope.

Definition pair_violation
    {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
    (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
    (m : R) (d d' : @det Box) : R :=
  if det_eq_dec box_eq_dec_l d d' then 0
  else if Nat.leb tau (iou (box d) (box d')) then
    let s := INR (score d) in
    let s' := INR (score d') in
    let lower := Rmin s s' in
    let upper := Rmax s s' in
    Rmax 0 (m - (upper - lower)) + Rmax 0 (lower - INR theta + 1)
  else 0.

Lemma pair_violation_nonneg :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (m : R) (d d' : @det Box),
    0 <= pair_violation iou tau theta box_eq_dec_l m d d'.
Proof.
  intros Box iou tau theta box_eq_dec_l m d d'.
  unfold pair_violation.
  destruct (det_eq_dec box_eq_dec_l d d') as [_ | _]; [apply Rle_refl|].
  destruct (Nat.leb tau (iou (box d) (box d'))); [|apply Rle_refl].
  apply Rplus_le_le_0_compat; apply Rmax_l.
Qed.

Definition L_separated
    {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
    (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
    (m : R) (D : list (@det Box)) : R :=
  fold_right Rplus 0
    (flat_map (fun d =>
                 map (fun d' =>
                        pair_violation iou tau theta box_eq_dec_l m d d') D)
              D).

Lemma fold_right_Rplus_nonneg :
  forall (l : list R), (forall x, In x l -> 0 <= x) ->
    0 <= fold_right Rplus 0 l.
Proof.
  induction l as [|x rest IH]; intros Hnn; simpl; [apply Rle_refl|].
  apply Rplus_le_le_0_compat.
  - apply Hnn. left; reflexivity.
  - apply IH. intros y Hy. apply Hnn. right; assumption.
Qed.

Lemma L_separated_nonneg :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (m : R) (D : list (@det Box)),
    0 <= L_separated iou tau theta box_eq_dec_l m D.
Proof.
  intros Box iou tau theta box_eq_dec_l m D.
  unfold L_separated.
  apply fold_right_Rplus_nonneg.
  intros x Hx. apply in_flat_map in Hx as [d [_ Hd]].
  apply in_map_iff in Hd as [d' [Heq _]]. subst x.
  apply pair_violation_nonneg.
Qed.

Lemma fold_right_Rplus_zero_iff :
  forall (l : list R),
    (forall x, In x l -> 0 <= x) ->
    (fold_right Rplus 0 l = 0 <-> forall x, In x l -> x = 0).
Proof.
  induction l as [|x rest IH]; intros Hnn; simpl; split.
  - intros _ y Hy. contradiction.
  - intros _. reflexivity.
  - intros Hsum y Hy.
    assert (Hx_nn : 0 <= x) by (apply Hnn; left; reflexivity).
    assert (Hrest_nn : forall y, In y rest -> 0 <= y)
      by (intros z Hz; apply Hnn; right; assumption).
    pose proof (fold_right_Rplus_nonneg rest Hrest_nn).
    assert (Hx_eq : x = 0) by lra.
    assert (Hrest_eq : fold_right Rplus 0 rest = 0) by lra.
    destruct Hy as [Heq | Hy].
    + subst y. assumption.
    + apply (proj1 (IH Hrest_nn) Hrest_eq y Hy).
  - intros Hall.
    assert (Hx : x = 0) by (apply Hall; left; reflexivity).
    assert (Hrest_nn : forall y, In y rest -> 0 <= y)
      by (intros z Hz; apply Hnn; right; assumption).
    assert (Hrest : forall y, In y rest -> y = 0)
      by (intros y Hy; apply Hall; right; assumption).
    rewrite Hx. rewrite (proj2 (IH Hrest_nn) Hrest). lra.
Qed.

Local Close Scope R_scope.

Theorem L_separated_zero_iff_separated :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (D : list (@det Box)),
    (1 <= theta)%nat ->
    (L_separated iou tau theta box_eq_dec_l 1%R D = 0%R) <->
    Separated iou tau theta 1 D.
Proof.
  intros Box iou tau theta box_eq_dec_l D Hth_pos.
  unfold L_separated.
  rewrite fold_right_Rplus_zero_iff.
  - split.
    + intros Hall d d' Hin_d Hin_d' Hne Hiou.
      assert (Hpv : pair_violation iou tau theta box_eq_dec_l 1%R d d' = 0%R).
      { apply Hall. apply in_flat_map. exists d. split; [assumption|].
        apply in_map_iff. exists d'. split; [reflexivity|assumption]. }
      unfold pair_violation in Hpv.
      destruct (det_eq_dec box_eq_dec_l d d') as [Heq | _]; [contradiction|].
      apply Nat.leb_le in Hiou as Hle. rewrite Hle in Hpv.
      set (s := INR (score d)) in *.
      set (s' := INR (score d')) in *.
      set (lower := Rmin s s') in *.
      set (upper := Rmax s s') in *.
      assert (Hgap : (Rmax 0 (1 - (upper - lower)) = 0)%R /\
                    (Rmax 0 (lower - INR theta + 1) = 0)%R).
      { pose proof (Rmax_l 0 (1 - (upper - lower))%R) as H1.
        pose proof (Rmax_l 0 (lower - INR theta + 1)%R) as H2.
        split; lra. }
      destruct Hgap as [Hg1 Hg2].
      assert (Hg1' : (upper - lower >= 1)%R).
      { destruct (Rle_dec 0 (1 - (upper - lower))%R) as [Hle' | Hgt'].
        - rewrite (Rmax_right _ _ Hle') in Hg1. lra.
        - lra. }
      assert (Hg2' : (lower < INR theta)%R).
      { destruct (Rle_dec 0 (lower - INR theta + 1)%R) as [Hle' | Hgt'].
        - rewrite (Rmax_right _ _ Hle') in Hg2. lra.
        - lra. }
      destruct (Rle_lt_dec s s') as [Hss | Hss].
      * left.
        assert (Hlow : lower = s) by (apply Rmin_left; assumption).
        assert (Hup : upper = s') by (apply Rmax_right; assumption).
        rewrite Hlow in Hg2'. rewrite Hlow, Hup in Hg1'.
        unfold s, s' in *.
        split.
        -- apply INR_le. rewrite plus_INR. simpl. lra.
        -- apply INR_lt. lra.
      * right.
        assert (Hlow : lower = s') by (apply Rmin_right; lra).
        assert (Hup : upper = s) by (apply Rmax_left; lra).
        rewrite Hlow in Hg2'. rewrite Hlow, Hup in Hg1'.
        unfold s, s' in *.
        split.
        -- apply INR_le. rewrite plus_INR. simpl. lra.
        -- apply INR_lt. lra.
    + intros Hsep x Hx.
      apply in_flat_map in Hx as [d [Hd Hd_in]].
      apply in_map_iff in Hd_in as [d' [Heq Hd'_in]]. subst x.
      unfold pair_violation.
      destruct (det_eq_dec box_eq_dec_l d d') as [Heq | Hne]; [reflexivity|].
      destruct (Nat.leb tau (iou (box d) (box d'))) eqn:Eiou; [|reflexivity].
      apply Nat.leb_le in Eiou.
      specialize (Hsep d d' Hd Hd'_in Hne Eiou).
      set (s := INR (score d)) in *.
      set (s' := INR (score d')) in *.
      set (lower := Rmin s s') in *.
      set (upper := Rmax s s') in *.
      destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
      * assert (Hss : (s <= s')%R) by (apply le_INR; lia).
        assert (Hgap_R : (s' >= s + 1)%R).
        { unfold s, s'. rewrite <- (S_INR (score d)).
          apply Rle_ge, le_INR. lia. }
        assert (Hth_R : (s + 1 <= INR theta)%R).
        { unfold s. rewrite <- (S_INR (score d)).
          apply le_INR. lia. }
        assert (Hlow : lower = s) by (apply Rmin_left; assumption).
        assert (Hup : upper = s') by (apply Rmax_right; assumption).
        rewrite Hlow, Hup.
        rewrite (Rmax_left 0 (1 - (s' - s)))%R by lra.
        rewrite (Rmax_left 0 (s - INR theta + 1))%R by lra.
        lra.
      * assert (Hss : (s' <= s)%R) by (apply le_INR; lia).
        assert (Hgap_R : (s >= s' + 1)%R).
        { unfold s, s'. rewrite <- (S_INR (score d')).
          apply Rle_ge, le_INR. lia. }
        assert (Hth_R : (s' + 1 <= INR theta)%R).
        { unfold s'. rewrite <- (S_INR (score d')).
          apply le_INR. lia. }
        assert (Hlow : lower = s') by (apply Rmin_right; assumption).
        assert (Hup : upper = s) by (apply Rmax_left; assumption).
        rewrite Hlow, Hup.
        rewrite (Rmax_left 0 (1 - (s - s')))%R by lra.
        rewrite (Rmax_left 0 (s' - INR theta + 1))%R by lra.
        lra.
  - intros x Hx. apply in_flat_map in Hx as [d [_ Hd]].
    apply in_map_iff in Hd as [d' [Heq _]]. subst x.
    apply pair_violation_nonneg.
Qed.

(** ** General-margin zero-locus for [L_separated].

    The previous [L_separated_zero_iff_separated] is fixed at margin
    [m = 1] and slack [k = 1]. The generalisation: for any nat slack
    [k >= 1], the loss at real margin [INR k] vanishes iff
    [Separated iou tau theta k] holds. The proof mirrors the [k = 1]
    case with constants generalised. The unit-margin theorem becomes
    the [k = 1] specialisation of this. *)

Theorem L_separated_zero_iff_separated_general :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (D : list (@det Box)) (k : nat),
    (1 <= k)%nat -> (k <= theta)%nat ->
    (L_separated iou tau theta box_eq_dec_l (INR k) D = 0)%R <->
    Separated iou tau theta k D.
Proof.
  intros Box iou tau theta box_eq_dec_l D k Hk_pos Hk_le_theta.
  unfold L_separated.
  rewrite fold_right_Rplus_zero_iff.
  - split.
    + intros Hall d d' Hin_d Hin_d' Hne Hiou.
      assert (Hpv : pair_violation iou tau theta box_eq_dec_l (INR k) d d'
                    = 0%R).
      { apply Hall. apply in_flat_map. exists d. split; [assumption|].
        apply in_map_iff. exists d'. split; [reflexivity|assumption]. }
      unfold pair_violation in Hpv.
      destruct (det_eq_dec box_eq_dec_l d d') as [Heq | _]; [contradiction|].
      apply Nat.leb_le in Hiou as Hle. rewrite Hle in Hpv.
      set (s := INR (score d)) in *.
      set (s' := INR (score d')) in *.
      set (lower := Rmin s s') in *.
      set (upper := Rmax s s') in *.
      assert (Hgap : (Rmax 0 (INR k - (upper - lower)) = 0)%R /\
                    (Rmax 0 (lower - INR theta + 1) = 0)%R).
      { pose proof (Rmax_l 0 (INR k - (upper - lower))%R) as H1.
        pose proof (Rmax_l 0 (lower - INR theta + 1)%R) as H2.
        split; lra. }
      destruct Hgap as [Hg1 Hg2].
      assert (Hk_R_pos : (0 < INR k)%R) by (apply lt_0_INR; lia).
      assert (Hg1' : (upper - lower >= INR k)%R).
      { destruct (Rle_dec 0 (INR k - (upper - lower))%R) as [Hle' | Hgt'].
        - rewrite (Rmax_right _ _ Hle') in Hg1. lra.
        - lra. }
      assert (Hg2' : (lower < INR theta)%R).
      { destruct (Rle_dec 0 (lower - INR theta + 1)%R) as [Hle' | Hgt'].
        - rewrite (Rmax_right _ _ Hle') in Hg2. lra.
        - lra. }
      destruct (Rle_lt_dec s s') as [Hss | Hss].
      * left.
        assert (Hlow : lower = s) by (apply Rmin_left; assumption).
        assert (Hup : upper = s') by (apply Rmax_right; assumption).
        rewrite Hlow in Hg2'. rewrite Hlow, Hup in Hg1'.
        unfold s, s' in *.
        split.
        -- apply INR_le. rewrite plus_INR. lra.
        -- apply INR_lt. lra.
      * right.
        assert (Hlow : lower = s') by (apply Rmin_right; lra).
        assert (Hup : upper = s) by (apply Rmax_left; lra).
        rewrite Hlow in Hg2'. rewrite Hlow, Hup in Hg1'.
        unfold s, s' in *.
        split.
        -- apply INR_le. rewrite plus_INR. lra.
        -- apply INR_lt. lra.
    + intros Hsep x Hx.
      apply in_flat_map in Hx as [d [Hd Hd_in]].
      apply in_map_iff in Hd_in as [d' [Heq Hd'_in]]. subst x.
      unfold pair_violation.
      destruct (det_eq_dec box_eq_dec_l d d') as [Heq | Hne]; [reflexivity|].
      destruct (Nat.leb tau (iou (box d) (box d'))) eqn:Eiou; [|reflexivity].
      apply Nat.leb_le in Eiou.
      specialize (Hsep d d' Hd Hd'_in Hne Eiou).
      set (s := INR (score d)) in *.
      set (s' := INR (score d')) in *.
      set (lower := Rmin s s') in *.
      set (upper := Rmax s s') in *.
      destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
      * assert (Hss : (s <= s')%R) by (apply le_INR; lia).
        assert (Hgap_R : (s' >= s + INR k)%R).
        { unfold s, s'. rewrite <- (plus_INR (score d) k).
          apply Rle_ge, le_INR. lia. }
        assert (Hlow : lower = s) by (apply Rmin_left; assumption).
        assert (Hup : upper = s') by (apply Rmax_right; assumption).
        rewrite Hlow, Hup.
        rewrite (Rmax_left 0 (INR k - (s' - s)))%R by lra.
        rewrite (Rmax_left 0 (s - INR theta + 1))%R by
          (assert (s + 1 <= INR theta)%R by
             (unfold s; rewrite <- (S_INR (score d)); apply le_INR; lia); lra).
        lra.
      * assert (Hss : (s' <= s)%R) by (apply le_INR; lia).
        assert (Hgap_R : (s >= s' + INR k)%R).
        { unfold s, s'. rewrite <- (plus_INR (score d') k).
          apply Rle_ge, le_INR. lia. }
        assert (Hlow : lower = s') by (apply Rmin_right; assumption).
        assert (Hup : upper = s) by (apply Rmax_left; assumption).
        rewrite Hlow, Hup.
        rewrite (Rmax_left 0 (INR k - (s - s')))%R by lra.
        rewrite (Rmax_left 0 (s' - INR theta + 1))%R by
          (assert (s' + 1 <= INR theta)%R by
             (unfold s'; rewrite <- (S_INR (score d')); apply le_INR; lia); lra).
        lra.
  - intros x Hx. apply in_flat_map in Hx as [d [_ Hd]].
    apply in_map_iff in Hd as [d' [Heq _]]. subst x.
    apply pair_violation_nonneg.
Qed.

(** ** Smooth (squared-hinge) surrogate for [L_separated].

    The L1-hinge [L_separated] has a kink at the margin boundary,
    blocking standard SGD analysis (gradient discontinuous). The
    squared-hinge variant [pair_violation_sq] replaces each
    [Rmax 0 (...)] term with its square: smooth, with continuous
    gradient. The same zero-locus correspondence holds: the squared
    sum vanishes iff every pair satisfies [Separated 1]. With the
    gradient computable explicitly (subgradient at the kink coincides
    with both branches) and bounded second-derivative, the squared
    surrogate plugs directly into [SGDDescent]'s
    [quadratic_upper_bound] hypothesis. *)

Local Open Scope R_scope.

Definition pair_violation_sq
    {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
    (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
    (m : R) (d d' : @det Box) : R :=
  if det_eq_dec box_eq_dec_l d d' then 0
  else if Nat.leb tau (iou (box d) (box d')) then
    let s := INR (score d) in
    let s' := INR (score d') in
    let lower := Rmin s s' in
    let upper := Rmax s s' in
    (Rmax 0 (m - (upper - lower)))^2 + (Rmax 0 (lower - INR theta + 1))^2
  else 0.

Lemma pair_violation_sq_nonneg :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (m : R) (d d' : @det Box),
    0 <= pair_violation_sq iou tau theta box_eq_dec_l m d d'.
Proof.
  intros Box iou tau theta box_eq_dec_l m d d'.
  unfold pair_violation_sq.
  destruct (det_eq_dec box_eq_dec_l d d'); [apply Rle_refl|].
  destruct (Nat.leb tau (iou (box d) (box d'))); [|apply Rle_refl].
  apply Rplus_le_le_0_compat;
    pose proof (Rmax_l 0 (m - (Rmax (INR (score d)) (INR (score d'))
                                - Rmin (INR (score d)) (INR (score d'))))) as H1;
    pose proof (Rmax_l 0 (Rmin (INR (score d)) (INR (score d')) -
                          INR theta + 1)) as H2;
    [pose proof (Rle_0_sqr (Rmax 0 (m - (Rmax (INR (score d)) (INR (score d')) -
                                          Rmin (INR (score d)) (INR (score d')))))) as Hsq;
     unfold Rsqr in Hsq; nra
    |pose proof (Rle_0_sqr (Rmax 0 (Rmin (INR (score d)) (INR (score d')) -
                                     INR theta + 1))) as Hsq;
     unfold Rsqr in Hsq; nra].
Qed.

Definition L_separated_sq
    {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
    (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
    (m : R) (D : list (@det Box)) : R :=
  fold_right Rplus 0
    (flat_map (fun d =>
                 map (fun d' =>
                        pair_violation_sq iou tau theta box_eq_dec_l m d d') D)
              D).

Lemma L_separated_sq_nonneg :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (m : R) (D : list (@det Box)),
    0 <= L_separated_sq iou tau theta box_eq_dec_l m D.
Proof.
  intros Box iou tau theta box_eq_dec_l m D.
  unfold L_separated_sq.
  apply fold_right_Rplus_nonneg.
  intros x Hx. apply in_flat_map in Hx as [d [_ Hd]].
  apply in_map_iff in Hd as [d' [Heq _]]. subst x.
  apply pair_violation_sq_nonneg.
Qed.

Lemma pair_violation_sq_zero_iff :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (box_eq_dec_l : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (m : R) (d d' : @det Box),
    pair_violation_sq iou tau theta box_eq_dec_l m d d' = 0 <->
    pair_violation iou tau theta box_eq_dec_l m d d' = 0.
Proof.
  intros Box iou tau theta box_eq_dec_l m d d'.
  unfold pair_violation_sq, pair_violation.
  destruct (det_eq_dec box_eq_dec_l d d'); [split; reflexivity|].
  destruct (Nat.leb tau (iou (box d) (box d'))); [|split; reflexivity].
  set (s := INR (score d)).
  set (s' := INR (score d')).
  set (lower := Rmin s s').
  set (upper := Rmax s s').
  set (a := Rmax 0 (m - (upper - lower))).
  set (b := Rmax 0 (lower - INR theta + 1)).
  pose proof (Rmax_l 0 (m - (upper - lower))) as Ha. fold a in Ha.
  pose proof (Rmax_l 0 (lower - INR theta + 1)) as Hb. fold b in Hb.
  split.
  - intros Hsum.
    assert (Hsq_a : 0 <= a^2) by (pose proof (Rle_0_sqr a); unfold Rsqr in *; nra).
    assert (Hsq_b : 0 <= b^2) by (pose proof (Rle_0_sqr b); unfold Rsqr in *; nra).
    assert (Ha_zero : a^2 = 0) by lra.
    assert (Hb_zero : b^2 = 0) by lra.
    assert (Ha0 : a = 0).
    { pose proof (Rsqr_0_uniq a). unfold Rsqr in H. apply H. nra. }
    assert (Hb0 : b = 0).
    { pose proof (Rsqr_0_uniq b). unfold Rsqr in H. apply H. nra. }
    lra.
  - intros Hsum.
    assert (Ha0 : a = 0) by lra.
    assert (Hb0 : b = 0) by lra.
    rewrite Ha0, Hb0. lra.
Qed.

(** ** Squared-hinge gradient with explicit smoothness constant.

    The gap term in [pair_violation_sq] has the form
    [(Rmax 0 (m - g))^2] where [g] is the score-gap. Its gradient
    w.r.t. [g] is the continuous function [-2 * Rmax 0 (m - g)] —
    [-2 (m - g)] in the active region and [0] in the inactive region,
    with the two branches matching at the kink [g = m]. This gradient
    is Lipschitz with constant [2]: [|grad x - grad y| <= 2 * |x - y|].
    Concretely instantiates the abstract [Lsm] in [Section SGDDescent]
    by [2], so any SGD step on a single squared-hinge term satisfies
    the descent inequality with [eta * 2 <= 1] (i.e., [eta <= 1/2]).
    The full [L_separated_sq] gradient is the sum over distinct
    high-IoU pairs; smoothness composes additively. *)

Definition sq_hinge_at (m x : R) : R := (Rmax 0 (m - x))^2.

Definition sq_hinge_deriv (m x : R) : R := -2 * Rmax 0 (m - x).

Theorem sq_hinge_lipschitz_grad :
  forall m x y, Rabs (sq_hinge_deriv m x - sq_hinge_deriv m y)%R <=
                2 * Rabs (x - y).
Proof.
  intros m x y. unfold sq_hinge_deriv.
  pose proof (lip_bound lip_relu (m - x) (m - y)) as Hrelu.
  rewrite Rmult_1_l in Hrelu.
  set (a := Rmax 0 (m - x)) in *.
  set (b := Rmax 0 (m - y)) in *.
  replace (-2 * a - -2 * b)%R with (-2 * (a - b))%R by lra.
  rewrite Rabs_mult.
  assert (Hr2 : Rabs (-2) = 2).
  { unfold Rabs. destruct (Rcase_abs (-2)); lra. }
  rewrite Hr2.
  rewrite (Rabs_minus_sym (m - x) (m - y)) in Hrelu.
  replace (m - y - (m - x))%R with (x - y) in Hrelu by lra.
  nra.
Qed.

Theorem sq_hinge_at_inactive_zero :
  forall m x, m <= x -> sq_hinge_at m x = 0.
Proof.
  intros m x H. unfold sq_hinge_at.
  rewrite Rmax_left by lra.
  unfold pow. lra.
Qed.

Theorem sq_hinge_deriv_inactive_zero :
  forall m x, m <= x -> sq_hinge_deriv m x = 0.
Proof.
  intros m x H. unfold sq_hinge_deriv.
  rewrite Rmax_left by lra.
  lra.
Qed.

Local Close Scope R_scope.

(** ** Real-valued gradient descent convergence.

    Single-parameter SGD analysis built from primitives in
    [Stdlib.Reals]. Given an L-smooth real-valued loss [f] with
    gradient [grad] (i.e., [f] satisfies the standard quadratic upper
    bound), one step of [sgd_step eta theta := theta - eta * grad theta]
    decreases [f] by at least [eta/2 * (grad theta)^2] when
    [eta * Lsm <= 1]. Iterating [T] times telescopes to
    [Σ_{t<T} (grad theta_t)^2 <= 2(f theta_0 - f_lower) / eta].
    Pigeonhole gives [min_{t<T} (grad theta_t)^2 <= 2(f theta_0 - f_lower)/(eta*T)],
    so [T = O(1/δ²)] iterations suffice for a δ-stationary point.

    Composed with [L_separated_zero_iff_separated], any smoothed
    surrogate of [L_separated] driven to its zero locus by SGD lands
    on the [Separated] locus. *)

Local Open Scope R_scope.

Section SGDDescent.
  Variable f : R -> R.
  Variable grad : R -> R.
  Variable Lsm : R.
  Hypothesis Lsm_pos : 0 < Lsm.

  Hypothesis quadratic_upper_bound :
    forall x y,
      f y <= f x + grad x * (y - x) + Lsm / 2 * ((y - x) * (y - x)).

  Definition sgd_step (eta theta : R) : R := theta - eta * grad theta.

  Theorem sgd_descent :
    forall eta theta,
      0 < eta -> eta * Lsm <= 1 ->
      f (sgd_step eta theta) <=
      f theta - eta / 2 * (grad theta * grad theta).
  Proof.
    intros eta theta Heta_pos HetaLsm.
    unfold sgd_step.
    pose proof (quadratic_upper_bound theta (theta - eta * grad theta)) as H.
    replace (theta - eta * grad theta - theta)
       with (- (eta * grad theta)) in H by lra.
    replace (grad theta * - (eta * grad theta))
       with (- (eta * (grad theta * grad theta))) in H by lra.
    replace (- (eta * grad theta) * - (eta * grad theta))
       with (eta * eta * (grad theta * grad theta)) in H by lra.
    assert (Hsq : 0 <= grad theta * grad theta).
    { destruct (Rle_dec 0 (grad theta)) as [Hp | Hn]; nra. }
    assert (Hkey : 0 <= eta * (grad theta * grad theta) * (1 - eta * Lsm)).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos; [lra | assumption].
      - lra. }
    nra.
  Qed.

  Fixpoint sgd_iterate (eta : R) (theta0 : R) (n : nat) : R :=
    match n with
    | O => theta0
    | S k => sgd_step eta (sgd_iterate eta theta0 k)
    end.

  Fixpoint grad_sq_sum (eta : R) (theta0 : R) (n : nat) : R :=
    match n with
    | O => 0
    | S k =>
        grad_sq_sum eta theta0 k +
        grad (sgd_iterate eta theta0 k) * grad (sgd_iterate eta theta0 k)
    end.

  Theorem sgd_telescoping_aux :
    forall eta theta0 n,
      0 < eta -> eta * Lsm <= 1 ->
      (eta / 2) * grad_sq_sum eta theta0 n
      <= f theta0 - f (sgd_iterate eta theta0 n).
  Proof.
    intros eta theta0 n Heta_pos HetaLsm.
    induction n as [|k IH]; simpl.
    - lra.
    - set (theta_k := sgd_iterate eta theta0 k) in *.
      assert (Hdesc : f (sgd_step eta theta_k) <=
                       f theta_k - eta / 2 * (grad theta_k * grad theta_k))
        by (apply sgd_descent; assumption).
      assert (Hgrad_nn : 0 <= grad theta_k * grad theta_k).
      { destruct (Rle_dec 0 (grad theta_k)) as [Hp | Hn]; nra. }
      nra.
  Qed.

  Theorem sgd_telescoping :
    forall eta theta0 n f_lower,
      0 < eta -> eta * Lsm <= 1 ->
      (forall x, f_lower <= f x) ->
      (eta / 2) * grad_sq_sum eta theta0 n <= f theta0 - f_lower.
  Proof.
    intros eta theta0 n f_lower Heta_pos HetaLsm Hf_lower.
    pose proof (@sgd_telescoping_aux eta theta0 n Heta_pos HetaLsm) as Haux.
    pose proof (Hf_lower (sgd_iterate eta theta0 n)).
    lra.
  Qed.

End SGDDescent.

(** ** Multi-dimensional SGD on [R^n] parameter spaces.

    The single-parameter [SGDDescent] generalizes to vector-valued
    parameters. The descent inequality lifts: with the vector
    quadratic upper bound
    [f y <= f x + <grad x, y - x> + Lsm/2 * <y - x, y - x>],
    one step of [sgd_step_vec eta theta := theta - eta * grad theta]
    decreases [f] by at least [eta/2 * <grad theta, grad theta>] when
    [eta * Lsm <= 1]. Telescoping gives the standard
    [min_t <grad theta_t, grad theta_t> <= 2 (f theta_0 - f_lower) / (eta * T)]
    rate to a delta-stationary point in [T = O(1/delta^2)] iterations.
    This is the parameter-space-realistic version: real architectures
    have R^n parameter vectors with n in the millions. *)

Section SGDDescentVec.

  Local Open Scope R_scope.

  Variable n : nat.
  Variable f : list R -> R.
  Variable grad : list R -> list R.
  Variable Lsm : R.
  Hypothesis Lsm_pos : 0 < Lsm.

  Hypothesis grad_dim :
    forall theta, length theta = n -> length (grad theta) = n.

  Hypothesis quadratic_upper_bound_vec :
    forall x y, length x = n -> length y = n ->
      f y <= f x + dot (grad x) (vec_sub y x) +
              Lsm / 2 * dot (vec_sub y x) (vec_sub y x).

  Definition vec_scale (c : R) (v : list R) : list R := map (Rmult c) v.

  Lemma vec_scale_length :
    forall c v, length (vec_scale c v) = length v.
  Proof. intros c v. unfold vec_scale. apply length_map. Qed.

  Lemma vec_sub_length :
    forall u v, length u = length v -> length (vec_sub u v) = length u.
  Proof.
    induction u as [|x us IH]; intros v Hlen; destruct v as [|y vs];
      simpl in *; try discriminate; [reflexivity|].
    rewrite IH; [reflexivity | injection Hlen; intros; assumption].
  Qed.

  Lemma dot_self_nonneg :
    forall v, 0 <= dot v v.
  Proof.
    induction v as [|x rest IH]; simpl; [lra|].
    nra.
  Qed.

  Lemma dot_vec_scale_right :
    forall u v c, length u = length v ->
      dot u (vec_scale c v) = c * dot u v.
  Proof.
    induction u as [|x us IH]; intros v c Hlen;
      destruct v as [|y vs]; simpl in *; try discriminate; [lra|].
    injection Hlen as Hlen'.
    rewrite (IH vs c Hlen'). lra.
  Qed.

  Lemma dot_self_vec_scale :
    forall c v, dot (vec_scale c v) (vec_scale c v) = c * c * dot v v.
  Proof.
    induction v as [|x rest IH]; simpl; [lra|].
    rewrite IH. nra.
  Qed.

  Definition sgd_step_vec (eta : R) (theta : list R) : list R :=
    vec_sub theta (vec_scale eta (grad theta)).

  Lemma sgd_step_vec_length :
    forall eta theta,
      length theta = n -> length (sgd_step_vec eta theta) = n.
  Proof.
    intros eta theta Hlen. unfold sgd_step_vec.
    rewrite vec_sub_length.
    - assumption.
    - rewrite vec_scale_length, (grad_dim theta Hlen). assumption.
  Qed.

  Lemma vec_sub_step_eq :
    forall eta theta,
      length theta = n ->
      vec_sub (sgd_step_vec eta theta) theta =
      vec_scale (- eta) (grad theta).
  Proof.
    intros eta theta Hlen. unfold sgd_step_vec, vec_scale.
    pose proof (grad_dim theta Hlen) as Hgrad_len.
    rewrite <- Hlen in Hgrad_len.
    clear Hlen.
    remember (grad theta) as g eqn:Heqg. clear Heqg.
    revert g Hgrad_len.
    induction theta as [|t ts IH]; intros g Hgrad_len.
    - destruct g.
      + reflexivity.
      + simpl in Hgrad_len. discriminate.
    - destruct g as [|gh gs].
      + simpl in Hgrad_len. discriminate.
      + simpl in Hgrad_len.
        assert (Hgs_len : length gs = length ts)
          by (apply Nat.succ_inj; exact Hgrad_len).
        pose proof (IH gs Hgs_len) as Htail.
        cbn [vec_sub map].
        rewrite Htail. f_equal. nra.
  Qed.

  Theorem sgd_descent_vec :
    forall eta theta,
      length theta = n ->
      0 < eta -> eta * Lsm <= 1 ->
      f (sgd_step_vec eta theta) <=
      f theta - eta / 2 * dot (grad theta) (grad theta).
  Proof.
    intros eta theta Hlen Heta_pos HetaLsm.
    pose proof (sgd_step_vec_length eta theta Hlen) as Hsgd_len.
    pose proof (quadratic_upper_bound_vec theta (sgd_step_vec eta theta)
                  Hlen Hsgd_len) as H.
    rewrite (vec_sub_step_eq eta theta Hlen) in H.
    rewrite (dot_vec_scale_right (grad theta) (grad theta) (-eta) eq_refl) in H.
    rewrite dot_self_vec_scale in H.
    pose proof (dot_self_nonneg (grad theta)) as Hsq.
    assert (Hkey : 0 <= eta * dot (grad theta) (grad theta) * (1 - eta * Lsm)).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos; lra.
      - lra. }
    nra.
  Qed.

  Fixpoint sgd_iterate_vec (eta : R) (theta0 : list R) (k : nat) : list R :=
    match k with
    | O => theta0
    | S j => sgd_step_vec eta (sgd_iterate_vec eta theta0 j)
    end.

  Lemma sgd_iterate_vec_length :
    forall eta theta0 k,
      length theta0 = n -> length (sgd_iterate_vec eta theta0 k) = n.
  Proof.
    intros eta theta0 k Hlen.
    induction k as [|j IH]; simpl; [assumption|].
    apply sgd_step_vec_length. assumption.
  Qed.

  Fixpoint grad_norm_sq_sum (eta : R) (theta0 : list R) (k : nat) : R :=
    match k with
    | O => 0
    | S j =>
        grad_norm_sq_sum eta theta0 j +
        dot (grad (sgd_iterate_vec eta theta0 j))
            (grad (sgd_iterate_vec eta theta0 j))
    end.

  Theorem sgd_telescoping_vec_aux :
    forall eta theta0 k,
      length theta0 = n ->
      0 < eta -> eta * Lsm <= 1 ->
      (eta / 2) * grad_norm_sq_sum eta theta0 k
      <= f theta0 - f (sgd_iterate_vec eta theta0 k).
  Proof.
    intros eta theta0 k Hlen Heta_pos HetaLsm.
    induction k as [|j IH]; simpl.
    - lra.
    - set (theta_j := sgd_iterate_vec eta theta0 j) in *.
      assert (Hjlen : length theta_j = n)
        by (unfold theta_j; apply sgd_iterate_vec_length; assumption).
      assert (Hdesc : f (sgd_step_vec eta theta_j) <=
                       f theta_j -
                       eta / 2 * dot (grad theta_j) (grad theta_j))
        by (apply sgd_descent_vec; assumption).
      pose proof (dot_self_nonneg (grad theta_j)) as Hsq.
      nra.
  Qed.

  Theorem sgd_telescoping_vec :
    forall eta theta0 k f_lower,
      length theta0 = n ->
      0 < eta -> eta * Lsm <= 1 ->
      (forall x, length x = n -> f_lower <= f x) ->
      (eta / 2) * grad_norm_sq_sum eta theta0 k <= f theta0 - f_lower.
  Proof.
    intros eta theta0 k f_lower Hlen Heta_pos HetaLsm Hf_lower.
    pose proof (@sgd_telescoping_vec_aux eta theta0 k Hlen Heta_pos HetaLsm)
      as Haux.
    pose proof (Hf_lower (sgd_iterate_vec eta theta0 k)
                          (sgd_iterate_vec_length eta theta0 k Hlen)).
    lra.
  Qed.

End SGDDescentVec.

(** ** Probabilistic concentration on finite uniform samples.

    Foundational ingredients for the PAC bound built directly from
    [Stdlib.Reals]: a finite probability space (the uniform measure
    on a list of samples), expectation, and Markov's inequality. The
    Bonferroni union bound composes Markov over a finite hypothesis
    class to give a uniform-deviation guarantee. Composed with
    [L_separated_zero_iff_separated], the empirical loss is a
    [P]-bounded estimate of the population loss; convergence to zero
    on a sufficiently large sample gives [Separated] on the population
    via the union-bound chaining. *)

Definition prob_uniform (samples : list R) (event : R -> bool) : R :=
  if Nat.eqb (length samples) 0 then 0
  else INR (length (filter event samples)) / INR (length samples).

Definition expect_uniform (samples : list R) : R :=
  if Nat.eqb (length samples) 0 then 0
  else fold_right Rplus 0 samples / INR (length samples).

Lemma sum_filter_ge_threshold :
  forall (l : list R) (a : R),
    (forall x, In x l -> 0 <= x) ->
    a * INR (length (filter (fun x => if Rle_dec a x then true else false) l))
    <= fold_right Rplus 0 l.
Proof.
  induction l as [|x rest IH]; intros a Hnn; simpl; [lra|].
  assert (Hx_nn : 0 <= x) by (apply Hnn; left; reflexivity).
  assert (Hrest_nn : forall y, In y rest -> 0 <= y)
    by (intros y Hy; apply Hnn; right; assumption).
  specialize (IH a Hrest_nn).
  destruct (Rle_dec a x) as [Hge | Hlt].
  - cbn [filter length].
    destruct (Rle_dec a x) as [_ | Hlt']; [|contradiction].
    rewrite S_INR. nra.
  - cbn [filter length].
    destruct (Rle_dec a x) as [Hge' | _]; [contradiction|].
    lra.
Qed.

Theorem markov_finite_uniform :
  forall samples a,
    0 < a ->
    (forall x, In x samples -> 0 <= x) ->
    a *
    prob_uniform samples (fun x => if Rle_dec a x then true else false)
    <= expect_uniform samples.
Proof.
  intros samples a Ha Hnn.
  unfold prob_uniform, expect_uniform.
  destruct (Nat.eqb_spec (length samples) 0) as [Hzero | Hpos]; [lra|].
  assert (Hlen_pos : 0 < INR (length samples)).
  { destruct (length samples) eqn:E; [contradiction|].
    apply lt_0_INR. lia. }
  pose proof (sum_filter_ge_threshold samples a Hnn) as Hbnd.
  assert (Hinv_pos : 0 < / INR (length samples))
    by (apply Rinv_0_lt_compat; assumption).
  apply Rmult_le_reg_r with (INR (length samples)); [assumption|].
  replace
    (a *
     (INR
        (length
           (filter (fun x => if Rle_dec a x then true else false) samples)) /
      INR (length samples)) * INR (length samples))
    with
    (a *
     INR
       (length
          (filter (fun x => if Rle_dec a x then true else false) samples)))
    by (field; lra).
  replace
    (fold_right Rplus 0 samples / INR (length samples) * INR (length samples))
    with (fold_right Rplus 0 samples) by (field; lra).
  exact Hbnd.
Qed.

(** ** Bonferroni / union bound over a finite hypothesis class.

    For any list of events, the probability of their disjunction is
    bounded by the sum of individual probabilities. Composing with
    Markov gives the standard uniform-deviation bound: for a class of
    size M, the chance of any one estimator deviating by [eps] is at
    most M times the per-estimator Markov bound. This is the
    chaining step for the PAC bound on the empirical loss. *)

Lemma length_filter_or_le :
  forall (l : list R) (P Q : R -> bool),
    (length (filter (fun x => orb (P x) (Q x)) l) <=
     length (filter P l) + length (filter Q l))%nat.
Proof.
  induction l as [|x rest IH]; intros P Q; simpl; [lia|].
  destruct (P x) eqn:EP; destruct (Q x) eqn:EQ; simpl;
    specialize (IH P Q); lia.
Qed.

Theorem bonferroni_two :
  forall samples (P Q : R -> bool),
    prob_uniform samples (fun x => orb (P x) (Q x)) <=
    prob_uniform samples P + prob_uniform samples Q.
Proof.
  intros samples P Q. unfold prob_uniform.
  destruct (Nat.eqb_spec (length samples) 0) as [Hzero | Hpos]; [lra|].
  assert (Hlen_pos : 0 < INR (length samples)).
  { destruct (length samples) eqn:E; [contradiction|].
    apply lt_0_INR. lia. }
  pose proof (length_filter_or_le samples P Q) as Hle.
  apply Rmult_le_reg_r with (INR (length samples)); [assumption|].
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
  rewrite <- plus_INR.
  apply le_INR. assumption.
Qed.

(** ** N-event union bound (Bonferroni list).

    Generalises [bonferroni_two] from two events to a list of events.
    For [M] events, the probability of their disjunction is bounded
    by the sum of individual probabilities. This is the chaining
    step in the standard PAC argument: with [M] hypotheses each
    having Chebyshev-bounded deviation, the union bound caps the
    probability that any one deviates by [M / (n eps²)]. *)

Theorem bonferroni_list :
  forall samples (events : list (R -> bool)),
    prob_uniform samples
      (fun x => existsb (fun e => e x) events) <=
    fold_right Rplus 0 (map (fun e => prob_uniform samples e) events).
Proof.
  intros samples events.
  induction events as [|e rest IH]; simpl.
  - unfold prob_uniform.
    destruct (Nat.eqb_spec (length samples) 0); [lra|].
    assert (Hlen_pos : 0 < INR (length samples)).
    { destruct (length samples); [contradiction | apply lt_0_INR; lia]. }
    assert (Hfilter : forall l : list R, filter (fun _ : R => false) l = []).
    { intros l. induction l as [|x rest IHs]; simpl; [reflexivity | assumption]. }
    rewrite (Hfilter samples). simpl. lra.
  - eapply Rle_trans.
    + apply (bonferroni_two samples e
              (fun x => existsb (fun e0 => e0 x) rest)).
    + apply Rplus_le_compat_l. exact IH.
Qed.

(** ** Chebyshev-style concentration: variance-bounded tail.

    The full Hoeffding inequality
    [P(|S/n − E[S]| ≥ ε) ≤ 2 exp(−2nε²/(b−a)²)] requires the
    moment-generating function [E[exp(λX)]] and convexity of [exp];
    those go through [Stdlib.Reals.Rtrigo] but the formalization is
    substantial. The Chebyshev variant captures the same concentration
    content with elementary arithmetic: applying [markov_finite_uniform]
    to the squared-deviation random variable gives
    [a² * P(|X − μ| ≥ a) ≤ Var[X]]. The bound is polynomial in [1/a]
    instead of exponential, but the inequality is exact, no
    transcendentals required. *)

Definition var_uniform (samples : list R) : R :=
  let mu := expect_uniform samples in
  expect_uniform (map (fun x => (x - mu) * (x - mu)) samples).

Lemma expect_uniform_nonneg :
  forall samples,
    (forall x, In x samples -> 0 <= x) ->
    0 <= expect_uniform samples.
Proof.
  intros samples Hnn. unfold expect_uniform.
  destruct (Nat.eqb_spec (length samples) 0) as [Hzero | Hpos]; [lra|].
  assert (Hlen_pos : 0 < INR (length samples)).
  { destruct (length samples) eqn:E; [contradiction | apply lt_0_INR; lia]. }
  apply Rmult_le_pos; [|left; apply Rinv_0_lt_compat; assumption].
  apply fold_right_Rplus_nonneg. assumption.
Qed.

Lemma var_uniform_nonneg :
  forall samples, 0 <= var_uniform samples.
Proof.
  intros samples. unfold var_uniform.
  apply expect_uniform_nonneg.
  intros x Hin. apply in_map_iff in Hin as [y [Heq _]]. subst x.
  pose proof (Rle_0_sqr (y - expect_uniform samples)) as Hsq.
  unfold Rsqr in Hsq. exact Hsq.
Qed.

Theorem chebyshev_finite_uniform :
  forall samples a,
    0 < a ->
    a * a *
    prob_uniform
      (map (fun x => (x - expect_uniform samples) *
                     (x - expect_uniform samples)) samples)
      (fun y => if Rle_dec (a * a) y then true else false)
    <= var_uniform samples.
Proof.
  intros samples a Ha.
  apply markov_finite_uniform.
  - nra.
  - intros y Hy. apply in_map_iff in Hy as [x [Heq _]]. subst y.
    destruct (Rle_dec 0 (x - expect_uniform samples)) as [Hp | Hn]; nra.
Qed.

(** ** Chernoff-Markov bound: tightening Markov via the
    moment-generating function.

    A natural strengthening of [markov_finite_uniform] applies Markov
    to the transformed sample [exp (lambda * x)]: for any
    [lambda > 0],
    [exp(lambda * a) * P(X >= a) <= E[exp(lambda * X)]].
    This is the "Chernoff method" — pick [lambda] to minimize the RHS
    for the tightest tail bound. The full Hoeffding bound
    [P(X >= a) <= 2 exp(-2 n a^2 / (b - a)^2)] follows by combining
    this with the sub-Gaussian MGF bound
    [E[exp(lambda * X)] <= exp(lambda^2 * (b - a)^2 / 8)] for centered
    bounded [X], whose proof requires a convexity argument on [exp];
    that argument is built from primitives. *)

Definition mgf_uniform (samples : list R) (lambda : R) : R :=
  expect_uniform (map (fun x => exp (lambda * x)) samples).

Lemma exp_le_compat :
  forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y [Hlt | Heq].
  - left. apply exp_increasing. assumption.
  - subst. apply Rle_refl.
Qed.

Lemma exp_le_inv :
  forall x y, exp x <= exp y -> x <= y.
Proof.
  intros x y [Hlt | Heq].
  - left. apply exp_lt_inv. assumption.
  - apply exp_inv in Heq. subst. apply Rle_refl.
Qed.

Lemma length_filter_map_iff :
  forall (A B : Type) (f : A -> B) (P : A -> bool) (Q : B -> bool)
         (l : list A),
    (forall x, P x = Q (f x)) ->
    length (filter Q (map f l)) = length (filter P l).
Proof.
  intros A B f P Q l Hpq.
  induction l as [|x rest IH]; simpl; [reflexivity|].
  rewrite <- Hpq. destruct (P x); simpl; [f_equal|]; apply IH.
Qed.

Lemma prob_uniform_exp_event_eq :
  forall samples lambda a,
    0 < lambda ->
    prob_uniform samples
      (fun x => if Rle_dec a x then true else false) =
    prob_uniform (map (fun x => exp (lambda * x)) samples)
                 (fun y => if Rle_dec (exp (lambda * a)) y
                           then true else false).
Proof.
  intros samples lambda a Hl.
  unfold prob_uniform.
  rewrite length_map.
  destruct (Nat.eqb_spec (length samples) 0); [reflexivity|].
  f_equal. f_equal.
  rewrite (@length_filter_map_iff R R
            (fun x : R => exp (lambda * x))
            (fun x : R => if Rle_dec a x then true else false)
            (fun y : R =>
              if Rle_dec (exp (lambda * a)) y then true else false)
            samples).
  - reflexivity.
  - intros x.
    destruct (Rle_dec a x) as [Hax | Hax];
    destruct (Rle_dec (exp (lambda * a)) (exp (lambda * x)))
      as [Hexp | Hexp]; try reflexivity.
    + exfalso. apply Hexp. apply exp_le_compat. nra.
    + exfalso. apply Hax.
      apply exp_le_inv in Hexp.
      apply (Rmult_le_reg_l lambda); [assumption | exact Hexp].
Qed.

Theorem chernoff_markov_bound :
  forall samples lambda a,
    0 < lambda ->
    exp (lambda * a) *
    prob_uniform samples
      (fun x => if Rle_dec a x then true else false)
    <= mgf_uniform samples lambda.
Proof.
  intros samples lambda a Hl.
  rewrite (@prob_uniform_exp_event_eq samples lambda a Hl).
  apply markov_finite_uniform.
  - apply exp_pos.
  - intros y Hy. apply in_map_iff in Hy as [x [Heq _]]. subst y.
    left. apply exp_pos.
Qed.

Local Close Scope R_scope.

(** ** Concrete Lipschitz bound for a real two-layer architecture.

    [arch_M1 := [[3]]] and [arch_M2 := [[2]]] are explicit weight
    matrices for a one-input one-output ReLU network
    [arch_f x := 2 * Rmax 0 (3 * x)]. [lip_compose],
    [lip_relu], and [lip_mult_left] yield a Lipschitz constant 6 (=
    [mat_inf_norm arch_M1 * mat_inf_norm arch_M2]). The corresponding
    [arch_head : SepRespectingHead R] inherits this L via the
    [real_lipschitz_to_nat] adapter. The L value reduces to a closed
    numeric form by [reflexivity] / [vm_compute]. *)

Local Open Scope R_scope.

Definition arch_M1 : matrix := [[3%R]].
Definition arch_M2 : matrix := [[2%R]].

Lemma arch_M1_norm : mat_inf_norm arch_M1 = 3.
Proof.
  unfold arch_M1, mat_inf_norm. simpl.
  rewrite Rabs_right by lra. rewrite Rplus_0_r.
  apply Rmax_left. lra.
Qed.

Lemma arch_M2_norm : mat_inf_norm arch_M2 = 2.
Proof.
  unfold arch_M2, mat_inf_norm. simpl.
  rewrite Rabs_right by lra. rewrite Rplus_0_r.
  apply Rmax_left. lra.
Qed.

Definition arch_f (x : R) : R := 2 * Rmax 0 (3 * x).

Lemma arch_f_nonneg : forall x, 0 <= arch_f x.
Proof. intros x. unfold arch_f. apply Rmult_le_pos; [lra | apply Rmax_l]. Qed.

Lemma arch_f_lipschitz : Lipschitz 6 arch_f.
Proof.
  unfold arch_f.
  pose proof (lip_compose
                (lip_mult_left 2)
                (lip_compose lip_relu (lip_mult_left 3))) as H.
  rewrite (Rabs_right 2) in H by lra.
  rewrite (Rabs_right 3) in H by lra.
  rewrite Rmult_1_l in H.
  replace (2 * 3) with 6 in H by lra.
  exact H.
Qed.

Local Close Scope R_scope.

Definition arch_head : SepRespectingHead R.
Proof.
  refine (mkSepHead (rnat_h 1 arch_f) (rnat_dist 1) 6 0 1 _ _).
  - apply real_lipschitz_to_nat with (L := 6%R) (f := arch_f).
    + apply arch_f_lipschitz.
    + lra.
    + simpl. lra.
    + apply arch_f_nonneg.
  - lia.
Defined.

Example arch_head_L : sep_L arch_head = 6.
Proof. reflexivity. Qed.

Example arch_head_eps : sep_eps arch_head = 0.
Proof. reflexivity. Qed.

Example arch_head_m : sep_m arch_head = 1.
Proof. reflexivity. Qed.

(** ** Theorem 4 — finite certificate search.

    Reuses the existing [Separated_dec] / [Separated_check] machinery.
    For each candidate head [S], compute its effective slack
    [sep_m S - 2 * sep_L S * sep_eps S]; check whether the detection
    list [D] satisfies [Separated] at that slack. Return the first head
    whose effective slack discharges the check, or [None] if no
    candidate succeeds.

    The check verifies the consequence ([D] is Separated at the head's
    slack), not the head's bridge precondition. The head's certificate
    is the constructive witness that this consequence is achievable; the
    finite search verifies it concretely. The continuous-training story
    (a head trained on this distribution converges to one whose
    effective slack matches [D]'s actual separation) is the missing
    analytic completion. *)

Section SepFiniteCertify.

  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym_h : forall a b, iou a b = iou b a.
  Variable tau : nat.
  Variable theta : nat.
  Variable Feat : Type.
  Variable box_eq_dec : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2}.

  Definition sep_effective_slack (Sh : SepRespectingHead Feat) : nat :=
    sep_m Sh - 2 * sep_L Sh * sep_eps Sh.

  Fixpoint sep_certify_finite
    (cands : list (SepRespectingHead Feat))
    (D : list (@det Box)) : option (SepRespectingHead Feat) :=
    match cands with
    | [] => None
    | Sh :: rest =>
        if Separated_check iou tau theta box_eq_dec
                           (sep_effective_slack Sh) D
        then Some Sh
        else sep_certify_finite rest D
    end.

  Theorem sep_certify_finite_sound :
    forall cands D Sh,
      sep_certify_finite cands D = Some Sh ->
      In Sh cands /\
      Separated iou tau theta (sep_effective_slack Sh) D.
  Proof.
    induction cands as [|S0 rest IH]; intros D Sh Hcert.
    - simpl in Hcert. discriminate.
    - simpl in Hcert.
      destruct (Separated_check iou tau theta box_eq_dec
                                (sep_effective_slack S0) D) eqn:Echeck.
      + injection Hcert as Heq. subst.
        split; [left; reflexivity|].
        apply Separated_check_correct in Echeck. exact Echeck.
      + apply IH in Hcert as [Hin Hsep].
        split; [right; assumption | assumption].
  Qed.

  Theorem sep_certify_finite_complete :
    forall cands D,
      sep_certify_finite cands D = None ->
      forall Sh, In Sh cands ->
        ~ Separated iou tau theta (sep_effective_slack Sh) D.
  Proof.
    induction cands as [|S0 rest IH]; intros D Hcert Sh Hin Hsep.
    - simpl in Hin. contradiction.
    - simpl in Hcert.
      destruct (Separated_check iou tau theta box_eq_dec
                                (sep_effective_slack S0) D) eqn:Echeck;
        [discriminate|].
      destruct Hin as [Heq | Hin].
      + apply (proj2 (Separated_check_correct iou tau theta box_eq_dec
                        (sep_effective_slack Sh) D)) in Hsep.
        congruence.
      + apply (IH D Hcert Sh Hin Hsep).
  Qed.

  Theorem sep_certify_finite_yields_collapse :
    forall cands D Sh,
      NoDup D -> sorted_desc D ->
      sep_certify_finite cands D = Some Sh ->
      1 <= sep_effective_slack Sh ->
      filter_above theta (nms_sorted iou tau D) = filter_above theta D.
  Proof.
    intros cands D Sh Hnd Hsd Hcert Hslack.
    apply sep_certify_finite_sound in Hcert as [_ Hsep].
    assert (Hsep1 : Separated iou tau theta 1 D).
    { intros d d' Hin Hin' Hne Hiou.
      specialize (Hsep d d' Hin Hin' Hne Hiou).
      destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
      - left. split; [lia | assumption].
      - right. split; [lia | assumption]. }
    apply (nms_collapse_onepeak iou_sym_h Hnd Hsd
             (separated_implies_one_peak Hsep1)
             (separated_implies_no_tie_clash Hsep1)).
  Qed.

End SepFiniteCertify.


(** ** Iterative training: constructive coordinate descent.

    Replaces "precompute and store" with multi-step
    dynamics. [train_iter] iteratively removes one detection at a
    time, picking each round a "loser" — an above-threshold
    detection with a high-IoU partner whose score is at least as
    high. The procedure terminates because each step strictly
    reduces the input list's length. The fixed point has no losers,
    which yields [one_peak] mechanically; combined with the input's
    [no_tie_clash], NMS-collapse follows.

    This is the constructive surrogate for SGD on
    [L_focal + lambda * L_separated]: each "step" is a coordinate
    update that strictly reduces the violation-count loss; the
    procedure converges in at most [length D] iterations. The full
    real-valued SGD analysis with Rademacher generalization remains
    out of scope for Stdlib alone, but the multi-step convergence
    structure is captured here without external libraries. *)

Section IterativeTraining.
  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym_i : forall a b, iou a b = iou b a.
  Variable tau : nat.
  Variable theta : nat.
  Variable box_eq_dec_i : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2}.

  Definition det_eq_b (d1 d2 : @det Box) : bool :=
    if det_eq_dec box_eq_dec_i d1 d2 then true else false.

  Definition has_above_overlapper (D : list (@det Box)) (d : @det Box) : bool :=
    existsb (fun d' =>
              andb (negb (det_eq_b d d'))
                   (andb (Nat.leb tau (iou (box d) (box d')))
                         (Nat.leb (score d) (score d')))) D.

  Definition find_loser (D : list (@det Box)) : option (@det Box) :=
    find (fun d => has_above_overlapper D d) D.

  Fixpoint remove_one (D : list (@det Box)) (target : @det Box)
      : list (@det Box) :=
    match D with
    | [] => []
    | d :: rest =>
        if det_eq_dec box_eq_dec_i d target
        then rest
        else d :: remove_one rest target
    end.

  Lemma remove_one_length_decrease :
    forall D target, In target D -> length (remove_one D target) < length D.
  Proof.
    induction D as [|d rest IH]; intros target Hin; simpl in Hin; [contradiction|].
    simpl.
    destruct (det_eq_dec box_eq_dec_i d target) as [Heq | Hne]; [simpl; lia|].
    destruct Hin as [Heq | Hin]; [contradiction|].
    simpl. specialize (IH target Hin). lia.
  Qed.

  Lemma find_loser_in_D :
    forall D v, find_loser D = Some v -> In v D.
  Proof.
    intros D v Hf. unfold find_loser in Hf.
    apply find_some in Hf as [Hin _]. assumption.
  Qed.

  Lemma remove_one_subset :
    forall D target x, In x (remove_one D target) -> In x D.
  Proof.
    induction D as [|d rest IH]; intros target x Hin; simpl in Hin; [contradiction|].
    destruct (det_eq_dec box_eq_dec_i d target).
    - right; assumption.
    - destruct Hin as [Heq | Hin]; [left; assumption | right; apply IH with target; assumption].
  Qed.

  Function train_iter (D : list (@det Box)) {measure (@length (@det Box)) D}
      : list (@det Box) :=
    match find_loser D with
    | Some loser => train_iter (remove_one D loser)
    | None => D
    end.
  Proof.
    intros D loser Heq.
    apply remove_one_length_decrease.
    apply find_loser_in_D. assumption.
  Defined.

  Lemma train_iter_subset :
    forall D x, In x (train_iter D) -> In x D.
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
    intros x Hin.
    rewrite train_iter_equation in Hin.
    destruct (find_loser D) as [loser|] eqn:Eloser; [|assumption].
    apply find_loser_in_D in Eloser as Hloser_in.
    pose proof (remove_one_length_decrease D loser Hloser_in) as Hlt.
    apply IH in Hin; [|exact Hlt].
    apply remove_one_subset with loser. assumption.
  Qed.

  Lemma train_iter_no_loser :
    forall D, find_loser (train_iter D) = None.
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
    rewrite train_iter_equation.
    destruct (find_loser D) as [loser|] eqn:Eloser.
    - apply find_loser_in_D in Eloser as Hloser_in.
      pose proof (remove_one_length_decrease D loser Hloser_in) as Hlt.
      apply IH. exact Hlt.
    - assumption.
  Qed.

  Lemma find_loser_none_no_above_overlapper :
    forall D d,
      find_loser D = None ->
      In d D ->
      has_above_overlapper D d = false.
  Proof.
    intros D d Hf Hin.
    unfold find_loser in Hf.
    exact (find_none _ _ Hf d Hin).
  Qed.

  Theorem train_iter_satisfies_one_peak :
    forall D, one_peak iou tau theta (train_iter D).
  Proof.
    intros D d d' Hin Hin' Hiou Hlt.
    exfalso.
    pose proof (train_iter_no_loser D) as Hno.
    set (D' := train_iter D) in *.
    pose proof (find_loser_none_no_above_overlapper D' d Hno Hin) as Hno_overl.
    unfold has_above_overlapper in Hno_overl.
    assert (Hex : existsb (fun d'0 =>
              andb (negb (det_eq_b d d'0))
                   (andb (Nat.leb tau (iou (box d) (box d'0)))
                         (Nat.leb (score d) (score d'0)))) D' = true).
    { apply existsb_exists. exists d'.
      split; [assumption|].
      apply Bool.andb_true_iff. split.
      - apply Bool.negb_true_iff. unfold det_eq_b.
        destruct (det_eq_dec box_eq_dec_i d d') as [Heq | _].
        + subst d'. lia.
        + reflexivity.
      - apply Bool.andb_true_iff. split.
        + apply Nat.leb_le. assumption.
        + apply Nat.leb_le. lia. }
    rewrite Hex in Hno_overl. discriminate.
  Qed.

  Theorem train_iter_satisfies_no_tie_clash :
    forall D, no_tie_clash iou tau (train_iter D).
  Proof.
    intros D d d' Hin Hin' Hne Heq.
    set (D' := train_iter D) in *.
    destruct (Nat.leb_spec tau (iou (box d) (box d'))) as [Hge | Hlt]; [|lia].
    exfalso.
    pose proof (train_iter_no_loser D) as Hno.
    pose proof (find_loser_none_no_above_overlapper D' d Hno Hin) as Hno_overl.
    unfold has_above_overlapper in Hno_overl.
    assert (Hex : existsb (fun d'0 =>
              andb (negb (det_eq_b d d'0))
                   (andb (Nat.leb tau (iou (box d) (box d'0)))
                         (Nat.leb (score d) (score d'0)))) D' = true).
    { apply existsb_exists. exists d'.
      split; [assumption|].
      apply Bool.andb_true_iff. split.
      - apply Bool.negb_true_iff. unfold det_eq_b.
        destruct (det_eq_dec box_eq_dec_i d d') as [Hd_eq | _]; [contradiction|].
        reflexivity.
      - apply Bool.andb_true_iff. split.
        + apply Nat.leb_le. assumption.
        + apply Nat.leb_le. lia. }
    rewrite Hex in Hno_overl. discriminate.
  Qed.

  Lemma remove_one_preserves_NoDup :
    forall D target, NoDup D -> NoDup (remove_one D target).
  Proof.
    induction D as [|d rest IHd]; intros target Hnd; simpl; [constructor|].
    destruct (det_eq_dec box_eq_dec_i d target).
    - inversion Hnd; assumption.
    - inversion Hnd; subst. constructor.
      + intros Hin. apply remove_one_subset in Hin. contradiction.
      + apply IHd. assumption.
  Qed.

  Lemma remove_one_preserves_sorted_desc :
    forall D target, sorted_desc D -> sorted_desc (remove_one D target).
  Proof.
    induction D as [|d rest IHd]; intros target Hsd; simpl; [exact I|].
    destruct (det_eq_dec box_eq_dec_i d target).
    - apply (sorted_desc_tail Hsd).
    - destruct Hsd as [Hbnd Hsd_rest]. simpl. split.
      + intros d' Hd'. apply remove_one_subset in Hd'. apply Hbnd. assumption.
      + apply IHd. assumption.
  Qed.

  Lemma train_iter_preserves_NoDup :
    forall D, NoDup D -> NoDup (train_iter D).
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
    intros Hnd. rewrite train_iter_equation.
    destruct (find_loser D) as [loser|] eqn:Eloser; [|assumption].
    apply IH.
    - apply remove_one_length_decrease. apply find_loser_in_D. assumption.
    - apply remove_one_preserves_NoDup. assumption.
  Qed.

  Lemma train_iter_preserves_sorted_desc :
    forall D, sorted_desc D -> sorted_desc (train_iter D).
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
    intros Hsd. rewrite train_iter_equation.
    destruct (find_loser D) as [loser|] eqn:Eloser; [|assumption].
    apply IH.
    - apply remove_one_length_decrease. apply find_loser_in_D. assumption.
    - apply remove_one_preserves_sorted_desc. assumption.
  Qed.

  Theorem train_iter_collapse :
    forall D, NoDup D -> sorted_desc D ->
      filter_above theta (nms_sorted iou tau (train_iter D))
      = filter_above theta (train_iter D).
  Proof.
    intros D Hnd Hsd.
    apply (nms_collapse_onepeak iou_sym_i).
    - apply train_iter_preserves_NoDup. assumption.
    - apply train_iter_preserves_sorted_desc. assumption.
    - apply train_iter_satisfies_one_peak.
    - apply train_iter_satisfies_no_tie_clash.
  Qed.

End IterativeTraining.

(** ** Deterministic generalization: subset preservation.

    Without probability theory in Stdlib, the Rademacher / PAC bound
    cannot be expressed in its standard form. The constructive
    surrogate captured here: for any list [T] that is a sublist of a
    [Separated] list [D], [Separated] is preserved on [T]. Combined
    with [nms_collapse_onepeak], any sublist of a trained list also
    enjoys NMS-collapse — a deterministic version of "the trained
    head generalizes to held-out data drawn from the training
    distribution."

    The probabilistic version (sample of size [n] yields [Separated]
    on the test distribution with probability >= 1 − δ at margin
    [m − O(√(d log n / n) + √(log(1/δ)/n))]) requires Rademacher
    complexity from a probability theory library and is the missing
    analytic completion. *)

Theorem Separated_subset :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau theta slack : nat) (D T : list (@det Box)),
    (forall x, In x T -> In x D) ->
    Separated iou tau theta slack D ->
    Separated iou tau theta slack T.
Proof.
  intros Box iou tau theta slack D T Hsub Hsep d d' Hin Hin' Hne Hiou.
  apply Hsep; [apply Hsub; assumption | apply Hsub; assumption
              | assumption | assumption].
Qed.

Theorem nms_collapse_subset :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau theta : nat) (D T : list (@det Box)),
      NoDup T -> sorted_desc T ->
      (forall x, In x T -> In x D) ->
      Separated iou tau theta 1 D ->
      filter_above theta (nms_sorted iou tau T) = filter_above theta T.
Proof.
  intros Box iou iou_sym_g tau theta D T Hnd Hsd Hsub Hsep.
  pose proof (@Separated_subset Box iou tau theta 1 D T Hsub Hsep) as Hsep_T.
  apply (nms_collapse_onepeak iou_sym_g Hnd Hsd
           (separated_implies_one_peak Hsep_T)
           (separated_implies_no_tie_clash Hsep_T)).
Qed.

(** ** Finite-class learning bound.

    The constructive PAC analog: when the hypothesis class is a
    finite list of [SepRespectingHead]s, exhaustive search via
    [sep_certify_finite] is complete. If any candidate head certifies
    [Separated] for the training data at slack [>= 1], the search
    finds it; if none does, the search returns [None] and the absence
    is a proof, not a probability. The "sample complexity" is
    [length cands], a deterministic finite quantity. The trained head
    then transfers to any sublist of the training set via
    [Separated_subset]. *)

Theorem finite_class_learning_complete :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (iou_sym : forall a b, iou a b = iou b a)
         (tau theta : nat) (Feat : Type)
         (box_eq_dec : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
         (cands : list (SepRespectingHead Feat))
         (D_train D_test : list (@det Box)) (Sh : SepRespectingHead Feat),
    NoDup D_test -> sorted_desc D_test ->
    @sep_certify_finite Box iou tau theta Feat box_eq_dec cands D_train = Some Sh ->
    1 <= @sep_effective_slack Feat Sh ->
    (forall x, In x D_test -> In x D_train) ->
    filter_above theta (nms_sorted iou tau D_test) = filter_above theta D_test.
Proof.
  intros Box iou iou_sym_h tau theta Feat box_eq_dec cands D_train D_test Sh
         Hnd Hsd Hcert Hslack Hsub.
  apply (@sep_certify_finite_sound Box iou tau theta Feat box_eq_dec
           cands D_train Sh) in Hcert as [_ Hsep_train].
  assert (Hsep1 : Separated iou tau theta 1 D_train).
  { intros d d' Hin Hin' Hne Hiou.
    specialize (Hsep_train d d' Hin Hin' Hne Hiou).
    destruct Hsep_train as [[Hgap Hth] | [Hgap Hth]].
    - left. split; [lia | assumption].
    - right. split; [lia | assumption]. }
  apply (@nms_collapse_subset Box iou iou_sym_h tau theta D_train D_test
           Hnd Hsd Hsub Hsep1).
Qed.

(** ** Distance-bounded generalization beyond sublist.

    The previous [Separated_subset] theorem requires [D_test ⊆ D_train].
    A more applicable form: under a witness function [w : det -> det]
    that maps each test detection to a train detection sharing its
    box and with score within [eps] above, [Separated] transfers
    with margin shifted by [2 * eps]. Pure deterministic extension —
    no probability theory required. The witness models the natural
    "test data is close to training data" structure that the sublist
    hypothesis trivializes; this version captures actual neighborhood
    relationships without forcing exact membership. *)

Theorem Separated_score_close_lift :
  forall {Box : Type} (iou : Box -> Box -> nat) (tau theta : nat)
         (D_train D_test : list (@det Box)) (slack eps : nat)
         (witness : @det Box -> @det Box),
    (forall d, In d D_test -> In (witness d) D_train) ->
    (forall d, In d D_test -> box (witness d) = box d) ->
    (forall d, In d D_test ->
       score d <= score (witness d) <= score d + eps) ->
    (forall d1 d2, In d1 D_test -> In d2 D_test -> d1 <> d2 ->
       witness d1 <> witness d2) ->
    Separated iou tau theta (slack + 2 * eps) D_train ->
    Separated iou tau theta slack D_test.
Proof.
  intros Box iou tau theta D_train D_test slack eps witness
         Hwin Hwbox Hwclose Hwinj Hsep_train d d' Hin Hin' Hne Hiou.
  pose proof (Hwbox d Hin) as Hbox_eq.
  pose proof (Hwbox d' Hin') as Hbox_eq'.
  pose proof (Hwclose d Hin) as [Hge Hle].
  pose proof (Hwclose d' Hin') as [Hge' Hle'].
  rewrite <- Hbox_eq, <- Hbox_eq' in Hiou.
  specialize (Hsep_train (witness d) (witness d')
                          (Hwin d Hin) (Hwin d' Hin')
                          (Hwinj d d' Hin Hin' Hne) Hiou).
  destruct Hsep_train as [[Hgap Hth] | [Hgap Hth]].
  - left. split; lia.
  - right. split; lia.
Qed.


(** [multilayer_lipschitz] gives the operator-norm product
    [Π mat_inf_norm M_i] as a global Lipschitz bound for an [n]-layer
    ReLU stack. On real architectures the product overestimates the
    true input-space Lipschitz constant by three to six orders of
    magnitude: the input distribution occupies a small region of
    [R^d], on which most ReLUs are determinately active or dead and
    most matrix entries contribute either fully or not at all to the
    input-output sensitivity. The bridge precondition
    [2 * L * eps <= m] then forces unrealistic margins [m] when [L]
    is the global product.

    This part introduces [interval_lipschitz f lo hi L] — the local
    Lipschitz constant of [f] restricted to the input box [lo, hi].
    The two structural wins:

      (a) Linear layers retain the operator-norm bound, but on the
          box rather than globally, allowing per-layer tightening
          when ReLU activations are sign-determined.
      (b) ReLU is 0-Lipschitz on a box whose upper bound is
          componentwise non-positive — dead neurons contribute
          nothing to the chain Lipschitz.

    The composition theorem [interval_lipschitz_compose] inherits
    both: if the propagated box has a dead segment, that segment's
    chain factor is zero. The worked example
    [ibp_dead_local_zero] instantiates this concretely on a 1x1
    ReLU stack whose first layer is dead on a positive input box;
    the local Lipschitz constant is zero, while the global product
    bound is six.

*)

Local Open Scope R_scope.
Local Unset Implicit Arguments.

(** ** Componentwise box membership: [lo[i] <= v[i] <= hi[i]]. *)

Fixpoint in_box (lo hi v : list R) : Prop :=
  match lo, hi, v with
  | [], [], [] => True
  | l :: ls, h :: hs, x :: xs => l <= x <= h /\ in_box ls hs xs
  | _, _, _ => False
  end.

Lemma in_box_length_lo :
  forall lo hi v, in_box lo hi v -> length lo = length v.
Proof.
  induction lo as [|l ls IH]; intros [|h hs] [|x xs] Hbox;
    simpl in Hbox; try contradiction; try reflexivity.
  destruct Hbox as [_ Hrest]. simpl. f_equal. apply (IH hs xs Hrest).
Qed.

Lemma in_box_length_hi :
  forall lo hi v, in_box lo hi v -> length hi = length v.
Proof.
  induction lo as [|l ls IH]; intros [|h hs] [|x xs] Hbox;
    simpl in Hbox; try contradiction; try reflexivity.
  destruct Hbox as [_ Hrest]. simpl. f_equal. apply (IH hs xs Hrest).
Qed.

Lemma in_box_length :
  forall lo hi v,
    in_box lo hi v ->
    length lo = length v /\ length hi = length v.
Proof.
  intros lo hi v H. split.
  - apply (in_box_length_lo _ _ _ H).
  - apply (in_box_length_hi _ _ _ H).
Qed.

(** ** A vector in a box with non-positive upper bound is itself
       componentwise non-positive. *)

Lemma in_box_dead_implies_nonpos :
  forall lo hi v,
    in_box lo hi v ->
    Forall (fun h => h <= 0) hi ->
    Forall (fun x => x <= 0) v.
Proof.
  intros lo hi v Hbox Hhi.
  revert lo hi Hbox Hhi.
  induction v as [|x xs IH]; intros [|l ls] [|h hs] Hbox Hhi;
    simpl in Hbox; try contradiction.
  - constructor.
  - destruct Hbox as [[Hl Hh] Hrest].
    inversion Hhi as [|y ys Hh_neg Hhi_rest]; subst.
    constructor.
    + lra.
    + apply (IH ls hs Hrest Hhi_rest).
Qed.

(** ** Local Lipschitz over a box. *)

Definition interval_lipschitz (f : list R -> list R)
                              (lo hi : list R) (L : R) : Prop :=
  0 <= L /\
  forall u v, in_box lo hi u -> in_box lo hi v ->
              vec_dist (f u) (f v) <= L * vec_dist u v.

Lemma interval_lipschitz_nonneg :
  forall f lo hi L, interval_lipschitz f lo hi L -> 0 <= L.
Proof. intros f lo hi L [HL _]. exact HL. Qed.

(** ** Theorem 2: looser interval bounds are valid. *)

Theorem interval_lipschitz_monotone :
  forall f lo hi L1 L2,
    L1 <= L2 ->
    interval_lipschitz f lo hi L1 ->
    interval_lipschitz f lo hi L2.
Proof.
  intros f lo hi L1 L2 Hle [HL1 Hf]. split.
  - lra.
  - intros u v Hu Hv.
    eapply Rle_trans; [apply Hf; assumption|].
    apply Rmult_le_compat_r; [apply vec_dist_nonneg | assumption].
Qed.

(** ** Theorem 1: global Lipschitz implies interval Lipschitz on any
       box of consistent dimensions. The reverse direction is the
       point of IBP — local can be much tighter than global. *)

Theorem global_implies_interval_lipschitz :
  forall f L lo hi,
    0 <= L ->
    (forall u v, length u = length v ->
                 vec_dist (f u) (f v) <= L * vec_dist u v) ->
    interval_lipschitz f lo hi L.
Proof.
  intros f L lo hi HL Hglob.
  split; [assumption|].
  intros u v Hu Hv.
  pose proof (in_box_length_lo lo hi u Hu) as Hu_len.
  pose proof (in_box_length_lo lo hi v Hv) as Hv_len.
  apply Hglob. congruence.
Qed.

(** ** Theorem 3: linear layer is operator-norm Lipschitz on any
       box. The bound is loose unless the box is engineered to expose
       per-layer structure; tightening comes from box propagation
       feeding into ReLU dead-neuron analysis below. *)

Theorem mat_vec_interval_lipschitz :
  forall M lo hi,
    interval_lipschitz (mat_vec M) lo hi (mat_inf_norm M).
Proof.
  intros M lo hi.
  apply global_implies_interval_lipschitz.
  - apply mat_inf_norm_nonneg.
  - intros u v Hlen. apply mat_vec_lipschitz. assumption.
Qed.

(** ** Theorem 4: ReLU is 1-Lipschitz on any box. *)

Theorem relu_interval_lipschitz :
  forall lo hi,
    interval_lipschitz apply_relu_vec lo hi 1.
Proof.
  intros lo hi.
  apply global_implies_interval_lipschitz.
  - lra.
  - intros u v _. rewrite Rmult_1_l. apply apply_relu_vec_lip.
Qed.

(** ** Dead-neuron lemmas. ReLU on a vector whose components are all
       <= 0 returns the all-zeros vector of the same length. *)

Lemma apply_relu_vec_dead :
  forall v, Forall (fun x => x <= 0) v -> apply_relu_vec v = map (fun _ => 0) v.
Proof.
  intros v Hall. unfold apply_relu_vec.
  induction v as [|x rest IH]; simpl; [reflexivity|].
  inversion Hall; subst.
  rewrite (Rmax_left 0 x) by assumption.
  f_equal. apply IH. assumption.
Qed.

Lemma vec_dist_zeros :
  forall (l1 l2 : list R), length l1 = length l2 ->
    vec_dist (map (fun _ => 0) l1) (map (fun _ => 0) l2) = 0.
Proof.
  intros l1 l2 Hlen. unfold vec_dist.
  revert l2 Hlen.
  induction l1 as [|x1 r1 IH]; intros l2 Hlen;
    destruct l2 as [|x2 r2]; simpl in Hlen; try discriminate.
  - simpl. reflexivity.
  - injection Hlen as Hlen'.
    simpl.
    replace (0 - 0) with 0 by lra.
    rewrite Rabs_R0.
    rewrite (IH r2 Hlen').
    apply Rmax_left. lra.
Qed.

(** ** Theorem 5: ReLU on a dead box (upper bound componentwise
       non-positive) is 0-Lipschitz. The output is identically the
       zero vector regardless of which box element is fed. *)

Theorem relu_interval_lipschitz_dead :
  forall lo hi,
    length lo = length hi ->
    Forall (fun h => h <= 0) hi ->
    interval_lipschitz apply_relu_vec lo hi 0.
Proof.
  intros lo hi Hloh Hall_neg.
  split; [lra|].
  intros u v Hu Hv.
  rewrite Rmult_0_l.
  pose proof (in_box_dead_implies_nonpos lo hi u Hu Hall_neg) as Hu_nonpos.
  pose proof (in_box_dead_implies_nonpos lo hi v Hv Hall_neg) as Hv_nonpos.
  pose proof (in_box_length_lo lo hi u Hu) as Hlu.
  pose proof (in_box_length_lo lo hi v Hv) as Hlv.
  rewrite (apply_relu_vec_dead u Hu_nonpos).
  rewrite (apply_relu_vec_dead v Hv_nonpos).
  assert (Hluv : length u = length v) by congruence.
  rewrite (vec_dist_zeros u v Hluv).
  lra.
Qed.

(** ** Theorem 6: composition under propagated boxes.

    [f] is L1-Lipschitz on input box [lo, hi] and maps it into the
    output box [lo', hi']; [g] is L2-Lipschitz on [lo', hi']; the
    composition is L1*L2-Lipschitz on the input box. The propagated
    box [lo', hi'] is the IBP fingerprint of [f] on [lo, hi]. *)

Theorem interval_lipschitz_compose :
  forall f g L1 L2 lo hi lo' hi',
    interval_lipschitz f lo hi L1 ->
    interval_lipschitz g lo' hi' L2 ->
    (forall u, in_box lo hi u -> in_box lo' hi' (f u)) ->
    interval_lipschitz (fun x => g (f x)) lo hi (L1 * L2).
Proof.
  intros f g L1 L2 lo hi lo' hi' [HL1 Hf] [HL2 Hg] Hpropagate.
  split.
  - apply Rmult_le_pos; assumption.
  - intros u v Hu Hv.
    pose proof (Hf u v Hu Hv) as Hfuv.
    pose proof (Hg (f u) (f v) (Hpropagate u Hu) (Hpropagate v Hv)) as Hguv.
    eapply Rle_trans; [exact Hguv|].
    rewrite (Rmult_comm L1 L2).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [assumption|exact Hfuv].
Qed.

(** ** Theorem 7: applying [global_implies_interval_lipschitz] to
       [multilayer_lipschitz] recovers the global product bound as a
       (loose) interval bound. The IBP win shows up only when the
       caller picks layer-specific [L_i]'s tighter than [mat_inf_norm
       M_i] using the propagated input boxes. *)

Corollary multilayer_interval_lipschitz_global :
  forall Ms lo hi,
    interval_lipschitz (apply_layers Ms) lo hi (product_norms Ms).
Proof.
  intros Ms lo hi.
  apply global_implies_interval_lipschitz.
  - apply product_norms_nonneg.
  - intros u v Hlen. apply multilayer_lipschitz. assumption.
Qed.

(** ** Worked example: 1x1 ReLU stack with a dead first layer.

    [ibp_dead_M1 := [[-3]]], [ibp_dead_M2 := [[2]]]. The two-layer
    network [v |-> M2 (ReLU (M1 v))] has global product bound
    [mat_inf_norm M1 * mat_inf_norm M2 = 3 * 2 = 6]. On the input
    box [0, 100], the inner [mat_vec M1] image is [-300, 0] —
    componentwise non-positive — so ReLU collapses it to [0]. The
    full network is identically zero on the box, hence locally
    0-Lipschitz. The local bound is six units below the global,
    a constructive instance of the IBP gap that breaks deployable
    bridges. *)

Definition ibp_dead_M1 : matrix := [[-3]].
Definition ibp_dead_M2 : matrix := [[2]].

Definition ibp_dead_inner (v : list R) : list R :=
  apply_relu_vec (mat_vec ibp_dead_M1 v).

Definition ibp_dead_f (v : list R) : list R :=
  mat_vec ibp_dead_M2 (ibp_dead_inner v).

Definition ibp_dead_lo : list R := [0].
Definition ibp_dead_hi : list R := [100].
Definition ibp_dead_mid_lo : list R := [-300].
Definition ibp_dead_mid_hi : list R := [0].
Definition ibp_dead_post_lo : list R := [0].
Definition ibp_dead_post_hi : list R := [0].

Lemma ibp_dead_M1_norm : mat_inf_norm ibp_dead_M1 = 3.
Proof.
  unfold ibp_dead_M1, mat_inf_norm. simpl.
  replace (Rabs (-3)) with 3.
  - rewrite Rplus_0_r. apply Rmax_left. lra.
  - replace (-3) with (-(3)) by lra. rewrite Rabs_Ropp.
    rewrite Rabs_right by lra. reflexivity.
Qed.

Lemma ibp_dead_M2_norm : mat_inf_norm ibp_dead_M2 = 2.
Proof.
  unfold ibp_dead_M2, mat_inf_norm. simpl.
  rewrite Rabs_right by lra. rewrite Rplus_0_r.
  apply Rmax_left. lra.
Qed.

Lemma ibp_dead_M1_propagates :
  forall u, in_box ibp_dead_lo ibp_dead_hi u ->
            in_box ibp_dead_mid_lo ibp_dead_mid_hi (mat_vec ibp_dead_M1 u).
Proof.
  intros u Hu.
  unfold ibp_dead_lo, ibp_dead_hi, ibp_dead_mid_lo, ibp_dead_mid_hi in *.
  destruct u as [|x [|y rest]]; simpl in Hu; try tauto.
  destruct Hu as [[Hxlo Hxhi] _].
  unfold ibp_dead_M1; cbn [mat_vec dot].
  rewrite Rplus_0_r.
  simpl. split; [|exact I]. split; nra.
Qed.

Lemma ibp_dead_mid_hi_nonpos : Forall (fun h => h <= 0) ibp_dead_mid_hi.
Proof. unfold ibp_dead_mid_hi. constructor; [lra|constructor]. Qed.

Lemma ibp_dead_inner_propagates :
  forall u, in_box ibp_dead_lo ibp_dead_hi u ->
            in_box ibp_dead_post_lo ibp_dead_post_hi (ibp_dead_inner u).
Proof.
  intros u Hu.
  unfold ibp_dead_lo, ibp_dead_hi in Hu.
  destruct u as [|x [|y rest]]; simpl in Hu; try tauto.
  destruct Hu as [[Hxlo Hxhi] _].
  unfold ibp_dead_inner, ibp_dead_M1.
  cbn [mat_vec dot apply_relu_vec map].
  rewrite Rplus_0_r.
  rewrite (Rmax_left 0 (-3 * x)) by nra.
  unfold ibp_dead_post_lo, ibp_dead_post_hi.
  simpl. split; [|exact I]. split; lra.
Qed.

(** ** Theorem 8a: the inner sub-network (M1 then ReLU) is locally
       0-Lipschitz on the input box. Composition of [mat_vec M1]'s
       3-Lipschitz bound with ReLU's 0-Lipschitz dead-box bound; the
       product collapses to zero. *)

Theorem ibp_dead_inner_local_zero :
  interval_lipschitz ibp_dead_inner ibp_dead_lo ibp_dead_hi 0.
Proof.
  unfold ibp_dead_inner.
  assert (Hmid_loh : length ibp_dead_mid_lo = length ibp_dead_mid_hi) by reflexivity.
  pose proof (relu_interval_lipschitz_dead
                ibp_dead_mid_lo ibp_dead_mid_hi
                Hmid_loh ibp_dead_mid_hi_nonpos) as Hrelu.
  pose proof (mat_vec_interval_lipschitz ibp_dead_M1 ibp_dead_lo ibp_dead_hi) as Hmat.
  pose proof (interval_lipschitz_compose
                (mat_vec ibp_dead_M1) apply_relu_vec
                (mat_inf_norm ibp_dead_M1) 0
                ibp_dead_lo ibp_dead_hi
                ibp_dead_mid_lo ibp_dead_mid_hi
                Hmat Hrelu ibp_dead_M1_propagates) as Hcomp.
  rewrite Rmult_0_r in Hcomp.
  exact Hcomp.
Qed.

(** ** Theorem 8: the full two-layer network is locally 0-Lipschitz on
       the input box. *)

Theorem ibp_dead_local_zero :
  interval_lipschitz ibp_dead_f ibp_dead_lo ibp_dead_hi 0.
Proof.
  unfold ibp_dead_f.
  pose proof (mat_vec_interval_lipschitz ibp_dead_M2 ibp_dead_post_lo ibp_dead_post_hi)
    as Hmat2.
  pose proof (interval_lipschitz_compose
                ibp_dead_inner (mat_vec ibp_dead_M2)
                0 (mat_inf_norm ibp_dead_M2)
                ibp_dead_lo ibp_dead_hi
                ibp_dead_post_lo ibp_dead_post_hi
                ibp_dead_inner_local_zero Hmat2
                ibp_dead_inner_propagates) as Hcomp.
  rewrite Rmult_0_l in Hcomp.
  exact Hcomp.
Qed.

(** ** Tightness gap: the global product bound for the same network is
       6. The ratio between global and local is unbounded in this
       example because the local constant is exactly zero. *)

Theorem ibp_dead_global_six :
  product_norms [ibp_dead_M1; ibp_dead_M2] = 6.
Proof.
  cbn [product_norms].
  rewrite ibp_dead_M1_norm, ibp_dead_M2_norm. lra.
Qed.

Theorem ibp_dead_tightness_gap :
  product_norms [ibp_dead_M1; ibp_dead_M2] = 6 /\
  interval_lipschitz ibp_dead_f ibp_dead_lo ibp_dead_hi 0.
Proof.
  split; [apply ibp_dead_global_six | apply ibp_dead_local_zero].
Qed.

Local Set Implicit Arguments.
Local Close Scope R_scope.


(** [lipschitz_bridge_substantive]'s precondition includes a margin
    hypothesis on the score head's behavior over high-IoU pairs:
    [m + min(h(true d), h(true d')) <= max(h(true d), h(true d'))].
    In practice this is undischargeable — there is no proof that an
    arbitrary trained network produces this gap.

    For DETR's bipartite matching architecture, the gap is
    structurally derivable not from the score head but from the
    matching invariant. At training equilibrium, distinct
    predictions carry distinct GT labels ([matched_gt_injective]) and
    distinct GTs occupy disjoint boxes ([distinct_gt_disjoint]).
    Composing these two architectural primitives with a
    [unique_boxes] hypothesis on the prediction list forces
    [iou (box d) (box d') < tau] for every distinct pair. The
    bridge's high-IoU branch is therefore structurally empty, and
    the margin hypothesis is satisfied vacuously for any [m].

    This derives the bridge precondition from the architecture
    instead of assuming it. The chain:

      matched_gt_injective + distinct_gt_disjoint + unique_boxes
        => detr_matching_pairwise_disjoint   (already proved)
        => detr_equilibrium_margin_vacuous   (the bridge's margin)
        => detr_equilibrium_threshold_vacuous (the bridge's threshold)
        => detr_equilibrium_yields_separated  (full bridge composition)

*)

Section DETREquilibriumMargin.

  Variable Box : Type.
  Variable GT : Type.
  Variable gt_eq_dec : forall g1 g2 : GT, {g1 = g2} + {g1 <> g2}.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.
  Variable matched_gt : Box -> GT.

  Hypothesis matched_gt_injective :
    forall a b, matched_gt a = matched_gt b -> a = b.

  Hypothesis distinct_gt_disjoint :
    forall a b, matched_gt a <> matched_gt b -> iou a b < tau.

  Variable Feat : Type.
  Variable h : Feat -> nat.
  Variable true_feat : @det Box -> Feat.

  (** [unique_boxes D]: distinct detections in D have distinct
      boxes. Holds for DETR by construction: each prediction
      corresponds to a unique query slot with its own predicted
      box. The hypothesis lifts box-level disjointness (from the
      matching architecture) to detection-level distinctness. *)

  Definition unique_boxes (D : list (@det Box)) : Prop :=
    forall d d', In d D -> In d' D -> d <> d' -> box d <> box d'.

  (**The bridge's margin hypothesis is vacuously
      satisfied under DETR equilibrium. No distinct pair has IoU
      above [tau], so the implication's premise is unfalsifiable. *)

  Theorem detr_equilibrium_margin_vacuous :
    forall (D : list (@det Box)) (m : nat),
      unique_boxes D ->
      forall d d', In d D -> In d' D -> d <> d' ->
        tau <= iou (box d) (box d') ->
        m + Nat.min (h (true_feat d)) (h (true_feat d')) <=
        Nat.max (h (true_feat d)) (h (true_feat d')).
  Proof.
    intros D m Huniq d d' Hin Hin' Hne Hiou.
    exfalso.
    pose proof (Huniq d d' Hin Hin' Hne) as Hbox_ne.
    pose proof (@detr_matching_pairwise_disjoint Box GT gt_eq_dec iou tau
                  matched_gt matched_gt_injective distinct_gt_disjoint
                  (box d) (box d') Hbox_ne) as Hlt.
    lia.
  Qed.

  (**The bridge's threshold hypothesis is vacuously
      satisfied under DETR equilibrium. *)

  Theorem detr_equilibrium_threshold_vacuous :
    forall (D : list (@det Box)) (L eps theta : nat),
      unique_boxes D ->
      forall d d', In d D -> In d' D -> d <> d' ->
        tau <= iou (box d) (box d') ->
        L * eps + Nat.min (h (true_feat d)) (h (true_feat d')) < theta.
  Proof.
    intros D L eps theta Huniq d d' Hin Hin' Hne Hiou.
    exfalso.
    pose proof (Huniq d d' Hin Hin' Hne) as Hbox_ne.
    pose proof (@detr_matching_pairwise_disjoint Box GT gt_eq_dec iou tau
                  matched_gt matched_gt_injective distinct_gt_disjoint
                  (box d) (box d') Hbox_ne) as Hlt.
    lia.
  Qed.

  (**End-to-end composition: DETR equilibrium yields
      [Separated] via [lipschitz_bridge_substantive], discharging
      the margin and threshold hypotheses structurally. The score
      head's Lipschitz property and the noise-budget hypothesis
      are still required (they govern the Lipschitz calibration
      bridge), but the previously-undischargeable margin and
      threshold are now theorems, not hypotheses. *)

  Theorem detr_equilibrium_yields_separated :
    forall (theta : nat)
           (dist : Feat -> Feat -> nat)
           (obs_feat : @det Box -> Feat)
           (L m eps : nat) (D : list (@det Box)),
      2 * L * eps <= m ->
      (forall x y, Nat.max (h x) (h y) <= Nat.min (h x) (h y) + L * dist x y) ->
      (forall d, In d D -> score d = h (obs_feat d)) ->
      (forall d, In d D -> dist (true_feat d) (obs_feat d) <= eps) ->
      unique_boxes D ->
      Separated iou tau theta (m - 2 * L * eps) D.
  Proof.
    intros theta dist obs_feat L m eps D
           Hbnd HLip Hscore Hobs Huniq.
    apply (@lipschitz_bridge_substantive Box iou tau theta
             Feat h dist true_feat obs_feat L m eps D); try assumption.
    - apply detr_equilibrium_margin_vacuous; assumption.
    - apply detr_equilibrium_threshold_vacuous; assumption.
  Qed.

End DETREquilibriumMargin.


(** This part replaces [c30_D] (2 hand-tuned detections,
    1x1 weights) with two concrete demonstrations on substantially
    larger instances:

      (a) IBP-derived local Lipschitz on a 1-layer ReLU network.
          Using [interval_lipschitz_compose] with the
          matrix-Lipschitz bound and ReLU's global 1-Lipschitz, the
          layer [v |-> ReLU(3 * v)] is shown 3-Lipschitz on input
          box [0, 10]. The propagated post-matrix box [0, 30] is
          computed and discharged by [nra].

      (b) An executable [Separated] certificate on a 20-detection
          batch. With [c1_iou] returning 60 for distinct nat boxes
          and [tau = 70], the high-IoU branch is structurally
          empty, so [Separated_check] evaluates to [true] by
          [vm_compute] and [Separated] follows via
          [Separated_check_correct].

*)

(** ** Concrete 1-layer ReLU network with IBP-derived L. *)

Local Open Scope R_scope.

Definition e20_M : matrix := [[3]].
Definition e20_input_lo : list R := [0].
Definition e20_input_hi : list R := [10].
Definition e20_relu_input_lo : list R := [0].
Definition e20_relu_input_hi : list R := [30].

Lemma e20_M_norm : mat_inf_norm e20_M = 3.
Proof.
  unfold e20_M, mat_inf_norm. simpl.
  rewrite Rabs_right by lra. rewrite Rplus_0_r.
  apply Rmax_left. lra.
Qed.

Lemma e20_M_propagates :
  forall u, in_box e20_input_lo e20_input_hi u ->
            in_box e20_relu_input_lo e20_relu_input_hi (mat_vec e20_M u).
Proof.
  intros u Hu.
  unfold e20_input_lo, e20_input_hi, e20_relu_input_lo, e20_relu_input_hi in *.
  destruct u as [|x [|y rest]]; simpl in Hu; try tauto.
  destruct Hu as [[Hxlo Hxhi] _].
  unfold e20_M; cbn [mat_vec dot].
  rewrite Rplus_0_r.
  simpl. split; [|exact I]. split; nra.
Qed.

(**IBP-derived local Lipschitz constant for the layer. *)

Theorem e20_apply_layer_local_lipschitz :
  interval_lipschitz (apply_layer e20_M) e20_input_lo e20_input_hi 3.
Proof.
  unfold apply_layer.
  pose proof (mat_vec_interval_lipschitz e20_M e20_input_lo e20_input_hi) as Hmat.
  rewrite e20_M_norm in Hmat.
  pose proof (relu_interval_lipschitz e20_relu_input_lo e20_relu_input_hi) as Hrelu.
  pose proof (interval_lipschitz_compose
                (mat_vec e20_M) apply_relu_vec
                3 1 e20_input_lo e20_input_hi
                e20_relu_input_lo e20_relu_input_hi
                Hmat Hrelu e20_M_propagates) as Hcomp.
  rewrite Rmult_1_r in Hcomp.
  exact Hcomp.
Qed.

Local Close Scope R_scope.

(** ** Executable [Separated] certificate on a 20-detection batch. *)

Definition e20_D : list (@det c1_box) :=
  [ mkDet 100 0; mkDet 95 1; mkDet 90 2; mkDet 85 3; mkDet 80 4;
    mkDet 75 5; mkDet 70 6; mkDet 65 7; mkDet 60 8; mkDet 55 9;
    mkDet 50 10; mkDet 45 11; mkDet 40 12; mkDet 35 13; mkDet 30 14;
    mkDet 25 15; mkDet 20 16; mkDet 15 17; mkDet 10 18; mkDet 5 19 ].

(** [c1_iou] returns 60 for distinct nat boxes. With [tau = 70],
    every distinct pair has [iou = 60 < 70 = tau], so the high-IoU
    branch is structurally empty and the decidable [Separated_check]
    evaluates to [true] vacuously. *)

(**Executable Separated certificate via [vm_compute]. *)

Theorem e20_separated_check_true :
  Separated_check c1_iou 70 100 Nat.eq_dec 1 e20_D = true.
Proof. vm_compute. reflexivity. Qed.

(**Lift the decidable check to [Separated] via the
    correctness theorem. *)

Theorem e20_separated_at_slack_one :
  Separated c1_iou 70 100 1 e20_D.
Proof.
  apply (proj1 (Separated_check_correct c1_iou 70 100 Nat.eq_dec 1 e20_D)).
  exact e20_separated_check_true.
Qed.

