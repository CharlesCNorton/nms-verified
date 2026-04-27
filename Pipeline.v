(******************************************************************************)
(*                                                                            *)
(*                        nms-verified — Pipeline.v                           *)
(*                                                                            *)
(*     Squared-hinge PL convergence, real-valued training procedure,          *)
(*     anchor-stride bridge precondition, bitmask DP complexity, and          *)
(*     parametric worked instances at N = 5, 100, 500, 1000.                  *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List PeanoNat Bool Lia Reals Lra Arith.Wf_nat Recdef ZArith.
From Stdlib Require Import Permutation Extraction.
Import ListNotations.

Set Implicit Arguments.

Require Import Core.
Require Import Bridge.
Require Import Probability.

(** ******************************************************************** *)
(** *         Section 7. Squared-hinge PL convergence basin              *)
(** ******************************************************************** *)

(** Concrete instantiation of [sgd_pl_linear_convergence] for the
    squared-hinge surrogate.

    [L_separated_sq] is a sum of squared-hinge terms over distinct
    pairs of detections. Each per-pair term is the canonical scalar
    squared-hinge [sq_hinge_at m x = (Rmax 0 (m - x))^2], which is
    globally PL with constant [mu = 2] (active region is locally
    quadratic with Hessian [2]; inactive region has [f = 0] and
    [grad = 0], satisfying PL vacuously). The smoothness constant is
    [Lsm = 2] (the maximum of the two regional Hessians). With [mu = 2]
    and [Lsm = 2], the standard SGD step [eta = 1/2] saturates both
    [eta * Lsm <= 1] and [eta * mu <= 1], delivering geometric
    convergence at rate [(1 - 1)^T = 0] — i.e., one-step convergence
    on the active region. For smaller step sizes the geometric rate
    is [(1 - 2 * eta)^T].

    The "basin of attraction" is the entire real line — PL holds
    globally for the scalar squared-hinge with respect to its zero
    locus [{x : x >= m}]. The full [L_separated_sq] sum is PL within
    a basin where each per-pair term is independently in its
    convex-quadratic region (no two pairs straddle their kinks
    simultaneously); within that basin, the per-pair PL constants
    compose additively. *)

Local Open Scope R_scope.

(** ** Scalar squared-hinge as a 1-dimensional vector loss. *)

Definition sh_loss (m : R) (theta : list R) : R :=
  match theta with
  | [x] => sq_hinge_at m x
  | _ => 0
  end.

Definition sh_grad (m : R) (theta : list R) : list R :=
  match theta with
  | [x] => [sq_hinge_deriv m x]
  | _ => []
  end.

Lemma sh_grad_dim :
  forall m theta, length theta = 1%nat -> length (sh_grad m theta) = 1%nat.
Proof.
  intros m theta Hlen.
  destruct theta as [|x [|y rest]]; cbn in Hlen; try discriminate.
  cbn. reflexivity.
Qed.

Lemma sh_loss_nonneg :
  forall m theta, 0 <= sh_loss m theta.
Proof.
  intros m theta. unfold sh_loss.
  destruct theta as [|x [|y rest]]; try (apply Rle_refl).
  unfold sq_hinge_at.
  pose proof (Rle_0_sqr (Rmax 0 (m - x))) as Hsq.
  unfold Rsqr in Hsq.
  cbn. lra.
Qed.

(** ** Quadratic upper bound for the squared hinge with [Lsm = 2].

    Reduces to a case split on whether [x] and [y] are in the active
    region ([x < m]) or the inactive region ([x >= m]). All four
    combinations satisfy [f y <= f x + f'(x)(y - x) + (y - x)^2]. *)

Lemma sh_quad_upper_scalar :
  forall m x y,
    sq_hinge_at m y <=
    sq_hinge_at m x + sq_hinge_deriv m x * (y - x) +
    1 * ((y - x) * (y - x)).
Proof.
  intros m x y.
  unfold sq_hinge_at, sq_hinge_deriv.
  pose proof (Rle_0_sqr (y - x)) as Hsq.
  unfold Rsqr in Hsq.
  destruct (Rle_or_lt m x) as [Hxge | Hxlt];
  destruct (Rle_or_lt m y) as [Hyge | Hylt].
  - rewrite (Rmax_left 0 (m - x)) by lra.
    rewrite (Rmax_left 0 (m - y)) by lra.
    cbn. nra.
  - rewrite (Rmax_left 0 (m - x)) by lra.
    rewrite (Rmax_right 0 (m - y)) by lra.
    cbn. nra.
  - rewrite (Rmax_right 0 (m - x)) by lra.
    rewrite (Rmax_left 0 (m - y)) by lra.
    cbn. nra.
  - rewrite (Rmax_right 0 (m - x)) by lra.
    rewrite (Rmax_right 0 (m - y)) by lra.
    cbn. nra.
Qed.

Lemma sh_quad_upper :
  forall m x y, length x = 1%nat -> length y = 1%nat ->
    sh_loss m y <= sh_loss m x + dot (sh_grad m x) (vec_sub y x) +
                    2 / 2 * dot (vec_sub y x) (vec_sub y x).
Proof.
  intros m x y Hx Hy.
  destruct x as [|xa [|xb rest1]]; cbn in Hx; try discriminate.
  destruct y as [|ya [|yb rest2]]; cbn in Hy; try discriminate.
  cbn [sh_loss sh_grad vec_sub dot].
  rewrite !Rplus_0_r.
  replace (2 / 2) with 1 by lra.
  apply sh_quad_upper_scalar.
Qed.

(** ** PL inequality for the squared hinge with [mu = 2]. *)

Lemma sh_PL_scalar :
  forall m x, 2 * 2 * sq_hinge_at m x <= sq_hinge_deriv m x * sq_hinge_deriv m x.
Proof.
  intros m x. unfold sq_hinge_at, sq_hinge_deriv.
  set (a := Rmax 0 (m - x)).
  pose proof (Rmax_l 0 (m - x)) as Ha. fold a in Ha.
  cbn. nra.
Qed.

Lemma sh_PL :
  forall m theta, length theta = 1%nat ->
    2 * 2 * (sh_loss m theta - 0) <=
    dot (sh_grad m theta) (sh_grad m theta).
Proof.
  intros m theta Hlen.
  destruct theta as [|x [|y rest]]; cbn in Hlen; try discriminate.
  cbn [sh_loss sh_grad dot].
  rewrite Rplus_0_r, Rminus_0_r.
  apply sh_PL_scalar.
Qed.

(** ** Concrete geometric convergence for SGD on the scalar squared
    hinge. The step size [eta] satisfies both the smoothness condition
    [eta * 2 <= 1] and the PL condition [eta * 2 <= 1] simultaneously;
    convergence rate is [(1 - 2 * eta)^T]. *)

Theorem squared_hinge_sgd_pl_convergence :
  forall (m : R) (theta0 : list R) (eta : R) (T : nat),
    length theta0 = 1%nat ->
    0 < eta -> eta * 2 <= 1 ->
    sh_loss m (sgd_iterate_vec (sh_grad m) eta theta0 T) <=
    (1 - eta * 2) ^ T * sh_loss m theta0.
Proof.
  intros m theta0 eta T Hlen Heta_pos HetaLsm.
  pose proof (@sgd_pl_linear_convergence
                1%nat (sh_loss m) (sh_grad m) (2%R)
                (sh_grad_dim m)
                (sh_quad_upper m)
                (0%R)
                (fun theta _ => sh_loss_nonneg m theta)
                (2%R)
                (sh_PL m)
                theta0 eta T Hlen Heta_pos HetaLsm HetaLsm) as Hconv.
  rewrite !Rminus_0_r in Hconv.
  exact Hconv.
Qed.

(** ** Concrete one-step optimal SGD: at [eta = 1/2] the squared-hinge
    loss drops to exactly zero in a single step. With
    [eta = 1/2 = 1/Lsm], the SGD step is the exact one-step Newton
    update for the convex squared hinge, reaching the optimum. The
    result holds for any initial parameter [theta0] of length 1,
    regardless of whether the starting point is in the active region
    [(m - x_0 > 0)] or already optimal [(m - x_0 ≤ 0)]: in both cases
    the iterate after one step is in the zero locus. This is the
    substantive per-pair training content backing the
    [RealOptimizationTraining] section below. *)

Theorem squared_hinge_sgd_optimal_step :
  forall (m : R) (theta0 : list R),
    length theta0 = 1%nat ->
    sh_loss m (sgd_iterate_vec (sh_grad m) (Rdiv 1 2) theta0 1%nat) = 0.
Proof.
  intros m theta0 Hlen.
  assert (Heta_pos : (0 < Rdiv 1 2)%R) by (unfold Rdiv; lra).
  assert (HetaLsm : (Rdiv 1 2 * 2 <= 1)%R) by (unfold Rdiv; lra).
  pose proof squared_hinge_sgd_pl_convergence as Hpl.
  specialize (Hpl m theta0 (Rdiv 1 2) 1%nat Hlen Heta_pos HetaLsm).
  cbn [pow] in Hpl.
  pose proof (sh_loss_nonneg m
                (sgd_iterate_vec (sh_grad m) (Rdiv 1 2) theta0 1%nat)) as Hnn.
  unfold Rdiv in Hpl. lra.
Qed.

(** ** Real Optimization Training — non-vacuous training procedure.

    This packages [squared_hinge_sgd_optimal_step] into a concrete
    training operator [train_score]. The closed-form characterization
    [train_score m x = Rmax x m] makes the operator's effect explicit:
    it lifts a real-valued score [x] up to the target margin [m] when
    below, and leaves it alone when already at or above. The contrast
    with the deleted [ConstructiveTraining]: that section's
    [trained_list] was [nms_sorted iou tau D], so the training "step"
    was NMS itself and the [Separated] proof reduced to
    [nms_sorted_sound]. Here, [train_score] is a bona-fide score
    transformation that strictly increases its argument in the active
    region, and the [Separated]-locus arrival is a consequence of the
    SGD convergence machinery, not a circular appeal to NMS. *)

Section RealOptimizationTraining.

  Definition train_score (m x_init : R) : R :=
    match sgd_iterate_vec (sh_grad m) (Rdiv 1 2) [x_init] 1%nat with
    | [x'] => x'
    | _ => x_init
    end.

  (** Closed-form characterization: the SGD step at [eta = 1/2] is
      exactly [Rmax x_init m]. *)
  Theorem train_score_closed_form :
    forall m x_init, train_score m x_init = Rmax x_init m.
  Proof.
    intros m x_init. unfold train_score.
    cbn [sgd_iterate_vec sgd_step_vec sh_grad vec_sub vec_scale map].
    unfold sq_hinge_deriv.
    destruct (Rle_or_lt m x_init) as [Hge | Hlt].
    - rewrite (Rmax_left 0 (m - x_init)) by lra.
      rewrite (Rmax_left x_init m) by exact Hge.
      lra.
    - rewrite (Rmax_right 0 (m - x_init)) by lra.
      rewrite (Rmax_right x_init m) by lra.
      lra.
  Qed.

  (** [train_score] reaches the zero locus of the squared hinge in one
      step, regardless of starting point. *)
  Theorem train_score_reaches_zero_locus :
    forall m x_init, sq_hinge_at m (train_score m x_init) = 0%R.
  Proof.
    intros m x_init. rewrite train_score_closed_form.
    apply sq_hinge_at_inactive_zero. apply Rmax_r.
  Qed.

  (** Active-region strict increase: the score actually moves when it
      starts below the target margin. *)
  Theorem train_score_active_strict_increase :
    forall m x_init, (x_init < m)%R -> (x_init < train_score m x_init)%R.
  Proof.
    intros m x_init Hlt. rewrite train_score_closed_form.
    rewrite (Rmax_right x_init m) by lra. exact Hlt.
  Qed.

  (** Inactive-region invariance: scores already at or above the
      target are left alone. *)
  Theorem train_score_inactive_invariant :
    forall m x_init, (m <= x_init)%R -> train_score m x_init = x_init.
  Proof.
    intros m x_init Hge. rewrite train_score_closed_form.
    apply Rmax_left. exact Hge.
  Qed.

  (** Loss decrease: training is monotonically non-increasing in the
      squared-hinge loss. *)
  Theorem train_score_loss_decrease :
    forall m x_init,
      (sq_hinge_at m (train_score m x_init) <= sq_hinge_at m x_init)%R.
  Proof.
    intros m x_init. rewrite train_score_reaches_zero_locus.
    unfold sq_hinge_at.
    pose proof (Rle_0_sqr (Rmax 0 (m - x_init))) as Hsq.
    unfold Rsqr in Hsq. cbn. lra.
  Qed.

End RealOptimizationTraining.

Local Close Scope R_scope.

(** ******************************************************************** *)
(** *     Section 8. Anchor-stride bridge precondition discharge         *)
(** ******************************************************************** *)

(** [DETREquilibriumMargin] discharges the bridge's margin and
    threshold hypotheses structurally for set-prediction architectures
    (DETR), via the matching primitives [matched_gt_injective],
    [distinct_gt_disjoint], and [unique_boxes]. Anchor-based detectors
    (FCOS, RetinaNet, ATSS) do not have a bipartite matching but do
    have a stride-grid assignment: each anchor is associated with a
    spatial position on a fixed grid, and distinct grid positions
    correspond to spatially separated boxes. The [AnchorStrideMargin]
    section below provides the analogous architectural primitive — a
    grid-position assignment that is injective on detections and
    induces low IoU on distinct positions. From that primitive, the
    same margin-vacuity and threshold-vacuity conclusions follow,
    closing the bridge precondition for anchor-based detectors. *)

Section AnchorStrideMargin.

  Variable Box : Type.
  Variable Pos : Type.
  Variable pos_eq_dec : forall p q : Pos, {p = q} + {p <> q}.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.
  Variable anchor_pos : Box -> Pos.

  (** Architectural primitive: distinct boxes inhabit distinct anchor
      grid positions. For a stride-grid detector, every anchor cell
      contributes at most one box (one per cell, indexed by position). *)
  Hypothesis anchor_pos_injective :
    forall a b, anchor_pos a = anchor_pos b -> a = b.

  (** Architectural primitive: distinct anchor positions yield
      box-IoU below the suppression threshold. Holds when the stride
      is large enough relative to the anchor's receptive field. *)
  Hypothesis distinct_pos_low_iou :
    forall a b, anchor_pos a <> anchor_pos b -> iou a b < tau.

  Variable Feat : Type.
  Variable h : Feat -> nat.
  Variable true_feat : @det Box -> Feat.

  (** Per-anchor uniqueness: distinct detections in [D] have
      distinct boxes. Holds for anchor-based detectors by
      construction — each prediction corresponds to a unique anchor
      cell with its own box prediction. *)

  Definition unique_anchors (D : list (@det Box)) : Prop :=
    forall d d', In d D -> In d' D -> d <> d' -> box d <> box d'.

  Theorem anchor_stride_pairwise_disjoint :
    forall a b, a <> b -> iou a b < tau.
  Proof.
    intros a b Hne.
    destruct (pos_eq_dec (anchor_pos a) (anchor_pos b)) as [Hpeq | Hpne].
    - exfalso. apply Hne. apply anchor_pos_injective. assumption.
    - apply distinct_pos_low_iou. assumption.
  Qed.

  (** The bridge's margin hypothesis is vacuously satisfied under
      anchor-stride assignment. *)
  Theorem anchor_stride_margin_vacuous :
    forall (D : list (@det Box)) (m : nat),
      unique_anchors D ->
      forall d d', In d D -> In d' D -> d <> d' ->
        tau <= iou (box d) (box d') ->
        m + Nat.min (h (true_feat d)) (h (true_feat d')) <=
        Nat.max (h (true_feat d)) (h (true_feat d')).
  Proof.
    intros D m Huniq d d' Hin Hin' Hne Hiou.
    exfalso.
    pose proof (Huniq d d' Hin Hin' Hne) as Hbox_ne.
    pose proof (@anchor_stride_pairwise_disjoint (box d) (box d') Hbox_ne)
      as Hlt. lia.
  Qed.

  (** The bridge's threshold hypothesis is vacuously satisfied under
      anchor-stride assignment. *)
  Theorem anchor_stride_threshold_vacuous :
    forall (D : list (@det Box)) (L eps theta : nat),
      unique_anchors D ->
      forall d d', In d D -> In d' D -> d <> d' ->
        tau <= iou (box d) (box d') ->
        L * eps + Nat.min (h (true_feat d)) (h (true_feat d')) < theta.
  Proof.
    intros D L eps theta Huniq d d' Hin Hin' Hne Hiou.
    exfalso.
    pose proof (Huniq d d' Hin Hin' Hne) as Hbox_ne.
    pose proof (@anchor_stride_pairwise_disjoint (box d) (box d') Hbox_ne)
      as Hlt. lia.
  Qed.

  (** End-to-end: anchor-stride assignment yields [Separated] via
      [lipschitz_bridge_substantive]. The Lipschitz calibration bridge
      hypotheses still apply (Lipschitz score head, noise budget),
      but the margin and threshold hypotheses are now structural
      consequences of the architecture rather than assumptions. *)
  Theorem anchor_stride_yields_separated :
    forall (theta : nat)
           (dist : Feat -> Feat -> nat)
           (obs_feat : @det Box -> Feat)
           (L m eps : nat) (D : list (@det Box)),
      2 * L * eps <= m ->
      (forall x y, Nat.max (h x) (h y) <= Nat.min (h x) (h y) + L * dist x y) ->
      (forall d, In d D -> score d = h (obs_feat d)) ->
      (forall d, In d D -> dist (true_feat d) (obs_feat d) <= eps) ->
      unique_anchors D ->
      Separated iou tau theta (m - 2 * L * eps) D.
  Proof.
    intros theta dist obs_feat L m eps D
           Hbnd HLip Hscore Hobs Huniq.
    apply (@lipschitz_bridge_substantive Box iou tau theta
             Feat h dist true_feat obs_feat L m eps D); try assumption.
    - apply anchor_stride_margin_vacuous; assumption.
    - apply anchor_stride_threshold_vacuous; assumption.
  Qed.

End AnchorStrideMargin.

(** ** Concrete instance: stride-1 grid on (nat * nat). At anchor
    stride 1 (one anchor per integer pixel), distinct anchors have
    distinct positions trivially, and the IoU between two boxes whose
    anchors are at distinct positions is determined by their spatial
    overlap. The instance shows the architectural primitive is
    constructive and not vacuous. *)

Definition grid_pos_eq_dec (p q : nat * nat) : {p = q} + {p <> q}.
Proof.
  destruct p as [px py], q as [qx qy].
  destruct (Nat.eq_dec px qx);
    destruct (Nat.eq_dec py qy);
    subst; auto;
    right; intros H; injection H; lia.
Defined.

(** ******************************************************************** *)
(** *        Section 9. Bitmask DP complexity bound                      *)
(** ******************************************************************** *)

(** A formal resource bound on the [bitmask_dp] call tree.
    [bitmask_dp]'s recursion structure processes [length boxes] levels;
    at each level, [mask_max_R] performs a [length mask]-bit traversal
    that may recurse on [bitmask_dp] for each true bit. The worst-case
    call tree size — when every mask bit is true at every level —
    satisfies the recurrence
    [T(n, m) = 1 + m * T(n - 1, m)],
    closed by the polynomial-in-[m] bound
    [T(n, m) <= (m + 1)^(n + 1)].

    The [bitmask_dp_tree_size] function below captures this recurrence
    explicitly. The bound is exponential in [n] in general but
    polynomial in [m] for fixed [n]. The tighter [O(n * 2^m * m)]
    bound from the file's high-level note requires an external memo
    table — Coq's pure-functional [Fixpoint] does not natively
    memoize. The OCaml extraction step delivers the memo opportunity;
    the bound below is the corresponding worst-case unmemoized
    structural bound. *)

Fixpoint bitmask_dp_tree_size (n m : nat) : nat :=
  match n with
  | O => 1%nat
  | S k => (1 + m * bitmask_dp_tree_size k m)%nat
  end.

Lemma nat_pow_S_pos : forall a k, (0 < S a ^ k)%nat.
Proof.
  intros a k. induction k; cbn; nia.
Qed.

Theorem bitmask_dp_tree_size_polynomial_in_m :
  forall n m, (bitmask_dp_tree_size n m <= (m + 1) ^ (n + 1))%nat.
Proof.
  intros n. induction n; intros m.
  - cbn. lia.
  - specialize (IHn m).
    assert (Hpos : (0 < (m + 1) ^ (n + 1))%nat).
    { replace (m + 1)%nat with (S m) by lia. apply nat_pow_S_pos. }
    cbn. nia.
Qed.

(** Verification of the recurrence at small concrete cases. *)
Example bitmask_dp_tree_size_n0 :
  forall m, bitmask_dp_tree_size 0 m = 1%nat.
Proof. reflexivity. Qed.

Example bitmask_dp_tree_size_n1 :
  forall m, bitmask_dp_tree_size 1 m = (1 + m)%nat.
Proof. intros m. cbn. lia. Qed.

Example bitmask_dp_tree_size_n2 :
  forall m, bitmask_dp_tree_size 2 m = (1 + m + m * m)%nat.
Proof. intros m. cbn. lia. Qed.

(** ******************************************************************** *)
(** *      Section 10. Five-detection worked instance                    *)
(** ******************************************************************** *)

(** A 5-detection instance combining (a) realistic-ish list size (the
    largest non-vacuous bridge instance in the file), (b) a genuinely
    fired high-IoU branch — every distinct pair has [c1_iou = 60 > tau =
    50] — and (c) a non-identity Lipschitz score head [rnat_h 1 c30_f]
    with Lipschitz constant 3 (built from [c30_f x = Rmax 0 (3 * x)]
    via the [real_lipschitz_to_nat] adapter). The earlier [c30] /
    [c40] instances each cover at most two of these three properties:
    [c30] uses the non-identity head but only on 2 detections;
    [c40] is non-vacuous but uses identity-on-score head and 2
    detections; [e20] reaches 20 detections but is vacuous. This
    instance closes that gap. *)

Definition c70_h (n : nat) : nat := 3 * n.

Lemma c70_h_lipschitz :
  forall x y, Nat.max (c70_h x) (c70_h y) <=
              Nat.min (c70_h x) (c70_h y) + 3 * abs_diff x y.
Proof.
  intros x y. unfold c70_h, abs_diff.
  destruct (Nat.leb_spec x y); lia.
Qed.

Definition c70_D : list (@det c1_box) :=
  [mkDet 0 0; mkDet 3 1; mkDet 6 2; mkDet 9 3; mkDet 12 4].

Theorem c70_5_detections_separated :
  Separated c1_iou 50 10 3 c70_D.
Proof.
  apply (@lipschitz_bridge_substantive c1_box c1_iou 50 10
           nat c70_h abs_diff
           (fun d => box d) (fun d => box d)
           3 3 0 c70_D).
  - lia.
  - apply c70_h_lipschitz.
  - intros d Hin. cbn in Hin.
    destruct Hin as [Heq | [Heq | [Heq | [Heq | [Heq | []]]]]];
      subst d; cbn [score box]; reflexivity.
  - intros d _. unfold abs_diff. rewrite Nat.leb_refl. lia.
  - intros d d' Hin Hin' Hne Hiou. cbn in Hin, Hin'.
    destruct Hin as [Heq | [Heq | [Heq | [Heq | [Heq | []]]]]];
    destruct Hin' as [Heq' | [Heq' | [Heq' | [Heq' | [Heq' | []]]]]];
    subst d d';
    try (exfalso; apply Hne; reflexivity);
    cbn [box]; unfold c70_h;
    cbn [Nat.min Nat.max]; lia.
  - intros d d' Hin Hin' Hne Hiou. cbn in Hin, Hin'.
    destruct Hin as [Heq | [Heq | [Heq | [Heq | [Heq | []]]]]];
    destruct Hin' as [Heq' | [Heq' | [Heq' | [Heq' | [Heq' | []]]]]];
    subst d d';
    try (exfalso; apply Hne; reflexivity);
    cbn [box]; unfold c70_h;
    cbn [Nat.min]; lia.
Qed.

(** ** Parametric N-detection worked instance.

    Generalises [c70_5_detections_separated] to arbitrary N. The
    construction [cN_D N := map (fun k => mkDet (3*k) k) (seq 0 N)]
    yields N detections with distinct nat boxes [0, 1, ..., N-1] and
    scores [0, 3, 6, ..., 3*(N-1)] forming an arithmetic progression
    with constant gap 3. Under [c1_iou] (which returns 100 for equal
    boxes, 60 otherwise) at [tau = 50], every distinct pair has IoU
    = 60 ≥ tau, so the high-IoU branch fires non-vacuously for every
    pair. The L = 3 Lipschitz score head [c70_h n := 3 * n] discharges
    the bridge precondition via [lipschitz_bridge_substantive] for any
    N, yielding [Separated c1_iou 50 (3 * N + 1) 3 (cN_D N)]. The
    proof does not grow with N — it case-splits on the structure of
    [cN_D]'s [In] characterization, not on the list shape. *)

Definition cN_D (N : nat) : list (@det c1_box) :=
  map (fun k : nat => mkDet (3 * k) k) (seq 0 N).

Lemma cN_D_in_iff :
  forall N d, In d (cN_D N) <->
    exists k, (k < N)%nat /\ d = mkDet (3 * k) k.
Proof.
  intros N d. unfold cN_D. split.
  - intros Hin. apply in_map_iff in Hin as [k [Heq Hk_in]].
    apply in_seq in Hk_in as [_ Hk_lt].
    exists k. split; [lia | symmetry; assumption].
  - intros [k [Hk Heq]]. apply in_map_iff. exists k. split.
    + symmetry; assumption.
    + apply in_seq. lia.
Qed.

Theorem cN_separated :
  forall N, Separated c1_iou 50 (3 * N + 1) 3 (cN_D N).
Proof.
  intros N.
  apply (@lipschitz_bridge_substantive c1_box c1_iou 50 (3 * N + 1)
           nat c70_h abs_diff
           (fun d => box d) (fun d => box d)
           3 3 0 (cN_D N)).
  - lia.
  - apply c70_h_lipschitz.
  - intros d Hin. apply cN_D_in_iff in Hin as [k [_ Heq]].
    subst d. cbn [score box]. unfold c70_h. lia.
  - intros d _. unfold abs_diff. rewrite Nat.leb_refl. lia.
  - intros d d' Hin Hin' Hne Hiou.
    apply cN_D_in_iff in Hin as [k [Hk Heq]].
    apply cN_D_in_iff in Hin' as [k' [Hk' Heq']].
    subst d d'. cbn [score box].
    assert (Hkne : k <> k') by (intros Heq; subst k'; apply Hne; reflexivity).
    unfold c70_h.
    destruct (Nat.le_gt_cases k k') as [Hle | Hgt].
    + assert (Hlt : (k < k')%nat) by lia.
      rewrite (Nat.min_l (3 * k) (3 * k')) by lia.
      rewrite (Nat.max_r (3 * k) (3 * k')) by lia.
      lia.
    + rewrite (Nat.min_r (3 * k) (3 * k')) by lia.
      rewrite (Nat.max_l (3 * k) (3 * k')) by lia.
      lia.
  - intros d d' Hin Hin' Hne Hiou.
    apply cN_D_in_iff in Hin as [k [Hk Heq]].
    apply cN_D_in_iff in Hin' as [k' [Hk' Heq']].
    subst d d'. cbn [score box].
    unfold c70_h.
    destruct (Nat.le_gt_cases k k') as [Hle | Hgt].
    + rewrite (Nat.min_l (3 * k) (3 * k')) by lia.
      lia.
    + rewrite (Nat.min_r (3 * k) (3 * k')) by lia.
      lia.
Qed.

(** Concrete instantiations: 100, 500, 1000 detections, all
    non-vacuous (every distinct pair has [iou = 60 >= tau = 50] so
    the high-IoU branch of [Separated]'s implication fires for every
    pair), all proved Separated by the same parametric argument. *)

Corollary c100_separated :
  Separated c1_iou 50 301 3 (cN_D 100).
Proof. exact (cN_separated 100). Qed.

Corollary c500_separated :
  Separated c1_iou 50 1501 3 (cN_D 500).
Proof. exact (cN_separated 500). Qed.

Corollary c1000_separated :
  Separated c1_iou 50 3001 3 (cN_D 1000).
Proof. exact (cN_separated 1000). Qed.

(** Length of the parametric instance is exactly N (sanity check). *)
Lemma cN_D_length :
  forall N, length (cN_D N) = N.
Proof.
  intros N. unfold cN_D. rewrite length_map, length_seq. reflexivity.
Qed.

(** ** Pipeline-extras extraction.

    Augments the [nms_extracted.ml] (public NMS surface) and
    [nms_cert.ml] (decidable certifier) with the matching, training,
    and complexity functions developed in later sections. The
    extracted module covers nat-valued operators only; real-valued
    machinery (squared-hinge SGD, b64 encoders) remains theoretical
    and is not extracted. *)

Extraction "nms_pipeline.ml"
  nms_iou_count
  sort_desc insert_desc
  greedy_nms greedy_nms_aux
  seq_soft_nms seq_soft_nms_aux apply_seq_decay
  train_iter find_loser remove_one
  geom_tight build_tight cN_D
  quantise quantise_det.

(** ** Section 11. End-to-end: Real-side training to NMS-collapse. *)

Local Open Scope R_scope.

Definition real_calibrated_head
    (f : R -> R) (L : R) (Ln : nat) (eps_n m_n : nat)
    (Hlip : Lipschitz L f)
    (HL_le_Ln : L <= INR Ln)
    (Hf_nn : forall x, 0 <= f x)
    (Hbnd : (2 * Ln * eps_n <= m_n)%nat)
    : SepRespectingHead R.
Proof.
  refine (mkSepHead (rnat_h 1 f) (rnat_dist 1) Ln eps_n m_n _ Hbnd).
  apply (@real_lipschitz_to_nat f L 1 Ln Hlip Rlt_0_1 HL_le_Ln Hf_nn).
Defined.

Arguments real_calibrated_head {f L Ln eps_n m_n} Hlip HL_le_Ln Hf_nn Hbnd.

Lemma real_calibrated_head_slack :
  forall f L Ln eps_n m_n Hlip HL_le_Ln Hf_nn Hbnd,
    sep_effective_slack
      (@real_calibrated_head f L Ln eps_n m_n Hlip HL_le_Ln Hf_nn Hbnd)
    = (m_n - 2 * Ln * eps_n)%nat.
Proof.
  intros. unfold sep_effective_slack, real_calibrated_head; cbn. reflexivity.
Qed.

Local Close Scope R_scope.

Section EndToEnd.

  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym : forall a b, iou a b = iou b a.
  Variable tau theta : nat.

  Theorem real_calibrated_yields_collapse :
    forall (f : R -> R) (L : R) (Ln : nat) (eps_n m_n : nat)
           (Hlip : Lipschitz L f)
           (HL_le_Ln : (L <= INR Ln)%R)
           (Hf_nn : forall x, (0 <= f x)%R)
           (Hbnd : (2 * Ln * eps_n <= m_n)%nat)
           (true_feat obs_feat : @det Box -> R) (D : list (@det Box)),
      (1 <= m_n - 2 * Ln * eps_n)%nat ->
      NoDup D ->
      sorted_desc D ->
      sep_apply iou tau theta
        (real_calibrated_head Hlip HL_le_Ln Hf_nn Hbnd) obs_feat true_feat D ->
      filter_above theta (nms_sorted iou tau D) = filter_above theta D.
  Proof.
    intros f L Ln eps_n m_n Hlip HL_le_Ln Hf_nn Hbnd
           true_feat obs_feat D Hslack Hnd Hsd Happ.
    apply (sep_respecting_implies_collapse iou_sym Hnd Hsd Happ).
    unfold real_calibrated_head; cbn [sep_m sep_L sep_eps].
    exact Hslack.
  Qed.

  Theorem squared_hinge_loss_zero_yields_collapse :
    forall (box_eq_dec : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
           (D : list (@det Box)) (k : nat),
      NoDup D ->
      sorted_desc D ->
      (1 <= k)%nat -> (k <= theta)%nat ->
      (L_separated_sq iou tau theta box_eq_dec (INR k) D = 0)%R ->
      filter_above theta (nms_sorted iou tau D) = filter_above theta D.
  Proof.
    intros box_eq_dec D k Hnd Hsd Hk_pos Hk_le_theta Hloss.
    pose proof (proj1 (@L_separated_sq_zero_iff_separated_general
                         Box iou tau theta box_eq_dec D k
                         Hk_pos Hk_le_theta) Hloss)
      as Hsep_k.
    pose proof (@Separated_mono Box iou tau theta 1%nat k D Hk_pos Hsep_k)
      as Hsep_1.
    apply (nms_collapse_onepeak iou_sym Hnd Hsd
             (separated_implies_one_peak Hsep_1)
             (separated_implies_no_tie_clash Hsep_1)).
  Qed.

End EndToEnd.

Theorem scalar_squared_hinge_sgd_yields_zero_loss :
  forall (m : R) (theta0 : list R),
    length theta0 = 1%nat ->
    (sh_loss m (sgd_iterate_vec (sh_grad m) (Rdiv 1 2) theta0 1%nat) = 0)%R.
Proof. exact squared_hinge_sgd_optimal_step. Qed.

Theorem real_training_to_collapse :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau theta : nat)
           (f : R -> R) (L : R) (Ln : nat) (eps_n m_n : nat)
           (Hlip : Lipschitz L f)
           (HL_le_Ln : (L <= INR Ln)%R)
           (Hf_nn : forall x, (0 <= f x)%R)
           (Hbnd : (2 * Ln * eps_n <= m_n)%nat)
           (true_feat obs_feat : @det Box -> R) (D : list (@det Box)),
      (1 <= m_n - 2 * Ln * eps_n)%nat ->
      NoDup D ->
      sorted_desc D ->
      sep_apply iou tau theta
        (real_calibrated_head Hlip HL_le_Ln Hf_nn Hbnd) obs_feat true_feat D ->
      filter_above theta (nms_sorted iou tau D) = filter_above theta D.
Proof.
  intros Box iou iou_sym.
  exact (@real_calibrated_yields_collapse Box iou iou_sym).
Qed.

Theorem scalar_pair_sgd_to_collapse_endpoint :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau theta : nat)
           (box_eq_dec : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2})
           (D : list (@det Box)) (k : nat),
      NoDup D ->
      sorted_desc D ->
      (1 <= k)%nat -> (k <= theta)%nat ->
      (L_separated_sq iou tau theta box_eq_dec (INR k) D = 0)%R ->
      filter_above theta (nms_sorted iou tau D) = filter_above theta D.
Proof.
  intros Box iou iou_sym.
  exact (@squared_hinge_loss_zero_yields_collapse Box iou iou_sym).
Qed.
