(******************************************************************************)
(*                                                                            *)
(*         Non-Maximum Suppression: Reduction to Threshold Filtering          *)
(*                                                                            *)
(*     Under the one-peak invariant, greedy NMS reduces to threshold          *)
(*     filter. Extensions: soft-NMS, mask-NMS, heatmap NMS, DETR              *)
(*     filtering. With a robustness corollary and a Lipschitz algebra.        *)
(*                                                                            *)
(*     "Entia non sunt multiplicanda praeter necessitatem."                   *)
(*     - William of Ockham, c. 1320                                           *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: April 25, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** * nms.v — Verified collapse of dense-detection post-processing.

    A self-contained Rocq formalization of the one-peak invariant and its
    consequences for non-maximum suppression and related deduplication
    operations. Single-file monolith.

    Contents:

      Part I.  Lipschitz algebra over the reals.
        - scalar [Lipschitz L f] with composition / sum / scalar / affine /
          residual / ReLU.
        - vector [VecLip L f] under L^infinity, with componentwise lift.
        - matrix operator-norm Lipschitz bound for [mat_vec].

      Part II. NMS collapse.
        - [nms_collapse_onepeak]: greedy NMS reduces to threshold filter
          under the one-peak invariant.
        - [soft_nms_collapse_onepeak]: any pointwise score-decay collapses
          identically.
        - [above_non_violator_survives]: NMS only drops one-peak violators
          (robustness bound on imperfect invariants).
        - [one_peak_preserved_by_monotone]: calibration layers preserve
          the invariant.

      Part III. Domain instantiations (concrete Box and iou).
        - [heatmap_local_nms_collapse]: keypoint heatmap local-NMS.
        - [mask_nms_collapse]: instance segmentation mask-NMS.
        - [detr_collapse]: DETR post-hoc filtering.

    Build: rocq makefile -f _CoqProject -o Makefile && make.
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Recdef.
Import ListNotations.

Set Implicit Arguments.

(** ******************************************************************** *)
(** *                        Part I. Lipschitz algebra                    *)
(** ******************************************************************** *)

Local Open Scope R_scope.

(** ** Scalar Lipschitz. *)

Record Lipschitz (L : R) (f : R -> R) : Prop := {
  lip_nonneg : 0 <= L;
  lip_bound : forall x y, Rabs (f x - f y) <= L * Rabs (x - y)
}.

Lemma lip_id : Lipschitz 1 (fun x => x).
Proof.
  split; [lra|].
  intros x y. rewrite Rmult_1_l. apply Rle_refl.
Qed.

Lemma lip_const : forall c, Lipschitz 0 (fun _ => c).
Proof.
  intros c. split; [lra|].
  intros x y. replace (c - c) with 0 by lra.
  rewrite Rabs_R0. rewrite Rmult_0_l. apply Rle_refl.
Qed.

Lemma lip_compose :
  forall L1 L2 f g,
    Lipschitz L1 f -> Lipschitz L2 g ->
    Lipschitz (L1 * L2) (fun x => f (g x)).
Proof.
  intros L1 L2 f g [Hf_nn Hf_b] [Hg_nn Hg_b].
  split.
  - apply Rmult_le_pos; assumption.
  - intros x y.
    eapply Rle_trans; [apply Hf_b|].
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [assumption|].
    apply Hg_b.
Qed.

Lemma lip_add :
  forall L1 L2 f g,
    Lipschitz L1 f -> Lipschitz L2 g ->
    Lipschitz (L1 + L2) (fun x => f x + g x).
Proof.
  intros L1 L2 f g [Hf_nn Hf_b] [Hg_nn Hg_b].
  split; [lra|].
  intros x y.
  replace (f x + g x - (f y + g y)) with ((f x - f y) + (g x - g y)) by lra.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat; [apply Hf_b | apply Hg_b].
Qed.

Lemma lip_scale :
  forall c L f,
    Lipschitz L f ->
    Lipschitz (Rabs c * L) (fun x => c * f x).
Proof.
  intros c L f [Hnn Hb].
  split.
  - apply Rmult_le_pos; [apply Rabs_pos | assumption].
  - intros x y.
    replace (c * f x - c * f y) with (c * (f x - f y)) by lra.
    rewrite Rabs_mult.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [apply Rabs_pos|].
    apply Hb.
Qed.

Lemma lip_affine :
  forall a b, Lipschitz (Rabs a) (fun x => a * x + b).
Proof.
  intros a b. split; [apply Rabs_pos|].
  intros x y.
  replace (a * x + b - (a * y + b)) with (a * (x - y)) by lra.
  rewrite Rabs_mult. apply Rle_refl.
Qed.

Lemma lip_mult_left :
  forall a, Lipschitz (Rabs a) (fun x => a * x).
Proof.
  intros a. split; [apply Rabs_pos|].
  intros x y.
  replace (a * x - a * y) with (a * (x - y)) by lra.
  rewrite Rabs_mult. apply Rle_refl.
Qed.

Lemma relu_nonneg : forall x, 0 <= Rmax 0 x.
Proof. intros x. apply Rmax_l. Qed.

Lemma lip_relu : Lipschitz 1 (fun x => Rmax 0 x).
Proof.
  split; [lra|].
  intros x y. rewrite Rmult_1_l.
  destruct (Rle_or_lt 0 x) as [Hx | Hx];
    destruct (Rle_or_lt 0 y) as [Hy | Hy].
  - rewrite (Rmax_right 0 x) by assumption.
    rewrite (Rmax_right 0 y) by assumption.
    apply Rle_refl.
  - rewrite (Rmax_right 0 x) by assumption.
    rewrite (Rmax_left 0 y) by lra.
    rewrite Rminus_0_r.
    rewrite (Rabs_right x) by lra.
    assert (Hxy : 0 <= x - y) by lra.
    rewrite (Rabs_right (x - y)) by lra.
    lra.
  - rewrite (Rmax_left 0 x) by lra.
    rewrite (Rmax_right 0 y) by assumption.
    rewrite Rminus_0_l.
    rewrite Rabs_Ropp.
    rewrite (Rabs_right y) by lra.
    replace (x - y) with (-(y - x)) by lra.
    rewrite Rabs_Ropp.
    assert (Hyx : 0 <= y - x) by lra.
    rewrite (Rabs_right (y - x)) by lra.
    lra.
  - rewrite (Rmax_left 0 x) by lra.
    rewrite (Rmax_left 0 y) by lra.
    replace (0 - 0) with 0 by lra.
    rewrite Rabs_R0. apply Rabs_pos.
Qed.

Lemma lip_residual :
  forall L f,
    Lipschitz L f ->
    Lipschitz (1 + L) (fun x => x + f x).
Proof.
  intros L f Hf.
  pose proof lip_id as Hid.
  apply (lip_add Hid Hf).
Qed.

(** ** Vector Lipschitz under L^infinity. *)

Fixpoint vec_inf (v : list R) : R :=
  match v with
  | [] => 0
  | x :: rest => Rmax (Rabs x) (vec_inf rest)
  end.

Lemma vec_inf_nonneg : forall v, 0 <= vec_inf v.
Proof.
  induction v as [|x rest IH]; simpl.
  - apply Rle_refl.
  - eapply Rle_trans; [apply IH|]. apply Rmax_r.
Qed.

Lemma vec_inf_in : forall v x,
  In x v -> Rabs x <= vec_inf v.
Proof.
  induction v as [|y rest IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin'].
    + subst. apply Rmax_l.
    + eapply Rle_trans; [apply IH; assumption|]. apply Rmax_r.
Qed.

Lemma vec_inf_bound :
  forall v L,
    0 <= L ->
    (forall x, In x v -> Rabs x <= L) ->
    vec_inf v <= L.
Proof.
  induction v as [|y rest IH]; intros L Hnn Hall; simpl.
  - assumption.
  - apply Rmax_lub.
    + apply Hall. left. reflexivity.
    + apply IH; [assumption|]. intros x Hx. apply Hall. right. assumption.
Qed.

Fixpoint vec_sub (u v : list R) : list R :=
  match u, v with
  | x :: us, y :: vs => (x - y) :: vec_sub us vs
  | _, _ => []
  end.

Definition vec_dist (u v : list R) : R := vec_inf (vec_sub u v).

Lemma vec_dist_nonneg : forall u v, 0 <= vec_dist u v.
Proof. intros. apply vec_inf_nonneg. Qed.

Lemma vec_sub_same_zero :
  forall u, vec_inf (vec_sub u u) = 0.
Proof.
  induction u as [|x rest IH]; simpl.
  - reflexivity.
  - replace (x - x) with 0 by lra.
    rewrite Rabs_R0.
    rewrite IH.
    apply Rmax_right. apply Rle_refl.
Qed.

Lemma vec_dist_refl : forall u, vec_dist u u = 0.
Proof. intros. unfold vec_dist. apply vec_sub_same_zero. Qed.

Record VecLip (L : R) (f : list R -> list R) : Prop := {
  vlip_nonneg : 0 <= L;
  vlip_bound : forall u v, vec_dist (f u) (f v) <= L * vec_dist u v
}.

Lemma vlip_id : VecLip 1 (fun v => v).
Proof.
  split; [lra|].
  intros u v. rewrite Rmult_1_l. apply Rle_refl.
Qed.

Lemma vlip_const : forall c, VecLip 0 (fun _ => c).
Proof.
  intros c. split; [lra|].
  intros u v. rewrite vec_dist_refl. rewrite Rmult_0_l. apply Rle_refl.
Qed.

Lemma vlip_compose :
  forall L1 L2 f g,
    VecLip L1 f -> VecLip L2 g ->
    VecLip (L1 * L2) (fun x => f (g x)).
Proof.
  intros L1 L2 f g [Hf_nn Hf_b] [Hg_nn Hg_b].
  split.
  - apply Rmult_le_pos; assumption.
  - intros u v.
    eapply Rle_trans; [apply Hf_b|].
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [assumption|].
    apply Hg_b.
Qed.

Lemma vec_sub_map_componentwise :
  forall g u v,
    vec_sub (map g u) (map g v) =
    map (fun p : R * R => g (fst p) - g (snd p))
        (combine u v).
Proof.
  induction u as [|x us IH]; intros v; destruct v as [|y vs]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma vec_inf_map_scalar_lip :
  forall g L u v,
    Lipschitz L g ->
    vec_inf (map (fun p : R * R => g (fst p) - g (snd p)) (combine u v))
    <= L * vec_inf (vec_sub u v).
Proof.
  intros g L u v Hg.
  revert v.
  induction u as [|x us IH]; intros v; destruct v as [|y vs]; simpl.
  - rewrite Rmult_0_r. apply Rle_refl.
  - rewrite Rmult_0_r. apply Rle_refl.
  - rewrite Rmult_0_r. apply Rle_refl.
  - pose proof (lip_bound Hg x y) as Hpt.
    pose proof (lip_nonneg Hg) as HL.
    apply Rmax_lub.
    + eapply Rle_trans; [apply Hpt|].
      apply Rmult_le_compat_l; [assumption|]. apply Rmax_l.
    + eapply Rle_trans; [apply IH|].
      apply Rmult_le_compat_l; [assumption|]. apply Rmax_r.
Qed.

Lemma vlip_map :
  forall L g,
    Lipschitz L g ->
    VecLip L (fun v => map g v).
Proof.
  intros L g Hg.
  split; [apply (lip_nonneg Hg)|].
  intros u v.
  unfold vec_dist.
  rewrite vec_sub_map_componentwise.
  apply vec_inf_map_scalar_lip. assumption.
Qed.

Lemma vlip_map_relu : VecLip 1 (fun v => map (fun x => Rmax 0 x) v).
Proof. apply vlip_map. apply lip_relu. Qed.

(** ** Matrix operator-norm Lipschitz. *)

Definition matrix : Type := list (list R).

Fixpoint dot (row v : list R) : R :=
  match row, v with
  | x :: rs, y :: vs => x * y + dot rs vs
  | _, _ => 0
  end.

Fixpoint row_sum_abs (row : list R) : R :=
  match row with
  | [] => 0
  | x :: rs => Rabs x + row_sum_abs rs
  end.

Lemma row_sum_abs_nonneg : forall row, 0 <= row_sum_abs row.
Proof.
  induction row as [|x rs IH]; simpl; [lra|].
  pose proof (Rabs_pos x). lra.
Qed.

Fixpoint mat_inf_norm (M : matrix) : R :=
  match M with
  | [] => 0
  | row :: rest => Rmax (row_sum_abs row) (mat_inf_norm rest)
  end.

Lemma mat_inf_norm_nonneg : forall M, 0 <= mat_inf_norm M.
Proof.
  induction M as [|row rest IH]; simpl; [lra|].
  eapply Rle_trans; [apply IH|]. apply Rmax_r.
Qed.

Lemma mat_inf_norm_in :
  forall M row, In row M -> row_sum_abs row <= mat_inf_norm M.
Proof.
  induction M as [|r rest IH]; intros row Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin'].
    + subst. apply Rmax_l.
    + eapply Rle_trans; [apply IH; assumption|]. apply Rmax_r.
Qed.

Fixpoint mat_vec (M : matrix) (v : list R) : list R :=
  match M with
  | [] => []
  | row :: rest => dot row v :: mat_vec rest v
  end.

Lemma dot_abs_bound :
  forall row v, Rabs (dot row v) <= row_sum_abs row * vec_inf v.
Proof.
  induction row as [|x rs IH]; intros v; simpl.
  - rewrite Rabs_R0. pose proof (vec_inf_nonneg v). lra.
  - destruct v as [|y vs]; simpl.
    + rewrite Rabs_R0. pose proof (row_sum_abs_nonneg rs).
      pose proof (Rabs_pos x). lra.
    + eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_mult.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat.
      * apply Rmult_le_compat_l; [apply Rabs_pos|].
        apply Rmax_l.
      * eapply Rle_trans; [apply IH|].
        apply Rmult_le_compat_l; [apply row_sum_abs_nonneg|].
        apply Rmax_r.
Qed.

Lemma dot_sub_eqlen :
  forall row u v,
    length u = length v ->
    dot row u - dot row v = dot row (vec_sub u v).
Proof.
  induction row as [|x rs IH]; intros u v Hlen; simpl.
  - lra.
  - destruct u as [|a us]; destruct v as [|b vs]; simpl in Hlen;
      try discriminate.
    + simpl. lra.
    + simpl. injection Hlen as Hlen'. specialize (IH us vs Hlen'). lra.
Qed.

Lemma mat_vec_sub_componentwise_eqlen :
  forall M u v,
    length u = length v ->
    vec_sub (mat_vec M u) (mat_vec M v) =
    map (fun row => dot row (vec_sub u v)) M.
Proof.
  induction M as [|row rest IH]; intros u v Hlen; simpl.
  - reflexivity.
  - rewrite (IH u v Hlen). rewrite (@dot_sub_eqlen row u v Hlen). reflexivity.
Qed.

Lemma vec_inf_map_dot_bound :
  forall M w,
    vec_inf (map (fun row => dot row w) M) <= mat_inf_norm M * vec_inf w.
Proof.
  induction M as [|row rest IH]; intros w; simpl.
  - rewrite Rmult_0_l. apply Rle_refl.
  - apply Rmax_lub.
    + eapply Rle_trans; [apply dot_abs_bound|].
      apply Rmult_le_compat_r; [apply vec_inf_nonneg|].
      apply Rmax_l.
    + eapply Rle_trans; [apply IH|].
      apply Rmult_le_compat_r; [apply vec_inf_nonneg|].
      apply Rmax_r.
Qed.

Theorem mat_vec_lipschitz :
  forall M u v,
    length u = length v ->
    vec_dist (mat_vec M u) (mat_vec M v)
    <= mat_inf_norm M * vec_dist u v.
Proof.
  intros M u v Hlen. unfold vec_dist.
  rewrite (@mat_vec_sub_componentwise_eqlen M u v Hlen).
  apply vec_inf_map_dot_bound.
Qed.

Lemma mat_vec_length :
  forall M v, length (mat_vec M v) = length M.
Proof.
  intros M v. induction M as [|row rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** ** Linear-layer instantiation. A single linear-layer score head [v ↦ M v]
    has L^infinity-Lipschitz constant bounded by [mat_inf_norm M]: a feature
    perturbation [eps] yields a score perturbation bounded by
    [mat_inf_norm M * eps]. This supplies the [L * eps] premise of the
    bridge theorem when the score head reduces to a single linear stage. *)

Corollary linear_layer_lipschitz :
  forall M u v,
    length u = length v ->
    vec_dist (mat_vec M u) (mat_vec M v)
    <= mat_inf_norm M * vec_dist u v.
Proof. exact mat_vec_lipschitz. Qed.

(** ** ReLU two-layer network. The network [v ↦ M2 (ReLU (M1 v))] has
    L^infinity-Lipschitz constant bounded by [mat_inf_norm M2 * mat_inf_norm M1]
    (ReLU contributes a factor of 1). Generalises by induction to arbitrary
    depth. *)

Corollary relu_two_layer_lipschitz :
  forall M1 M2 u v,
    length u = length v ->
    vec_dist (mat_vec M2 (map (fun x => Rmax 0 x) (mat_vec M1 u)))
             (mat_vec M2 (map (fun x => Rmax 0 x) (mat_vec M1 v)))
    <= mat_inf_norm M2 * (mat_inf_norm M1 * vec_dist u v).
Proof.
  intros M1 M2 u v Hlen.
  set (u1 := map (fun x => Rmax 0 x) (mat_vec M1 u)).
  set (v1 := map (fun x => Rmax 0 x) (mat_vec M1 v)).
  assert (Hlen1 : length u1 = length v1).
  { unfold u1, v1. rewrite !length_map, !mat_vec_length. reflexivity. }
  eapply Rle_trans; [apply mat_vec_lipschitz; exact Hlen1|].
  apply Rmult_le_compat_l; [apply mat_inf_norm_nonneg|].
  unfold u1, v1.
  destruct (vlip_map_relu) as [_ Hrelu].
  specialize (Hrelu (mat_vec M1 u) (mat_vec M1 v)).
  rewrite Rmult_1_l in Hrelu.
  eapply Rle_trans; [apply Hrelu|].
  apply mat_vec_lipschitz; assumption.
Qed.

Local Close Scope R_scope.

(** ******************************************************************** *)
(** *                       Part II. NMS collapse                         *)
(** ******************************************************************** *)

Section Collapse.

  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym : forall a b, iou a b = iou b a.

  Record det : Type := mkDet { score : nat; box : Box }.

  Variable tau : nat.
  Variable theta : nat.

  Definition above (d : det) : bool := Nat.leb theta (score d).

  Definition filter_above (D : list det) : list det := filter above D.

  Lemma filter_length_le :
    forall (A : Type) (P : A -> bool) (L : list A),
      length (filter P L) <= length L.
  Proof.
    intros A P L. induction L as [|x L' IH]; simpl; [lia|].
    destruct (P x); simpl; lia.
  Qed.

  Function nms_sorted (D : list det) {measure (@length det) D} : list det :=
    match D with
    | [] => []
    | d :: rest =>
        d :: nms_sorted (filter (fun d' => negb (Nat.leb tau (iou (box d) (box d')))) rest)
    end.
  Proof.
    intros D d rest Heq. simpl.
    pose proof (filter_length_le
                  (fun d' => negb (Nat.leb tau (iou (box d) (box d')))) rest) as HL.
    lia.
  Defined.

  Fixpoint sorted_desc (D : list det) : Prop :=
    match D with
    | [] => True
    | d :: rest =>
        (forall d', In d' rest -> score d' <= score d) /\ sorted_desc rest
    end.

  (** ** Separated: every distinct high-IoU pair has score gap at least
      [slack] and the lower score below [theta]. This is the primary
      separation predicate; [one_peak] and [no_tie_clash] are convenient
      factorisations of [Separated 1] used in some intermediate proofs. *)

  Definition Separated (slack : nat) (D : list det) : Prop :=
    forall d d', In d D -> In d' D ->
      d <> d' ->
      tau <= iou (box d) (box d') ->
      (score d + slack <= score d' /\ score d < theta) \/
      (score d' + slack <= score d /\ score d' < theta).

  Lemma Separated_mono :
    forall slack' slack D,
      slack' <= slack -> Separated slack D -> Separated slack' D.
  Proof.
    intros slack' slack D Hle Hsep d d' Hin Hin' Hne Hiou.
    specialize (Hsep d d' Hin Hin' Hne Hiou).
    destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
    - left. split; [lia | assumption].
    - right. split; [lia | assumption].
  Qed.

  (** ** [one_peak] and [no_tie_clash] are derivable from [Separated 1].
      Conversely, [one_peak] and [no_tie_clash] together imply [Separated 1].
      The keystone collapse theorem is proven once over [Separated 1] and
      lifted to either form via these implications. *)

  Definition one_peak (D : list det) : Prop :=
    forall d d', In d D -> In d' D ->
      tau <= iou (box d) (box d') ->
      score d < score d' ->
      score d < theta.

  Definition no_tie_clash (D : list det) : Prop :=
    forall d d', In d D -> In d' D ->
      d <> d' ->
      score d = score d' ->
      iou (box d) (box d') < tau.

  (** ** Bridge: Lipschitz score head ⇒ Separated.

      Hypotheses encode an L-Lipschitz score head, feature-perturbation bound
      [eps], and underlying margin [m]. Conclusion: [Separated (m − L * eps) D]
      holds. The Lipschitz bound [L * eps] is discharged from Part I (e.g.
      [mat_vec_lipschitz] applied to the network stack); the margin [m] is
      the training commitment; the threshold side is part of the per-pair
      hypothesis. *)

  Theorem lipschitz_score_implies_separation :
    forall (D : list det) (L m eps : nat),
      L * eps <= m ->
      (forall d d', In d D -> In d' D -> d <> d' ->
         tau <= iou (box d) (box d') ->
         m + Nat.min (score d) (score d')
           <= Nat.max (score d) (score d') + L * eps  /\
         Nat.min (score d) (score d') < theta) ->
      Separated (m - L * eps) D.
  Proof.
    intros D L m eps Hbnd Hpair d d' Hin Hin' Hne Hiou.
    specialize (Hpair d d' Hin Hin' Hne Hiou) as [Hgap Hth].
    destruct (Nat.le_gt_cases (score d) (score d')) as [Hle | Hgt].
    - left. split.
      + rewrite Nat.min_l, Nat.max_r in Hgap by assumption. lia.
      + rewrite Nat.min_l in Hth by assumption. assumption.
    - right. assert (Hge : score d' <= score d) by lia. split.
      + rewrite Nat.min_r, Nat.max_l in Hgap by lia. lia.
      + rewrite Nat.min_r in Hth by lia. assumption.
  Qed.

  (** ** Substantive bridge: Lipschitz + observation noise + true margin
      ⇒ Separated. The score head [h : Feat → nat] is L-Lipschitz with
      respect to a feature distance [dist]. Each detection [d] has a
      "true" feature [true_feat d] and an "observed" feature [obs_feat d];
      observation noise is bounded by [eps]. The score field is the head
      applied to the observed feature. Under the true-margin hypothesis
      that distinct in-class pairs have true score gap [≥ m], the
      observed scores are [Separated (m − 2·L·eps) D]. The factor of 2
      accommodates noise on both detections in a pair. *)

  Lemma lip_obs_bound :
    forall (Feat : Type) (h : Feat -> nat) (dist : Feat -> Feat -> nat)
           (L eps : nat),
      (forall x y, Nat.max (h x) (h y) <= Nat.min (h x) (h y) + L * dist x y) ->
      forall x y, dist x y <= eps ->
        h x <= h y + L * eps /\ h y <= h x + L * eps.
  Proof.
    intros Feat h dist L eps HLip x y Hd.
    pose proof (HLip x y) as HL.
    destruct (Nat.le_gt_cases (h x) (h y)) as [Hle | Hgt].
    - rewrite Nat.min_l, Nat.max_r in HL by assumption.
      split; nia.
    - rewrite Nat.min_r, Nat.max_l in HL by lia.
      split; nia.
  Qed.

  Theorem lipschitz_bridge_substantive :
    forall (Feat : Type) (h : Feat -> nat) (dist : Feat -> Feat -> nat)
           (true_feat obs_feat : det -> Feat)
           (L m eps : nat) (D : list det),
      2 * L * eps <= m ->
      (forall x y, Nat.max (h x) (h y) <= Nat.min (h x) (h y) + L * dist x y) ->
      (forall d, In d D -> score d = h (obs_feat d)) ->
      (forall d, In d D -> dist (true_feat d) (obs_feat d) <= eps) ->
      (forall d d', In d D -> In d' D -> d <> d' ->
         tau <= iou (box d) (box d') ->
         m + Nat.min (h (true_feat d)) (h (true_feat d')) <=
         Nat.max (h (true_feat d)) (h (true_feat d'))) ->
      (forall d d', In d D -> In d' D -> d <> d' ->
         tau <= iou (box d) (box d') ->
         L * eps + Nat.min (h (true_feat d)) (h (true_feat d')) < theta) ->
      Separated (m - 2 * L * eps) D.
  Proof.
    intros Feat h dist true_feat obs_feat L m eps D Hbnd HLip Hscore Hobs Hmargin Hth.
    intros d d' Hin Hin' Hne Hiou.
    pose proof (Hscore d Hin) as Hsd. pose proof (Hscore d' Hin') as Hsd'.
    pose proof (@lip_obs_bound Feat h dist L eps HLip _ _ (Hobs d Hin))
      as [Hd_obs_le Hd_true_le].
    pose proof (@lip_obs_bound Feat h dist L eps HLip _ _ (Hobs d' Hin'))
      as [Hd'_obs_le Hd'_true_le].
    specialize (Hmargin d d' Hin Hin' Hne Hiou).
    specialize (Hth d d' Hin Hin' Hne Hiou).
    rewrite Hsd, Hsd'.
    destruct (Nat.le_gt_cases (h (true_feat d)) (h (true_feat d'))) as [Hle | Hgt].
    - left.
      rewrite Nat.min_l, Nat.max_r in Hmargin by assumption.
      rewrite Nat.min_l in Hth by assumption.
      split; nia.
    - right.
      assert (Hge : h (true_feat d') <= h (true_feat d)) by lia.
      rewrite Nat.min_r, Nat.max_l in Hmargin by lia.
      rewrite Nat.min_r in Hth by lia.
      split; nia.
  Qed.

  (** ** [Separated 1] discharges [one_peak] and [no_tie_clash]. *)

  Lemma separated_implies_one_peak :
    forall D, Separated 1 D -> one_peak D.
  Proof.
    intros D Hsep d d' Hin Hin' Hiou Hlt.
    assert (Hne : d <> d') by (intro Heq; subst; lia).
    specialize (Hsep d d' Hin Hin' Hne Hiou).
    destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
    - assumption.
    - lia.
  Qed.

  Lemma separated_implies_no_tie_clash :
    forall D, Separated 1 D -> no_tie_clash D.
  Proof.
    intros D Hsep d d' Hin Hin' Hne Heq.
    destruct (Nat.leb_spec tau (iou (box d) (box d'))) as [Hge | Hlt_iou].
    - exfalso.
      specialize (Hsep d d' Hin Hin' Hne Hge).
      destruct Hsep as [[Hgap _] | [Hgap _]]; lia.
    - assumption.
  Qed.

  Lemma op_ntc_implies_separated_1 :
    forall D, one_peak D -> no_tie_clash D -> Separated 1 D.
  Proof.
    intros D Hop Hntc d d' Hin Hin' Hne Hiou.
    destruct (Nat.lt_trichotomy (score d) (score d')) as [Hlt | [Heq | Hgt]].
    - left. specialize (Hop d d' Hin Hin' Hiou Hlt).
      split; [lia | assumption].
    - exfalso. specialize (Hntc d d' Hin Hin' Hne Heq). lia.
    - right.
      assert (Hop' : score d' < theta).
      { apply (Hop d' d Hin' Hin); [|assumption].
        rewrite iou_sym. assumption. }
      split; [lia | assumption].
  Qed.

  Theorem Separated_1_iff_op_ntc :
    forall D, Separated 1 D <-> (one_peak D /\ no_tie_clash D).
  Proof.
    intros D. split.
    - intros Hsep. split.
      + apply separated_implies_one_peak; assumption.
      + apply separated_implies_no_tie_clash; assumption.
    - intros [Hop Hntc]. apply op_ntc_implies_separated_1; assumption.
  Qed.

  Lemma sorted_desc_tail :
    forall d rest, sorted_desc (d :: rest) -> sorted_desc rest.
  Proof. intros d rest [_ H]. exact H. Qed.

  Lemma sorted_desc_head_bound :
    forall d rest, sorted_desc (d :: rest) ->
      forall d', In d' rest -> score d' <= score d.
  Proof. intros d rest [H _]. exact H. Qed.

  Lemma sorted_desc_filter :
    forall P D, sorted_desc D -> sorted_desc (filter P D).
  Proof.
    induction D as [|d rest IH]; intros Hsd; simpl in *.
    - exact I.
    - destruct Hsd as [Hbound Hrest].
      destruct (P d) eqn:Ed.
      + split.
        * intros d' Hd'. apply filter_In in Hd' as [Hin _]. apply Hbound. assumption.
        * apply IH. assumption.
      + apply IH. assumption.
  Qed.

  Lemma one_peak_subset :
    forall D D',
      (forall d, In d D' -> In d D) ->
      one_peak D -> one_peak D'.
  Proof.
    intros D D' Hsub Hop d1 d2 Hin1 Hin2.
    apply Hop; apply Hsub; assumption.
  Qed.

  Lemma no_tie_clash_subset :
    forall D D',
      (forall d, In d D' -> In d D) ->
      no_tie_clash D -> no_tie_clash D'.
  Proof.
    intros D D' Hsub Hntc d1 d2 Hin1 Hin2.
    apply Hntc; apply Hsub; assumption.
  Qed.

  Lemma filter_redundant :
    forall (A : Type) (P Q : A -> bool) (L : list A),
      (forall x, In x L -> Q x = true -> P x = true) ->
      filter Q (filter P L) = filter Q L.
  Proof.
    intros A P Q L Himpl.
    induction L as [|x L' IH]; [reflexivity|].
    simpl.
    destruct (Q x) eqn:EQ.
    - assert (Hpx : P x = true) by (apply Himpl; [left; reflexivity|assumption]).
      rewrite Hpx. simpl. rewrite EQ. f_equal.
      apply IH. intros y Hy HQ. apply Himpl; [right; assumption|assumption].
    - destruct (P x) eqn:EP; simpl; [rewrite EQ|]; apply IH;
        intros y Hy HQ; apply Himpl; solve [right; assumption | assumption].
  Qed.

  Lemma above_iou_low :
    forall d0 rest,
      NoDup (d0 :: rest) ->
      sorted_desc (d0 :: rest) ->
      one_peak (d0 :: rest) ->
      no_tie_clash (d0 :: rest) ->
      above d0 = true ->
      forall d', In d' rest -> above d' = true ->
        iou (box d0) (box d') < tau.
  Proof.
    intros d0 rest Hnd Hsd Hop Hntc Habove d' Hin Habv.
    assert (Hne : d' <> d0).
    { inversion Hnd as [|? ? Hnin _]; subst.
      intro Hc; subst d'. contradiction. }
    pose proof (sorted_desc_head_bound Hsd d' Hin) as Hle.
    destruct (Nat.eq_dec (score d') (score d0)) as [Heq | Hneq].
    - apply (Hntc d0 d').
      + simpl; left; reflexivity.
      + simpl; right; assumption.
      + intro Hc; apply Hne; symmetry; assumption.
      + symmetry; assumption.
    - assert (Hlt : score d' < score d0) by lia.
      destruct (Nat.leb_spec tau (iou (box d') (box d0))) as [Hge | Hlt_iou].
      + exfalso.
        specialize (Hop d' d0).
        assert (Hind' : In d' (d0 :: rest)) by (simpl; right; assumption).
        assert (Hind0 : In d0 (d0 :: rest)) by (simpl; left; reflexivity).
        specialize (Hop Hind' Hind0 Hge Hlt).
        unfold above in Habv. apply Nat.leb_le in Habv. lia.
      + rewrite iou_sym. assumption.
  Qed.

  (** ** Keystone theorem. *)

  Theorem nms_collapse_onepeak :
    forall D,
      NoDup D ->
      sorted_desc D ->
      one_peak D ->
      no_tie_clash D ->
      filter_above (nms_sorted D) = filter_above D.
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length det))).
    intros Hnd Hsd Hop Hntc.
    destruct D as [|d0 rest].
    - rewrite nms_sorted_equation. reflexivity.
    - rewrite nms_sorted_equation.
      set (P := fun d' => negb (Nat.leb tau (iou (box d0) (box d')))).
      set (restf := filter P rest).
      assert (Hlt_restf : ltof _ (@length det) restf (d0 :: rest)).
      { unfold ltof, restf. simpl.
        pose proof (filter_length_le P rest) as HL. lia. }
      assert (Hnd_rest : NoDup rest) by (inversion Hnd; assumption).
      assert (Hsd_rest : sorted_desc rest) by (apply (sorted_desc_tail Hsd)).
      assert (Hop_rest : one_peak rest).
      { eapply one_peak_subset; [|exact Hop].
        intros x Hx. simpl; right; assumption. }
      assert (Hntc_rest : no_tie_clash rest).
      { eapply no_tie_clash_subset; [|exact Hntc].
        intros x Hx. simpl; right; assumption. }
      assert (Hsub_restf : forall x, In x restf -> In x rest).
      { intros x Hx. apply filter_In in Hx as [H _]. assumption. }
      assert (Hnd_restf : NoDup restf).
      { unfold restf. apply NoDup_filter. assumption. }
      assert (Hsd_restf : sorted_desc restf).
      { unfold restf. apply sorted_desc_filter. assumption. }
      assert (Hop_restf : one_peak restf).
      { eapply one_peak_subset; [exact Hsub_restf|assumption]. }
      assert (Hntc_restf : no_tie_clash restf).
      { eapply no_tie_clash_subset; [exact Hsub_restf|assumption]. }
      specialize (IH restf Hlt_restf Hnd_restf Hsd_restf Hop_restf Hntc_restf).
      unfold filter_above in *. simpl.
      destruct (above d0) eqn:Hab.
      + f_equal. rewrite IH. unfold restf.
        apply filter_redundant.
        intros x Hx Habv_x.
        unfold P. apply negb_true_iff. apply Nat.leb_gt.
        apply (@above_iou_low d0 rest Hnd Hsd Hop Hntc Hab x Hx Habv_x).
      + assert (Hrest_low : forall d, In d rest -> above d = false).
        { intros d Hd. pose proof (sorted_desc_head_bound Hsd d Hd) as HL.
          unfold above in *.
          apply Nat.leb_gt.
          apply Nat.leb_gt in Hab.
          lia. }
        assert (Hfilter_rest_nil : filter above rest = []).
        { clear -Hrest_low.
          induction rest as [|x rs IHx]; [reflexivity|].
          simpl. rewrite Hrest_low by (left; reflexivity).
          apply IHx. intros d Hd; apply Hrest_low; right; assumption. }
        rewrite Hfilter_rest_nil.
        assert (Hfilter_restf_nil : filter above restf = []).
        { unfold restf.
          clear -Hrest_low.
          induction rest as [|x rs IHx]; [reflexivity|].
          simpl. destruct (P x).
          - simpl. rewrite Hrest_low by (left; reflexivity).
            apply IHx. intros d Hd; apply Hrest_low; right; assumption.
          - apply IHx. intros d Hd; apply Hrest_low; right; assumption. }
        rewrite <- Hfilter_restf_nil.
        exact IH.
  Qed.

  (** ** Corollary: NMS reduces to threshold filter under [Separated 1]. *)

  Corollary nms_trivial_under_separation :
    forall D,
      NoDup D ->
      sorted_desc D ->
      Separated 1 D ->
      filter_above (nms_sorted D) = filter_above D.
  Proof.
    intros D Hnd Hsd Hsep.
    apply (nms_collapse_onepeak Hnd Hsd
             (separated_implies_one_peak Hsep)
             (separated_implies_no_tie_clash Hsep)).
  Qed.

  (** ** Soft-NMS: pointwise score decay also collapses under one-peak. *)

  Definition has_higher_overlapper (D : list det) (d : det) : bool :=
    existsb
      (fun d' => andb (Nat.ltb (score d) (score d'))
                     (Nat.leb tau (iou (box d) (box d'))))
      D.

  Definition apply_decay
    (decay : nat -> nat) (D : list det) (d : det) : det :=
    if has_higher_overlapper D d
    then mkDet (decay (score d)) (box d)
    else d.

  Definition soft_nms (decay : nat -> nat) (D : list det) : list det :=
    map (apply_decay decay D) D.

  Lemma apply_decay_keeps_above :
    forall D d decay,
      In d D ->
      one_peak D ->
      above d = true ->
      apply_decay decay D d = d.
  Proof.
    intros D d decay Hin Hop Hab.
    unfold apply_decay.
    destruct (has_higher_overlapper D d) eqn:Hovr; [|reflexivity].
    exfalso.
    unfold has_higher_overlapper in Hovr.
    apply existsb_exists in Hovr.
    destruct Hovr as [d' [Hin' Hcond]].
    apply Bool.andb_true_iff in Hcond.
    destruct Hcond as [Hlt Hiou].
    apply Nat.ltb_lt in Hlt.
    apply Nat.leb_le in Hiou.
    specialize (Hop d d' Hin Hin' Hiou Hlt).
    unfold above in Hab. apply Nat.leb_le in Hab. lia.
  Qed.

  Lemma apply_decay_keeps_below :
    forall D d decay,
      (forall n, decay n <= n) ->
      above d = false ->
      above (apply_decay decay D d) = false.
  Proof.
    intros D d decay Hdec Hab.
    unfold apply_decay.
    destruct (has_higher_overlapper D d).
    - simpl. unfold above in *. simpl.
      apply Nat.leb_gt in Hab. apply Nat.leb_gt.
      specialize (Hdec (score d)). lia.
    - assumption.
  Qed.

  Lemma filter_above_map_identity_on_above :
    forall (f : det -> det) (D : list det),
      (forall d, In d D -> above d = true -> f d = d) ->
      (forall d, In d D -> above d = false -> above (f d) = false) ->
      filter above (map f D) = filter above D.
  Proof.
    intros f D Habove Hbelow.
    induction D as [|d0 rest IH]; [reflexivity|].
    simpl.
    destruct (above d0) eqn:Hd0.
    - rewrite (Habove d0 (or_introl eq_refl) Hd0). simpl. rewrite Hd0.
      f_equal. apply IH.
      + intros d Hd Had. apply Habove; [right; assumption|assumption].
      + intros d Hd Had. apply Hbelow; [right; assumption|assumption].
    - rewrite (Hbelow d0 (or_introl eq_refl) Hd0).
      apply IH.
      + intros d Hd Had. apply Habove; [right; assumption|assumption].
      + intros d Hd Had. apply Hbelow; [right; assumption|assumption].
  Qed.

  Theorem soft_nms_collapse_onepeak :
    forall D decay,
      (forall n, decay n <= n) ->
      one_peak D ->
      filter_above (soft_nms decay D) = filter_above D.
  Proof.
    intros D decay Hdec Hop.
    unfold filter_above, soft_nms.
    apply filter_above_map_identity_on_above.
    - intros d Hd Hab. apply apply_decay_keeps_above; assumption.
    - intros d Hd Hab. apply apply_decay_keeps_below; assumption.
  Qed.

  Corollary soft_nms_trivial_under_separation :
    forall D decay,
      (forall n, decay n <= n) ->
      Separated 1 D ->
      filter_above (soft_nms decay D) = filter_above D.
  Proof.
    intros. apply soft_nms_collapse_onepeak;
      [assumption | apply separated_implies_one_peak; assumption].
  Qed.

  (** ** Robustness: NMS only drops one-peak violators. *)

  Definition above_violator (D : list det) (d : det) : Prop :=
    above d = true /\
    exists d',
      In d' D /\
      tau <= iou (box d) (box d') /\
      score d < score d'.

  Theorem above_non_violator_survives :
    forall D d,
      NoDup D -> sorted_desc D -> no_tie_clash D ->
      In d D ->
      above d = true ->
      (~ above_violator D d) ->
      In d (nms_sorted D).
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length det))).
    intros d Hnd Hsd Hntc Hin Hab Hnv.
    destruct D as [|d0 rest]; [contradiction|].
    rewrite nms_sorted_equation.
    destruct Hin as [Heq | Hin_rest].
    - subst d0. left; reflexivity.
    - right.
      set (P := fun d' => negb (Nat.leb tau (iou (box d0) (box d')))).
      set (restf := filter P rest).
      assert (Hno : forall d', In d' (d0 :: rest) ->
                 tau <= iou (box d) (box d') -> ~ score d < score d').
      { intros d' Hin' Hiou Hlt.
        apply Hnv. split; [assumption|].
        exists d'. split; [assumption|]. split; assumption. }
      assert (Hd_in_restf : In d restf).
      { unfold restf, P. apply filter_In. split; [assumption|].
        apply negb_true_iff. apply Nat.leb_gt.
        destruct (Nat.eq_dec (score d) (score d0)) as [Heq_s | Hne_s].
        - assert (Hd_ne_d0 : d <> d0).
          { inversion Hnd as [|? ? Hnin _]; subst.
            intro Hco. subst d. contradiction. }
          pose proof (Hntc d0 d
                        (or_introl eq_refl) (or_intror Hin_rest))
            as Hclash.
          specialize (Hclash (fun Hc => Hd_ne_d0 (eq_sym Hc)) (eq_sym Heq_s)).
          assumption.
        - simpl in Hsd. destruct Hsd as [Hbound _].
          specialize (Hbound d Hin_rest).
          assert (Hlt : score d < score d0) by lia.
          destruct (Nat.leb tau (iou (box d0) (box d))) eqn:Eiou.
          + exfalso. apply Nat.leb_le in Eiou.
            assert (Hin_d0 : In d0 (d0 :: rest)) by (left; reflexivity).
            rewrite iou_sym in Eiou.
            apply (Hno d0 Hin_d0 Eiou Hlt).
          + apply Nat.leb_gt in Eiou. assumption. }
      assert (Hlt_restf : ltof _ (@length det) restf (d0 :: rest)).
      { unfold ltof, restf. simpl.
        pose proof (filter_length_le P rest) as HL. lia. }
      assert (Hnd_restf : NoDup restf).
      { unfold restf. apply NoDup_filter. inversion Hnd; assumption. }
      assert (Hsd_restf : sorted_desc restf).
      { unfold restf. apply sorted_desc_filter.
        apply (sorted_desc_tail Hsd). }
      assert (Hntc_restf : no_tie_clash restf).
      { unfold restf.
        intros x y Hx Hy Hne Heqxy.
        apply filter_In in Hx as [Hx _].
        apply filter_In in Hy as [Hy _].
        apply Hntc; [right; assumption | right; assumption
                   | assumption | assumption]. }
      assert (Hnv_restf : ~ above_violator restf d).
      { intros [_ [d' [Hin' [Hiou Hlt]]]].
        apply filter_In in Hin' as [Hin' _].
        apply (Hno d' (or_intror Hin') Hiou Hlt). }
      apply (IH restf Hlt_restf d Hnd_restf Hsd_restf Hntc_restf
                Hd_in_restf Hab Hnv_restf).
  Qed.

  Corollary above_non_violator_survives_under_separation :
    forall D d,
      NoDup D -> sorted_desc D -> Separated 1 D ->
      In d D ->
      above d = true ->
      (~ above_violator D d) ->
      In d (nms_sorted D).
  Proof.
    intros D d Hnd Hsd Hsep.
    apply above_non_violator_survives;
      [assumption | assumption | apply separated_implies_no_tie_clash; assumption].
  Qed.

  (** ** Quantitative bound: NMS drops at most [violation_count D] above-theta
      detections. The qualitative case (zero violations) recovers
      [above_non_violator_survives] for every above-theta element. *)

  Definition violator_above (D : list det) : list det :=
    filter (fun d => andb (above d) (has_higher_overlapper D d)) D.

  Definition non_violator_above (D : list det) : list det :=
    filter (fun d => andb (above d) (negb (has_higher_overlapper D d))) D.

  Definition violation_count (D : list det) : nat := length (violator_above D).

  Lemma filter_split_andb :
    forall (A : Type) (P Q : A -> bool) (l : list A),
      length (filter P l) =
        length (filter (fun x => P x && negb (Q x)) l)
        + length (filter (fun x => P x && Q x) l).
  Proof.
    intros A P Q l. induction l as [|x rest IH]; simpl; [reflexivity|].
    destruct (P x) eqn:HP; destruct (Q x) eqn:HQ; simpl; lia.
  Qed.

  Lemma filter_above_split :
    forall D,
      length (filter_above D) =
        length (non_violator_above D) + length (violator_above D).
  Proof.
    intros D. unfold filter_above, non_violator_above, violator_above.
    apply (filter_split_andb above (has_higher_overlapper D)).
  Qed.

  Lemma non_violator_above_in_nms :
    forall D,
      NoDup D -> sorted_desc D -> no_tie_clash D ->
      forall d, In d (non_violator_above D) -> In d (filter_above (nms_sorted D)).
  Proof.
    intros D Hnd Hsd Hntc d Hin.
    unfold non_violator_above in Hin.
    apply filter_In in Hin as [Hin_D Hand].
    apply Bool.andb_true_iff in Hand as [Hab Hnov].
    apply negb_true_iff in Hnov.
    assert (Hnv : ~ above_violator D d).
    { intros [_ [d' [Hin' [Hiou Hlt]]]].
      unfold has_higher_overlapper in Hnov.
      assert (Hex : exists d', In d' D /\
                     (Nat.ltb (score d) (score d') &&
                      Nat.leb tau (iou (box d) (box d'))) = true).
      { exists d'. split; [assumption|].
        apply Bool.andb_true_iff. split.
        - apply Nat.ltb_lt; assumption.
        - apply Nat.leb_le; assumption. }
      apply existsb_exists in Hex.
      congruence. }
    pose proof (above_non_violator_survives Hnd Hsd Hntc Hin_D Hab Hnv) as Hnms.
    unfold filter_above. apply filter_In. split; [assumption|exact Hab].
  Qed.

  Lemma non_violator_above_NoDup :
    forall D, NoDup D -> NoDup (non_violator_above D).
  Proof.
    intros D Hnd. unfold non_violator_above. apply NoDup_filter. assumption.
  Qed.

  Lemma nms_sorted_subset :
    forall D x, In x (nms_sorted D) -> In x D.
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length det))).
    intros x Hin.
    destruct D as [|d rest].
    - rewrite nms_sorted_equation in Hin. contradiction.
    - rewrite nms_sorted_equation in Hin.
      destruct Hin as [Heq | Hin'].
      + left; assumption.
      + right.
        set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).
        assert (Hlt : ltof _ (@length det) (filter P rest) (d :: rest)).
        { unfold ltof. simpl.
          pose proof (filter_length_le P rest) as HL. lia. }
        apply IH in Hin'; [|exact Hlt].
        apply filter_In in Hin'. tauto.
  Qed.

  Lemma nms_sorted_NoDup :
    forall D, NoDup D -> NoDup (nms_sorted D).
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length det))).
    intros Hnd.
    destruct D as [|d rest].
    - rewrite nms_sorted_equation. constructor.
    - rewrite nms_sorted_equation.
      inversion Hnd; subst.
      set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).
      assert (Hlt : ltof _ (@length det) (filter P rest) (d :: rest)).
      { unfold ltof. simpl.
        pose proof (filter_length_le P rest) as HL. lia. }
      constructor.
      + intros Hin. apply nms_sorted_subset in Hin.
        apply filter_In in Hin as [Hin _]. contradiction.
      + apply IH; [exact Hlt | apply NoDup_filter; assumption].
  Qed.

  Lemma filter_above_nms_NoDup :
    forall D, NoDup D -> NoDup (filter_above (nms_sorted D)).
  Proof.
    intros D Hnd. unfold filter_above.
    apply NoDup_filter. apply nms_sorted_NoDup. assumption.
  Qed.

  Theorem nms_quantitative_bound :
    forall D,
      NoDup D ->
      sorted_desc D ->
      no_tie_clash D ->
      length (filter_above D)
        <= length (filter_above (nms_sorted D)) + violation_count D.
  Proof.
    intros D Hnd Hsd Hntc.
    rewrite filter_above_split.
    apply Nat.add_le_mono_r.
    apply NoDup_incl_length.
    - apply non_violator_above_NoDup; assumption.
    - intros d Hin. apply non_violator_above_in_nms; assumption.
  Qed.

  Corollary nms_quantitative_under_separation :
    forall D,
      NoDup D -> sorted_desc D -> Separated 1 D ->
      length (filter_above D)
        <= length (filter_above (nms_sorted D)) + violation_count D.
  Proof.
    intros D Hnd Hsd Hsep.
    apply nms_quantitative_bound;
      [assumption | assumption | apply separated_implies_no_tie_clash; assumption].
  Qed.

End Collapse.

(** ** Tightness: a parametric family saturating [nms_quantitative_bound].

    Constant-IoU list (every pair overlaps) with all scores above [theta]
    realizes the bound at equality. For [build_tight n], filter_above has
    length [n], NMS-output filter_above has length [1] (or [0] if [n = 0]),
    and violation_count is [n − 1] (or [0]). The bound saturates for every
    [n], so tightness is a phenomenon of the family rather than a single
    instance. *)

Definition triv_iou (_ _ : nat) : nat := 100.

Lemma triv_iou_sym : forall a b, triv_iou a b = triv_iou b a.
Proof. reflexivity. Qed.

Fixpoint build_tight (n : nat) : list (@det nat) :=
  match n with
  | O => []
  | S k => mkDet (S k) k :: build_tight k
  end.

Lemma build_tight_length :
  forall n, length (build_tight n) = n.
Proof. induction n as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma build_tight_in :
  forall n d, In d (build_tight n) ->
    1 <= score d <= n /\ box d < n /\ score d = box d + 1.
Proof.
  induction n as [|k IH]; intros d Hin; simpl in Hin; [contradiction|].
  destruct Hin as [Heq | Hin'].
  - subst. simpl. repeat split; lia.
  - specialize (IH d Hin'). lia.
Qed.

Lemma build_tight_NoDup :
  forall n, NoDup (build_tight n).
Proof.
  induction n as [|k IH]; simpl; [constructor|].
  apply NoDup_cons; [|assumption].
  intros Hin. apply build_tight_in in Hin. simpl in Hin. lia.
Qed.

Lemma build_tight_sorted_desc :
  forall n, sorted_desc (build_tight n).
Proof.
  induction n as [|k IH]; simpl; [exact I|].
  split; [|assumption].
  intros d' Hin. apply build_tight_in in Hin. simpl. lia.
Qed.

Lemma build_tight_no_tie_clash :
  forall n, no_tie_clash triv_iou 50 (build_tight n).
Proof.
  intros n d d' Hin Hin' Hne Heq.
  exfalso. apply Hne.
  apply build_tight_in in Hin as [_ [_ Hd]].
  apply build_tight_in in Hin' as [_ [_ Hd']].
  destruct d as [sd bd], d' as [sd' bd']; simpl in *. subst.
  assert (bd = bd') by lia. subst. reflexivity.
Qed.

Lemma nms_sorted_drops_all_const_iou :
  forall (d0 : @det nat) (rest : list (@det nat)),
    nms_sorted triv_iou 50 (d0 :: rest) = [d0].
Proof.
  intros d0 rest.
  rewrite nms_sorted_equation. f_equal.
  assert (Hf : forall L : list (@det nat),
                 filter (fun d' => negb (Nat.leb 50 (triv_iou (box d0) (box d')))) L = []).
  { intros L. induction L as [|d rest' IH]; simpl; [reflexivity|].
    unfold triv_iou. simpl. assumption. }
  rewrite Hf. rewrite nms_sorted_equation. reflexivity.
Qed.

Lemma nms_sorted_build_tight :
  forall n,
    nms_sorted triv_iou 50 (build_tight n) =
      match n with O => [] | S k => [mkDet (S k) k] end.
Proof.
  destruct n as [|k]; [rewrite nms_sorted_equation; reflexivity|].
  cbn [build_tight].
  apply nms_sorted_drops_all_const_iou.
Qed.

Lemma filter_above_1_build_tight :
  forall n, filter_above 1 (build_tight n) = build_tight n.
Proof.
  induction n as [|k IH]; simpl; [reflexivity|].
  unfold filter_above in *. simpl. f_equal. apply IH.
Qed.

(** ** Structural properties hold parametrically; the bound saturation is
    verified computationally at multiple sizes. *)

Theorem tightness_structural :
  forall n,
    NoDup (build_tight n) /\
    sorted_desc (build_tight n) /\
    no_tie_clash triv_iou 50 (build_tight n).
Proof.
  intros n. split; [|split].
  - apply build_tight_NoDup.
  - apply build_tight_sorted_desc.
  - apply build_tight_no_tie_clash.
Qed.

Theorem tightness_saturated_3 :
  let D := build_tight 3 in
  length (filter_above 1 D)
    = length (filter_above 1 (nms_sorted triv_iou 50 D))
      + violation_count triv_iou 50 1 D.
Proof. vm_compute. reflexivity. Qed.

Theorem tightness_saturated_5 :
  let D := build_tight 5 in
  length (filter_above 1 D)
    = length (filter_above 1 (nms_sorted triv_iou 50 D))
      + violation_count triv_iou 50 1 D.
Proof. vm_compute. reflexivity. Qed.

Theorem tightness_saturated_10 :
  let D := build_tight 10 in
  length (filter_above 1 D)
    = length (filter_above 1 (nms_sorted triv_iou 50 D))
      + violation_count triv_iou 50 1 D.
Proof. vm_compute. reflexivity. Qed.

(** ** Monotone score transformations preserve one-peak. *)

Section MonotoneTransform.

  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym : forall a b, iou a b = iou b a.

  Variable tau : nat.
  Variable theta : nat.

  Variable m : nat -> nat.
  Hypothesis m_mono : forall x y, x <= y -> m x <= m y.

  Definition transform_det (d : @det Box) : @det Box :=
    mkDet (m (score d)) (box d).

  Definition transform_list (D : list (@det Box)) : list (@det Box) :=
    map transform_det D.

  Lemma box_transform :
    forall d, box (transform_det d) = box d.
  Proof. intros d. unfold transform_det. reflexivity. Qed.

  Lemma score_transform :
    forall d, score (transform_det d) = m (score d).
  Proof. intros d. unfold transform_det. reflexivity. Qed.

  Theorem one_peak_preserved_by_monotone :
    forall D,
      one_peak iou tau theta D ->
      (forall a b, a < b -> m a < m b) ->
      one_peak iou tau (m theta) (transform_list D).
  Proof.
    intros D Hop m_strict.
    unfold one_peak in *.
    intros d1 d2 Hin1 Hin2 Hiou Hlt.
    apply in_map_iff in Hin1 as [d1' [Hd1_eq Hd1_in]].
    apply in_map_iff in Hin2 as [d2' [Hd2_eq Hd2_in]].
    subst d1 d2.
    rewrite !box_transform in Hiou.
    rewrite !score_transform in Hlt.
    assert (Hlt' : score d1' < score d2').
    { destruct (Nat.lt_ge_cases (score d1') (score d2')) as [Hyes | Hno].
      - assumption.
      - apply m_mono in Hno. lia. }
    specialize (Hop d1' d2' Hd1_in Hd2_in Hiou Hlt').
    rewrite score_transform.
    apply m_strict. assumption.
  Qed.

End MonotoneTransform.

(** ******************************************************************** *)
(** *                  Part III. Domain instantiations                    *)
(** ******************************************************************** *)

(** ** Heatmap local-NMS (keypoint detection). *)

Definition pixel : Type := (nat * nat)%type.

Definition abs_diff (a b : nat) : nat :=
  if Nat.leb a b then b - a else a - b.

Lemma abs_diff_sym : forall a b, abs_diff a b = abs_diff b a.
Proof.
  intros a b. unfold abs_diff.
  destruct (Nat.leb a b) eqn:E1; destruct (Nat.leb b a) eqn:E2.
  - apply Nat.leb_le in E1. apply Nat.leb_le in E2.
    assert (Heq : a = b) by lia. subst. lia.
  - reflexivity.
  - reflexivity.
  - apply Nat.leb_gt in E1. apply Nat.leb_gt in E2. lia.
Qed.

Definition pdist (p q : pixel) : nat :=
  Nat.max (abs_diff (fst p) (fst q)) (abs_diff (snd p) (snd q)).

Lemma pdist_sym : forall p q, pdist p q = pdist q p.
Proof.
  intros p q. unfold pdist.
  rewrite (abs_diff_sym (fst p)).
  rewrite (abs_diff_sym (snd p)).
  reflexivity.
Qed.

Definition heatmap_iou (r : nat) (p q : pixel) : nat :=
  if Nat.leb (pdist p q) r then 1 else 0.

Lemma heatmap_iou_sym :
  forall r p q, heatmap_iou r p q = heatmap_iou r q p.
Proof.
  intros r p q. unfold heatmap_iou.
  rewrite pdist_sym. reflexivity.
Qed.

Theorem heatmap_local_nms_collapse :
  forall (r theta : nat) (D : list (@det pixel)),
    NoDup D ->
    sorted_desc D ->
    one_peak (heatmap_iou r) 1 theta D ->
    no_tie_clash (heatmap_iou r) 1 D ->
    filter_above theta (nms_sorted (heatmap_iou r) 1 D) =
    filter_above theta D.
Proof.
  intros r theta D Hnd Hsd Hop Hntc.
  apply (nms_collapse_onepeak (heatmap_iou_sym r) Hnd Hsd Hop Hntc).
Qed.

(** ** Heatmap pixel separation entails [Separated]. If all distinct
    detections in [D] have pixel distance strictly greater than [r], then
    no pair has heatmap-IoU >= 1, so [Separated (heatmap_iou r) 1] holds
    vacuously for any [theta] and [slack]. *)

Lemma heatmap_pixel_separation :
  forall (r theta slack : nat) (D : list (@det pixel)),
    (forall d d', In d D -> In d' D -> d <> d' ->
       r < pdist (box d) (box d')) ->
    Separated (heatmap_iou r) 1 theta slack D.
Proof.
  intros r theta slack D Hsep d d' Hin Hin' Hne Hiou.
  exfalso.
  unfold heatmap_iou in Hiou.
  destruct (Nat.leb (pdist (box d) (box d')) r) eqn:E.
  - apply Nat.leb_le in E.
    specialize (Hsep d d' Hin Hin' Hne). lia.
  - inversion Hiou.
Qed.

(** ** Counterexample to the converse of [nms_collapse_onepeak]: equality
    of [filter_above (nms_sorted D)] and [filter_above D] does not imply
    [Separated 1 D]. The empty-filter case (no detections above [theta])
    trivially satisfies the equality but allows below-theta tied pairs that
    violate [Separated]. *)

Definition cex_D : list (@det nat) := [mkDet 0 1; mkDet 0 2].

Example converse_fails :
  NoDup cex_D /\
  sorted_desc cex_D /\
  filter_above 1 (nms_sorted triv_iou 50 cex_D) = filter_above 1 cex_D /\
  ~ Separated triv_iou 50 1 1 cex_D.
Proof.
  unfold cex_D. split; [|split; [|split]].
  - apply NoDup_cons.
    + simpl. intros [H | H]; [inversion H; lia | contradiction].
    + apply NoDup_cons; [simpl; intros H; contradiction | apply NoDup_nil].
  - simpl. split; [|split; [|exact I]].
    + intros d' [H | H]; [subst; simpl; lia | contradiction].
    + intros d' H; contradiction.
  - vm_compute. reflexivity.
  - intros Hsep.
    specialize (Hsep (mkDet 0 1) (mkDet 0 2)).
    assert (HinL : In (mkDet 0 1) [mkDet 0 1; mkDet 0 2]) by (simpl; auto).
    assert (HinR : In (mkDet 0 2) [mkDet 0 1; mkDet 0 2]) by (simpl; auto).
    assert (Hne : mkDet 0 1 <> mkDet 0 2) by (intro H; inversion H; lia).
    assert (Hiou : 50 <= triv_iou (box (mkDet 0 1)) (box (mkDet 0 2)))
      by (unfold triv_iou; lia).
    specialize (Hsep HinL HinR Hne Hiou).
    cbn in Hsep. lia.
Qed.

(** ** Mask-NMS (instance segmentation). *)

Section MaskNMS.

  Variable Mask : Type.

  Variable mask_size : Mask -> nat.

  Variable mask_inter_card : Mask -> Mask -> nat.
  Variable mask_union_card : Mask -> Mask -> nat.

  Hypothesis mask_inter_sym :
    forall m1 m2, mask_inter_card m1 m2 = mask_inter_card m2 m1.
  Hypothesis mask_union_sym :
    forall m1 m2, mask_union_card m1 m2 = mask_union_card m2 m1.

  Definition mask_iou (m1 m2 : Mask) : nat :=
    let i := mask_inter_card m1 m2 in
    let u := mask_union_card m1 m2 in
    if Nat.eqb u 0 then 0 else (i * 100) / u.

  Lemma mask_iou_sym :
    forall m1 m2, mask_iou m1 m2 = mask_iou m2 m1.
  Proof.
    intros m1 m2. unfold mask_iou.
    rewrite (mask_inter_sym m1 m2).
    rewrite (mask_union_sym m1 m2).
    reflexivity.
  Qed.

  Theorem mask_nms_collapse :
    forall (tau theta : nat) (D : list (@det Mask)),
      NoDup D ->
      sorted_desc D ->
      one_peak mask_iou tau theta D ->
      no_tie_clash mask_iou tau D ->
      filter_above theta (nms_sorted mask_iou tau D) =
      filter_above theta D.
  Proof.
    intros. apply (nms_collapse_onepeak mask_iou_sym); assumption.
  Qed.

End MaskNMS.

(** ** DETR post-hoc filtering (integer-coordinate boxes). *)

Definition ibox : Type := (nat * nat * nat * nat)%type.

Definition ibox_x1 (b : ibox) : nat := fst (fst (fst b)).
Definition ibox_y1 (b : ibox) : nat := snd (fst (fst b)).
Definition ibox_x2 (b : ibox) : nat := snd (fst b).
Definition ibox_y2 (b : ibox) : nat := snd b.

Definition ibox_area (b : ibox) : nat :=
  let w := ibox_x2 b - ibox_x1 b in
  let h := ibox_y2 b - ibox_y1 b in
  w * h.

Definition ibox_inter_area (a b : ibox) : nat :=
  let x1 := Nat.max (ibox_x1 a) (ibox_x1 b) in
  let y1 := Nat.max (ibox_y1 a) (ibox_y1 b) in
  let x2 := Nat.min (ibox_x2 a) (ibox_x2 b) in
  let y2 := Nat.min (ibox_y2 a) (ibox_y2 b) in
  let w := if Nat.leb x1 x2 then x2 - x1 else 0 in
  let h := if Nat.leb y1 y2 then y2 - y1 else 0 in
  w * h.

Definition ibox_iou (a b : ibox) : nat :=
  let inter := ibox_inter_area a b in
  let union := ibox_area a + ibox_area b - inter in
  if Nat.eqb union 0 then 0 else (inter * 100) / union.

Lemma ibox_inter_area_sym : forall a b, ibox_inter_area a b = ibox_inter_area b a.
Proof.
  intros a b. unfold ibox_inter_area.
  rewrite (Nat.max_comm (ibox_x1 a)).
  rewrite (Nat.max_comm (ibox_y1 a)).
  rewrite (Nat.min_comm (ibox_x2 a)).
  rewrite (Nat.min_comm (ibox_y2 a)).
  reflexivity.
Qed.

Lemma ibox_iou_sym : forall a b, ibox_iou a b = ibox_iou b a.
Proof.
  intros a b. unfold ibox_iou.
  rewrite (ibox_inter_area_sym a b).
  replace (ibox_area a + ibox_area b) with (ibox_area b + ibox_area a) by lia.
  reflexivity.
Qed.

Theorem detr_collapse :
  forall (tau theta : nat) (D : list (@det ibox)),
    NoDup D ->
    sorted_desc D ->
    one_peak ibox_iou tau theta D ->
    no_tie_clash ibox_iou tau D ->
    filter_above theta (nms_sorted ibox_iou tau D) =
    filter_above theta D.
Proof.
  intros. apply (nms_collapse_onepeak ibox_iou_sym); assumption.
Qed.
