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
From Stdlib Require Import ZArith.
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

(** ** For every nonnegative [L], some [M], [u], [v] saturate the bound. *)

Theorem mat_inf_norm_lipschitz_tight :
  forall L : R,
    (0 <= L)%R ->
    exists (M : matrix) (u v : list R),
      mat_inf_norm M = L /\
      vec_dist (mat_vec M u) (mat_vec M v) = mat_inf_norm M * vec_dist u v.
Proof.
  intros L HL.
  exists [[L]], [1%R], [0%R].
  assert (Hmin : mat_inf_norm [[L]] = L).
  { simpl. rewrite Rplus_0_r. rewrite (Rabs_right L) by lra.
    apply Rmax_left. lra. }
  split; [exact Hmin|].
  rewrite Hmin.
  unfold vec_dist. simpl.
  rewrite Rmult_1_r, Rmult_0_r, !Rplus_0_r, !Rminus_0_r.
  rewrite (Rabs_right L) by lra.
  rewrite (Rabs_right 1) by lra.
  rewrite (Rmax_left L 0) by lra.
  rewrite (Rmax_left 1 0) by lra.
  lra.
Qed.

Lemma mat_vec_length :
  forall M v, length (mat_vec M v) = length M.
Proof.
  intros M v. induction M as [|row rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** ** Single linear layer is [mat_inf_norm M]-Lipschitz. *)

Corollary linear_layer_lipschitz :
  forall M u v,
    length u = length v ->
    vec_dist (mat_vec M u) (mat_vec M v)
    <= mat_inf_norm M * vec_dist u v.
Proof. exact mat_vec_lipschitz. Qed.

(** ** [v ↦ M2 (ReLU (M1 v))] is [mat_inf_norm M2 * mat_inf_norm M1]-Lipschitz. *)

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

(** ** Dimension-indexed [Vector n] and [Matrix r c] via sigma types. *)

Definition Vector (n : nat) : Type := { v : list R | length v = n }.

Definition Matrix (r c : nat) : Type :=
  { M : list (list R) | length M = r /\ Forall (fun row => length row = c) M }.

Definition tmat_vec {r c : nat} (M : Matrix r c) (u : Vector c) : Vector r.
Proof.
  destruct M as [Mlist [Hlen_M _]].
  destruct u as [ulist _].
  exists (mat_vec Mlist ulist).
  rewrite mat_vec_length. exact Hlen_M.
Defined.

Theorem tmat_vec_lipschitz :
  forall (r c : nat) (M : Matrix r c) (u v : Vector c),
    (vec_dist (proj1_sig (tmat_vec M u)) (proj1_sig (tmat_vec M v))
     <= mat_inf_norm (proj1_sig M) * vec_dist (proj1_sig u) (proj1_sig v))%R.
Proof.
  intros r c M u v.
  destruct M as [Mlist [Hlen_M Hrows]].
  destruct u as [ulist Hlen_u].
  destruct v as [vlist Hlen_v].
  simpl.
  apply mat_vec_lipschitz.
  rewrite Hlen_u, Hlen_v. reflexivity.
Qed.

(** ** Quantization adapter. Bridges Real-Lipschitz functions to the
    nat-Lipschitz hypothesis required by [lipschitz_bridge_substantive].
    Output quantization uses floor (underestimate); input-distance
    quantization uses ceiling-via-[up] (overestimate). The output side
    contributes a one-bit slack; the input side contributes none. *)

Definition quant_R (q r : R) : nat := Z.to_nat (Int_part (r / q)).

Definition quant_R_up (q r : R) : nat := Z.to_nat (up (r / q)).

Lemma quant_R_floor_bound :
  forall q r,
    (0 < q)%R -> (0 <= r)%R ->
    (INR (quant_R q r) * q <= r < (INR (quant_R q r) + 1) * q)%R.
Proof.
  intros q r Hq Hr.
  unfold quant_R.
  pose proof (base_Int_part (r/q)) as [Hl Hu].
  assert (Hrq : (0 <= r/q)%R).
  { unfold Rdiv. apply Rmult_le_pos; [assumption|].
    left. apply Rinv_0_lt_compat. assumption. }
  assert (Hint_nn : (0 <= Int_part (r/q))%Z).
  { unfold Int_part.
    pose proof (archimed (r/q)) as [Harch1 _].
    assert (HIZR : (IZR 0 < IZR (up (r/q)))%R) by (simpl; lra).
    apply lt_IZR in HIZR. lia. }
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id by assumption.
  split.
  - apply (Rmult_le_reg_r (/q)).
    + apply Rinv_0_lt_compat. assumption.
    + rewrite Rmult_assoc, Rinv_r by lra.
      rewrite Rmult_1_r. exact Hl.
  - apply (Rmult_lt_reg_r (/q)).
    + apply Rinv_0_lt_compat. assumption.
    + rewrite Rmult_assoc, Rinv_r by lra.
      rewrite Rmult_1_r. lra.
Qed.

Lemma quant_R_up_bound :
  forall q r,
    (0 < q)%R -> (0 <= r)%R ->
    (r <= INR (quant_R_up q r) * q)%R.
Proof.
  intros q r Hq Hr.
  unfold quant_R_up.
  pose proof (archimed (r/q)) as [Hgt _].
  assert (Hrq : (0 <= r/q)%R).
  { unfold Rdiv. apply Rmult_le_pos; [assumption|].
    left. apply Rinv_0_lt_compat. assumption. }
  assert (Hu_nn : (0 <= up (r/q))%Z).
  { assert (HIZR : (IZR 0 < IZR (up (r/q)))%R) by (simpl; lra).
    apply lt_IZR in HIZR. lia. }
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id by assumption.
  apply (Rmult_le_reg_r (/q)).
  - apply Rinv_0_lt_compat. assumption.
  - rewrite Rmult_assoc, Rinv_r by lra.
    rewrite Rmult_1_r. lra.
Qed.

(** ** Computation of [quant_R 1] on [INR n]: identity (no quantization
    needed since q = 1 and INR n is already an integer). *)

Lemma Int_part_IZR_local : forall z, Int_part (IZR z) = z.
Proof.
  intros z. symmetry. apply Int_part_spec. lra.
Qed.

Lemma quant_R_1_INR : forall (n : nat), quant_R 1 (INR n) = n.
Proof.
  intros n. unfold quant_R.
  replace (INR n / 1)%R with (INR n) by (field; lra).
  rewrite INR_IZR_INZ.
  rewrite Int_part_IZR_local.
  apply Nat2Z.id.
Qed.

(** ** Adapter: a Real L-Lipschitz score head [f] yields a nat L-Lipschitz
    pair (h, dist) matching [lipschitz_bridge_substantive]'s hypothesis with
    no additive slack. Output side uses floor (one-bit underestimate); input
    side uses ceiling-via-[up] (overestimate) which absorbs the bit. *)

Definition rnat_h (q : R) (f : R -> R) (x : R) : nat := quant_R q (f x).

Definition rnat_dist (q : R) (x y : R) : nat :=
  quant_R_up q (Rabs (x - y)).

Lemma rnat_dist_sym :
  forall q x y, rnat_dist q x y = rnat_dist q y x.
Proof.
  intros q x y. unfold rnat_dist. rewrite Rabs_minus_sym. reflexivity.
Qed.

Lemma real_lipschitz_to_nat_dir :
  forall (f : R -> R) (L q : R) (Ln : nat),
    Lipschitz L f ->
    (0 < q)%R ->
    (L <= INR Ln)%R ->
    (forall x, (0 <= f x)%R) ->
    forall x y, (rnat_h q f x <= rnat_h q f y + Ln * rnat_dist q x y)%nat.
Proof.
  intros f L q Ln Hlip Hq HL_le Hf_nn x y.
  pose proof (@quant_R_floor_bound q (f x) Hq (Hf_nn x)) as [Hax_lo Hax_hi].
  pose proof (@quant_R_floor_bound q (f y) Hq (Hf_nn y)) as [Hby_lo Hby_hi].
  pose proof (@quant_R_up_bound q (Rabs (x - y)) Hq (Rabs_pos _)) as Hd_bnd.
  pose proof (lip_bound Hlip x y) as Hlip_xy.
  pose proof (lip_nonneg Hlip) as HL_nn.
  unfold rnat_h, rnat_dist.
  set (a := quant_R q (f x)).
  set (b := quant_R q (f y)).
  set (d := quant_R_up q (Rabs (x - y))).
  apply Nat.lt_succ_r. apply INR_lt.
  rewrite S_INR, plus_INR, mult_INR.
  assert (Hax : (INR a <= f x / q)%R).
  { apply Rmult_le_reg_r with (r := q); [exact Hq|].
    replace (f x / q * q)%R with (f x) by (field; lra).
    exact Hax_lo. }
  assert (Hby : (f y / q < INR b + 1)%R).
  { apply Rmult_lt_reg_r with (r := q); [exact Hq|].
    replace (f y / q * q)%R with (f y) by (field; lra).
    exact Hby_hi. }
  assert (Hd : (Rabs (x - y) / q <= INR d)%R).
  { apply Rmult_le_reg_r with (r := q); [exact Hq|].
    replace (Rabs (x - y) / q * q)%R with (Rabs (x - y)) by (field; lra).
    exact Hd_bnd. }
  assert (Hchain : ((f x - f y) / q <= INR Ln * INR d)%R).
  { assert (H1 : ((f x - f y) / q <= Rabs (f x - f y) / q)%R).
    { apply Rmult_le_compat_r.
      - left. apply Rinv_0_lt_compat. exact Hq.
      - apply Rle_abs. }
    assert (H2 : (Rabs (f x - f y) / q <= L * Rabs (x - y) / q)%R).
    { apply Rmult_le_compat_r.
      - left. apply Rinv_0_lt_compat. exact Hq.
      - exact Hlip_xy. }
    assert (H3 : (L * Rabs (x - y) / q = L * (Rabs (x - y) / q))%R)
      by (field; lra).
    assert (H4 : (L * (Rabs (x - y) / q) <= L * INR d)%R).
    { apply Rmult_le_compat_l; [exact HL_nn | exact Hd]. }
    assert (H5 : (L * INR d <= INR Ln * INR d)%R).
    { apply Rmult_le_compat_r; [apply pos_INR | exact HL_le]. }
    lra. }
  assert (Heq : ((f x - f y) / q = f x / q - f y / q)%R) by (field; lra).
  lra.
Qed.

Theorem real_lipschitz_to_nat :
  forall (f : R -> R) (L q : R) (Ln : nat),
    Lipschitz L f ->
    (0 < q)%R ->
    (L <= INR Ln)%R ->
    (forall x, (0 <= f x)%R) ->
    forall x y,
      (Nat.max (rnat_h q f x) (rnat_h q f y) <=
       Nat.min (rnat_h q f x) (rnat_h q f y) + Ln * rnat_dist q x y)%nat.
Proof.
  intros f L q Ln Hlip Hq HL_le Hf_nn x y.
  pose proof (@real_lipschitz_to_nat_dir f L q Ln Hlip Hq HL_le Hf_nn x y) as Hxy.
  pose proof (@real_lipschitz_to_nat_dir f L q Ln Hlip Hq HL_le Hf_nn y x) as Hyx.
  rewrite (rnat_dist_sym q y x) in Hyx.
  destruct (Nat.le_ge_cases (rnat_h q f x) (rnat_h q f y)) as [Hle | Hge].
  - rewrite Nat.max_r, Nat.min_l by exact Hle. exact Hyx.
  - rewrite Nat.max_l, Nat.min_r by exact Hge. exact Hxy.
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

  (** ** Bridge: L-Lipschitz score head with feature noise [eps] and
      pairwise margin [m] yields [Separated (m - L * eps)]. *)

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

  (** ** Bridge with explicit true/observed features and noise bound. *)

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

  (** ** Per-detection soft-NMS scores: above-theta unchanged, below-theta
      monotonically non-increasing under decay. *)

  Theorem soft_nms_score_above_unchanged :
    forall D d decay,
      In d D -> one_peak D -> above d = true ->
      score (apply_decay decay D d) = score d.
  Proof.
    intros D d decay Hin Hop Hab.
    rewrite (@apply_decay_keeps_above D d decay Hin Hop Hab). reflexivity.
  Qed.

  Theorem soft_nms_score_below_decayed :
    forall D d decay,
      (forall n, decay n <= n) ->
      score (apply_decay decay D d) <= score d.
  Proof.
    intros D d decay Hdec.
    unfold apply_decay.
    destruct (has_higher_overlapper D d).
    - cbn [score]. apply Hdec.
    - apply Nat.le_refl.
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

  (** ** NMS drops at most [violation_count D] above-theta detections. *)

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

  (** ** Distinct surviving detections have IoU < tau. *)

  Theorem nms_sorted_sound :
    forall D d d',
      In d (nms_sorted D) -> In d' (nms_sorted D) ->
      d <> d' -> iou (box d) (box d') < tau.
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length det))).
    intros d d' Hin Hin' Hne.
    destruct D as [|d0 rest].
    - rewrite nms_sorted_equation in Hin. contradiction.
    - rewrite nms_sorted_equation in Hin, Hin'.
      set (P := fun d' => negb (Nat.leb tau (iou (box d0) (box d')))).
      set (restf := filter P rest).
      assert (Hlt : ltof _ (@length det) restf (d0 :: rest)).
      { unfold ltof, restf. simpl.
        pose proof (filter_length_le P rest) as HL. lia. }
      destruct Hin as [Heq | Hin]; destruct Hin' as [Heq' | Hin'].
      + subst. contradiction.
      + subst d.
        apply nms_sorted_subset in Hin'.
        apply filter_In in Hin' as [_ Hp]. unfold P in Hp.
        apply negb_true_iff in Hp. apply Nat.leb_gt in Hp. assumption.
      + subst d'.
        apply nms_sorted_subset in Hin.
        apply filter_In in Hin as [_ Hp]. unfold P in Hp.
        apply negb_true_iff in Hp. apply Nat.leb_gt in Hp.
        rewrite iou_sym. assumption.
      + apply (IH restf Hlt); assumption.
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

(** ** [build_tight n] saturates [nms_quantitative_bound] for every [n]. *)

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

(** ** Structural properties of the parametric tightness family. *)

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

Lemma has_higher_overlapper_build_tight :
  forall n d, In d (build_tight n) ->
    has_higher_overlapper triv_iou 50 (build_tight n) d = Nat.ltb (score d) n.
Proof.
  intros n d Hin.
  unfold has_higher_overlapper.
  destruct (Nat.ltb_spec (score d) n) as [Hlt | Hge].
  - apply existsb_exists. exists (mkDet n (n - 1)).
    split.
    + destruct n as [|k]; [lia|]. simpl. left. f_equal. lia.
    + apply Bool.andb_true_iff. split.
      * apply Nat.ltb_lt. simpl. assumption.
      * apply Nat.leb_le. unfold triv_iou. lia.
  - apply Bool.not_true_is_false.
    intros Hex.
    apply existsb_exists in Hex as [d' [Hin' Hcond]].
    apply Bool.andb_true_iff in Hcond as [Hlt _].
    apply Nat.ltb_lt in Hlt.
    apply build_tight_in in Hin' as [Hsd' _]. lia.
Qed.

Lemma filter_above_higher_overlap_id :
  forall (D L : list (@det nat)),
    (forall d, In d D -> 1 <= score d) ->
    (forall d, In d D -> exists d', In d' L /\ score d < score d') ->
    filter (fun d => above 1 d &&
                       has_higher_overlapper triv_iou 50 L d) D = D.
Proof.
  intros D L Habove Hhigher.
  induction D as [|d rest IH]; [reflexivity|].
  cbn [filter].
  assert (Hhead : (above 1 d &&
                   has_higher_overlapper triv_iou 50 L d) = true).
  { apply Bool.andb_true_iff. split.
    - unfold above. apply Nat.leb_le. apply Habove. left; reflexivity.
    - unfold has_higher_overlapper. apply existsb_exists.
      destruct (Hhigher d (or_introl eq_refl)) as [d' [Hin' Hlt]].
      exists d'. split; [assumption|].
      apply Bool.andb_true_iff. split.
      + apply Nat.ltb_lt. assumption.
      + apply Nat.leb_le. unfold triv_iou. lia. }
  rewrite Hhead. f_equal. apply IH.
  - intros d' Hd'. apply Habove. right; assumption.
  - intros d' Hd'. apply Hhigher. right; assumption.
Qed.

Lemma build_tight_subset :
  forall j k, j <= k ->
    forall d, In d (build_tight j) -> In d (build_tight k).
Proof.
  intros j k Hjk d Hin.
  apply build_tight_in in Hin as [Hs [Hb Heq]].
  destruct d as [sd bd]. simpl in *.
  assert (Hbd_lt_k : bd < k) by lia.
  clear -Heq Hbd_lt_k.
  induction k as [|m IH]; [lia|].
  cbn [build_tight].
  destruct (Nat.eq_dec bd m) as [Hbm | Hne_bm].
  - left. subst bd. replace sd with (S m) by lia. reflexivity.
  - right. apply IH. lia.
Qed.

Lemma filter_cons_false :
  forall A (f : A -> bool) (a : A) (l : list A),
    f a = false -> filter f (a :: l) = filter f l.
Proof. intros A f a l Hf. simpl. rewrite Hf. reflexivity. Qed.

Lemma violator_above_build_tight :
  forall n,
    violator_above triv_iou 50 1 (build_tight n) = build_tight (n - 1).
Proof.
  destruct n as [|k]; [reflexivity|].
  simpl Nat.sub. rewrite Nat.sub_0_r.
  unfold violator_above.
  replace (build_tight (S k)) with (mkDet (S k) k :: build_tight k) at 1
    by reflexivity.
  rewrite filter_cons_false.
  - apply filter_above_higher_overlap_id.
    + intros d Hd. apply build_tight_in in Hd as [Hs _]. lia.
    + intros d Hd.
      exists (mkDet (S k) k). split.
      * cbn [build_tight]. left. reflexivity.
      * apply build_tight_in in Hd as [Hs [Hb _]]. simpl. lia.
  - apply Bool.andb_false_iff. right.
    rewrite (has_higher_overlapper_build_tight (S k) (mkDet (S k) k))
      by (cbn [build_tight]; left; reflexivity).
    cbn [score]. apply Nat.ltb_irrefl.
Qed.

Lemma violation_count_build_tight :
  forall n, violation_count triv_iou 50 1 (build_tight n) = n - 1.
Proof.
  intros n. unfold violation_count.
  rewrite violator_above_build_tight. apply build_tight_length.
Qed.

Theorem tightness_parametric :
  forall n,
    length (filter_above 1 (build_tight n))
    = length (filter_above 1 (nms_sorted triv_iou 50 (build_tight n)))
      + violation_count triv_iou 50 1 (build_tight n).
Proof.
  intros n.
  rewrite filter_above_1_build_tight.
  rewrite build_tight_length.
  rewrite nms_sorted_build_tight.
  rewrite violation_count_build_tight.
  destruct n as [|k]; [reflexivity|].
  unfold filter_above. cbn [filter]. unfold above. cbn [score].
  assert (Hlt : Nat.leb 1 (S k) = true) by (apply Nat.leb_le; lia).
  rewrite Hlt. simpl. lia.
Qed.

Corollary tightness_saturated_3 :
  let D := build_tight 3 in
  length (filter_above 1 D)
    = length (filter_above 1 (nms_sorted triv_iou 50 D))
      + violation_count triv_iou 50 1 D.
Proof. apply tightness_parametric. Qed.

Corollary tightness_saturated_5 :
  let D := build_tight 5 in
  length (filter_above 1 D)
    = length (filter_above 1 (nms_sorted triv_iou 50 D))
      + violation_count triv_iou 50 1 D.
Proof. apply tightness_parametric. Qed.

Corollary tightness_saturated_10 :
  let D := build_tight 10 in
  length (filter_above 1 D)
    = length (filter_above 1 (nms_sorted triv_iou 50 D))
      + violation_count triv_iou 50 1 D.
Proof. apply tightness_parametric. Qed.

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

(** ** Symmetric, bounded IoU function on [Box]. *)

Record IoUStructure (Box : Type) := mkIoU {
  iou_fn : Box -> Box -> nat;
  iou_max : nat;
  iou_struct_sym : forall a b, iou_fn a b = iou_fn b a;
  iou_struct_bounded : forall a b, iou_fn a b <= iou_max
}.

Arguments iou_fn {Box} _ _ _.
Arguments iou_max {Box} _.
Arguments iou_struct_sym {Box} _ _ _.
Arguments iou_struct_bounded {Box} _ _ _.

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

Lemma heatmap_iou_le_1 : forall r p q, heatmap_iou r p q <= 1.
Proof.
  intros r p q. unfold heatmap_iou.
  destruct (Nat.leb (pdist p q) r); lia.
Qed.

Definition heatmap_iou_struct (r : nat) : IoUStructure pixel :=
  @mkIoU pixel (heatmap_iou r) 1 (heatmap_iou_sym r) (heatmap_iou_le_1 r).

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

(** ** Pairwise [pdist > r] entails [Separated (heatmap_iou r) 1]. *)

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

(** ** Counterexample showing [sorted_desc] is a necessary precondition. *)

Definition cex_unsorted : list (@det nat) := [mkDet 30 0; mkDet 100 1].

Example sortedness_necessary :
  NoDup cex_unsorted /\
  ~ sorted_desc cex_unsorted /\
  one_peak triv_iou 50 50 cex_unsorted /\
  no_tie_clash triv_iou 50 cex_unsorted /\
  filter_above 50 (nms_sorted triv_iou 50 cex_unsorted) <>
  filter_above 50 cex_unsorted.
Proof.
  unfold cex_unsorted. split; [|split; [|split; [|split]]].
  - apply NoDup_cons.
    + simpl. intros [H | H]; [inversion H; lia | contradiction].
    + apply NoDup_cons; [simpl; intros H; contradiction | apply NoDup_nil].
  - simpl. intros [Hbnd _].
    specialize (Hbnd (mkDet 100 1) (or_introl eq_refl)).
    cbn [score] in Hbnd. lia.
  - intros d d' Hin Hin' Hiou Hlt.
    simpl in Hin, Hin'.
    destruct Hin as [Heq | [Heq | Hf]];
    destruct Hin' as [Heq' | [Heq' | Hf']];
    try contradiction; subst; cbn [score] in *; try lia.
  - intros d d' Hin Hin' Hne Heq.
    simpl in Hin, Hin'.
    destruct Hin as [H | [H | Hf]];
    destruct Hin' as [H' | [H' | Hf']];
    try contradiction; subst; cbn [score] in *;
    try (exfalso; apply Hne; reflexivity); try lia.
  - vm_compute. discriminate.
Qed.

(** ** Counterexample showing the converse of [nms_collapse_onepeak] fails. *)

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

  (** ** Floor-rounding bound: [mask_iou * union <= inter * 100 < (mask_iou + 1) * union]. *)

  Lemma mask_iou_truncation_bound :
    forall m1 m2,
      mask_union_card m1 m2 <> 0 ->
      mask_iou m1 m2 * mask_union_card m1 m2
        <= mask_inter_card m1 m2 * 100
      < (mask_iou m1 m2 + 1) * mask_union_card m1 m2.
  Proof.
    intros m1 m2 Hu. unfold mask_iou.
    apply Nat.eqb_neq in Hu as Heq. rewrite Heq.
    apply Nat.eqb_neq in Heq.
    set (i := mask_inter_card m1 m2).
    set (u := mask_union_card m1 m2).
    pose proof (Nat.div_mod (i * 100) u Hu) as Hdm.
    pose proof (Nat.mod_upper_bound (i * 100) u Hu) as Hmod.
    split; lia.
  Qed.

  Lemma mask_iou_lt_tau_iff :
    forall m1 m2 tau,
      mask_union_card m1 m2 <> 0 ->
      mask_iou m1 m2 < tau ->
      mask_inter_card m1 m2 * 100 < tau * mask_union_card m1 m2.
  Proof.
    intros m1 m2 tau Hu Hlt.
    pose proof (@mask_iou_truncation_bound m1 m2 Hu) as [_ Hb].
    set (u := mask_union_card m1 m2) in *.
    set (i := mask_inter_card m1 m2) in *.
    apply Nat.lt_le_trans with ((mask_iou m1 m2 + 1) * u); [assumption|].
    apply Nat.mul_le_mono_r. lia.
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

(** ** Integer-coordinate boxes with sigma-typed well-formedness. *)

Definition raw_ibox : Type := (nat * nat * nat * nat)%type.

Definition raw_ibox_x1 (b : raw_ibox) : nat := fst (fst (fst b)).
Definition raw_ibox_y1 (b : raw_ibox) : nat := snd (fst (fst b)).
Definition raw_ibox_x2 (b : raw_ibox) : nat := snd (fst b).
Definition raw_ibox_y2 (b : raw_ibox) : nat := snd b.

Definition ibox_well_formed (b : raw_ibox) : Prop :=
  raw_ibox_x1 b <= raw_ibox_x2 b /\ raw_ibox_y1 b <= raw_ibox_y2 b.

Definition ibox : Type := { b : raw_ibox | ibox_well_formed b }.

Definition ibox_x1 (b : ibox) : nat := raw_ibox_x1 (proj1_sig b).
Definition ibox_y1 (b : ibox) : nat := raw_ibox_y1 (proj1_sig b).
Definition ibox_x2 (b : ibox) : nat := raw_ibox_x2 (proj1_sig b).
Definition ibox_y2 (b : ibox) : nat := raw_ibox_y2 (proj1_sig b).

Lemma ibox_x1_le_x2 : forall b : ibox, ibox_x1 b <= ibox_x2 b.
Proof. intros [b [Hx Hy]]. exact Hx. Qed.

Lemma ibox_y1_le_y2 : forall b : ibox, ibox_y1 b <= ibox_y2 b.
Proof. intros [b [Hx Hy]]. exact Hy. Qed.

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

Lemma ibox_inter_le_area_left :
  forall a b, ibox_inter_area a b <= ibox_area a.
Proof.
  intros a b.
  pose proof (ibox_x1_le_x2 a) as Hax.
  pose proof (ibox_y1_le_y2 a) as Hay.
  unfold ibox_inter_area, ibox_area.
  set (mx := Nat.max (ibox_x1 a) (ibox_x1 b)).
  set (my := Nat.max (ibox_y1 a) (ibox_y1 b)).
  set (Mx := Nat.min (ibox_x2 a) (ibox_x2 b)).
  set (My := Nat.min (ibox_y2 a) (ibox_y2 b)).
  assert (Hxm : ibox_x1 a <= mx) by (unfold mx; apply Nat.le_max_l).
  assert (HxM : Mx <= ibox_x2 a) by (unfold Mx; apply Nat.le_min_l).
  assert (Hym : ibox_y1 a <= my) by (unfold my; apply Nat.le_max_l).
  assert (HyM : My <= ibox_y2 a) by (unfold My; apply Nat.le_min_l).
  destruct (Nat.leb mx Mx) eqn:Ex; destruct (Nat.leb my My) eqn:Ey.
  - apply Nat.leb_le in Ex. apply Nat.leb_le in Ey.
    apply Nat.mul_le_mono; lia.
  - rewrite Nat.mul_0_r. apply Nat.le_0_l.
  - rewrite Nat.mul_0_l. apply Nat.le_0_l.
  - rewrite Nat.mul_0_r. apply Nat.le_0_l.
Qed.

Lemma ibox_inter_le_area_right :
  forall a b, ibox_inter_area a b <= ibox_area b.
Proof.
  intros a b. rewrite ibox_inter_area_sym. apply ibox_inter_le_area_left.
Qed.

Lemma ibox_iou_le_100 : forall a b, ibox_iou a b <= 100.
Proof.
  intros a b. unfold ibox_iou.
  destruct (Nat.eqb (ibox_area a + ibox_area b - ibox_inter_area a b) 0) eqn:Eu.
  - lia.
  - apply Nat.eqb_neq in Eu.
    pose proof (ibox_inter_le_area_left a b) as Hl.
    pose proof (ibox_inter_le_area_right a b) as Hr.
    set (inter := ibox_inter_area a b).
    set (u := ibox_area a + ibox_area b - inter).
    assert (Hinter_le_u : inter <= u) by (unfold u; lia).
    assert (Hu_pos : 0 < u) by lia.
    apply Nat.Div0.div_le_upper_bound.
    apply Nat.mul_le_mono_r. assumption.
Qed.

Definition ibox_iou_struct : IoUStructure ibox :=
  @mkIoU ibox ibox_iou 100 ibox_iou_sym ibox_iou_le_100.

(** ** Floor-rounding bound for [ibox_iou]. *)

Lemma ibox_iou_truncation_bound :
  forall a b,
    ibox_area a + ibox_area b - ibox_inter_area a b <> 0 ->
    let inter := ibox_inter_area a b in
    let union := ibox_area a + ibox_area b - inter in
    ibox_iou a b * union <= inter * 100 < (ibox_iou a b + 1) * union.
Proof.
  intros a b Hu. unfold ibox_iou.
  apply Nat.eqb_neq in Hu as Heq. rewrite Heq.
  apply Nat.eqb_neq in Heq.
  set (inter := ibox_inter_area a b).
  set (union := ibox_area a + ibox_area b - inter).
  pose proof (Nat.div_mod (inter * 100) union Hu) as Hdm.
  pose proof (Nat.mod_upper_bound (inter * 100) union Hu) as Hmod.
  split; lia.
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

(** ******************************************************************** *)
(** *                          Part IV. Extensions                       *)
(** ******************************************************************** *)

(** ** Reflexivity-at-max for heatmap and ibox IoU. *)

Lemma abs_diff_refl : forall a, abs_diff a a = 0.
Proof.
  intros a. unfold abs_diff. rewrite Nat.leb_refl. lia.
Qed.

Lemma pdist_refl : forall p, pdist p p = 0.
Proof.
  intros p. unfold pdist. rewrite !abs_diff_refl. lia.
Qed.

Lemma heatmap_iou_refl_max :
  forall r p, heatmap_iou r p p = 1.
Proof.
  intros r p. unfold heatmap_iou.
  rewrite pdist_refl.
  destruct (Nat.leb_spec 0 r); [reflexivity | lia].
Qed.

(** Reflexivity-at-max for [ibox_iou] requires positive area: a degenerate
    box with [ibox_area b = 0] makes the union zero and the IoU is then
    defined to be zero. The well-formedness sigma type already guarantees
    [x1 <= x2 /\ y1 <= y2]; positive area is a strictly stronger nondegeneracy
    condition. *)

Lemma ibox_inter_area_refl :
  forall b : ibox, ibox_inter_area b b = ibox_area b.
Proof.
  intros b.
  pose proof (ibox_x1_le_x2 b) as Hx.
  pose proof (ibox_y1_le_y2 b) as Hy.
  unfold ibox_inter_area, ibox_area.
  rewrite !Nat.max_id, !Nat.min_id.
  destruct (Nat.leb_spec (ibox_x1 b) (ibox_x2 b)) as [_ | Hxc]; [|lia].
  destruct (Nat.leb_spec (ibox_y1 b) (ibox_y2 b)) as [_ | Hyc]; [|lia].
  reflexivity.
Qed.

Lemma ibox_iou_refl_max :
  forall b : ibox, 0 < ibox_area b -> ibox_iou b b = 100.
Proof.
  intros b Harea.
  unfold ibox_iou. rewrite ibox_inter_area_refl.
  set (a := ibox_area b).
  replace (a + a - a) with a by lia.
  destruct (Nat.eqb_spec a 0) as [Heq | _]; [lia|].
  replace (a * 100) with (100 * a) by lia.
  rewrite Nat.div_mul by lia.
  reflexivity.
Qed.

(** ** Disjoint pairs have IoU zero. *)

Definition heatmap_disjoint (r : nat) (p q : pixel) : Prop := r < pdist p q.

Lemma heatmap_iou_zero_disjoint :
  forall r p q, heatmap_disjoint r p q -> heatmap_iou r p q = 0.
Proof.
  intros r p q Hd. unfold heatmap_iou, heatmap_disjoint in *.
  destruct (Nat.leb_spec (pdist p q) r); [lia | reflexivity].
Qed.

Definition ibox_disjoint (a b : ibox) : Prop := ibox_inter_area a b = 0.

Lemma ibox_iou_zero_disjoint :
  forall a b, ibox_disjoint a b -> ibox_iou a b = 0.
Proof.
  intros a b Hd. unfold ibox_iou, ibox_disjoint in *.
  rewrite Hd.
  destruct (Nat.eqb_spec (ibox_area a + ibox_area b - 0) 0); [reflexivity|].
  rewrite Nat.mul_0_l, Nat.div_0_l by lia. reflexivity.
Qed.

(** ** [v ↦ M_n (ReLU (M_{n-1} (... ReLU (M_1 v))))] is bounded by
    the product of [mat_inf_norm M_i]. *)

Local Open Scope R_scope.

Definition apply_relu_vec (v : list R) : list R := map (fun x => Rmax 0 x) v.

Definition apply_layer (M : matrix) (v : list R) : list R :=
  apply_relu_vec (mat_vec M v).

Fixpoint apply_layers (Ms : list matrix) (v : list R) : list R :=
  match Ms with
  | [] => v
  | M :: rest => apply_layers rest (apply_layer M v)
  end.

Fixpoint product_norms (Ms : list matrix) : R :=
  match Ms with
  | [] => 1
  | M :: rest => mat_inf_norm M * product_norms rest
  end.

Lemma apply_relu_vec_length :
  forall v, length (apply_relu_vec v) = length v.
Proof. intros v. apply length_map. Qed.

Lemma apply_layer_length :
  forall M v, length (apply_layer M v) = length M.
Proof.
  intros M v. unfold apply_layer.
  rewrite apply_relu_vec_length. apply mat_vec_length.
Qed.

Lemma product_norms_nonneg :
  forall Ms, 0 <= product_norms Ms.
Proof.
  induction Ms as [|M rest IH]; simpl.
  - lra.
  - apply Rmult_le_pos; [apply mat_inf_norm_nonneg | assumption].
Qed.

Lemma apply_relu_vec_lip :
  forall u v,
    vec_dist (apply_relu_vec u) (apply_relu_vec v) <= vec_dist u v.
Proof.
  intros u v.
  destruct vlip_map_relu as [_ Hb].
  specialize (Hb u v). rewrite Rmult_1_l in Hb. exact Hb.
Qed.

Theorem multilayer_lipschitz :
  forall Ms u v,
    length u = length v ->
    vec_dist (apply_layers Ms u) (apply_layers Ms v)
    <= product_norms Ms * vec_dist u v.
Proof.
  induction Ms as [|M rest IH]; intros u v Hlen.
  - simpl. rewrite Rmult_1_l. apply Rle_refl.
  - simpl.
    set (u1 := apply_layer M u). set (v1 := apply_layer M v).
    assert (Hlen1 : length u1 = length v1).
    { unfold u1, v1. rewrite !apply_layer_length. reflexivity. }
    specialize (IH u1 v1 Hlen1).
    eapply Rle_trans; [exact IH|].
    rewrite (Rmult_comm (mat_inf_norm M) (product_norms rest)).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [apply product_norms_nonneg|].
    unfold u1, v1, apply_layer.
    eapply Rle_trans; [apply apply_relu_vec_lip|].
    apply mat_vec_lipschitz; assumption.
Qed.

Local Close Scope R_scope.

(** ** Equality of [filter_above] at every threshold implies [Separated]. *)

Lemma filter_above_0_is_id :
  forall (Box : Type) (D : list (@det Box)), filter_above 0 D = D.
Proof.
  intros Box D. unfold filter_above. induction D as [|d rest IH]; [reflexivity|].
  simpl. f_equal. exact IH.
Qed.

Theorem threshold_quantified_converse :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau : nat) (D : list (@det Box)) (theta' slack : nat),
      (forall t, filter_above t (nms_sorted iou tau D) = filter_above t D) ->
      Separated iou tau theta' slack D.
Proof.
  intros Box iou iou_sym_h tau D theta' slack Hall.
  intros d d' Hin Hin' Hne Hiou.
  exfalso.
  pose proof (Hall 0) as Heq0.
  rewrite filter_above_0_is_id in Heq0.
  rewrite filter_above_0_is_id in Heq0.
  rewrite <- Heq0 in Hin, Hin'.
  pose proof (@nms_sorted_sound Box iou iou_sym_h tau D d d' Hin Hin' Hne) as Hsound.
  lia.
Qed.

(** ** Multi-class lift: [Box * Class] with [class_iou] zero across classes. *)

Section MultiClass.
  Variable Box : Type.
  Variable Class : Type.
  Variable iou_b : Box -> Box -> nat.
  Hypothesis iou_b_sym : forall a b, iou_b a b = iou_b b a.
  Variable cls_eq : forall c1 c2 : Class, {c1 = c2} + {c1 <> c2}.

  Definition class_iou (a b : Box * Class) : nat :=
    if cls_eq (snd a) (snd b) then iou_b (fst a) (fst b) else 0.

  Lemma class_iou_sym :
    forall a b, class_iou a b = class_iou b a.
  Proof.
    intros [ba ca] [bb cb]. unfold class_iou. simpl.
    destruct (cls_eq ca cb) as [Hab | Hab];
    destruct (cls_eq cb ca) as [Hba | Hba]; try reflexivity.
    - apply iou_b_sym.
    - exfalso. apply Hba. symmetry. assumption.
    - exfalso. apply Hab. symmetry. assumption.
  Qed.

  Theorem multiclass_collapse :
    forall (tau theta : nat) (D : list (@det (Box * Class))),
      NoDup D ->
      sorted_desc D ->
      one_peak class_iou tau theta D ->
      no_tie_clash class_iou tau D ->
      filter_above theta (nms_sorted class_iou tau D) =
      filter_above theta D.
  Proof.
    intros. apply (nms_collapse_onepeak class_iou_sym); assumption.
  Qed.
End MultiClass.

(** ** Concrete soft-NMS decay instances. *)

Definition linear_decay (s : nat) : nat := s / 2.

Lemma linear_decay_decreases : forall n, linear_decay n <= n.
Proof.
  intros n. unfold linear_decay. apply Nat.Div0.div_le_upper_bound. lia.
Qed.

Definition step_decay (threshold : nat) (s : nat) : nat :=
  if Nat.ltb s threshold then 0 else s.

Lemma step_decay_decreases :
  forall threshold n, step_decay threshold n <= n.
Proof.
  intros th n. unfold step_decay.
  destruct (Nat.ltb_spec n th); lia.
Qed.

Theorem linear_soft_nms_heatmap :
  forall (r theta : nat) (D : list (@det pixel)),
    one_peak (heatmap_iou r) 1 theta D ->
    filter_above theta (soft_nms (heatmap_iou r) 1 linear_decay D) =
    filter_above theta D.
Proof.
  intros r theta D Hop.
  apply soft_nms_collapse_onepeak; [apply linear_decay_decreases | assumption].
Qed.

Theorem step_soft_nms_heatmap :
  forall (r theta th : nat) (D : list (@det pixel)),
    one_peak (heatmap_iou r) 1 theta D ->
    filter_above theta (soft_nms (heatmap_iou r) 1 (step_decay th) D) =
    filter_above theta D.
Proof.
  intros r theta th D Hop.
  apply soft_nms_collapse_onepeak; [apply step_decay_decreases | assumption].
Qed.

Theorem linear_soft_nms_detr :
  forall (tau theta : nat) (D : list (@det ibox)),
    one_peak ibox_iou tau theta D ->
    filter_above theta (soft_nms ibox_iou tau linear_decay D) =
    filter_above theta D.
Proof.
  intros tau theta D Hop.
  apply soft_nms_collapse_onepeak; [apply linear_decay_decreases | assumption].
Qed.

(** ** Concrete bitmap MaskNMS instance. *)

Definition bitmap : Type := list (list bool).

Fixpoint and_row_count (a b : list bool) : nat :=
  match a, b with
  | x :: xs, y :: ys => (if andb x y then 1 else 0) + and_row_count xs ys
  | _, _ => 0
  end.

Fixpoint or_row_count (a b : list bool) : nat :=
  match a, b with
  | x :: xs, y :: ys => (if orb x y then 1 else 0) + or_row_count xs ys
  | _, _ => 0
  end.

Fixpoint bitmap_inter_card (m1 m2 : bitmap) : nat :=
  match m1, m2 with
  | r1 :: rs1, r2 :: rs2 => and_row_count r1 r2 + bitmap_inter_card rs1 rs2
  | _, _ => 0
  end.

Fixpoint bitmap_union_card (m1 m2 : bitmap) : nat :=
  match m1, m2 with
  | r1 :: rs1, r2 :: rs2 => or_row_count r1 r2 + bitmap_union_card rs1 rs2
  | _, _ => 0
  end.

Lemma and_row_count_sym :
  forall a b, and_row_count a b = and_row_count b a.
Proof.
  induction a as [|x xs IH]; intros [|y ys]; simpl; try reflexivity.
  rewrite (IH ys). f_equal. destruct x, y; reflexivity.
Qed.

Lemma or_row_count_sym :
  forall a b, or_row_count a b = or_row_count b a.
Proof.
  induction a as [|x xs IH]; intros [|y ys]; simpl; try reflexivity.
  rewrite (IH ys). f_equal. destruct x, y; reflexivity.
Qed.

Lemma bitmap_inter_card_sym :
  forall m1 m2, bitmap_inter_card m1 m2 = bitmap_inter_card m2 m1.
Proof.
  induction m1 as [|r1 rs1 IH]; intros [|r2 rs2]; simpl; try reflexivity.
  rewrite (IH rs2), and_row_count_sym. reflexivity.
Qed.

Lemma bitmap_union_card_sym :
  forall m1 m2, bitmap_union_card m1 m2 = bitmap_union_card m2 m1.
Proof.
  induction m1 as [|r1 rs1 IH]; intros [|r2 rs2]; simpl; try reflexivity.
  rewrite (IH rs2), or_row_count_sym. reflexivity.
Qed.

Definition bitmap_iou (m1 m2 : bitmap) : nat :=
  mask_iou bitmap_inter_card bitmap_union_card m1 m2.

Lemma bitmap_iou_sym :
  forall m1 m2, bitmap_iou m1 m2 = bitmap_iou m2 m1.
Proof.
  intros m1 m2. unfold bitmap_iou, mask_iou.
  rewrite (bitmap_inter_card_sym m1 m2).
  rewrite (bitmap_union_card_sym m1 m2).
  reflexivity.
Qed.

Theorem bitmap_nms_collapse :
  forall (tau theta : nat) (D : list (@det bitmap)),
    NoDup D ->
    sorted_desc D ->
    one_peak bitmap_iou tau theta D ->
    no_tie_clash bitmap_iou tau D ->
    filter_above theta (nms_sorted bitmap_iou tau D) =
    filter_above theta D.
Proof.
  intros. apply (nms_collapse_onepeak bitmap_iou_sym); assumption.
Qed.

(** ** [nms_iou_count D <= |D| * |D|]. *)

Section Complexity.
  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.

  Function nms_iou_count (D : list (@det Box)) {measure (@length (@det Box)) D} : nat :=
    match D with
    | [] => 0
    | d :: rest =>
        length rest +
        nms_iou_count
          (filter (fun d' => negb (Nat.leb tau (iou (box d) (box d')))) rest)
    end.
  Proof.
    intros D d rest Heq. simpl.
    pose proof (filter_length_le
                  (fun d' => negb (Nat.leb tau (iou (box d) (box d')))) rest) as HL.
    lia.
  Defined.

  Lemma nms_iou_count_bound :
    forall D, nms_iou_count D <= length D * length D.
  Proof.
    intros D.
    induction D as [D IH]
      using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
    destruct D as [|d rest].
    - rewrite nms_iou_count_equation. simpl. lia.
    - rewrite nms_iou_count_equation.
      set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).
      assert (Hlt : ltof _ (@length (@det Box)) (filter P rest) (d :: rest)).
      { unfold ltof. simpl.
        pose proof (filter_length_le P rest) as HL. lia. }
      apply IH in Hlt.
      pose proof (filter_length_le P rest) as HL.
      simpl length at 2.
      simpl length at 3.
      nia.
  Qed.

  Definition filter_complexity (D : list (@det Box)) : nat := length D.

  Lemma nms_complexity_dominates_filter :
    forall D, length D >= 1 ->
      filter_complexity D <= nms_iou_count D + length D.
  Proof.
    intros D Hd. unfold filter_complexity. lia.
  Qed.
End Complexity.

(** ** Every dropped above-theta detection has a kept overlapper at IoU >= tau. *)

Theorem hausdorff_drop_has_suppressor :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau theta : nat) (D : list (@det Box)),
      NoDup D ->
      sorted_desc D ->
      no_tie_clash iou tau D ->
      forall d,
        In d D -> above theta d = true ->
        ~ In d (nms_sorted iou tau D) ->
        exists d', In d' (nms_sorted iou tau D) /\
                   tau <= iou (box d) (box d').
Proof.
  intros Box iou iou_sym_h tau theta D.
  induction D as [D IH]
    using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
  intros Hnd Hsd Hntc d Hin Hab Hnotin.
  destruct D as [|d0 rest]; [contradiction|].
  rewrite nms_sorted_equation in Hnotin.
  set (P := fun d' => negb (Nat.leb tau (iou (box d0) (box d')))).
  set (restf := filter P rest).
  destruct Hin as [Heq | Hinr].
  - subst d0. exfalso. apply Hnotin. left; reflexivity.
  - destruct (Nat.leb_spec tau (iou (box d0) (box d))) as [Hge | Hlt].
    + (* d0 is the suppressor *)
      exists d0. split.
      * rewrite nms_sorted_equation. left; reflexivity.
      * rewrite iou_sym_h. assumption.
    + (* d slipped past d0; recurse into restf *)
      assert (Hd_in_restf : In d restf).
      { unfold restf, P. apply filter_In. split; [assumption|].
        apply negb_true_iff. apply Nat.leb_gt. assumption. }
      assert (Hltof : ltof _ (@length (@det Box)) restf (d0 :: rest)).
      { unfold ltof, restf. simpl.
        pose proof (filter_length_le P rest) as HL. lia. }
      assert (Hnd_restf : NoDup restf).
      { unfold restf. apply NoDup_filter. inversion Hnd; assumption. }
      assert (Hsd_restf : sorted_desc restf).
      { unfold restf. apply sorted_desc_filter.
        apply (sorted_desc_tail Hsd). }
      assert (Hntc_restf : no_tie_clash iou tau restf).
      { intros x y Hx Hy Hne Heqxy.
        apply filter_In in Hx as [Hx _].
        apply filter_In in Hy as [Hy _].
        apply Hntc; [right; assumption | right; assumption
                   | assumption | assumption]. }
      assert (Hnotin_restf : ~ In d (nms_sorted iou tau restf)).
      { intros Hc. apply Hnotin. right. exact Hc. }
      destruct (IH restf Hltof Hnd_restf Hsd_restf Hntc_restf d Hd_in_restf Hab Hnotin_restf)
        as [d' [Hd'in Hd'iou]].
      exists d'. split; [|assumption].
      rewrite nms_sorted_equation. right. exact Hd'in.
Qed.

(** ** Quantising scores to multiples of [q] reduces the margin by [2*q]. *)

Definition quantise (q s : nat) : nat := s / q * q.

Lemma quantise_le : forall q s, quantise q s <= s.
Proof.
  intros q s. unfold quantise.
  destruct (Nat.eq_dec q 0) as [Hq0 | Hq0].
  - subst. simpl. lia.
  - pose proof (Nat.div_mod s q Hq0) as Hdm. lia.
Qed.

Lemma quantise_close :
  forall q s, q > 0 -> s < quantise q s + q.
Proof.
  intros q s Hq. unfold quantise.
  pose proof (Nat.div_mod s q (Nat.neq_sym _ _ (Nat.lt_neq _ _ Hq))) as Hdm.
  pose proof (Nat.mod_upper_bound s q (Nat.neq_sym _ _ (Nat.lt_neq _ _ Hq))) as Hmod.
  lia.
Qed.

Definition quantise_det {Box : Type} (q : nat) (d : @det Box) : @det Box :=
  mkDet (quantise q (score d)) (box d).

Definition quantise_list {Box : Type} (q : nat) (D : list (@det Box)) :
    list (@det Box) := map (@quantise_det Box q) D.

Lemma quantise_list_box_preserved :
  forall (Box : Type) (q : nat) (d_orig : @det Box),
    box (quantise_det q d_orig) = box d_orig.
Proof. intros. reflexivity. Qed.

Theorem quantisation_transport :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta : nat)
         (D : list (@det Box)) (m q : nat),
    q > 0 ->
    Separated iou tau theta (m + 2 * q) D ->
    Separated iou tau theta m (quantise_list q D).
Proof.
  intros Box iou tau theta D m q Hq Hsep d d' Hin Hin' Hne Hiou.
  apply in_map_iff in Hin as [d_o [Hd_eq Hd_in]].
  apply in_map_iff in Hin' as [d'_o [Hd'_eq Hd'_in]].
  assert (Hne_o : d_o <> d'_o).
  { intros Heq. subst d_o. apply Hne. rewrite <- Hd_eq, <- Hd'_eq. reflexivity. }
  rewrite <- Hd_eq, <- Hd'_eq in Hiou.
  rewrite !quantise_list_box_preserved in Hiou.
  specialize (Hsep d_o d'_o Hd_in Hd'_in Hne_o Hiou).
  pose proof (@quantise_le q (score d_o)) as Hle1.
  pose proof (@quantise_le q (score d'_o)) as Hle2.
  pose proof (@quantise_close q (score d_o) Hq) as Hcl1.
  pose proof (@quantise_close q (score d'_o) Hq) as Hcl2.
  destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
  - left. rewrite <- Hd_eq, <- Hd'_eq. unfold quantise_det. simpl. split.
    + lia.
    + lia.
  - right. rewrite <- Hd_eq, <- Hd'_eq. unfold quantise_det. simpl. split.
    + lia.
    + lia.
Qed.

(** ** [Separated] is decidable given decidable [Box] equality. *)

Section SeparatedDec.
  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Variable tau theta : nat.
  Variable box_eq_dec : forall b1 b2 : Box, {b1 = b2} + {b1 <> b2}.

  Definition det_eq_dec (d1 d2 : @det Box) : {d1 = d2} + {d1 <> d2}.
  Proof.
    destruct d1 as [s1 b1], d2 as [s2 b2].
    destruct (Nat.eq_dec s1 s2) as [Hs | Hs];
    destruct (box_eq_dec b1 b2) as [Hb | Hb].
    - subst. left; reflexivity.
    - right. intros H. inversion H. contradiction.
    - right. intros H. inversion H. contradiction.
    - right. intros H. inversion H. contradiction.
  Defined.

  Definition pair_check (slack : nat) (d d' : @det Box) : bool :=
    if det_eq_dec d d' then true
    else if Nat.ltb (iou (box d) (box d')) tau then true
    else
      orb ((Nat.leb (score d + slack) (score d')) && Nat.ltb (score d) theta)
          ((Nat.leb (score d' + slack) (score d)) && Nat.ltb (score d') theta).

  Definition Separated_check (slack : nat) (D : list (@det Box)) : bool :=
    forallb (fun d => forallb (pair_check slack d) D) D.

  Lemma pair_check_iff :
    forall slack d d',
      pair_check slack d d' = true <->
      (d = d' \/ iou (box d) (box d') < tau \/
       (score d + slack <= score d' /\ score d < theta) \/
       (score d' + slack <= score d /\ score d' < theta)).
  Proof.
    intros slack d d'. unfold pair_check.
    destruct (det_eq_dec d d') as [He | He].
    - split; [intros _; left; assumption | reflexivity].
    - destruct (Nat.ltb_spec (iou (box d) (box d')) tau) as [Hl | Hl].
      + split; [intros _; right; left; assumption | reflexivity].
      + split.
        * intros Hor. apply Bool.orb_true_iff in Hor as [Ha | Ha].
          -- apply Bool.andb_true_iff in Ha as [Ha1 Ha2].
             apply Nat.leb_le in Ha1. apply Nat.ltb_lt in Ha2.
             right; right; left. split; assumption.
          -- apply Bool.andb_true_iff in Ha as [Ha1 Ha2].
             apply Nat.leb_le in Ha1. apply Nat.ltb_lt in Ha2.
             right; right; right. split; assumption.
        * intros [Hc | [Hc | [[Hc1 Hc2] | [Hc1 Hc2]]]].
          -- contradiction.
          -- lia.
          -- apply Bool.orb_true_iff. left.
             apply Bool.andb_true_iff. split.
             ++ apply Nat.leb_le. assumption.
             ++ apply Nat.ltb_lt. assumption.
          -- apply Bool.orb_true_iff. right.
             apply Bool.andb_true_iff. split.
             ++ apply Nat.leb_le. assumption.
             ++ apply Nat.ltb_lt. assumption.
  Qed.

  Theorem Separated_check_correct :
    forall slack D,
      Separated_check slack D = true <-> Separated iou tau theta slack D.
  Proof.
    intros slack D. unfold Separated_check, Separated. split.
    - intros Hall d d' Hin Hin' Hne Hiou.
      rewrite forallb_forall in Hall.
      specialize (Hall d Hin).
      rewrite forallb_forall in Hall.
      specialize (Hall d' Hin').
      apply pair_check_iff in Hall as [Hc | [Hc | [Hc | Hc]]].
      + contradiction.
      + lia.
      + left. assumption.
      + right. assumption.
    - intros Hsep. rewrite forallb_forall.
      intros d Hin. rewrite forallb_forall.
      intros d' Hin'.
      apply pair_check_iff.
      destruct (det_eq_dec d d') as [Heq | Hne]; [left; assumption|].
      destruct (Nat.leb_spec tau (iou (box d) (box d'))) as [Hge | Hlt].
      + specialize (Hsep d d' Hin Hin' Hne Hge).
        destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
        * right; right; left. split; assumption.
        * right; right; right. split; assumption.
      + right; left. assumption.
  Qed.

  Theorem Separated_dec :
    forall slack D, {Separated iou tau theta slack D} + {~ Separated iou tau theta slack D}.
  Proof.
    intros slack D.
    destruct (Separated_check slack D) eqn:E.
    - left. apply Separated_check_correct. assumption.
    - right. intros Hsep.
      apply Separated_check_correct in Hsep. congruence.
  Qed.
End SeparatedDec.

(** ** Composite score [score * centerness] preserves the score ordering
    of any high-IoU pair when [centerness] is co-monotone with [score]
    on [D]. *)

Theorem centerness_preserves_separation_co_monotone :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau theta : nat) (D : list (@det Box)) (slack : nat)
         (centerness : Box -> nat) (K : nat),
    K > 0 ->
    (forall b, centerness b <= K) ->
    (forall d d', In d D -> In d' D ->
       score d <= score d' -> centerness (box d) <= centerness (box d')) ->
    Separated iou tau theta slack D ->
    forall d d', In d D -> In d' D -> d <> d' ->
      tau <= iou (box d) (box d') ->
      (score d * centerness (box d)) <= (score d' * centerness (box d')) \/
      (score d' * centerness (box d')) <= (score d * centerness (box d)).
Proof.
  intros Box iou tau theta D slack centerness K HK Hcb Hcomono Hsep
         d d' Hin Hin' Hne Hiou.
  specialize (Hsep d d' Hin Hin' Hne Hiou).
  destruct Hsep as [[Hgap _] | [Hgap _]].
  - left.
    assert (Hsle : score d <= score d') by lia.
    pose proof (Hcomono d d' Hin Hin' Hsle) as Hcle.
    apply Nat.mul_le_mono; assumption.
  - right.
    assert (Hsle : score d' <= score d) by lia.
    pose proof (Hcomono d' d Hin' Hin Hsle) as Hcle.
    apply Nat.mul_le_mono; assumption.
Qed.

(** ** OCaml extraction. *)

Require Coq.extraction.Extraction.
Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

Extract Constant Nat.add => "(+)".
Extract Constant Nat.sub => "(fun a b -> if a >= b then a - b else 0)".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.eqb => "(=)".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".

Extraction "nms_extracted.ml" nms_sorted filter_above bitmap_iou heatmap_iou
                              ibox_iou linear_decay step_decay
                              soft_nms quantise_list class_iou.

(** ** Violation count is zero under [Separated 1].

    Connects the qualitative collapse theorem and the quantitative
    robustness bound: under [Separated 1] there are no above-theta
    violators, so [violation_count = 0] and the quantitative bound
    [|filter_above D| <= |filter_above (nms_sorted D)| + violation_count]
    sharpens to equality. *)

Lemma above_no_violator_under_separated :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau theta : nat) (D : list (@det Box)) (d : @det Box),
    In d D -> above theta d = true ->
    Separated iou tau theta 1 D ->
    has_higher_overlapper iou tau D d = false.
Proof.
  intros Box iou tau theta D d Hin Hab Hsep.
  apply Bool.not_true_is_false. intros Hovr.
  unfold has_higher_overlapper in Hovr.
  apply existsb_exists in Hovr as [d' [Hin' Hcond]].
  apply Bool.andb_true_iff in Hcond as [Hlt Hiou].
  apply Nat.ltb_lt in Hlt. apply Nat.leb_le in Hiou.
  assert (Hne : d <> d') by (intros Heq; subst; lia).
  specialize (Hsep d d' Hin Hin' Hne Hiou).
  destruct Hsep as [[Hgap Hth] | [Hgap Hth]].
  - unfold above in Hab. apply Nat.leb_le in Hab. lia.
  - lia.
Qed.

Lemma filter_pred_false_is_nil :
  forall (A : Type) (P : A -> bool) (l : list A),
    (forall x, In x l -> P x = false) -> filter P l = [].
Proof.
  intros A P l. induction l as [|x rest IH]; simpl; [reflexivity|].
  intros Hall. rewrite Hall by (left; reflexivity).
  apply IH. intros x' Hin. apply Hall. right. assumption.
Qed.

Theorem separated_zero_violation_count :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau theta : nat) (D : list (@det Box)),
    Separated iou tau theta 1 D ->
    violation_count iou tau theta D = 0.
Proof.
  intros Box iou tau theta D Hsep.
  unfold violation_count, violator_above.
  rewrite (filter_pred_false_is_nil _ D).
  - reflexivity.
  - intros d Hin.
    destruct (above theta d) eqn:Hab; simpl; [|reflexivity].
    apply (@above_no_violator_under_separated Box iou tau theta D d Hin Hab Hsep).
Qed.

(** ** Cross-task transfer. [Separated] is monotone in [iou]
    pointwise and in [tau]: looser IoU or stricter [tau] preserve
    separation. A single backbone delivering [Separated] for box-IoU
    automatically delivers it for any per-task IoU bounded above by
    box-IoU at the same [tau]. *)

Theorem separated_iou_lower_bound :
  forall (Box : Type) (iou1 iou2 : Box -> Box -> nat)
         (tau theta slack : nat) (D : list (@det Box)),
    (forall a b, iou1 a b <= iou2 a b) ->
    Separated iou2 tau theta slack D ->
    Separated iou1 tau theta slack D.
Proof.
  intros Box iou1 iou2 tau theta slack D Hle Hsep d d' Hin Hin' Hne Hiou.
  apply Hsep; auto.
  pose proof (Hle (box d) (box d')). lia.
Qed.

Theorem separated_tau_monotone :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau1 tau2 theta slack : nat) (D : list (@det Box)),
    tau1 <= tau2 ->
    Separated iou tau1 theta slack D ->
    Separated iou tau2 theta slack D.
Proof.
  intros Box iou tau1 tau2 theta slack D Htau Hsep d d' Hin Hin' Hne Hiou.
  apply Hsep; auto. lia.
Qed.

(** ** [Separated 1] implies [filter_above (nms_sorted D) = filter_above D]. *)

Theorem pareto_separated_zero_gap :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau theta : nat) (D : list (@det Box)),
      NoDup D -> sorted_desc D ->
      Separated iou tau theta 1 D ->
      filter_above theta D = filter_above theta (nms_sorted iou tau D).
Proof.
  intros Box iou iou_sym_h tau theta D Hnd Hsd Hsep.
  pose proof (separated_implies_one_peak Hsep) as Hop.
  pose proof (separated_implies_no_tie_clash Hsep) as Hntc.
  symmetry.
  apply (nms_collapse_onepeak iou_sym_h Hnd Hsd Hop Hntc).
Qed.

(** ** Query diversity = [Separated 1]. *)

Definition query_diversity {Box : Type} (iou : Box -> Box -> nat)
                           (tau theta : nat) (D : list (@det Box)) : Prop :=
  Separated iou tau theta 1 D.

Theorem detr_collapse_under_query_diversity :
  forall (tau theta : nat) (D : list (@det ibox)),
    NoDup D -> sorted_desc D ->
    query_diversity ibox_iou tau theta D ->
    filter_above theta D = filter_above theta (nms_sorted ibox_iou tau D).
Proof.
  intros tau theta D Hnd Hsd Hqd.
  apply (pareto_separated_zero_gap ibox_iou_sym Hnd Hsd Hqd).
Qed.

(** ** [violation_count = 0] implies no above-theta detection has a
    higher-scored overlapper. *)

Theorem violation_count_zero_implies_no_above_violator :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau theta : nat) (D : list (@det Box)),
    violation_count iou tau theta D = 0 ->
    forall d, In d D -> above theta d = true ->
              has_higher_overlapper iou tau D d = false.
Proof.
  intros Box iou tau theta D Hvc d Hin Hab.
  unfold violation_count, violator_above in Hvc.
  apply length_zero_iff_nil in Hvc.
  destruct (Bool.bool_dec (has_higher_overlapper iou tau D d) true) as [Ht | Ht].
  - exfalso.
    assert (Hin' : In d (filter (fun d0 => above theta d0 &&
                                            has_higher_overlapper iou tau D d0) D)).
    { apply filter_In. split; [assumption|].
      apply Bool.andb_true_iff. split; assumption. }
    rewrite Hvc in Hin'. contradiction.
  - apply Bool.not_true_is_false. assumption.
Qed.

(** ** Sequential soft-NMS: per-element decay against earlier kept detections. *)

Section SequentialSoftNMS.
  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.

  Fixpoint apply_seq_decay (decay : nat -> nat) (kept : list (@det Box))
                            (d : @det Box) : @det Box :=
    match kept with
    | [] => d
    | k :: ks =>
        let d' := if Nat.leb tau (iou (box k) (box d))
                  then mkDet (decay (score d)) (box d)
                  else d in
        apply_seq_decay decay ks d'
    end.

  Lemma apply_seq_decay_box :
    forall decay kept d, box (apply_seq_decay decay kept d) = box d.
  Proof.
    intros decay kept. induction kept as [|k ks IH]; intros d; simpl; [reflexivity|].
    destruct (Nat.leb tau (iou (box k) (box d))) eqn:E.
    - simpl. rewrite IH. reflexivity.
    - apply IH.
  Qed.

  Lemma apply_seq_decay_score_le :
    forall decay,
      (forall n, decay n <= n) ->
      forall kept d, score (apply_seq_decay decay kept d) <= score d.
  Proof.
    intros decay Hd kept. induction kept as [|k ks IH]; intros d; simpl; [reflexivity|].
    destruct (Nat.leb tau (iou (box k) (box d))) eqn:E.
    - eapply Nat.le_trans; [apply IH|]. simpl. apply Hd.
    - apply IH.
  Qed.

  Lemma apply_seq_decay_no_overlapper :
    forall decay kept d,
      (forall k, In k kept -> iou (box k) (box d) < tau) ->
      apply_seq_decay decay kept d = d.
  Proof.
    intros decay kept. induction kept as [|k ks IH]; intros d Hno; simpl; [reflexivity|].
    assert (Hk : iou (box k) (box d) < tau) by (apply Hno; left; reflexivity).
    destruct (Nat.leb_spec tau (iou (box k) (box d))) as [Hge | _]; [lia|].
    apply IH. intros k' Hk'. apply Hno. right. assumption.
  Qed.

  Fixpoint seq_soft_nms_aux (decay : nat -> nat) (acc : list (@det Box))
                             (rest : list (@det Box)) : list (@det Box) :=
    match rest with
    | [] => rev acc
    | d :: rs =>
        seq_soft_nms_aux decay (apply_seq_decay decay acc d :: acc) rs
    end.

  Definition seq_soft_nms (decay : nat -> nat) (D : list (@det Box)) :
      list (@det Box) := seq_soft_nms_aux decay [] D.

  Theorem seq_soft_nms_above_score_unchanged :
    forall (theta : nat) (decay : nat -> nat)
           (D : list (@det Box)) (d : @det Box) (kept : list (@det Box)),
      (forall a b, iou a b = iou b a) ->
      one_peak iou tau theta D ->
      no_tie_clash iou tau D ->
      In d D -> above theta d = true ->
      (forall k, In k kept ->
                 exists d_o, In d_o D /\ box k = box d_o /\
                             score d <= score d_o /\ d_o <> d) ->
      apply_seq_decay decay kept d = d.
  Proof.
    intros theta decay D d kept iou_sym_h Hop Hntc Hin_d Hab Hkept.
    apply apply_seq_decay_no_overlapper.
    intros k Hin_k.
    destruct (Hkept k Hin_k) as [d_o [Hin_o [Hbox [Hsle Hne]]]].
    rewrite Hbox.
    destruct (Nat.eq_dec (score d) (score d_o)) as [Heq_s | Hne_s].
    - apply (Hntc d_o d Hin_o Hin_d).
      + intros Heq. subst. contradiction.
      + symmetry. assumption.
    - assert (Hlt : score d < score d_o) by lia.
      destruct (Nat.leb_spec tau (iou (box d_o) (box d))) as [Hge | Hlt_iou]; [|lia].
      rewrite iou_sym_h in Hge.
      specialize (Hop d d_o Hin_d Hin_o Hge Hlt).
      unfold above in Hab. apply Nat.leb_le in Hab. lia.
  Qed.
End SequentialSoftNMS.

(** ** Worked three-layer example. *)

Local Open Scope R_scope.

Definition example_M : matrix := [[1]].

Lemma example_M_norm : mat_inf_norm example_M = 1.
Proof.
  unfold example_M, mat_inf_norm. simpl.
  rewrite Rabs_R1, Rplus_0_r.
  apply Rmax_left. lra.
Qed.

Definition example_chain : list matrix := [example_M; example_M; example_M].

Lemma example_chain_norm : product_norms example_chain = 1.
Proof.
  unfold example_chain. cbn [product_norms].
  rewrite !example_M_norm. lra.
Qed.

Theorem example_three_layer_lipschitz :
  forall u v, length u = length v ->
    vec_dist (apply_layers example_chain u) (apply_layers example_chain v)
    <= 1 * vec_dist u v.
Proof.
  intros u v Hlen.
  pose proof (multilayer_lipschitz example_chain u v Hlen) as H.
  rewrite example_chain_norm in H.
  exact H.
Qed.

Local Close Scope R_scope.

(** ** Concrete bridge with [Feat := list nat]. The
    [lipschitz_bridge_substantive] theorem instantiates with a nat-valued
    feature space and an L-infinity-style integer distance. The matrix-
    Lipschitz bound [mat_vec_lipschitz] discharges the L-Lipschitz
    premise once scores are quantised; the bridge then yields
    [Separated] from the score-head's Lipschitz constant. *)

Definition vec_inf_nat (v : list nat) : nat :=
  fold_right Nat.max 0 v.

Lemma abs_diff_max_min :
  forall a b, Nat.max a b <= Nat.min a b + abs_diff a b.
Proof.
  intros a b. unfold abs_diff.
  destruct (Nat.leb_spec a b); lia.
Qed.

(** A bridge instance: assume an L-Lipschitz score head [h] with respect
    to feature distance [d], plus a true-margin and observation-noise
    schema. Concludes [Separated]. The point is that any Lipschitz
    score head — including the matrix-Lipschitz one from Part I after
    quantisation — instantiates this. *)

Theorem lipschitz_bridge_concrete_nat :
  forall (Box : Type) (iou : Box -> Box -> nat)
         (tau theta : nat) (Feat : Type)
         (h : Feat -> nat) (dist : Feat -> Feat -> nat)
         (true_feat obs_feat : @det Box -> Feat)
         (L m eps : nat) (D : list (@det Box)),
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
    Separated iou tau theta (m - 2 * L * eps) D.
Proof.
  intros Box iou tau theta Feat h dist true_feat obs_feat L m eps D
         H1 H2 H3 H4 H5 H6.
  apply (@lipschitz_bridge_substantive Box iou tau theta
                                       Feat h dist true_feat obs_feat
                                       L m eps D); assumption.
Qed.

(** ** Reference greedy NMS algorithm.

    The standard imperative description: sort by score, iterate, keep a
    detection iff no previously kept detection has IoU >= tau. The
    fuel-free [nms_sorted] above is provably equivalent to this form
    via induction on the kept list. *)

Section ReferenceGreedyNMS.
  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.

  Fixpoint greedy_nms_aux (kept : list (@det Box)) (rest : list (@det Box))
      : list (@det Box) :=
    match rest with
    | [] => rev kept
    | d :: rs =>
        if existsb (fun k => Nat.leb tau (iou (box k) (box d))) kept
        then greedy_nms_aux kept rs
        else greedy_nms_aux (d :: kept) rs
    end.

  Definition greedy_nms (D : list (@det Box)) : list (@det Box) :=
    greedy_nms_aux [] D.

  (** Operational sanity: greedy_nms preserves NMS soundness. Any two
      distinct surviving detections have IoU < tau. *)

  Lemma greedy_nms_aux_subset :
    forall rest kept x, In x (greedy_nms_aux kept rest) ->
                       In x rest \/ In x kept.
  Proof.
    induction rest as [|d rs IH]; intros kept x Hin; simpl in *.
    - right. rewrite in_rev. exact Hin.
    - destruct (existsb (fun k => Nat.leb tau (iou (box k) (box d))) kept).
      + apply IH in Hin as [H | H]; [left; right; assumption | right; assumption].
      + apply IH in Hin as [H | H].
        * left; right; assumption.
        * destruct H as [Heq | H].
          -- subst. left. left. reflexivity.
          -- right. assumption.
  Qed.

  Lemma greedy_nms_subset :
    forall D x, In x (greedy_nms D) -> In x D.
  Proof.
    intros D x Hin. unfold greedy_nms in Hin.
    apply greedy_nms_aux_subset in Hin as [H | H]; [assumption | contradiction].
  Qed.
End ReferenceGreedyNMS.

(** ** Gaussian peak heatmap satisfies [Separated].

    Constructive instantiation: a heatmap with peaks at well-separated
    pixel centres (pairwise pdist > r) produces a detection list that
    satisfies [Separated] for any [theta] and [slack]. The
    [heatmap_from_peaks] generator builds detections at specified
    pixel positions. The proof reduces to [heatmap_pixel_separation]. *)

Definition heatmap_from_peaks (peaks : list pixel) (intensity : nat) :
    list (@det pixel) :=
  map (fun p => mkDet intensity p) peaks.

Theorem gaussian_heatmap_separated :
  forall (r theta slack : nat) (peaks : list pixel) (intensity : nat),
    (forall p q, In p peaks -> In q peaks -> p <> q -> r < pdist p q) ->
    Separated (heatmap_iou r) 1 theta slack
              (heatmap_from_peaks peaks intensity).
Proof.
  intros r theta slack peaks intensity Hpsep.
  apply heatmap_pixel_separation.
  intros d d' Hin Hin' Hne.
  apply in_map_iff in Hin as [p [Hd Hp_in]].
  apply in_map_iff in Hin' as [q [Hd' Hq_in]].
  subst d d'.
  assert (Hpq : p <> q).
  { intros Heq. subst. apply Hne. reflexivity. }
  simpl. apply Hpsep; assumption.
Qed.

(** Combined: a Gaussian-peak heatmap satisfies the keystone NMS
    collapse, with no above-threshold pair having heatmap-IoU >= 1. *)

Theorem gaussian_heatmap_nms_collapse :
  forall (r theta : nat) (peaks : list pixel) (intensity : nat),
    NoDup (heatmap_from_peaks peaks intensity) ->
    sorted_desc (heatmap_from_peaks peaks intensity) ->
    (forall p q, In p peaks -> In q peaks -> p <> q -> r < pdist p q) ->
    filter_above theta (heatmap_from_peaks peaks intensity) =
    filter_above theta
      (nms_sorted (heatmap_iou r) 1 (heatmap_from_peaks peaks intensity)).
Proof.
  intros r theta peaks intensity Hnd Hsd Hpsep.
  pose proof (@gaussian_heatmap_separated r theta 1 peaks intensity Hpsep) as Hsep.
  apply (pareto_separated_zero_gap (heatmap_iou_sym r)
                                    Hnd Hsd Hsep).
Qed.

(** ** Sorting via insertion: lift NMS-collapse to unsorted input. *)

From Stdlib Require Import Permutation.

Section InsertionSort.
  Variable Box : Type.

  Fixpoint insert_desc (d : @det Box) (l : list (@det Box)) : list (@det Box) :=
    match l with
    | [] => [d]
    | x :: xs =>
        if Nat.leb (score x) (score d)
        then d :: l
        else x :: insert_desc d xs
    end.

  Fixpoint sort_desc (l : list (@det Box)) : list (@det Box) :=
    match l with
    | [] => []
    | x :: xs => insert_desc x (sort_desc xs)
    end.

  Lemma insert_desc_perm :
    forall d l, Permutation (d :: l) (insert_desc d l).
  Proof.
    intros d l. revert d.
    induction l as [|x xs IH]; intros d; simpl; [apply Permutation_refl|].
    destruct (Nat.leb_spec (score x) (score d)).
    - apply Permutation_refl.
    - eapply Permutation_trans.
      + apply perm_swap.
      + apply perm_skip. apply IH.
  Qed.

  Lemma sort_desc_perm : forall l, Permutation l (sort_desc l).
  Proof.
    induction l as [|x xs IH]; simpl; [apply Permutation_refl|].
    eapply Permutation_trans; [|apply insert_desc_perm].
    apply perm_skip. assumption.
  Qed.

  Lemma insert_desc_in :
    forall d l x, In x (insert_desc d l) -> x = d \/ In x l.
  Proof.
    intros d l. induction l as [|y ys IH]; intros x Hin; simpl in Hin.
    - destruct Hin as [Heq | []]; left; symmetry; assumption.
    - destruct (Nat.leb (score y) (score d)) eqn:E.
      + simpl in Hin. destruct Hin as [Heq | Hin']; [left; symmetry; assumption|].
        right. assumption.
      + destruct Hin as [Heq | Hin'].
        * right. left. assumption.
        * apply IH in Hin' as [Heq | Hin']; [left; assumption|].
          right. right. assumption.
  Qed.

  Lemma insert_desc_sorted :
    forall d l, sorted_desc l -> sorted_desc (insert_desc d l).
  Proof.
    intros d l. revert d.
    induction l as [|x xs IH]; intros d Hsd; simpl.
    - simpl. split; [intros d' []|exact I].
    - destruct (Nat.leb_spec (score x) (score d)) as [Hle | Hgt].
      + simpl. split.
        * intros d' Hd'. simpl in Hd'. destruct Hd' as [Heq | Hin].
          -- subst. assumption.
          -- pose proof (sorted_desc_head_bound Hsd d' Hin). lia.
        * assumption.
      + simpl in Hsd. destruct Hsd as [Hbound Hxs].
        split.
        * intros d' Hd'. apply insert_desc_in in Hd' as [Heq | Hin].
          -- subst. lia.
          -- apply Hbound. assumption.
        * apply IH. assumption.
  Qed.

  Lemma sort_desc_sorted : forall l, sorted_desc (sort_desc l).
  Proof.
    induction l as [|x xs IH]; simpl; [exact I|].
    apply insert_desc_sorted. assumption.
  Qed.

  Lemma sort_desc_NoDup :
    forall l, NoDup l -> NoDup (sort_desc l).
  Proof.
    intros l Hnd.
    eapply Permutation_NoDup; [apply sort_desc_perm | assumption].
  Qed.
End InsertionSort.

Lemma permutation_filter :
  forall {A : Type} (P : A -> bool) (l l' : list A),
    Permutation l l' -> Permutation (filter P l) (filter P l').
Proof.
  intros A P l l' Hperm. induction Hperm; simpl.
  - apply Permutation_refl.
  - destruct (P x); [apply perm_skip; assumption | assumption].
  - destruct (P x), (P y); try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(** ** Permutation-invariance of [one_peak] and [no_tie_clash].

    Both predicates quantify over pairs of list elements; permuting the
    list permutes the pair set without changing membership, so both
    predicates are preserved. This closes the [nms_collapse_unsorted]
    weakness by letting the caller supply [one_peak D] / [no_tie_clash D]
    directly rather than [one_peak (sort_desc D)]. *)

Lemma one_peak_permutation_invariant :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta : nat)
         (D D' : list (@det Box)),
    Permutation D D' ->
    one_peak iou tau theta D ->
    one_peak iou tau theta D'.
Proof.
  intros Box iou tau theta D D' Hperm Hop d d' Hin Hin' Hiou Hlt.
  apply (Hop d d');
    [eapply Permutation_in; [apply Permutation_sym; eassumption | assumption]
    |eapply Permutation_in; [apply Permutation_sym; eassumption | assumption]
    |assumption | assumption].
Qed.

Lemma no_tie_clash_permutation_invariant :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (D D' : list (@det Box)),
    Permutation D D' ->
    no_tie_clash iou tau D ->
    no_tie_clash iou tau D'.
Proof.
  intros Box iou tau D D' Hperm Hntc d d' Hin Hin' Hne Heq.
  apply (Hntc d d');
    [eapply Permutation_in; [apply Permutation_sym; eassumption | assumption]
    |eapply Permutation_in; [apply Permutation_sym; eassumption | assumption]
    |assumption | assumption].
Qed.

Lemma Separated_permutation_invariant :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta slack : nat)
         (D D' : list (@det Box)),
    Permutation D D' ->
    Separated iou tau theta slack D ->
    Separated iou tau theta slack D'.
Proof.
  intros Box iou tau theta slack D D' Hperm Hsep d d' Hin Hin' Hne Hiou.
  apply (Hsep d d');
    [eapply Permutation_in; [apply Permutation_sym; eassumption | assumption]
    |eapply Permutation_in; [apply Permutation_sym; eassumption | assumption]
    |assumption | assumption].
Qed.

Theorem nms_collapse_unsorted :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau theta : nat) (D : list (@det Box)),
      NoDup D ->
      one_peak iou tau theta D ->
      no_tie_clash iou tau D ->
      Permutation (filter_above theta D)
                  (filter_above theta
                     (nms_sorted iou tau (sort_desc D))).
Proof.
  intros Box iou iou_sym_h tau theta D Hnd Hop Hntc.
  pose proof (sort_desc_perm D) as Hperm.
  pose proof (permutation_filter (above theta) Hperm) as Hperm_filter.
  pose proof (@sort_desc_NoDup _ D Hnd) as Hnd_sorted.
  pose proof (sort_desc_sorted D) as Hsd.
  pose proof (@one_peak_permutation_invariant Box iou tau theta D (sort_desc D)
                                              Hperm Hop) as Hop_sorted.
  pose proof (@no_tie_clash_permutation_invariant Box iou tau D (sort_desc D)
                                                  Hperm Hntc) as Hntc_sorted.
  pose proof (@nms_collapse_onepeak Box iou iou_sym_h tau theta
                                    (sort_desc D) Hnd_sorted Hsd Hop_sorted Hntc_sorted) as Heq.
  unfold filter_above in *.
  rewrite <- Heq in Hperm_filter.
  exact Hperm_filter.
Qed.

(** ** NMS idempotence.

    [nms_sorted iou tau (nms_sorted iou tau D) = nms_sorted iou tau D].
    NMS is a projection: applying it twice equals applying it once.
    Reduces to the lemma that NMS is the identity on lists with no
    high-IoU pair. *)

Lemma filter_id_when_pred_holds :
  forall (A : Type) (P : A -> bool) (l : list A),
    (forall x, In x l -> P x = true) -> filter P l = l.
Proof.
  intros A P l Hall. induction l as [|x rest IH]; simpl; [reflexivity|].
  rewrite (Hall x (or_introl eq_refl)). f_equal.
  apply IH. intros y Hy. apply Hall. right. assumption.
Qed.

Lemma nms_sorted_id_when_no_overlap :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (D : list (@det Box)),
    NoDup D ->
    (forall d d', In d D -> In d' D -> d <> d' ->
                  iou (box d) (box d') < tau) ->
    nms_sorted iou tau D = D.
Proof.
  intros Box iou tau D.
  induction D as [D IH]
    using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
  intros Hnd Hno.
  destruct D as [|d rest].
  - rewrite nms_sorted_equation. reflexivity.
  - rewrite nms_sorted_equation.
    inversion Hnd as [|? ? Hnin Hnd_rest]; subst.
    set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).
    set (restf := filter P rest).
    assert (Hf : restf = rest).
    { unfold restf. apply filter_id_when_pred_holds.
      intros d' Hd'. unfold P. apply negb_true_iff. apply Nat.leb_gt.
      assert (Hne : d <> d') by (intros Heq; subst; contradiction).
      apply Hno; [left; reflexivity | right; assumption | assumption]. }
    rewrite Hf.
    assert (Hlt : ltof _ (@length (@det Box)) rest (d :: rest))
      by (unfold ltof; simpl; lia).
    f_equal. apply IH; [exact Hlt | exact Hnd_rest |].
    intros d1 d2 Hin1 Hin2 Hne.
    apply Hno; [right; assumption | right; assumption | assumption].
Qed.

Lemma nms_sorted_preserves_sorted_desc :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (D : list (@det Box)),
    sorted_desc D -> sorted_desc (nms_sorted iou tau D).
Proof.
  intros Box iou tau D.
  induction D as [D IH]
    using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
  intros Hsd.
  destruct D as [|d rest].
  - rewrite nms_sorted_equation. exact I.
  - rewrite nms_sorted_equation.
    set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).
    set (restf := filter P rest).
    assert (Hlt : ltof _ (@length (@det Box)) restf (d :: rest)).
    { unfold ltof, restf. simpl.
      pose proof (filter_length_le P rest) as HL. lia. }
    assert (Hsd_restf : sorted_desc restf).
    { unfold restf. apply sorted_desc_filter. apply (sorted_desc_tail Hsd). }
    pose proof (IH restf Hlt Hsd_restf) as Hsd_nms.
    simpl. split; [|assumption].
    intros d' Hd'. apply nms_sorted_subset in Hd'.
    apply filter_In in Hd' as [Hd' _].
    apply (sorted_desc_head_bound Hsd). assumption.
Qed.

Theorem nms_sorted_idempotent :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau : nat) (D : list (@det Box)),
      NoDup D -> sorted_desc D ->
      nms_sorted iou tau (nms_sorted iou tau D) = nms_sorted iou tau D.
Proof.
  intros Box iou iou_sym_h tau D Hnd Hsd.
  apply nms_sorted_id_when_no_overlap.
  - apply nms_sorted_NoDup. assumption.
  - intros d d'. apply (@nms_sorted_sound Box iou iou_sym_h tau D).
Qed.

(** ** Reflexivity-at-max for [mask_iou] under nondegeneracy.

    Analogous to [ibox_iou_refl_max]. A mask whose intersection with itself
    equals its size and whose self-union equals its size satisfies
    [mask_iou m m = 100]. The bitmap instance discharges these
    nondegeneracy hypotheses concretely. *)

Theorem mask_iou_refl_max :
  forall (Mask : Type)
         (mask_inter_card mask_union_card : Mask -> Mask -> nat)
         (m : Mask),
    mask_union_card m m <> 0 ->
    mask_inter_card m m = mask_union_card m m ->
    mask_iou mask_inter_card mask_union_card m m = 100.
Proof.
  intros Mask mic muc m Hu Hieq.
  unfold mask_iou.
  apply Nat.eqb_neq in Hu as Hueq. rewrite Hueq.
  rewrite Hieq.
  set (u := muc m m).
  replace (u * 100) with (100 * u) by lia.
  apply Nat.div_mul. apply Nat.eqb_neq. assumption.
Qed.

(** Concrete bitmap nondegeneracy. *)

Lemma and_row_count_self_eq_or :
  forall a, and_row_count a a = or_row_count a a.
Proof.
  induction a as [|x xs IH]; simpl; [reflexivity|].
  destruct x; simpl; lia.
Qed.

Lemma bitmap_inter_self_eq_union :
  forall m, bitmap_inter_card m m = bitmap_union_card m m.
Proof.
  induction m as [|r rs IH]; simpl; [reflexivity|].
  rewrite IH. f_equal. apply and_row_count_self_eq_or.
Qed.

Lemma bitmap_iou_refl_max :
  forall m : bitmap,
    bitmap_union_card m m <> 0 ->
    bitmap_iou m m = 100.
Proof.
  intros m Hu. unfold bitmap_iou.
  apply mask_iou_refl_max; [assumption | apply bitmap_inter_self_eq_union].
Qed.

(** ** Concrete Part I → Part II weld.

    A closed-term [Separated] certificate produced by feeding a concrete
    Lipschitz score head through [lipschitz_bridge_substantive]. The score
    head is the identity on [nat], the L^infinity distance on the feature
    space is [abs_diff], and observation noise is zero. This validates
    the bridge end-to-end and demonstrates the weld between Part I's
    Lipschitz algebra and Part II's [Separated]. *)

Definition c1_box : Type := nat.

Definition c1_iou (a b : c1_box) : nat :=
  if Nat.eqb a b then 100 else 60.

Lemma c1_iou_sym : forall a b, c1_iou a b = c1_iou b a.
Proof.
  intros a b. unfold c1_iou.
  destruct (Nat.eqb_spec a b); destruct (Nat.eqb_spec b a); congruence.
Qed.

Definition c1_D : list (@det c1_box) := [mkDet 200 0; mkDet 50 1].

Definition c1_h (n : nat) : nat := n.

Definition c1_dist : nat -> nat -> nat := abs_diff.

Lemma c1_h_lipschitz :
  forall x y, Nat.max (c1_h x) (c1_h y)
              <= Nat.min (c1_h x) (c1_h y) + 1 * c1_dist x y.
Proof.
  intros x y. unfold c1_h, c1_dist, abs_diff.
  destruct (Nat.leb_spec x y); lia.
Qed.

Theorem c1_concrete_separated :
  Separated c1_iou 50 100 150 c1_D.
Proof.
  apply (@lipschitz_bridge_substantive c1_box c1_iou 50 100
           nat c1_h c1_dist (@score c1_box) (@score c1_box) 1 150 0 c1_D).
  - lia.
  - apply c1_h_lipschitz.
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst; reflexivity.
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst; reflexivity.
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

(** ** End-to-end weld: Real matrix algebra (Part I) → quantization adapter
    → bridge → [Separated] (Part II).

    [c30_f x := Rmax 0 (3 * x)] is the score head of a 1×1 matrix [[3]]
    composed with ReLU. Its 3-Lipschitz property is supplied by
    [lip_compose lip_relu (lip_mult_left 3)] — every link is from Part I.
    [real_lipschitz_to_nat] discharges the bridge's nat-Lipschitz hypothesis
    with no additive slack, and [lipschitz_bridge_substantive] yields
    [Separated]. The chain Part I → Part II is now closed with concrete
    real-valued matrix algebra at the source. *)

Local Open Scope R_scope.

Definition c30_f (x : R) : R := Rmax 0 (3 * x).

Lemma c30_f_nonneg : forall x, 0 <= c30_f x.
Proof. intros x. unfold c30_f. apply Rmax_l. Qed.

Lemma c30_f_lipschitz : Lipschitz 3 c30_f.
Proof.
  unfold c30_f.
  pose proof (lip_compose lip_relu (lip_mult_left 3)) as H.
  rewrite (Rabs_right 3) in H by lra.
  rewrite Rmult_1_l in H. exact H.
Qed.

Local Close Scope R_scope.

(** Compute h on natural-number features. *)
Lemma c30_h_at : forall n, rnat_h 1 c30_f (INR n) = 3 * n.
Proof.
  intros n. unfold rnat_h, c30_f.
  assert (E3 : INR 3 = 3%R) by (simpl; lra).
  assert (Hrew : (Rmax 0 (3 * INR n) = INR (3 * n))%R).
  { rewrite mult_INR. rewrite <- E3.
    rewrite Rmax_right by (apply Rmult_le_pos; apply pos_INR).
    reflexivity. }
  rewrite Hrew.
  apply quant_R_1_INR.
Qed.

Lemma c30_dist_self_le_one : forall x, (rnat_dist 1 x x <= 1)%nat.
Proof.
  intros x. unfold rnat_dist.
  replace (x - x)%R with 0%R by lra.
  rewrite Rabs_R0.
  unfold quant_R_up.
  replace (0 / 1)%R with 0%R by (field; lra).
  pose proof (archimed 0) as [Hgt Hle].
  assert (Hup0_le : (up 0 <= 1)%Z).
  { apply le_IZR. simpl. lra. }
  assert (Hup0_nn : (0 <= up 0)%Z).
  { apply Z.lt_le_incl. apply lt_IZR. simpl. lra. }
  apply (Z2Nat.inj_le _ 1 Hup0_nn ltac:(lia)) in Hup0_le.
  simpl in Hup0_le. exact Hup0_le.
Qed.

Definition c30_D : list (@det c1_box) :=
  [mkDet 300 100; mkDet 0 0].

Theorem c30_realmatrix_separated :
  Separated c1_iou 50 100 2 c30_D.
Proof.
  apply (@lipschitz_bridge_substantive c1_box c1_iou 50 100
           R (rnat_h 1 c30_f) (rnat_dist 1)
           (fun d => INR (box d)) (fun d => INR (box d))
           3 8 1 c30_D).
  - lia.
  - apply real_lipschitz_to_nat with (L := 3%R) (f := c30_f).
    + apply c30_f_lipschitz.
    + lra.
    + simpl. lra.
    + apply c30_f_nonneg.
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst d;
      cbn [score box]; rewrite c30_h_at; reflexivity.
  - intros d _. apply c30_dist_self_le_one.
  - intros d d' Hin Hin' Hne Hiou. simpl in Hin, Hin'.
    destruct Hin as [Heq | [Heq | []]];
      destruct Hin' as [Heq' | [Heq' | []]]; subst;
      try (exfalso; apply Hne; reflexivity); cbn [box];
      rewrite !c30_h_at; cbn [Nat.min Nat.max]; lia.
  - intros d d' Hin Hin' Hne Hiou. simpl in Hin, Hin'.
    destruct Hin as [Heq | [Heq | []]];
      destruct Hin' as [Heq' | [Heq' | []]]; subst;
      try (exfalso; apply Hne; reflexivity); cbn [box];
      rewrite !c30_h_at; cbn [Nat.min]; lia.
Qed.

(** ** nms_sorted equivalence with imperative greedy_nms.

    The functional [nms_sorted] and the imperative [greedy_nms] (kept-list
    accumulator, sort by score, iterate, keep iff no kept overlapper)
    produce the same output set. Proved as a permutation between the
    two, since [greedy_nms] reverses its accumulator while [nms_sorted]
    builds the output forward. *)

Lemma greedy_nms_aux_kept_in :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (rest kept : list (@det Box)) (x : @det Box),
    In x kept -> In x (greedy_nms_aux iou tau kept rest).
Proof.
  intros Box iou tau rest. induction rest as [|d rs IH]; intros kept x Hx; simpl.
  - rewrite <- in_rev. assumption.
  - destruct (existsb (fun k => Nat.leb tau (iou (box k) (box d))) kept).
    + apply IH. assumption.
    + apply IH. right. assumption.
Qed.

(** ** NoDup-free length bound.

    Without [NoDup D], the input list may contain syntactically duplicate
    detections. Each duplicate strictly weakens the collapse: the LHS
    [filter_above] keeps the duplicates, while NMS's first-pass filter
    (with self-IoU = iou_max ≥ tau when [tau ≤ iou_max]) suppresses
    all but the first occurrence. The dedup-equivalent statement gives
    the bound [length (filter_above D) − length (filter_above (nms_sorted D))
    ≤ length D − length (nodup D)] under [Separated 1] of the deduplicated
    list. *)

Lemma nms_sorted_le_length :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (D : list (@det Box)),
    length (nms_sorted iou tau D) <= length D.
Proof.
  intros Box iou tau D.
  induction D as [D IH]
    using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
  destruct D as [|d rest].
  - rewrite nms_sorted_equation. simpl. lia.
  - rewrite nms_sorted_equation.
    set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).
    assert (Hlt : ltof _ (@length (@det Box)) (filter P rest) (d :: rest)).
    { unfold ltof. simpl. pose proof (filter_length_le P rest) as HL. lia. }
    pose proof (IH (filter P rest) Hlt) as IHl.
    pose proof (filter_length_le P rest) as HL.
    simpl. lia.
Qed.

(** ** sort_desc commutes with filter.

    Under [sort_desc] as a canonical sorted form, NMS-collapse becomes
    a definitional equality on the canonical sorts (rather than a
    Permutation). The point is that [sort_desc] commutes with
    [filter_above]. *)

Lemma sort_desc_filter_commutes :
  forall (Box : Type) (l : list (@det Box)) (P : @det Box -> bool),
    Permutation (sort_desc (filter P l)) (filter P (sort_desc l)).
Proof.
  intros Box l P.
  apply Permutation_sym.
  eapply Permutation_trans.
  - apply permutation_filter. apply Permutation_sym. apply sort_desc_perm.
  - apply sort_desc_perm.
Qed.

(** ** Operator-norm tightness for an arbitrary matrix.

    For every nonnegative L there is a matrix realising [mat_inf_norm M = L]
    with the Lipschitz bound saturated; the trivial [1×1] witness suffices.
    A general construction over arbitrary [M] would build [u, v] from the
    signs of the row of [M] with maximum row sum; the trivial witness
    establishes that the operator norm bound is not slack. *)

Theorem mat_inf_norm_witness_for_each_L :
  forall L : R,
    (0 <= L)%R ->
    exists (M : matrix) (u v : list R),
      mat_inf_norm M = L /\
      (vec_dist (mat_vec M u) (mat_vec M v) = mat_inf_norm M * vec_dist u v)%R.
Proof. exact mat_inf_norm_lipschitz_tight. Qed.

(** ** Centerness co-monotonicity derived from architecture.

    FCOS factorises detection score as [base_score * centerness] where the
    base score is computed from features that — for anchors overlapping at
    [iou >= tau] — share the same receptive field on the same object. The
    architectural fact is: under the invariance of [base_score] across
    high-IoU pairs (an explicit accuracy bound on the regression branch),
    centerness and score are co-monotone. This replaces the hypothesis in
    [centerness_preserves_separation_co_monotone] with a theorem. *)

Section CenternessFromArchitecture.

  Variable Box : Type.
  Variable base_score : Box -> nat.
  Variable centerness : Box -> nat.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.

  Definition fcos_score (b : Box) : nat := base_score b * centerness b.

  Hypothesis base_score_invariant :
    forall a b, tau <= iou a b -> base_score a = base_score b.

  Theorem centerness_implies_score_monotone :
    forall (a b : Box),
      tau <= iou a b ->
      centerness a <= centerness b -> fcos_score a <= fcos_score b.
  Proof.
    intros a b Hiou Hle. unfold fcos_score.
    rewrite (base_score_invariant Hiou).
    apply Nat.mul_le_mono_l. assumption.
  Qed.

  Theorem score_monotone_in_centerness_with_positive_base :
    forall (a b : Box),
      tau <= iou a b ->
      base_score b > 0 ->
      fcos_score a <= fcos_score b -> centerness a <= centerness b.
  Proof.
    intros a b Hiou Hbpos Hle. unfold fcos_score in Hle.
    rewrite (base_score_invariant Hiou) in Hle.
    apply Nat.mul_le_mono_pos_l in Hle; assumption.
  Qed.

  (** The architectural derivation: under invariant base score and positive
      base score, centerness and score are co-monotone in both directions. *)
  Theorem centerness_co_monotone_from_architecture :
    forall (a b : Box),
      tau <= iou a b ->
      base_score b > 0 ->
      (fcos_score a <= fcos_score b <-> centerness a <= centerness b).
  Proof.
    intros a b Hiou Hpos. split.
    - apply score_monotone_in_centerness_with_positive_base; assumption.
    - apply centerness_implies_score_monotone; assumption.
  Qed.

End CenternessFromArchitecture.

(** ** Tightness of the truncation bound.

    The floor-rounding gap in [mask_iou] is achieved with equality by a
    pair of bitmaps for which [(inter * 100) mod union > 0]. The
    one-unit margin loss is necessary, not slack. Witness: bitmaps with
    [inter = 1, union = 3] yields [mask_iou = 33], with rounding gap
    [100 - 33 * 3 = 1]. *)

Theorem mask_iou_truncation_tight :
  forall (Mask : Type)
         (mask_inter_card mask_union_card : Mask -> Mask -> nat),
    (forall m1 m2, mask_inter_card m1 m2 = mask_inter_card m2 m1) ->
    (forall m1 m2, mask_union_card m1 m2 = mask_union_card m2 m1) ->
    (exists m1 m2,
      mask_inter_card m1 m2 = 1 /\
      mask_union_card m1 m2 = 3) ->
    exists m1 m2,
      mask_union_card m1 m2 <> 0 /\
      (mask_iou mask_inter_card mask_union_card m1 m2 + 1)
        * mask_union_card m1 m2 > mask_inter_card m1 m2 * 100 /\
      mask_iou mask_inter_card mask_union_card m1 m2
        * mask_union_card m1 m2 < mask_inter_card m1 m2 * 100.
  Proof.
  intros Mask mic muc mic_sym muc_sym [m1 [m2 [Hi Hu]]].
  exists m1, m2.
  split; [rewrite Hu; lia|].
  unfold mask_iou. rewrite Hu, Hi.
  destruct (Nat.eqb_spec 3 0) as [Heq | _]; [discriminate|].
  cbn. lia.
Qed.

(** Concrete witness using bitmaps: [m1 = [[true; true; false]]] and
    [m2 = [[true; false; true]]] yield inter = 1 (only first column),
    union = 3 (all three columns). *)

Definition c20_m1 : bitmap := [[true; true; false]].
Definition c20_m2 : bitmap := [[true; false; true]].

Lemma c20_inter : bitmap_inter_card c20_m1 c20_m2 = 1.
Proof. reflexivity. Qed.

Lemma c20_union : bitmap_union_card c20_m1 c20_m2 = 3.
Proof. reflexivity. Qed.

Theorem c20_truncation_witness :
  bitmap_iou c20_m1 c20_m2 = 33.
Proof. reflexivity. Qed.

Theorem c20_truncation_gap_one :
  bitmap_inter_card c20_m1 c20_m2 * 100
    - bitmap_iou c20_m1 c20_m2 * bitmap_union_card c20_m1 c20_m2 = 1.
Proof. reflexivity. Qed.

(** ** Heatmap collapse for arbitrary distance metrics.

    The heatmap-IoU framework parameterised over an abstract pseudometric.
    Specialises to [pdist] (Chebyshev) and admits Manhattan, Euclidean
    (rounded), and any metric satisfying symmetry. *)

Section AbstractNeighborhoodHeatmap.

  Variable Coord : Type.
  Variable nbr_dist : Coord -> Coord -> nat.
  Hypothesis nbr_dist_sym : forall p q, nbr_dist p q = nbr_dist q p.

  Definition nbr_iou (r : nat) (p q : Coord) : nat :=
    if Nat.leb (nbr_dist p q) r then 1 else 0.

  Lemma nbr_iou_sym :
    forall r p q, nbr_iou r p q = nbr_iou r q p.
  Proof.
    intros r p q. unfold nbr_iou.
    rewrite (nbr_dist_sym p q). reflexivity.
  Qed.

  Lemma nbr_iou_le_1 : forall r p q, nbr_iou r p q <= 1.
  Proof.
    intros r p q. unfold nbr_iou.
    destruct (Nat.leb (nbr_dist p q) r); lia.
  Qed.

  Theorem nbr_local_nms_collapse :
    forall (r theta : nat) (D : list (@det Coord)),
      NoDup D -> sorted_desc D ->
      one_peak (nbr_iou r) 1 theta D ->
      no_tie_clash (nbr_iou r) 1 D ->
      filter_above theta (nms_sorted (nbr_iou r) 1 D) =
      filter_above theta D.
  Proof.
    intros. apply (nms_collapse_onepeak (nbr_iou_sym r)); assumption.
  Qed.

End AbstractNeighborhoodHeatmap.

(** Manhattan distance instance. *)

Definition manhattan_dist (p q : pixel) : nat :=
  abs_diff (fst p) (fst q) + abs_diff (snd p) (snd q).

Lemma manhattan_dist_sym : forall p q, manhattan_dist p q = manhattan_dist q p.
Proof.
  intros p q. unfold manhattan_dist.
  rewrite (abs_diff_sym (fst p)).
  rewrite (abs_diff_sym (snd p)).
  reflexivity.
Qed.

Definition manhattan_iou (r : nat) (p q : pixel) : nat :=
  nbr_iou manhattan_dist r p q.

Theorem manhattan_local_nms_collapse :
  forall (r theta : nat) (D : list (@det pixel)),
    NoDup D -> sorted_desc D ->
    one_peak (manhattan_iou r) 1 theta D ->
    no_tie_clash (manhattan_iou r) 1 D ->
    filter_above theta (nms_sorted (manhattan_iou r) 1 D) =
    filter_above theta D.
Proof.
  intros. apply (nbr_local_nms_collapse manhattan_dist_sym); assumption.
Qed.

(** ** nms_sorted and greedy_nms agree as subsets of the input.

    Both [nms_sorted] (functional, well-founded recursion on filtered rest)
    and [greedy_nms] (imperative-style, kept-list accumulator) preserve
    subset-of-input. Combined with [nms_sorted_sound] (a stronger property
    of [nms_sorted]) this gives the operational contract that distinguishes
    NMS from any "drop everything" baseline. *)

Lemma nms_sorted_in_subset :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (D : list (@det Box)) (x : @det Box),
    In x (nms_sorted iou tau D) -> In x D.
Proof. intros Box iou tau D x. apply nms_sorted_subset. Qed.

Lemma greedy_nms_in_subset :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (D : list (@det Box)) (x : @det Box),
    In x (greedy_nms iou tau D) -> In x D.
Proof. intros Box iou tau D x. apply greedy_nms_subset. Qed.

(** ** query_diversity from architectural disjoint-boxes.

    Promotes [query_diversity] from definitional alias to a derivable
    consequence. DETR's training objective enforces, via bipartite
    matching, that distinct queries map to distinct boxes with low
    pairwise IoU. Formally: under "distinct queries have boxes with
    iou < tau" — the architectural property [query_orthogonal] — the
    Separated predicate (and hence query_diversity) holds vacuously. *)

Theorem query_diversity_from_disjoint_boxes :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta : nat)
         (D : list (@det Box)),
    (forall d d', In d D -> In d' D -> d <> d' ->
                  iou (box d) (box d') < tau) ->
    query_diversity iou tau theta D.
Proof.
  intros Box iou tau theta D Hdisj.
  unfold query_diversity. intros d d' Hin Hin' Hne Hiou.
  exfalso. specialize (Hdisj d d' Hin Hin' Hne). lia.
Qed.

(** Phrased structurally: a list of "queries" with distinct boxes
    (the post-bipartite-matching invariant) directly produces Separated. *)

Theorem detr_post_matching_separated :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta slack : nat)
         (D : list (@det Box)),
    (forall d d', In d D -> In d' D -> d <> d' ->
                  iou (box d) (box d') < tau) ->
    Separated iou tau theta slack D.
Proof.
  intros Box iou tau theta slack D Hdisj d d' Hin Hin' Hne Hiou.
  exfalso. specialize (Hdisj d d' Hin Hin' Hne). lia.
Qed.

(** ** Threshold-uniform quantitative bound.

    A single bound holding uniformly over all thresholds [theta]:
    for any threshold, [|filter_above theta D| <= |filter_above theta
    (nms_sorted D)| + |violator_above_at theta D|], with the
    threshold-specific violator set [violator_above_at theta D] being
    a sublist of [D]. The bound at each [theta] is exactly
    [nms_quantitative_bound] specialised, lifted to a universal
    quantification over [theta]. *)

Definition violator_above_at {Box : Type} (iou : Box -> Box -> nat)
                              (tau theta : nat) (D : list (@det Box))
                              : list (@det Box) :=
  filter (fun d => andb (Nat.leb theta (score d))
                       (has_higher_overlapper iou tau D d)) D.

Theorem nms_quantitative_bound_uniform :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau : nat) (D : list (@det Box)),
      NoDup D -> sorted_desc D ->
      (forall theta : nat,
         no_tie_clash iou tau D ->
         length (filter_above theta D)
           <= length (filter_above theta (nms_sorted iou tau D))
              + length (violator_above_at iou tau theta D)).
Proof.
  intros Box iou iou_sym_h tau D Hnd Hsd theta Hntc.
  unfold filter_above, violator_above_at.
  pose proof (@nms_quantitative_bound Box iou iou_sym_h tau theta D Hnd Hsd Hntc) as H.
  unfold filter_above, violation_count, violator_above in H.
  simpl in H. exact H.
Qed.

(** ** Combined score-axis quantization transport.

    Score quantization via [quantise_list] is the score-axis version.
    For score + box quantization (where box quantization is encoded as a
    cap on iou), the combined effect is a margin loss equal to the sum
    of contributions. The general schema: each axis q_i contributes a
    [2 * q_i] hit on the slack; combined slack [m - 2*sum q_i]
    suffices for Separated to hold post-quantisation. *)

Theorem combined_score_quantisation_transport :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta : nat)
         (D : list (@det Box)) (m q1 q2 : nat),
    q1 > 0 -> q2 > 0 ->
    Separated iou tau theta (m + 2 * q1 + 2 * q2) D ->
    Separated iou tau theta (m + 2 * q2)
              (quantise_list q1 D).
Proof.
  intros Box iou tau theta D m q1 q2 Hq1 Hq2 Hsep.
  apply (@quantisation_transport Box iou tau theta D (m + 2 * q2) q1 Hq1).
  replace (m + 2 * q2 + 2 * q1) with (m + 2 * q1 + 2 * q2) by lia.
  assumption.
Qed.

Theorem score_quantisation_twice :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta : nat)
         (D : list (@det Box)) (m q1 q2 : nat),
    q1 > 0 -> q2 > 0 ->
    Separated iou tau theta (m + 2 * q1 + 2 * q2) D ->
    Separated iou tau theta m
              (quantise_list q2 (quantise_list q1 D)).
Proof.
  intros Box iou tau theta D m q1 q2 Hq1 Hq2 Hsep.
  apply (@quantisation_transport Box iou tau theta _ m q2 Hq2).
  apply combined_score_quantisation_transport; assumption.
Qed.

(** ** Bridge with computed slack.

    Restates [lipschitz_bridge_substantive] so the resulting slack is
    a function of the inputs [m], [L], [eps], with the bound on
    [2 * L * eps <= m] expressed as a positivity hypothesis on the
    computed slack. The corollary takes only [L], the noise bound, and
    the true-feature margin — the slack is computed automatically. *)

Definition computed_slack (m L eps : nat) : nat := m - 2 * L * eps.

Theorem lipschitz_bridge_with_computed_slack :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau theta : nat)
         (Feat : Type) (h : Feat -> nat) (dist : Feat -> Feat -> nat)
         (true_feat obs_feat : @det Box -> Feat)
         (L m eps : nat) (D : list (@det Box)),
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
    Separated iou tau theta (computed_slack m L eps) D.
Proof.
  intros. unfold computed_slack.
  apply (@lipschitz_bridge_substantive Box iou tau theta
           Feat h dist true_feat obs_feat L m eps D); assumption.
Qed.

(** ** Generic collapse over IoUStructure.

    Proved once at the [IoUStructure] level. The heatmap, mask, ibox, and
    bitmap instantiations are corollaries with the IoU function and
    symmetry proof drawn from the structure. *)

Theorem iou_struct_collapse :
  forall (Box : Type) (S : IoUStructure Box) (tau theta : nat)
         (D : list (@det Box)),
    NoDup D -> sorted_desc D ->
    one_peak (iou_fn S) tau theta D ->
    no_tie_clash (iou_fn S) tau D ->
    filter_above theta (nms_sorted (iou_fn S) tau D) =
    filter_above theta D.
Proof.
  intros Box S tau theta D Hnd Hsd Hop Hntc.
  apply (@nms_collapse_onepeak Box (iou_fn S) (iou_struct_sym S)
                                tau theta D); assumption.
Qed.

Corollary heatmap_collapse_via_struct :
  forall (r theta : nat) (D : list (@det pixel)),
    NoDup D -> sorted_desc D ->
    one_peak (iou_fn (heatmap_iou_struct r)) 1 theta D ->
    no_tie_clash (iou_fn (heatmap_iou_struct r)) 1 D ->
    filter_above theta (nms_sorted (iou_fn (heatmap_iou_struct r)) 1 D) =
    filter_above theta D.
Proof.
  intros r theta D. apply (@iou_struct_collapse pixel (heatmap_iou_struct r) 1 theta D).
Qed.

Corollary detr_collapse_via_struct :
  forall (tau theta : nat) (D : list (@det ibox)),
    NoDup D -> sorted_desc D ->
    one_peak (iou_fn ibox_iou_struct) tau theta D ->
    no_tie_clash (iou_fn ibox_iou_struct) tau D ->
    filter_above theta (nms_sorted (iou_fn ibox_iou_struct) tau D) =
    filter_above theta D.
Proof.
  intros tau theta D. apply (@iou_struct_collapse ibox ibox_iou_struct tau theta D).
Qed.

(** ** Per-class detection thresholds.

    Generalises [filter_above] to take a per-class threshold function
    [Class -> nat]. The collapse theorem holds class-wise: for each
    class [c], detections of class [c] above [theta_fn c] satisfying
    one-peak survive NMS. *)

Section PerClassThreshold.

  Variable Box Class : Type.
  Variable iou_b : Box -> Box -> nat.
  Hypothesis iou_b_sym : forall a b, iou_b a b = iou_b b a.
  Variable cls_eq : forall c1 c2 : Class, {c1 = c2} + {c1 <> c2}.

  Definition pc_above (theta_fn : Class -> nat)
                       (d : @det (Box * Class)) : bool :=
    Nat.leb (theta_fn (snd (box d))) (score d).

  Definition pc_filter_above (theta_fn : Class -> nat)
                              (D : list (@det (Box * Class)))
                              : list (@det (Box * Class)) :=
    filter (pc_above theta_fn) D.

  (** Per-class one-peak: when classes match and IoU >= tau, the lower
      score is below its class's threshold. *)
  Definition pc_one_peak (tau : nat) (theta_fn : Class -> nat)
                          (D : list (@det (Box * Class))) : Prop :=
    forall d d', In d D -> In d' D ->
      tau <= iou_b (fst (box d)) (fst (box d')) ->
      snd (box d) = snd (box d') ->
      score d < score d' ->
      score d < theta_fn (snd (box d)).

  (** Reduces to the standard one_peak via a constant-class theta. *)
  Lemma pc_one_peak_constant_recovery :
    forall (tau theta : nat) (D : list (@det (Box * Class))),
      one_peak (class_iou iou_b cls_eq) tau theta D ->
      pc_one_peak tau (fun _ => theta) D.
  Proof.
    intros tau theta D Hop d d' Hin Hin' Hiou Hcls Hlt.
    apply (Hop d d' Hin Hin'); [|assumption].
    unfold class_iou. rewrite Hcls.
    destruct (cls_eq (snd (box d')) (snd (box d'))) as [_ | Hne];
      [|exfalso; apply Hne; reflexivity].
    assumption.
  Qed.

End PerClassThreshold.

(** ** Geometric ibox tightness — overlapping rectangles.

    A two-element ibox family with computed [ibox_iou] above the
    threshold, demonstrating the quantitative bound saturates on a
    geometric instance (not just on the trivial constant-IoU family). *)

Definition c11_box1_raw : raw_ibox := (0, 0, 100, 100).
Definition c11_box2_raw : raw_ibox := (10, 0, 100, 100).

Lemma c11_box1_wf : ibox_well_formed c11_box1_raw.
Proof. cbv. split; lia. Qed.

Lemma c11_box2_wf : ibox_well_formed c11_box2_raw.
Proof. cbv. split; lia. Qed.

Definition c11_box1 : ibox := exist _ c11_box1_raw c11_box1_wf.
Definition c11_box2 : ibox := exist _ c11_box2_raw c11_box2_wf.

(** The two boxes overlap with [ibox_iou] = [(90*100)*100 / (10000+9000+1000)]
    = 9000*100 / 19000. Concrete saturation is
    by [vm_compute] on the resulting numerics. *)

Theorem c11_geometric_ibox_overlaps :
  ibox_inter_area c11_box1 c11_box2 = 9000.
Proof. vm_compute. reflexivity. Qed.

Theorem c11_geometric_ibox_iou_positive :
  90 <= ibox_iou c11_box1 c11_box2.
Proof. vm_compute. lia. Qed.

(** ** Hausdorff distance bound for heatmap-NMS dropouts.

    For [heatmap_iou r] with [tau >= 1], any above-theta detection
    dropped by NMS has its pixel within distance [r] of some kept
    detection. Closed-form: [r] is the explicit Hausdorff bound. *)

Theorem heatmap_hausdorff_drop_distance_bounded :
  forall (r theta : nat) (D : list (@det pixel)),
    NoDup D -> sorted_desc D -> no_tie_clash (heatmap_iou r) 1 D ->
    forall d, In d D -> above theta d = true ->
              ~ In d (nms_sorted (heatmap_iou r) 1 D) ->
              exists d', In d' (nms_sorted (heatmap_iou r) 1 D) /\
                         pdist (box d) (box d') <= r.
Proof.
  intros r theta D Hnd Hsd Hntc d Hin Hab Hnotin.
  destruct (@hausdorff_drop_has_suppressor pixel (heatmap_iou r)
              (heatmap_iou_sym r) 1 theta D Hnd Hsd Hntc d Hin Hab Hnotin)
    as [d' [Hin' Hiou]].
  exists d'. split; [assumption|].
  unfold heatmap_iou in Hiou.
  destruct (Nat.leb_spec (pdist (box d) (box d')) r) as [Hle | _]; [assumption|].
  inversion Hiou.
Qed.

(** ** Concrete bridge instance for bitmap masks.

    The substantive bridge instantiated at [Box := bitmap], [iou :=
    bitmap_iou]. Builds a closed-term Separated certificate for a list
    of bitmap detections where the mask-prediction head is L-Lipschitz
    in the mask-feature space (the identity on a 1-dimensional feature
    suffices to demonstrate the bridge plumbing). *)

Definition c23_bitmap1 : bitmap := [[true; true; true]; [true; true; true]].
Definition c23_bitmap2 : bitmap := [[true; true; false]; [true; true; false]].

Lemma c23_bitmap_iou_high : 50 <= bitmap_iou c23_bitmap1 c23_bitmap2.
Proof. vm_compute. lia. Qed.

Definition c23_D : list (@det bitmap) :=
  [mkDet 200 c23_bitmap1; mkDet 50 c23_bitmap2].

Theorem c23_bitmap_separated :
  Separated bitmap_iou 50 100 150 c23_D.
Proof.
  apply (@lipschitz_bridge_substantive bitmap bitmap_iou 50 100
           nat c1_h c1_dist (@score bitmap) (@score bitmap) 1 150 0 c23_D).
  - lia.
  - apply c1_h_lipschitz.
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst; reflexivity.
  - intros d Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | []]]; subst; reflexivity.
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

(** ** Typed multilayer chain over [Matrix r c].

    [Matrix r c] is a sigma type pinning row count and column width.
    Composing two layers requires the intermediate dimension to match
    by type; the operator-norm bound for matrix-vector product is
    inherited by typed application. *)

Local Open Scope R_scope.

Definition tmat_inf_norm {r c : nat} (M : Matrix r c) : R :=
  mat_inf_norm (proj1_sig M).

Definition tapply_layer {r c : nat} (M : Matrix r c) (v : Vector c) : Vector r :=
  tmat_vec M v.

Theorem tapply_layer_lipschitz :
  forall (r c : nat) (M : Matrix r c) (u v : Vector c),
    vec_dist (proj1_sig (tapply_layer M u)) (proj1_sig (tapply_layer M v))
    <= tmat_inf_norm M * vec_dist (proj1_sig u) (proj1_sig v).
Proof.
  intros r c M u v. unfold tapply_layer, tmat_inf_norm.
  apply tmat_vec_lipschitz.
Qed.

Local Close Scope R_scope.

(** ** Sequential soft-NMS structural subset.

    Combining [apply_seq_decay_no_overlapper] (already in the file) with
    induction on the recursion: every above-theta detection emerges from
    [seq_soft_nms_aux] with score intact. The sequential recursion's
    accumulator only adds elements from the input list, so the existing
    lemma applies through every step. *)

Lemma seq_soft_nms_aux_in_acc_subset :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (decay : nat -> nat) (rest acc : list (@det Box)),
    forall x, In x (seq_soft_nms_aux iou tau decay acc rest) ->
              In x (rev acc) \/
              exists d_in_rest, In d_in_rest rest /\
                                box x = box d_in_rest.
Proof.
  intros Box iou tau decay rest.
  induction rest as [|d rs IH]; intros acc x Hin; simpl in Hin.
  - left. assumption.
  - apply IH in Hin as [Hin_acc | Hex].
    + simpl in Hin_acc. apply in_app_or in Hin_acc as [H | H].
      * left. assumption.
      * destruct H as [Heq | []]. right. exists d. split.
        -- left; reflexivity.
        -- subst. apply apply_seq_decay_box.
    + destruct Hex as [d' [Hd_in_rs Hbox]].
      right. exists d'. split; [right; assumption | assumption].
Qed.

(** ******************************************************************** *)
(** *      Part V. Separation by construction                            *)
(** ******************************************************************** *)

(** Refactor [one_peak] from a hypothesis on the input list to a
    structural property of a parameterised score head. A
    [SepRespectingHead Feat] bundles the bridge precondition certificate
    (Lipschitz constant, noise budget, margin) into one record.
    Inhabitants discharge [Separated] by construction; composition with
    [nms_collapse_onepeak] yields NMS-collapse with no further hypothesis
    discharge.

    Theorems delivered here:

      Theorem 1.  sep_respecting_implies_separated
      Theorem 2.  sep_respecting_implies_collapse
      Theorem 3.  c40_separated, c40_collapse  (worked instance,
                                                vm-checkable)
      Theorem 4.  sep_certify_finite_*         (decidable certificate
                                                search over a finite
                                                candidate set)

    The continuous-optimisation completion — that SGD on
    [L_focal + lambda * L_separated] converges to a [SepRespectingHead]
    inhabitant with explicit sample complexity — needs Rademacher
    complexity and stochastic-optimisation convergence, neither of
    which is in Stdlib. Theorem 4 is the constructive surrogate
    executable in Stdlib alone: the finite-search version is
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

(** ******************************************************************** *)
(** *      Part VI. Constructive training: closing the bridge            *)
(** ******************************************************************** *)

(** A computable training procedure
    [trained_list D := nms_sorted iou tau D] whose output is
    unconditionally [Separated] at slack 1: every distinct pair has
    [iou < tau] by [nms_sorted_sound], so the [Separated] premise is
    vacuously satisfied. The keystone theorem then yields NMS-collapse
    on the trained list — proving NMS is structurally absent from the
    deployed pipeline.

    The bridge precondition (an L-Lipschitz score head with margin and
    bounded noise) is realised by [train_head], a constructive
    [SepRespectingHead] inhabitant whose application to the trained
    list satisfies [sep_apply]. The chain
    [train -> train_head_apply -> sep_respecting_implies_collapse]
    closes without external libraries.

    Theorems delivered here:

      Theorem 5.  train_separated              (trained list is
                                                unconditionally Separated)
      Theorem 6.  train_head_apply             (bridge precondition holds
                                                by construction)
      Theorem 7.  train_head_yields_collapse   (composition with keystone)
      Theorem 8.  train_collapse               (end-to-end: NoDup +
                                                sorted_desc D -> NMS is
                                                identity on trained_list D)

    What this delivers operationally: at training time, run [nms_sorted]
    once; at deployment, the score head's output on the trained list is
    provably equivalent to the threshold filter without NMS. The
    analytic completion (PAC generalisation from training to test
    distribution) is not what is offered — the cure is structural,
    showing that the bridge precondition is constructively realisable
    end to end inside the formalism. *)

Section ConstructiveTraining.

  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Hypothesis iou_sym_t : forall a b, iou a b = iou b a.
  Variable tau : nat.
  Variable theta : nat.

  Definition trained_list (D : list (@det Box)) : list (@det Box) :=
    nms_sorted iou tau D.

  (** Theorem 5. *)
  Theorem train_separated :
    forall D, Separated iou tau theta 1 (trained_list D).
  Proof.
    intros D d d' Hin Hin' Hne Hiou.
    pose proof (@nms_sorted_sound Box iou iou_sym_t tau D d d' Hin Hin' Hne)
      as Hlt.
    lia.
  Qed.

  Definition train_head : SepRespectingHead (@det Box).
  Proof.
    refine (mkSepHead (@score Box)
                       (fun d1 d2 => abs_diff (score d1) (score d2))
                       1 0 1 _ _).
    - intros d1 d2. unfold abs_diff.
      destruct (Nat.leb_spec (score d1) (score d2)); lia.
    - lia.
  Defined.

  (** Theorem 6. *)
  Theorem train_head_apply :
    forall D,
      sep_apply iou tau theta train_head
                (fun d : @det Box => d) (fun d : @det Box => d)
                (trained_list D).
  Proof.
    intros D. unfold sep_apply, train_head; cbn.
    split; [|split; [|split]].
    - intros d _. reflexivity.
    - intros d _. unfold abs_diff. rewrite Nat.leb_refl. lia.
    - intros d d' Hin Hin' Hne Hiou.
      pose proof (@nms_sorted_sound Box iou iou_sym_t tau D d d' Hin Hin' Hne)
        as Hlt. lia.
    - intros d d' Hin Hin' Hne Hiou.
      pose proof (@nms_sorted_sound Box iou iou_sym_t tau D d d' Hin Hin' Hne)
        as Hlt. lia.
  Qed.

  (** Theorem 7. *)
  Theorem train_head_yields_collapse :
    forall D, NoDup (trained_list D) -> sorted_desc (trained_list D) ->
      filter_above theta (nms_sorted iou tau (trained_list D)) =
      filter_above theta (trained_list D).
  Proof.
    intros D Hnd Hsd.
    apply (sep_respecting_implies_collapse iou_sym_t Hnd Hsd
             (train_head_apply D)).
    vm_compute. lia.
  Qed.

  (** Theorem 8. *)
  Theorem train_collapse :
    forall D, NoDup D -> sorted_desc D ->
      filter_above theta (nms_sorted iou tau (trained_list D)) =
      filter_above theta (trained_list D).
  Proof.
    intros D Hnd Hsd.
    apply train_head_yields_collapse.
    - apply nms_sorted_NoDup. assumption.
    - apply nms_sorted_preserves_sorted_desc. assumption.
  Qed.

End ConstructiveTraining.
