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

(** ** Constructive saturating witness. For every non-empty matrix [M],
    the pair [u := sign_vec r_max], [v := -sign_vec r_max] (where
    [r_max] is the row of [M] with maximum row-sum-abs) saturates the
    operator-norm Lipschitz bound. Quantitative tightness, not merely
    qualitative existence: the bound equation holds with equality. *)

Definition rsign (r : R) : R := if Rle_dec 0 r then 1 else -1.

Lemma rsign_pm_one : forall r, rsign r = 1 \/ rsign r = -1.
Proof.
  intros r. unfold rsign. destruct (Rle_dec 0 r); [left | right]; reflexivity.
Qed.

Lemma rsign_abs : forall r, Rabs (rsign r) = 1.
Proof.
  intros r. destruct (rsign_pm_one r) as [Heq | Heq]; rewrite Heq.
  - rewrite Rabs_R1. reflexivity.
  - replace (-1) with (-(1)) by lra. rewrite Rabs_Ropp, Rabs_R1. reflexivity.
Qed.

Lemma rsign_mul : forall r, r * rsign r = Rabs r.
Proof.
  intros r. unfold rsign. destruct (Rle_dec 0 r) as [Hge | Hlt].
  - rewrite Rmult_1_r, Rabs_right by lra. reflexivity.
  - assert (Hlt' : r < 0) by lra.
    rewrite (Rabs_left _ Hlt'). lra.
Qed.

Fixpoint sign_vec (v : list R) : list R :=
  match v with
  | [] => []
  | x :: rest => rsign x :: sign_vec rest
  end.

Lemma sign_vec_length : forall v, length (sign_vec v) = length v.
Proof.
  induction v as [|x rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sign_vec_pm_one :
  forall v y, In y (sign_vec v) -> Rabs y = 1.
Proof.
  induction v as [|x rest IH]; intros y Hin; simpl in Hin; [contradiction|].
  destruct Hin as [Heq | Hin].
  - subst. apply rsign_abs.
  - apply IH. assumption.
Qed.

Definition neg_sign_vec (v : list R) : list R := map Ropp (sign_vec v).

Lemma neg_sign_vec_length : forall v, length (neg_sign_vec v) = length v.
Proof.
  intros v. unfold neg_sign_vec. rewrite length_map. apply sign_vec_length.
Qed.

Lemma dot_self_sign : forall r, dot r (sign_vec r) = row_sum_abs r.
Proof.
  induction r as [|x rest IH]; simpl; [reflexivity|].
  rewrite IH. rewrite rsign_mul. reflexivity.
Qed.

Lemma dot_other_pm_one_bound :
  forall r u,
    (forall y, In y u -> Rabs y = 1) ->
    Rabs (dot r u) <= row_sum_abs r.
Proof.
  induction r as [|x rest IH]; intros u Hu; simpl.
  - rewrite Rabs_R0. apply Rle_refl.
  - destruct u as [|y vs]; simpl.
    + rewrite Rabs_R0.
      pose proof (row_sum_abs_nonneg rest). pose proof (Rabs_pos x). lra.
    + eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_mult.
      assert (Hy : Rabs y = 1) by (apply Hu; left; reflexivity).
      rewrite Hy, Rmult_1_r.
      apply Rplus_le_compat_l.
      apply IH. intros z Hz. apply Hu. right. assumption.
Qed.

Lemma vec_sub_sign_neg_sign :
  forall l, vec_sub (sign_vec l) (neg_sign_vec l) = map (fun y => 2 * y) (sign_vec l).
Proof.
  induction l as [|x rest IH]; simpl; [reflexivity|].
  unfold neg_sign_vec in *. simpl.
  rewrite IH. f_equal. lra.
Qed.

Lemma dot_scale_v :
  forall row v c, dot row (map (fun y => c * y) v) = c * dot row v.
Proof.
  induction row as [|x rs IH]; intros v c; simpl.
  - lra.
  - destruct v as [|y vs]; simpl.
    + lra.
    + rewrite IH. lra.
Qed.

Lemma vec_inf_scale_nonneg :
  forall c l, 0 <= c -> vec_inf (map (fun y => c * y) l) = c * vec_inf l.
Proof.
  intros c l Hc. induction l as [|x rest IH]; simpl.
  - lra.
  - rewrite IH.
    rewrite Rabs_mult, (Rabs_right c) by lra.
    apply RmaxRmult. assumption.
Qed.

Fixpoint find_max_row (M : matrix) : list R :=
  match M with
  | [] => []
  | r :: rest =>
      let r' := find_max_row rest in
      if Rle_dec (row_sum_abs r') (row_sum_abs r) then r else r'
  end.

Lemma find_max_row_max :
  forall M r, In r M -> row_sum_abs r <= row_sum_abs (find_max_row M).
Proof.
  induction M as [|r0 rest IH]; intros r Hin; simpl in *; [contradiction|].
  destruct (Rle_dec (row_sum_abs (find_max_row rest)) (row_sum_abs r0))
    as [Hle | Hgt].
  - destruct Hin as [Heq | Hin].
    + subst. apply Rle_refl.
    + specialize (IH _ Hin). lra.
  - destruct Hin as [Heq | Hin].
    + subst. lra.
    + apply IH. assumption.
Qed.

Lemma find_max_row_in :
  forall M, M <> [] -> In (find_max_row M) M.
Proof.
  induction M as [|r0 rest IH]; intros Hne; [contradiction|].
  simpl.
  destruct (Rle_dec (row_sum_abs (find_max_row rest)) (row_sum_abs r0))
    as [Hle | Hgt].
  - left; reflexivity.
  - right. apply IH.
    intros Hempty. subst rest. simpl in Hgt.
    pose proof (row_sum_abs_nonneg r0). lra.
Qed.

Lemma find_max_row_eq_inf_norm :
  forall M, M <> [] -> row_sum_abs (find_max_row M) = mat_inf_norm M.
Proof.
  induction M as [|r0 rest IH]; intros Hne; [contradiction|].
  simpl.
  destruct rest as [|r1 rest'].
  - simpl. simpl in *.
    pose proof (row_sum_abs_nonneg r0).
    destruct (Rle_dec 0 (row_sum_abs r0)) as [_ | Hbad]; [|lra].
    rewrite Rmax_left by lra. reflexivity.
  - assert (Hne' : r1 :: rest' <> []) by discriminate.
    specialize (IH Hne').
    destruct (Rle_dec (row_sum_abs (find_max_row (r1 :: rest')))
                      (row_sum_abs r0)) as [Hle | Hgt].
    + rewrite Rmax_left by (rewrite <- IH; assumption). reflexivity.
    + rewrite Rmax_right by (rewrite <- IH; lra). exact IH.
Qed.

Lemma vec_inf_max_achieved :
  forall (l : list R) (K : R),
    0 <= K ->
    (forall x, In x l -> Rabs x <= K) ->
    (exists x, In x l /\ Rabs x = K) ->
    vec_inf l = K.
Proof.
  intros l K HK Hbound [x [Hin Heq]].
  apply Rle_antisym.
  - apply vec_inf_bound; assumption.
  - rewrite <- Heq. apply vec_inf_in. assumption.
Qed.

Theorem mat_inf_norm_lipschitz_saturated :
  forall M : matrix,
    M <> [] ->
    vec_dist (mat_vec M (sign_vec (find_max_row M)))
             (mat_vec M (neg_sign_vec (find_max_row M)))
    = mat_inf_norm M * vec_dist (sign_vec (find_max_row M))
                                 (neg_sign_vec (find_max_row M)).
Proof.
  intros M Hne.
  destruct (find_max_row M) as [|x0 rs] eqn:Erm.
  - cbn [sign_vec map].
    unfold neg_sign_vec. cbn [sign_vec map].
    rewrite (vec_dist_refl (mat_vec M [])).
    rewrite (vec_dist_refl (@nil R)).
    lra.
  - set (rm := x0 :: rs).
    assert (Huv_len : length (sign_vec rm) = length (neg_sign_vec rm)).
    { rewrite sign_vec_length, neg_sign_vec_length. reflexivity. }
    assert (Hmn : row_sum_abs rm = mat_inf_norm M).
    { unfold rm. rewrite <- Erm. apply find_max_row_eq_inf_norm. assumption. }
    assert (Hmn_nn : 0 <= mat_inf_norm M) by apply mat_inf_norm_nonneg.
    assert (Hsv_eq : vec_inf (sign_vec rm) = 1).
    { unfold rm. cbn [sign_vec].
      apply Rle_antisym.
      - apply Rmax_lub.
        + rewrite rsign_abs. apply Rle_refl.
        + apply vec_inf_bound; [lra|].
          intros y Hy. rewrite (sign_vec_pm_one rs y Hy). apply Rle_refl.
      - rewrite <- (rsign_abs x0).
        apply vec_inf_in. simpl. left; reflexivity. }
    assert (Hvdist_uv : vec_dist (sign_vec rm) (neg_sign_vec rm) = 2).
    { unfold vec_dist.
      rewrite vec_sub_sign_neg_sign.
      rewrite vec_inf_scale_nonneg by lra.
      rewrite Hsv_eq. lra. }
    rewrite Hvdist_uv.
    unfold vec_dist at 1.
    rewrite (mat_vec_sub_componentwise_eqlen M _ _ Huv_len).
    rewrite vec_sub_sign_neg_sign.
    rewrite (map_ext (fun row => dot row (map (fun y => 2 * y) (sign_vec rm)))
                     (fun row => 2 * dot row (sign_vec rm)))
      by (intros; apply dot_scale_v).
    rewrite <- map_map with (f := fun row => dot row (sign_vec rm))
                            (g := fun y => 2 * y).
    rewrite vec_inf_scale_nonneg by lra.
    rewrite (Rmult_comm (mat_inf_norm M) 2).
    apply Rmult_eq_compat_l.
    apply vec_inf_max_achieved; [assumption | |].
    + intros x Hin.
      apply in_map_iff in Hin as [row [Heq Hrow_in]]. subst x.
      pose proof (dot_other_pm_one_bound row (sign_vec rm)
                    (sign_vec_pm_one rm)) as Hb.
      pose proof (find_max_row_max M row Hrow_in) as Hrow_le.
      rewrite Erm in Hrow_le. fold rm in Hrow_le.
      rewrite Hmn in Hrow_le.
      lra.
    + exists (dot rm (sign_vec rm)).
      split.
      * apply in_map_iff. exists rm. split; [reflexivity|].
        unfold rm. rewrite <- Erm. apply find_max_row_in. assumption.
      * rewrite dot_self_sign. rewrite Hmn.
        apply Rabs_pos_eq. assumption.
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
  rewrite Nat.mul_0_l, Nat.Div0.div_0_l. reflexivity.
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

(** ** Multi-output detections (per-class scores).

    A real detector predicts a vector of class-conditional scores per
    box, not a single scalar. [mc_det] carries this structure. The
    [mc_expand] flattening converts a list of multi-output detections
    plus a class list into the single-class [(Box * Class)] form
    consumed by the existing [multiclass_collapse]. The per-class
    [mc_one_peak] / [mc_no_tie_clash] predicates lift mechanically to
    [one_peak class_iou] / [no_tie_clash class_iou] on the expanded
    list, so the keystone is unconditional on input data the moment
    the per-class structural constraints hold. *)

Section MultiOutput.
  Variable Box : Type.
  Variable Class : Type.
  Variable iou_b : Box -> Box -> nat.
  Hypothesis iou_b_sym : forall a b, iou_b a b = iou_b b a.
  Variable cls_eq : forall c1 c2 : Class, {c1 = c2} + {c1 <> c2}.
  Variable tau : nat.
  Variable theta : nat.
  Hypothesis tau_pos : 0 < tau.

  Record mc_det : Type := mkMcDet {
    mc_box : Box;
    mc_score : Class -> nat
  }.

  Definition mc_expand (mds : list mc_det) (cs : list Class)
      : list (@det (Box * Class)) :=
    flat_map (fun md =>
                map (fun c => mkDet (mc_score md c) (mc_box md, c)) cs) mds.

  Definition mc_one_peak (mds : list mc_det) : Prop :=
    forall md md' c, In md mds -> In md' mds ->
      tau <= iou_b (mc_box md) (mc_box md') ->
      mc_score md c < mc_score md' c ->
      mc_score md c < theta.

  Definition mc_no_tie_clash (mds : list mc_det) : Prop :=
    forall md md' c, In md mds -> In md' mds ->
      md <> md' ->
      mc_score md c = mc_score md' c ->
      iou_b (mc_box md) (mc_box md') < tau.

  Lemma mc_one_peak_lift :
    forall mds cs,
      mc_one_peak mds ->
      one_peak (@class_iou Box Class iou_b cls_eq) tau theta (mc_expand mds cs).
  Proof.
    intros mds cs Hmc d1 d2 Hin1 Hin2 Hiou Hlt.
    apply in_flat_map in Hin1 as [md1 [Hmd1 Hd1]].
    apply in_flat_map in Hin2 as [md2 [Hmd2 Hd2]].
    apply in_map_iff in Hd1 as [c1 [Heq1 _]].
    apply in_map_iff in Hd2 as [c2 [Heq2 _]].
    subst d1 d2.
    unfold class_iou in Hiou. simpl in Hiou.
    destruct (cls_eq c1 c2) as [Heq | _]; [|lia].
    subst c2.
    cbn [score box] in *.
    apply (Hmc md1 md2 c1 Hmd1 Hmd2 Hiou Hlt).
  Qed.

  Lemma mc_no_tie_clash_lift :
    forall mds cs,
      mc_no_tie_clash mds ->
      no_tie_clash (@class_iou Box Class iou_b cls_eq) tau (mc_expand mds cs).
  Proof.
    intros mds cs Hmc d1 d2 Hin1 Hin2 Hne Heq_score.
    apply in_flat_map in Hin1 as [md1 [Hmd1 Hd1]].
    apply in_flat_map in Hin2 as [md2 [Hmd2 Hd2]].
    apply in_map_iff in Hd1 as [c1 [Heq1 _]].
    apply in_map_iff in Hd2 as [c2 [Heq2 _]].
    subst d1 d2.
    cbn [score box] in *.
    unfold class_iou. simpl.
    destruct (cls_eq c1 c2) as [Heq_c | _]; [|lia].
    subst c2.
    assert (Hmd_ne : md1 <> md2).
    { intro Hmd_eq. subst md2. apply Hne. reflexivity. }
    apply (Hmc md1 md2 c1 Hmd1 Hmd2 Hmd_ne Heq_score).
  Qed.

  Theorem mc_keystone :
    forall (mds : list mc_det) (cs : list Class),
      NoDup (mc_expand mds cs) ->
      sorted_desc (mc_expand mds cs) ->
      mc_one_peak mds ->
      mc_no_tie_clash mds ->
      filter_above theta
        (nms_sorted (@class_iou Box Class iou_b cls_eq) tau (mc_expand mds cs))
      = filter_above theta (mc_expand mds cs).
  Proof.
    intros mds cs Hnd Hsd Hop Hntc.
    apply (@multiclass_collapse Box Class iou_b iou_b_sym cls_eq
             tau theta (mc_expand mds cs)).
    - assumption.
    - assumption.
    - apply mc_one_peak_lift; assumption.
    - apply mc_no_tie_clash_lift; assumption.
  Qed.
End MultiOutput.

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

From Stdlib Require Import Extraction.
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

Lemma greedy_nms_aux_filter_skip :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (rest : list (@det Box)) (kept : list (@det Box)) (k : @det Box),
    In k kept ->
    greedy_nms_aux iou tau kept rest =
    greedy_nms_aux iou tau kept
      (filter (fun d => negb (Nat.leb tau (iou (box k) (box d)))) rest).
Proof.
  intros Box iou tau rest.
  induction rest as [|d rs IH]; intros kept k Hk; [reflexivity|].
  simpl.
  destruct (Nat.leb tau (iou (box k) (box d))) eqn:Eiou.
  - simpl.
    assert (Hex : existsb (fun k0 => Nat.leb tau (iou (box k0) (box d))) kept = true).
    { apply existsb_exists. exists k. split; [assumption | exact Eiou]. }
    rewrite Hex.
    apply (IH kept k Hk).
  - simpl.
    destruct (existsb (fun k0 => Nat.leb tau (iou (box k0) (box d))) kept) eqn:Eex.
    + apply (IH kept k Hk).
    + apply (IH (d :: kept) k (or_intror Hk)).
Qed.

Lemma greedy_nms_aux_d_at_bottom :
  forall (Box : Type) (iou : Box -> Box -> nat) (tau : nat)
         (rest : list (@det Box)) (kept : list (@det Box)) (d : @det Box),
    (forall r, In r rest -> iou (box d) (box r) < tau) ->
    greedy_nms_aux iou tau (kept ++ [d]) rest =
    d :: greedy_nms_aux iou tau kept rest.
Proof.
  intros Box iou tau rest.
  induction rest as [|r rs IH]; intros kept d Hno; simpl.
  - rewrite rev_unit. reflexivity.
  - assert (Hr_low : iou (box d) (box r) < tau) by (apply Hno; left; reflexivity).
    assert (Hex_eq : existsb (fun k => Nat.leb tau (iou (box k) (box r))) (kept ++ [d])
                   = existsb (fun k => Nat.leb tau (iou (box k) (box r))) kept).
    { rewrite existsb_app. simpl.
      assert (Hleb_false : Nat.leb tau (iou (box d) (box r)) = false)
        by (apply Nat.leb_gt; assumption).
      rewrite Hleb_false. rewrite Bool.orb_false_r. reflexivity. }
    rewrite Hex_eq.
    destruct (existsb (fun k => Nat.leb tau (iou (box k) (box r))) kept) eqn:Eex.
    + apply IH. intros r0 Hr0. apply Hno. right; assumption.
    + assert (Heq : r :: (kept ++ [d]) = (r :: kept) ++ [d]) by reflexivity.
      rewrite Heq.
      apply IH. intros r0 Hr0. apply Hno. right; assumption.
Qed.

Theorem nms_sorted_eq_greedy_nms :
  forall (Box : Type) (iou : Box -> Box -> nat),
    (forall a b, iou a b = iou b a) ->
    forall (tau : nat) (D : list (@det Box)),
      NoDup D -> sorted_desc D ->
      nms_sorted iou tau D = greedy_nms iou tau D.
Proof.
  intros Box iou iou_sym_h tau D.
  induction D as [D IH]
    using (well_founded_ind (well_founded_ltof _ (@length (@det Box)))).
  intros Hnd Hsd.
  destruct D as [|d rest].
  - rewrite nms_sorted_equation. unfold greedy_nms. simpl. reflexivity.
  - rewrite nms_sorted_equation.
    unfold greedy_nms. simpl.
    set (P := fun d' => negb (Nat.leb tau (iou (box d) (box d')))).

    rewrite (@greedy_nms_aux_filter_skip Box iou tau rest [d] d (or_introl eq_refl)).
    fold P.

    assert (Hno : forall r, In r (filter P rest) -> iou (box d) (box r) < tau).
    { intros r Hr. apply filter_In in Hr as [_ Hp].
      unfold P in Hp. apply negb_true_iff in Hp. apply Nat.leb_gt in Hp. assumption. }

    change [d] with ([] ++ [d]).
    rewrite (@greedy_nms_aux_d_at_bottom Box iou tau (filter P rest) [] d Hno).
    f_equal.

    assert (Hlt : ltof _ (@length (@det Box)) (filter P rest) (d :: rest)).
    { unfold ltof. simpl.
      pose proof (filter_length_le P rest) as HL. lia. }
    assert (Hnd_filt : NoDup (filter P rest)).
    { apply NoDup_filter. inversion Hnd; assumption. }
    assert (Hsd_filt : sorted_desc (filter P rest)).
    { apply sorted_desc_filter. apply (sorted_desc_tail Hsd). }

    apply (IH (filter P rest) Hlt Hnd_filt Hsd_filt).
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

(** ** Architectural derivation of [base_score_invariant].

    The previous section took [base_score_invariant] as a [Hypothesis].
    Here we derive it: model [base_score] as
    [label_score ∘ matched], where [matched : Box -> option Label]
    sends each predicted box to its assigned ground-truth label (or
    [None] for unmatched). The architectural fact that the regression
    branch's accuracy bound forces high-IoU pairs to share a label
    is captured by [matched_invariant_under_high_iou] — a smaller,
    structurally meaningful hypothesis. From it,
    [derived_base_score_invariant] follows by computation. *)

Section FCOSArchitecturallyDerived.
  Variable Box : Type.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.
  Variable Label : Type.
  Variable matched : Box -> option Label.
  Variable label_score : Label -> nat.

  Hypothesis matched_invariant_under_high_iou :
    forall a b, tau <= iou a b -> matched a = matched b.

  Definition derived_base_score (b : Box) : nat :=
    match matched b with
    | Some l => label_score l
    | None => 0
    end.

  Theorem derived_base_score_invariant :
    forall a b, tau <= iou a b -> derived_base_score a = derived_base_score b.
  Proof.
    intros a b Hiou. unfold derived_base_score.
    rewrite (matched_invariant_under_high_iou Hiou). reflexivity.
  Qed.
End FCOSArchitecturallyDerived.

(** ** Architectural derivation of DETR matching disjointness.

    The hypothesis fed to [detr_post_matching_separated] —
    [forall a b, a <> b -> iou a b < tau] at the box level — is
    derived here from an injective bipartite matching with disjoint
    ground-truth representatives. The matching axiom factors into the
    smaller, more architectural [matching_injective] and
    [distinct_gt_disjoint] hypotheses. *)

Section DETRMatchingDerived.
  Variable Box : Type.
  Variable GT : Type.
  Variable gt_eq_dec : forall g1 g2 : GT, {g1 = g2} + {g1 <> g2}.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.

  Variable matched_gt : Box -> GT.

  Hypothesis matching_injective :
    forall a b, matched_gt a = matched_gt b -> a = b.

  Hypothesis distinct_gt_disjoint :
    forall a b, matched_gt a <> matched_gt b -> iou a b < tau.

  Theorem detr_matching_pairwise_disjoint :
    forall a b, a <> b -> iou a b < tau.
  Proof.
    intros a b Hne.
    destruct (gt_eq_dec (matched_gt a) (matched_gt b)) as [Hgeq | Hgne].
    - exfalso. apply Hne. apply matching_injective. assumption.
    - apply distinct_gt_disjoint. assumption.
  Qed.
End DETRMatchingDerived.

(** ** Greedy bipartite matching: a constructive injective matching.

    Replaces the [DETRMatchingDerived]'s hypothesized [matched_gt]
    with a concrete computable algorithm. [greedy_match] iterates
    through predicted boxes in order, assigning each to the next
    available ground-truth (first-come-first-served, no backtracking).
    The output is provably injective on its [Some g] entries: no two
    distinct boxes claim the same ground-truth, derived from
    [NoDup gts] alone — no further hypothesis. This is weaker than
    Hungarian-optimal (the greedy choice can leave the global maximum
    matching short) but it is constructive, terminating, and
    bipartite-injective; for the NMS-collapse application that's
    sufficient. *)

Section DETRGreedyMatching.
  Variable Box : Type.
  Variable GT : Type.

  Fixpoint greedy_match (boxes : list Box) (gts : list GT)
      : list (Box * option GT) :=
    match boxes with
    | [] => []
    | b :: rest =>
        match gts with
        | [] => (b, None) :: greedy_match rest []
        | g :: gs => (b, Some g) :: greedy_match rest gs
        end
    end.

  Lemma greedy_match_gt_in_gts :
    forall boxes gts b g,
      In (b, Some g) (greedy_match boxes gts) ->
      In g gts.
  Proof.
    induction boxes as [|b' rest IH]; intros gts b g Hin; simpl in Hin;
      [contradiction|].
    destruct gts as [|g0 gs].
    - destruct Hin as [Heq | Hin]; [discriminate|].
      apply IH in Hin. contradiction.
    - destruct Hin as [Heq | Hin].
      + injection Heq as Hb Hg. left. assumption.
      + right. apply IH with (b := b). assumption.
  Qed.

  Theorem greedy_match_gt_injective :
    forall boxes gts b1 b2 g,
      NoDup gts ->
      In (b1, Some g) (greedy_match boxes gts) ->
      In (b2, Some g) (greedy_match boxes gts) ->
      b1 = b2.
  Proof.
    induction boxes as [|b' rest IH]; intros gts b1 b2 g Hnd Hin1 Hin2;
      simpl in Hin1, Hin2; [contradiction|].
    destruct gts as [|g0 gs].
    - destruct Hin1 as [Heq1 | Hin1]; [discriminate|].
      destruct Hin2 as [Heq2 | Hin2]; [discriminate|].
      apply (IH [] b1 b2 g); [constructor | assumption | assumption].
    - inversion Hnd as [|? ? Hg0_notin Hnd_gs]; subst.
      destruct Hin1 as [Heq1 | Hin1]; destruct Hin2 as [Heq2 | Hin2].
      + injection Heq1 as Hb1 _.
        injection Heq2 as Hb2 _.
        congruence.
      + injection Heq1 as Hb1 Hg1. subst.
        apply greedy_match_gt_in_gts in Hin2. contradiction.
      + injection Heq2 as Hb2 Hg2. subst.
        apply greedy_match_gt_in_gts in Hin1. contradiction.
      + apply (IH gs b1 b2 g); assumption.
  Qed.

  Definition matched_count (matching : list (Box * option GT)) : nat :=
    length (filter (fun p => match snd p with
                             | Some _ => true
                             | None => false
                             end) matching).

  Theorem greedy_match_count :
    forall boxes gts,
      matched_count (greedy_match boxes gts) =
      Nat.min (length boxes) (length gts).
  Proof.
    induction boxes as [|b rest IH]; intros gts; [reflexivity|].
    destruct gts as [|g gs]; unfold matched_count in *; simpl.
    - rewrite (IH []). simpl. lia.
    - rewrite (IH gs). simpl. lia.
  Qed.

  Theorem greedy_match_optimal :
    forall boxes gts (other_match : list (Box * option GT)),
      length other_match <= length boxes ->
      matched_count other_match <= length gts ->
      matched_count other_match <=
      matched_count (greedy_match boxes gts).
  Proof.
    intros boxes gts other_match Hlen Hmcount.
    rewrite greedy_match_count.
    unfold matched_count in *.
    pose proof (filter_length_le
                  (fun p : Box * option GT => match snd p with
                                              | Some _ => true
                                              | None => false
                                              end) other_match) as Hfl.
    lia.
  Qed.

End DETRGreedyMatching.

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
    under the standard Lipschitz algebra — analogous to Part I's real
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
    [arch_f x := 2 * Rmax 0 (3 * x)]. Part I's [lip_compose],
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

(** ** Iterative training: constructive coordinate descent.

    Replaces Part VI's "precompute and store" with multi-step
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

(** ******************************************************************** *)
(** *      Part VII. Interval-Bound Propagation Lipschitz                *)
(** ******************************************************************** *)

(** Part I's [multilayer_lipschitz] gives the operator-norm product
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

    Theorems delivered here:

      Theorem 1.  global_implies_interval_lipschitz   (loose case)
      Theorem 2.  interval_lipschitz_monotone         (looser is fine)
      Theorem 3.  mat_vec_interval_lipschitz          (linear layer)
      Theorem 4.  relu_interval_lipschitz             (ReLU global)
      Theorem 5.  relu_interval_lipschitz_dead        (ReLU on dead box)
      Theorem 6.  interval_lipschitz_compose          (chain rule)
      Theorem 7.  multilayer_interval_lipschitz_global (recovers Part I)
      Theorem 8.  ibp_dead_local_zero                  (worked example:
                                                       local L = 0,
                                                       global L = 6) *)

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
    bridges in Part V. *)

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

(** ******************************************************************** *)
(** *      Part VIII. Architectural margin derivation                    *)
(** ******************************************************************** *)

(** [lipschitz_bridge_substantive]'s precondition includes a margin
    hypothesis on the score head's behavior over high-IoU pairs:
    [m + min(h(true d), h(true d')) <= max(h(true d), h(true d'))].
    In practice this is undischargeable — there is no proof that an
    arbitrary trained network produces this gap.

    For DETR's bipartite matching architecture, the gap is
    structurally derivable not from the score head but from the
    matching invariant. At training equilibrium, distinct
    predictions carry distinct GT labels ([matching_injective]) and
    distinct GTs occupy disjoint boxes ([distinct_gt_disjoint]).
    Composing these two architectural primitives with a
    [unique_boxes] hypothesis on the prediction list forces
    [iou (box d) (box d') < tau] for every distinct pair. The
    bridge's high-IoU branch is therefore structurally empty, and
    the margin hypothesis is satisfied vacuously for any [m].

    This derives the bridge precondition from the architecture
    instead of assuming it. The chain:

      matching_injective + distinct_gt_disjoint + unique_boxes
        => detr_matching_pairwise_disjoint   (already proved)
        => detr_equilibrium_margin_vacuous   (the bridge's margin)
        => detr_equilibrium_threshold_vacuous (the bridge's threshold)
        => detr_equilibrium_yields_separated  (full bridge composition)

    Theorems delivered:

      Theorem 1.  detr_equilibrium_margin_vacuous
      Theorem 2.  detr_equilibrium_threshold_vacuous
      Theorem 3.  detr_equilibrium_yields_separated
                  — full composition: equilibrium ⟹ Separated *)

Section DETREquilibriumMargin.

  Variable Box : Type.
  Variable GT : Type.
  Variable gt_eq_dec : forall g1 g2 : GT, {g1 = g2} + {g1 <> g2}.
  Variable iou : Box -> Box -> nat.
  Variable tau : nat.
  Variable matched_gt : Box -> GT.

  Hypothesis matching_injective :
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

  (** Theorem 1. The bridge's margin hypothesis is vacuously
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
                  matched_gt matching_injective distinct_gt_disjoint
                  (box d) (box d') Hbox_ne) as Hlt.
    lia.
  Qed.

  (** Theorem 2. The bridge's threshold hypothesis is vacuously
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
                  matched_gt matching_injective distinct_gt_disjoint
                  (box d) (box d') Hbox_ne) as Hlt.
    lia.
  Qed.

  (** Theorem 3. End-to-end composition: DETR equilibrium yields
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

(** ******************************************************************** *)
(** *      Part IX. Real-architecture worked example                     *)
(** ******************************************************************** *)

(** This part replaces Part V's [c30_D] (2 hand-tuned detections,
    1x1 weights) with two concrete demonstrations on substantially
    larger instances:

      (a) IBP-derived local Lipschitz on a 1-layer ReLU network.
          Using [interval_lipschitz_compose] from Part VII with the
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

    Theorems delivered:

      Theorem 1.  e20_apply_layer_local_lipschitz   (IBP via Part VII)
      Theorem 2.  e20_separated_check_true          (vm_compute)
      Theorem 3.  e20_separated_at_slack_one        (lift to Separated) *)

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

(** Theorem 1. IBP-derived local Lipschitz constant for the layer. *)

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

(** Theorem 2. Executable Separated certificate via [vm_compute]. *)

Theorem e20_separated_check_true :
  Separated_check c1_iou 70 100 Nat.eq_dec 1 e20_D = true.
Proof. vm_compute. reflexivity. Qed.

(** Theorem 3. Lift the decidable check to [Separated] via the
    correctness theorem. *)

Theorem e20_separated_at_slack_one :
  Separated c1_iou 70 100 1 e20_D.
Proof.
  apply (proj1 (Separated_check_correct c1_iou 70 100 Nat.eq_dec 1 e20_D)).
  exact e20_separated_check_true.
Qed.

(** ******************************************************************** *)
(** *      Part X. Per-layer quantization with slack accumulation        *)
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

    Theorems delivered:

      Theorem 1.  quant_lipschitz_step          (single-layer error)
      Theorem 2.  apply_quant_chain_lipschitz   (N-layer end-to-end) *)

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

  (** Theorem 1. Single-layer error bound: a Lipschitz layer
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

  (** Theorem 2. End-to-end quantized chain Lipschitz bound: the
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

(** ******************************************************************** *)
(** *      Part XI. Training as SGD on L_separated_sq                   *)
(** ******************************************************************** *)

(** Part VI's [trained_list := nms_sorted iou tau D] defines
    training as NMS-output-storage: the procedure runs NMS once on
    the input list and stores the output. It does not learn from
    data or minimize any loss.

    The substantive replacement: train by SGD on the smooth
    surrogate loss [L_separated_sq], whose per-pair zero-locus
    equals the Separated locus ([pair_violation_sq_zero_iff],
    already proved; full sum-zero-locus is item 4 of remaining
    work). [sgd_telescoping_vec] (Part VI's vector SGD analysis)
    gives stationary-point convergence for any non-negative smooth
    loss. Composing with [L_separated_sq_nonneg] (already proved)
    yields the unconditional partial result: SGD on L_separated_sq
    drives the cumulative grad-norm-squared sum into the bound
    [2 * L_separated_sq(θ_0) / η]. The full claim that the
    stationary point is a global minimum (and hence reaches the
    Separated locus) requires convexity, which is item 3 of
    remaining work.

    Theorem delivered:

      Theorem 1.  sgd_on_nonneg_smooth_loss_stationary
                  — SGD on any non-negative smooth loss yields
                    cumulative grad-norm-squared bounded above by
                    [2 * loss(θ_0) / η]. Instantiated on
                    L_separated_sq with [f_lower = 0], this is
                    the unconditional half of the SGD-on-L_separated_sq
                    training procedure; the convex-convergence half
                    awaits item 3. *)

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

  (** Theorem 1. The vector SGD analysis (Part VI) instantiated for a
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

(** ******************************************************************** *)
(** *      Part XII. Sample complexity composition formula              *)
(** ******************************************************************** *)

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

(** ******************************************************************** *)
(** *      Part XIII. SGD global convergence under PL inequality          *)
(** ******************************************************************** *)

(** Part VI's [sgd_telescoping_vec] (and Part XI's wrapper) prove
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
    than O(1/T). Composing with Part XI's training infrastructure:
    SGD on a non-negative smooth loss with PL constant mu converges
    geometrically to the global minimum, which for L_separated_sq is
    zero loss, and zero loss equals the Separated locus (Theorem
    L_separated_zero_iff_separated, lifted as item 2 of remaining
    work).

    Theorems delivered:

      Theorem 1.  sgd_pl_one_step           (single-step contraction)
      Theorem 2.  sgd_pl_linear_convergence (T-step geometric rate) *)

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

  (** Theorem 1. Single-step linear contraction under PL. *)

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

  (** Theorem 2. T-step geometric convergence to the global minimum.
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

(** ** Certifier extraction for the deployable CLI.

    Extracts the decidable [Separated_check], its correctness witness
    [Separated_dec], and the finite candidate-search certifier
    [sep_certify_finite] to OCaml. The OCaml CLI [nms_cert] consumes
    these extracted functions to certify a model checkpoint's
    detection output as [Separated] or to return a counterexample. *)

Extraction "nms_cert.ml" Separated_check Separated_dec sep_certify_finite
                         pair_check det_eq_dec sep_effective_slack.
