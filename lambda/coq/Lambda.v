From Coq
Require Import List ListSet Program.Equality.

Section terms.

Context
  (variable : Type)
  (variable_eq_dec : forall x y:variable, {x = y} + {x <> y})
  (fresh_var : forall l : set variable, exists v : variable, ~In v l)
  .

Inductive Term : Type :=
    | V : variable -> Term
    | Lam : variable -> Term -> Term
    | App : Term -> Term -> Term
    .

Fixpoint free_vars (t : Term) : set variable :=
    match t with
    | V x => set_add variable_eq_dec x (empty_set variable)
    | App t1 t2 => set_union variable_eq_dec (free_vars t1) (free_vars t2)
    | Lam x t => set_remove variable_eq_dec x (free_vars t)
    end.

Lemma free_vars_nodup (t : Term) : NoDup (free_vars t).
Proof.
    induction t; simpl.
    - constructor; [|constructor]. intro. contradiction.
    - apply set_remove_nodup.  assumption.
    - apply set_union_nodup; assumption.
Qed.

Definition free (v : variable) (t : Term) : Prop :=
    In v (free_vars t).

Fixpoint bound_vars (t : Term) : set variable :=
    match t with
    | V x => empty_set variable
    | App t1 t2 => set_union variable_eq_dec (bound_vars t1) (bound_vars t2)
    | Lam x t => set_add variable_eq_dec x (bound_vars t)
    end.

Lemma bound_vars_nodup (t : Term) : NoDup (bound_vars t).
Proof.
    induction t; simpl.
    - constructor.
    - apply set_add_nodup.  assumption.
    - apply set_union_nodup; assumption.
Qed.

Definition bound (v : variable) (t : Term) : Prop :=
    In v (bound_vars t).

Fixpoint all_vars (t : Term) : set variable :=
    match t with
    | V x => set_add variable_eq_dec x (empty_set variable)
    | App t1 t2 => set_union variable_eq_dec (all_vars t1) (all_vars t2)
    | Lam x t => set_add variable_eq_dec x (all_vars t)
    end.

Lemma all_vars_nodup (t : Term) : NoDup (all_vars t).
Proof.
    induction t; simpl.
    - constructor; [|constructor]. intro. contradiction.
    - apply set_add_nodup.  assumption.
    - apply set_union_nodup; assumption.
Qed.

Lemma free_all_vars (t : Term) : incl (free_vars t) (all_vars t).
Proof.
    induction t; simpl; intros var Hvar.
    - intuition.
    - apply set_add_iff.
      pose proof (free_vars_nodup t) as Hvt.
      rewrite set_remove_iff in Hvar by assumption.
      right. intuition.
    - apply set_union_iff. apply set_union_iff in Hvar.
      intuition.
Qed.

Lemma bound_all_vars (t : Term) : incl (bound_vars t) (all_vars t).
Proof.
    induction t; simpl; intros var Hvar.
    - intuition.
    - apply set_add_iff. apply set_add_iff in Hvar. intuition.
    - apply set_union_iff. apply set_union_iff in Hvar.
      intuition.
Qed.

Definition occurs (v : variable) (t : Term) : Prop :=
    In v (all_vars t).

Lemma free_occurs (v : variable) (t : Term) : free v t -> occurs v t.
Proof.
    apply free_all_vars.
Qed.

Lemma bound_occurs (v : variable) (t : Term) : bound v t -> occurs v t.
Proof.
    apply bound_all_vars.
Qed.

(* [u/x] t = t' *)
Inductive subst_prop : Term -> variable -> Term -> Term -> Prop :=
    | subst_var_eq : forall u x y, x = y -> subst_prop u x (V y) u
    | subst_var_neq : forall u x y, x <> y -> subst_prop u x (V y) (V y)
    | subst_app : forall u x t1 t2 t1' t2',
        subst_prop u x t1 t1' ->
        subst_prop u x t2 t2' ->
        subst_prop u x (App t1 t2) (App t1' t2')
    | subst_lam : forall u x y t t',
        x <> y ->
        ~free y u ->
        subst_prop u x t t' ->
        subst_prop u x (Lam y t) (Lam y t')
    .

Lemma subst_free_vars u x t t' :
    subst_prop u x t t' ->
    forall v, free v t' <-> (v <> x /\ free v t) \/ (free x t /\ free v u).
Proof.
    intros Hsub.
    induction Hsub; intro v; unfold free; simpl.
    - subst. intuition.
    - split; [|intuition].
      intros [Heq|contra]; [|contradiction]. subst.
      left. intuition.
    - rewrite !set_union_iff.
      specialize (IHHsub1 v).
      specialize (IHHsub2 v).
      unfold free in IHHsub1, IHHsub2.
      rewrite! IHHsub1, IHHsub2.
      clear. intuition.
    - pose proof (free_vars_nodup t) as Hvt. pose proof (free_vars_nodup t') as Hvt'.
      rewrite! set_remove_iff by assumption.
      specialize (IHHsub v). unfold free in IHHsub. rewrite IHHsub.
      clear IHHsub Hvt Hvt' Hsub.
      split.
      + intros [[[Hvx Ht] | [Ht Hu]] Hvy]; [left|right]; intuition.
      + intros [[Hvx [Ht Hvy]]|[[Ht Hxy] Hu]].
        * split; [|assumption]. left. intuition.
        * split; [right; intuition|].
          unfold free in H0. intro contra. subst. contradiction.
Qed.

Lemma subst_exists x u t :
  ~bound x t ->
  (forall v, free v u -> ~bound v t) ->
  exists t1, subst_prop u x t t1.
Proof.
    induction t; intros Hx Hu.
    - destruct (variable_eq_dec x v).
      + subst. exists u. constructor. reflexivity.
      + exists (V v). constructor. assumption.
    - assert (Hxt : ~bound x t).
      { intro contra. elim Hx. apply set_add_iff. right. assumption. }
      assert (Hut : forall v, free v u -> ~bound v t).
      { intros y Hy contra. elim (Hu y Hy). apply set_add_iff. right. assumption. }
      specialize (IHt Hxt Hut).
      destruct IHt as [t1 Ht1].
      assert (Hxv : x <> v).
      { intro contra. elim Hx. apply set_add_iff. left. assumption. }
      exists (Lam v t1).
      apply (subst_lam u x v t t1 Hxv); [|assumption].
      intro contra. specialize (Hu v contra). elim Hu.
      apply set_add_iff. left. reflexivity.
    - assert (Hxt1 : ~bound x t1).
      { intro contra. elim Hx. apply set_union_iff. left. assumption. }
      assert (Hut1 : forall y, free y u -> ~bound y t1).
      { intros y Hy contra. elim (Hu y Hy). apply set_union_iff. left. assumption. }
      specialize (IHt1 Hxt1 Hut1).
      destruct IHt1 as [t1' Ht1'].
      assert (Hxt2 : ~bound x t2).
      { intro contra. elim Hx. apply set_union_iff. right. assumption. }
      assert (Hut2 : forall y, free y u -> ~bound y t2).
      { intros y Hy contra. elim (Hu y Hy). apply set_union_iff. right. assumption. }
      specialize (IHt2 Hxt2 Hut2).
      destruct IHt2 as [t2' Ht2'].
      exists (App t1' t2').
      constructor; assumption.
Qed.

Inductive alpha_eq : Term -> Term -> Prop :=
    | alpha_eq_refl : forall t, alpha_eq t t
    | alpha_eq_sym : forall u v, alpha_eq u v -> alpha_eq v u
    | alpha_eq_trans : forall u v t, alpha_eq u v -> alpha_eq v t -> alpha_eq u t
    | alpha_app_left : forall t1 t2 t1', alpha_eq t1 t1' -> alpha_eq (App t1 t2) (App t1' t2)
    | alpha_app_right : forall t1 t2 t2', alpha_eq t2 t2' -> alpha_eq (App t1 t2) (App t1 t2')
    | alpha_lam : forall x t1 t2, alpha_eq t1 t2 -> alpha_eq (Lam x t1) (Lam x t2)
    | alpha_rename : forall x t y t',
        ~free y t ->
        subst_prop (V y) x t t' ->
        alpha_eq (Lam x t) (Lam y t')
    .

Inductive alpha_eq_simple : Term -> Term -> Prop :=
    | alpha_eq_var : forall x y, x = y -> alpha_eq_simple (V x) (V y)
    | alpha_eq_app : forall t1 t2 t1' t2',
        alpha_eq_simple t1 t1' ->
        alpha_eq_simple t2 t2' ->
        alpha_eq_simple (App t1 t2) (App t1' t2')
    | alpha_eq_lam : forall x x' t t',
        x = x' ->
        alpha_eq_simple t t' ->
        alpha_eq_simple (Lam x t) (Lam x' t')
    | alpha_eq_rename : forall x x' y t t' t1 t1',
        x <> x' -> y <> x -> y <> x' -> ~free y t -> ~free y t' ->
        subst_prop (V y) x t t1 ->
        subst_prop (V y) x' t' t1' ->
        alpha_eq_simple t1 t1' ->
        alpha_eq_simple (Lam x t) (Lam x' t')
    .

Lemma alpha_eq_rename_exists_y x x' t t'
    : exists y, y <> x /\ y <> x' /\ ~occurs y t /\ ~occurs y t'.
Proof.
    unfold free.
    pose (x :: x' :: (all_vars t ++ all_vars t')) as fv.
    destruct (fresh_var fv) as [y Hy].
    exists y.
    subst fv.
    simpl in Hy. rewrite in_app_iff in Hy.
    intuition.
Qed.

Lemma alpha_eq_simple_refl t : alpha_eq_simple t t.
Proof.
    induction t.
    - constructor. reflexivity.
    - constructor; [reflexivity|assumption].
    - constructor; assumption.
Qed.

Lemma alpha_eq_simple_sym t1 t2 : alpha_eq_simple t1 t2 -> alpha_eq_simple t2 t1.
Proof.
    intro Ht. induction Ht.
    - constructor. subst. reflexivity.
    - constructor; assumption.
    - subst. constructor; [reflexivity|assumption].
    - apply (alpha_eq_rename x' x y t' t t1' t1); [congruence|..]; assumption.
Qed.

Lemma alpha_eq_simple_vars t1 t2 : alpha_eq_simple t1 t2 -> forall v, free v t1 <-> free v t2.
Proof.
    intro Ht12.
    induction Ht12; intros; unfold free; simpl.
    - subst. intuition.
    - rewrite !set_union_iff. unfold free in IHHt12_1, IHHt12_2.
      specialize (IHHt12_1 v). specialize (IHHt12_2 v).
      intuition.
    - specialize (IHHt12 v). subst.
      pose proof (free_vars_nodup t) as Hvt. pose proof (free_vars_nodup t') as Hvt'.
      rewrite !set_remove_iff by assumption.
      unfold free in IHHt12. intuition.
    - pose proof (free_vars_nodup t) as Hvt. pose proof (free_vars_nodup t') as Hvt'.
      specialize (IHHt12 v) as Hv.
      rewrite !set_remove_iff by assumption.
      apply subst_free_vars with (v := v) in H4.
      apply subst_free_vars with (v := v) in H5.
      unfold free in Hv.
      unfold free in H2, H3, H4, H5.
      rewrite H4, H5 in Hv. clear  H4 H5 Hvt Hvt'.
      simpl in Hv.
      split; intros Ht.
      + apply proj1 in Hv. apply and_comm in Ht. specialize (Hv (or_introl Ht)).
        apply and_comm.
        destruct Hv as [Hc | Hc]; [assumption|].
        destruct Hc as [Ht' [Hyv|contra]]; [|contradiction].
        subst. destruct Ht as [Hvx Ht]. contradiction.
      + apply proj2 in Hv. apply and_comm in Ht. specialize (Hv (or_introl Ht)).
        apply and_comm.
        destruct Hv as [Hc | Hc]; [assumption|].
        destruct Hc as [Ht' [Hyv|contra]]; [|contradiction].
        subst. destruct Ht as [Hvx Ht]. contradiction.
Qed.

Lemma alpha_subst_u u1 u2 x t t1' t2' :
    alpha_eq_simple u1 u2 ->
    subst_prop u1 x t t1' ->
    subst_prop u2 x t t2' ->
    alpha_eq_simple t1' t2'.
Proof.
    revert u1 u2 t1' t2'.
    induction t; intros u1 u2 t1' t2' Hu12 Ht1' Ht2'.
    - inversion Ht1'; inversion Ht2'; subst.
      + assumption.
      + contradiction.
      + contradiction.
      + constructor. reflexivity.
    - inversion Ht1'. subst. inversion Ht2'. subst.
      constructor; [reflexivity|].
      apply (IHt u1 u2); assumption.
    - inversion Ht1'. subst. inversion Ht2'. subst.
      constructor.
      + apply (IHt1 u1 u2); assumption.
      + apply (IHt2 u1 u2); assumption.
Qed.

Lemma alpha_subst_t u x t1 t2 t1' t2' :
    ~bound x t1 ->
    ~bound x t2 ->
    alpha_eq_simple t1 t2 ->
    subst_prop u x t1 t1' ->
    subst_prop u x t2 t2' ->
    alpha_eq_simple t1' t2'.
Proof.
    revert u t2 t1' t2'.
    induction t1; intros u t2 t1' t2' Ht12 Ht1' Ht2'.
    - inversion Ht12; subst. inversion Ht1'; inversion Ht2'; subst.
      + apply alpha_eq_simple_refl.
      + contradiction.
      + contradiction.
      + constructor. reflexivity.
    - inversion Ht1'. subst.
      inversion Ht12; subst.
      + inversion Ht2'. subst.
        constructor; [reflexivity|].
        apply (IHt1 u t'0); assumption.
      + inversion Ht2'. subst.
        specialize (alpha_eq_rename v x' y t'0 t'1) as Hren.
        assert (Hy0 : ~ free y t'0 ).
        { apply subst_free_vars with (v := y) in H14.
          intro contra. apply H14 in contra.
          destruct contra as [[Hxy Ht1]|[Ht1 Hu]]; try contradiction.

        }
        admit.
    - inversion Ht12; subst. inversion Ht1'. subst. inversion Ht2'. subst.
      constructor.
      + apply (IHt1_1 u t1'0); assumption.
      + apply (IHt1_2 u t2'0); assumption.
Qed.


Lemma alpha_eq_simple_tran t1 t2 t3 : alpha_eq_simple t1 t2 -> alpha_eq_simple t2 t3 -> alpha_eq_simple t1 t3.
Proof.
    revert t1 t3.
    induction t2; intros t1 t3 Ht1 Ht3.
    - inversion Ht1. subst. clear Ht1. inversion Ht3.  constructor. assumption.
    - inversion Ht1; inversion Ht3; subst.
      + constructor; [reflexivity|]. revert H3 H8. apply IHt2.
      + specialize (alpha_eq_rename v x'0 y t t'0).


End terms.