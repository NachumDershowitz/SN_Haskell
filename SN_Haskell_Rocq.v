(*************************************************************************)
(*  A Rocq formalization of de Vrijer's decreasing measure.                *)
(*                                                                       *)
(*  This is a first-order formal companion to SN_Haskell.hs.  The Haskell *)
(*  paper uses a higher-order/final representation for compact executable *)
(*  code.  Here we use intrinsically typed de Bruijn syntax, because that  *)
(*  is the convenient representation for a proof assistant: substitution  *)
(*  and contextual beta-reduction are explicit and machine-checked.  The  *)
(*  development imports Rocq's standard functional extensionality library  *)
(*  for equality of semantic functions.                                  *)
(*************************************************************************)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

Import ListNotations.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* ---------------------------------------------------------------------- *)
(* Types and de Vrijer's semantic domains.                                *)

Inductive ty : Type :=
| base : ty
| arr  : ty -> ty -> ty.

Notation "s ~~> t" := (arr s t) (at level 60, right associativity).

Fixpoint den (t : ty) : Type :=
  match t with
  | base => nat
  | arr s u => (den s -> den u) * nat
  end.

Definition star (t : ty) : den t -> nat :=
  match t return den t -> nat with
  | base => fun n => n
  | arr _ _ => fun p => snd p
  end.

Definition dot {s u : ty} (f : den (s ~~> u)) (a : den s) : den u :=
  fst f a.

Fixpoint add (t : ty) (k : nat) : den t -> den t :=
  match t return den t -> den t with
  | base => fun n => n + k
  | arr s u => fun p => (fun a => add u k (fst p a), snd p + k)
  end.

Fixpoint canon (t : ty) (n : nat) : den t :=
  match t return den t with
  | base => n
  | arr s u => (fun a => canon u (n + star s a), n)
  end.

Definition lamD (s u : ty) (body : den s -> den u) : den (s ~~> u) :=
  (fun a => add u (star s a + 1) (body a),
   star u (body (canon s 0))).

Definition appD {s u : ty} (f : den (s ~~> u)) (a : den s) : den u :=
  dot f a.

(* Recursive non-strict order, strict order, and admissibility. *)

Fixpoint ge (t : ty) : den t -> den t -> Prop :=
  match t return den t -> den t -> Prop with
  | base => fun a b => a >= b
  | arr s u => fun p q =>
      snd p >= snd q /\
      forall a, adm s a -> ge u (fst p a) (fst q a)
  end
with gt (t : ty) : den t -> den t -> Prop :=
  match t return den t -> den t -> Prop with
  | base => fun a b => a > b
  | arr s u => fun p q =>
      snd p > snd q /\
      forall a, adm s a -> gt u (fst p a) (fst q a)
  end
with adm (t : ty) : den t -> Prop :=
  match t return den t -> Prop with
  | base => fun _ => True
  | arr s u => fun p =>
      (forall a, adm s a -> adm u (fst p a)) /\
      (forall a b, adm s a -> adm s b -> ge s a b ->
                   ge u (fst p a) (fst p b)) /\
      (forall a b, adm s a -> adm s b -> gt s a b ->
                   gt u (fst p a) (fst p b))
  end.

(* ---------------------------------------------------------------------- *)
(* Elementary properties of the domains.                                  *)

Lemma pair_den_ext : forall s u (p q : den (s ~~> u)),
  (forall a, fst p a = fst q a) -> snd p = snd q -> p = q.
Proof.
  intros s u [f m] [g n] Hfg Hmn. simpl in *. subst n.
  f_equal. apply functional_extensionality. exact Hfg.
Qed.

Lemma gt_ge : forall t (a b : den t), gt t a b -> ge t a b.
Proof.
  induction t as [| s IHs u IHu]; simpl; intros a b H; simpl in H.
  - apply Nat.lt_le_incl; assumption.
  - destruct a as [f m], b as [g n]. simpl in H. destruct H as [Hmn Hfg]. simpl in *. split.
    + apply Nat.lt_le_incl; assumption.
    + intros x Hx. apply IHu. apply Hfg; assumption.
Qed.

Lemma gt_star : forall t (a b : den t), gt t a b -> star t a > star t b.
Proof.
  destruct t; simpl; intros a b H; simpl in H.
  - assumption.
  - destruct a as [f m], b as [g n]. simpl in H. exact (proj1 H).
Qed.

Lemma ge_star : forall t (a b : den t), ge t a b -> star t a >= star t b.
Proof.
  destruct t; simpl; intros a b H; simpl in H.
  - assumption.
  - destruct a as [f m], b as [g n]. simpl in H. exact (proj1 H).
Qed.

Lemma ge_refl : forall t (a : den t), adm t a -> ge t a a.
Proof.
  induction t as [| s IHs u IHu]; simpl; intros a Ha.
  - apply Nat.le_refl.
  - destruct a as [f n]. destruct Ha as [Hadm [Hge _]]. split.
    + apply Nat.le_refl.
    + intros x Hx. apply IHu. apply Hadm; assumption.
Qed.

Lemma ge_trans : forall t (a b c : den t),
  ge t a b -> ge t b c -> ge t a c.
Proof.
  induction t as [| s IHs u IHu]; simpl; intros a b c Hab Hbc; simpl in Hab, Hbc.
  - eapply Nat.le_trans; eauto.
  - destruct a as [f m], b as [g n], c as [h r].
    simpl in Hab, Hbc. destruct Hab as [Hmn Hfg]. destruct Hbc as [Hnr Hgh]. simpl in *. split.
    + eapply Nat.le_trans; eauto.
    + intros x Hx. eapply IHu; eauto.
Qed.

Lemma gt_ge_trans : forall t (a b c : den t),
  gt t a b -> ge t b c -> gt t a c.
Proof.
  induction t as [| s IHs u IHu]; simpl; intros a b c Hab Hbc; simpl in Hab, Hbc.
  - eapply Nat.le_lt_trans; eauto.
  - destruct a as [f m], b as [g n], c as [h r].
    simpl in Hab, Hbc. destruct Hab as [Hmn Hfg]. destruct Hbc as [Hnr Hgh]. simpl in *. split.
    + eapply Nat.le_lt_trans; eauto.
    + intros x Hx. eapply IHu; eauto.
Qed.

Lemma ge_gt_trans : forall t (a b c : den t),
  ge t a b -> gt t b c -> gt t a c.
Proof.
  induction t as [| s IHs u IHu]; simpl; intros a b c Hab Hbc; simpl in Hab, Hbc.
  - eapply Nat.lt_le_trans; eauto.
  - destruct a as [f m], b as [g n], c as [h r].
    simpl in Hab, Hbc. destruct Hab as [Hmn Hfg]. destruct Hbc as [Hnr Hgh]. simpl in *. split.
    + eapply Nat.lt_le_trans; eauto.
    + intros x Hx. eapply IHu; eauto.
Qed.

Lemma star_add : forall t k (a : den t),
  star t (add t k a) = star t a + k.
Proof.
  destruct t; simpl; reflexivity.
Qed.

Lemma add_zero : forall t (a : den t), add t 0 a = a.
Proof.
  induction t as [| s IHs u IHu]; simpl; intro a.
  - apply Nat.add_0_r.
  - destruct a as [f n]. apply pair_den_ext.
    + intro x. apply IHu.
    + apply Nat.add_0_r.
Qed.

Lemma nat_add_gt_by_k : forall a b k l,
  a >= b -> k > l -> a + k > b + l.
Proof.
  intros a b k l Hab Hkl.
  eapply Nat.lt_le_trans.
  - apply Nat.add_lt_mono_l; exact Hkl.
  - apply Nat.add_le_mono_r; exact Hab.
Qed.

Lemma add_ge_same : forall t k (a b : den t),
  adm t a -> adm t b -> ge t a b -> ge t (add t k a) (add t k b).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros k a b Ha Hb Hab; simpl in Ha, Hb, Hab.
  - apply Nat.add_le_mono; [assumption|apply Nat.le_refl].
  - destruct a as [f m], b as [g n]. simpl in *.
    destruct Ha as [Hadma [Hgea Hgta]]. destruct Hb as [Hadmb [Hgeb Hgtb]].
    destruct Hab as [Hmn Hfg]. split.
    + apply Nat.add_le_mono; [assumption|apply Nat.le_refl].
    + intros x Hx. apply IHu.
      * apply Hadma; assumption.
      * apply Hadmb; assumption.
      * apply Hfg; assumption.
Qed.

Lemma add_gt_same : forall t k (a b : den t),
  adm t a -> adm t b -> gt t a b -> gt t (add t k a) (add t k b).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros k a b Ha Hb Hab; simpl in Ha, Hb, Hab.
  - apply Nat.add_lt_mono_r; assumption.
  - destruct a as [f m], b as [g n]. simpl in *.
    destruct Ha as [Hadma [Hgea Hgta]]. destruct Hb as [Hadmb [Hgeb Hgtb]].
    destruct Hab as [Hmn Hfg]. split.
    + apply Nat.add_lt_mono_r; assumption.
    + intros x Hx. apply IHu.
      * apply Hadma; assumption.
      * apply Hadmb; assumption.
      * apply Hfg; assumption.
Qed.


Lemma nat_add_ge_by_k : forall a b k l,
  a >= b -> k >= l -> a + k >= b + l.
Proof.
  intros a b k l Hab Hkl.
  eapply Nat.le_trans.
  - apply Nat.add_le_mono_l. exact Hkl.
  - apply Nat.add_le_mono_r. exact Hab.
Qed.

Lemma add_ge_by_k : forall t k l (a b : den t),
  adm t a -> adm t b -> ge t a b -> k >= l ->
  ge t (add t k a) (add t l b).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros k l a b Ha Hb Hab Hkl; simpl in Ha, Hb, Hab.
  - apply nat_add_ge_by_k; assumption.
  - destruct a as [f m], b as [g n]. simpl in *.
    destruct Ha as [Hadma [Hgea Hgta]]. destruct Hb as [Hadmb [Hgeb Hgtb]].
    destruct Hab as [Hmn Hfg]. split.
    + apply nat_add_ge_by_k; assumption.
    + intros x Hx. apply IHu.
      * apply Hadma; assumption.
      * apply Hadmb; assumption.
      * apply Hfg; assumption.
      * assumption.
Qed.

Lemma add_gt_by_k : forall t k l (a b : den t),
  adm t a -> adm t b -> ge t a b -> k > l ->
  gt t (add t k a) (add t l b).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros k l a b Ha Hb Hab Hkl; simpl in Ha, Hb, Hab.
  - apply nat_add_gt_by_k; assumption.
  - destruct a as [f m], b as [g n]. simpl in *.
    destruct Ha as [Hadma [Hgea Hgta]]. destruct Hb as [Hadmb [Hgeb Hgtb]].
    destruct Hab as [Hmn Hfg]. split.
    + apply nat_add_gt_by_k; assumption.
    + intros x Hx. apply IHu.
      * apply Hadma; assumption.
      * apply Hadmb; assumption.
      * apply Hfg; assumption.
      * assumption.
Qed.

Lemma add_adm : forall t k (a : den t),
  adm t a -> adm t (add t k a).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros k a Ha.
  - exact I.
  - destruct a as [f n]. simpl in *.
    destruct Ha as [Hadm [Hge Hgt]]. repeat split.
    + intros x Hx. apply IHu. apply Hadm; assumption.
    + intros x y Hx Hy Hxy. apply add_ge_same.
      * apply Hadm; assumption.
      * apply Hadm; assumption.
      * apply Hge; assumption.
    + intros x y Hx Hy Hxy. apply add_gt_same.
      * apply Hadm; assumption.
      * apply Hadm; assumption.
      * apply Hgt; assumption.
Qed.

Lemma add_positive : forall t k (a : den t),
  adm t a -> k > 0 -> gt t (add t k a) a.
Proof.
  intros t k a Ha Hk. rewrite <- (add_zero t a) at 2.
  apply add_gt_by_k; try assumption.
  apply ge_refl; assumption.
Qed.

Lemma canon_ge : forall t n m, n >= m -> ge t (canon t n) (canon t m).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros n m Hnm.
  - assumption.
  - split.
    + assumption.
    + intros x Hx. apply IHu. apply Nat.add_le_mono; [assumption|apply Nat.le_refl].
Qed.

Lemma canon_gt : forall t n m, n > m -> gt t (canon t n) (canon t m).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros n m Hnm.
  - assumption.
  - split.
    + assumption.
    + intros x Hx. apply IHu. apply Nat.add_lt_mono_r; assumption.
Qed.

Lemma canon_adm : forall t n, adm t (canon t n).
Proof.
  induction t as [| s IHs u IHu]; simpl; intros n.
  - exact I.
  - repeat split.
    + intros x Hx. apply IHu.
    + intros x y Hx Hy Hxy. apply canon_ge.
      apply Nat.add_le_mono_l. apply ge_star; assumption.
    + intros x y Hx Hy Hxy. apply canon_gt.
      apply Nat.add_lt_mono_l. apply gt_star; assumption.
Qed.

Lemma lam_adm : forall s u (body : den s -> den u),
  (forall a, adm s a -> adm u (body a)) ->
  (forall a b, adm s a -> adm s b -> ge s a b -> ge u (body a) (body b)) ->
  adm (s ~~> u) (lamD s u body).
Proof.
  simpl; intros s u body Hbody_adm Hbody_ge. repeat split.
  - intros a Ha. apply add_adm. apply Hbody_adm; assumption.
  - intros a b Ha Hb Hab. apply add_ge_by_k.
    + apply Hbody_adm; assumption.
    + apply Hbody_adm; assumption.
    + apply Hbody_ge; assumption.
    + apply Nat.add_le_mono_r. apply ge_star; assumption.
  - intros a b Ha Hb Hab. apply add_gt_by_k.
    + apply Hbody_adm; assumption.
    + apply Hbody_adm; assumption.
    + apply Hbody_ge; try assumption. apply gt_ge; assumption.
    + apply Nat.add_lt_mono_r. apply gt_star; assumption.
Qed.

Lemma root_beta_decreases : forall s u (body : den s -> den u) (a : den s),
  adm s a -> adm u (body a) ->
  gt u (appD (lamD s u body) a) (body a).
Proof.
  intros s u body a Ha Hbody. unfold appD, dot, lamD. simpl.
  apply add_positive; [assumption|]. rewrite Nat.add_1_r. apply Nat.lt_0_succ.
Qed.

(* ---------------------------------------------------------------------- *)
(* Intrinsically typed de Bruijn syntax.                                  *)

Inductive var : list ty -> ty -> Type :=
| vz : forall Gamma t, var (t :: Gamma) t
| vs : forall Gamma t s, var Gamma t -> var (s :: Gamma) t.

Arguments vz {Gamma t}.
Arguments vs {Gamma t s} _.

Inductive tm : list ty -> ty -> Type :=
| TVar : forall Gamma t, var Gamma t -> tm Gamma t
| TApp : forall Gamma s u, tm Gamma (s ~~> u) -> tm Gamma s -> tm Gamma u
| TLam : forall Gamma s u, tm (s :: Gamma) u -> tm Gamma (s ~~> u).

Arguments TVar {Gamma t} _.
Arguments TApp {Gamma s u} _ _.
Arguments TLam {Gamma s u} _.

Definition Val (Gamma : list ty) := forall t, var Gamma t -> den t.
Definition Ren (Gamma Delta : list ty) := forall t, var Gamma t -> var Delta t.
Definition Sub (Gamma Delta : list ty) := forall t, var Gamma t -> tm Delta t.

Definition val_ext {Gamma s} (rho : Val Gamma) (a : den s) : Val (s :: Gamma).
Proof.
  intros t x. dependent destruction x.
  - exact a.
  - exact (rho _ x).
Defined.

Definition ren_ext {Gamma Delta s} (r : Ren Gamma Delta) :
  Ren (s :: Gamma) (s :: Delta).
Proof.
  intros t x. dependent destruction x.
  - exact vz.
  - exact (vs (r _ x)).
Defined.

Fixpoint rename {Gamma Delta t} (r : Ren Gamma Delta) (M : tm Gamma t)
  : tm Delta t :=
  match M in tm G t return Ren G Delta -> tm Delta t with
  | @TVar G t x => fun r => @TVar Delta t (r t x)
  | @TApp G s u M N => fun r => @TApp Delta s u (rename r M) (rename r N)
  | @TLam G s u M => fun r => @TLam Delta s u (rename (ren_ext r) M)
  end r.

Definition wk {Gamma s} : Ren Gamma (s :: Gamma) :=
  fun t x => vs x.

Definition sub_ext {Gamma Delta s} (sigma : Sub Gamma Delta) :
  Sub (s :: Gamma) (s :: Delta).
Proof.
  intros t x. dependent destruction x.
  - exact (TVar vz).
  - exact (rename wk (sigma _ x)).
Defined.

Fixpoint subst {Gamma Delta t} (sigma : Sub Gamma Delta) (M : tm Gamma t)
  : tm Delta t :=
  match M in tm G t return Sub G Delta -> tm Delta t with
  | @TVar G t x => fun sigma => sigma t x
  | @TApp G s u M N => fun sigma => @TApp Delta s u (subst sigma M) (subst sigma N)
  | @TLam G s u M => fun sigma => @TLam Delta s u (subst (sub_ext sigma) M)
  end sigma.

Definition sub0 {Gamma s} (N : tm Gamma s) : Sub (s :: Gamma) Gamma.
Proof.
  intros t x. dependent destruction x.
  - exact N.
  - exact (TVar x).
Defined.

Definition subst0 {Gamma s u} (N : tm Gamma s) (M : tm (s :: Gamma) u)
  : tm Gamma u :=
  subst (sub0 N) M.

Fixpoint eval {Gamma t} (rho : Val Gamma) (M : tm Gamma t) : den t :=
  match M in tm G t return Val G -> den t with
  | @TVar G t x => fun rho => rho t x
  | @TApp G s u M N => fun rho => appD (eval rho M) (eval rho N)
  | @TLam G s u M => fun rho => lamD _ _ (fun a => eval (val_ext rho a) M)
  end rho.

Lemma val_ext_vz : forall Gamma s (rho : Val Gamma) (a : den s),
  @val_ext Gamma s rho a s (@vz Gamma s) = a.
Proof. reflexivity. Qed.

Lemma val_ext_vs : forall Gamma s (rho : Val Gamma) (a : den s) t (x : var Gamma t),
  @val_ext Gamma s rho a t (@vs Gamma t s x) = rho t x.
Proof. reflexivity. Qed.

Lemma ren_ext_vz : forall Gamma Delta s (r : Ren Gamma Delta),
  @ren_ext Gamma Delta s r s (@vz Gamma s) = @vz Delta s.
Proof. reflexivity. Qed.

Lemma ren_ext_vs : forall Gamma Delta s (r : Ren Gamma Delta) t (x : var Gamma t),
  @ren_ext Gamma Delta s r t (@vs Gamma t s x) = @vs Delta t s (r t x).
Proof. reflexivity. Qed.

Lemma sub_ext_vz : forall Gamma Delta s (sigma : Sub Gamma Delta),
  @sub_ext Gamma Delta s sigma s (@vz Gamma s) = @TVar (s :: Delta) s (@vz Delta s).
Proof. reflexivity. Qed.

Lemma sub_ext_vs : forall Gamma Delta s (sigma : Sub Gamma Delta) t (x : var Gamma t),
  @sub_ext Gamma Delta s sigma t (@vs Gamma t s x) = rename (@wk Delta s) (sigma t x).
Proof. reflexivity. Qed.

Lemma sub0_vz : forall Gamma s (N : tm Gamma s),
  @sub0 Gamma s N s (@vz Gamma s) = N.
Proof. reflexivity. Qed.

Lemma sub0_vs : forall Gamma s (N : tm Gamma s) t (x : var Gamma t),
  @sub0 Gamma s N t (@vs Gamma t s x) = @TVar Gamma t x.
Proof. reflexivity. Qed.

(* Extensional equality of valuations suffices for equality of denotations. *)

Lemma eval_ext : forall Gamma t (M : tm Gamma t) (rho rho' : Val Gamma),
  (forall s (x : var Gamma s), rho s x = rho' s x) ->
  eval rho M = eval rho' M.
Proof.
  induction M; simpl; intros rho rho' Heq.
  - apply Heq.
  - rewrite IHM1 with (rho':=rho'); auto.
    rewrite IHM2 with (rho':=rho'); auto.
  - apply pair_den_ext.
    + intro a. unfold lamD. simpl. f_equal.
      apply IHM. intros r x. dependent destruction x.
      * repeat rewrite val_ext_vz. reflexivity.
      * repeat rewrite val_ext_vs. apply Heq.
    + unfold lamD. simpl. f_equal.
      apply IHM. intros r x. dependent destruction x.
      * repeat rewrite val_ext_vz. reflexivity.
      * repeat rewrite val_ext_vs. apply Heq.
Qed.

Lemma eval_rename : forall Gamma Delta t (r : Ren Gamma Delta)
    (rho : Val Delta) (M : tm Gamma t),
  eval rho (rename r M) = eval (fun s x => rho s (r s x)) M.
Proof.
  intros Gamma Delta t r rho M. revert Delta r rho.
  induction M; simpl; intros Delta r rho.
  - reflexivity.
  - rewrite IHM1. rewrite IHM2. reflexivity.
  - apply pair_den_ext.
    + intro a. unfold lamD. simpl. f_equal.
      rewrite (IHM _ (ren_ext r) (val_ext rho a)).
      apply eval_ext. intros q x. dependent destruction x.
      * rewrite ren_ext_vz. repeat rewrite val_ext_vz. reflexivity.
      * rewrite ren_ext_vs. repeat rewrite val_ext_vs. reflexivity.
    + unfold lamD. simpl. f_equal.
      rewrite (IHM _ (ren_ext r) (val_ext rho (canon s 0))).
      apply eval_ext. intros q x. dependent destruction x.
      * rewrite ren_ext_vz. repeat rewrite val_ext_vz. reflexivity.
      * rewrite ren_ext_vs. repeat rewrite val_ext_vs. reflexivity.
Qed.

Lemma eval_subst : forall Gamma Delta t (sigma : Sub Gamma Delta)
    (rho : Val Delta) (M : tm Gamma t),
  eval rho (subst sigma M) =
  eval (fun s x => eval rho (sigma s x)) M.
Proof.
  intros Gamma Delta t sigma rho M. revert Delta sigma rho.
  induction M; simpl; intros Delta sigma rho.
  - reflexivity.
  - rewrite IHM1. rewrite IHM2. reflexivity.
  - apply pair_den_ext.
    + intro a. unfold lamD. simpl. f_equal.
      rewrite (IHM _ (sub_ext sigma) (val_ext rho a)).
      apply eval_ext. intros q x. dependent destruction x.
      * rewrite sub_ext_vz. simpl. repeat rewrite val_ext_vz. reflexivity.
      * rewrite sub_ext_vs.
        rewrite (@eval_rename _ _ _ (@wk _ s) (val_ext rho a) (sigma _ x)).
        apply eval_ext. intros r y. unfold wk. rewrite val_ext_vs. reflexivity.
    + unfold lamD. simpl. f_equal.
      rewrite (IHM _ (sub_ext sigma) (val_ext rho (canon s 0))).
      apply eval_ext. intros q x. dependent destruction x.
      * rewrite sub_ext_vz. simpl. repeat rewrite val_ext_vz. reflexivity.
      * rewrite sub_ext_vs.
        rewrite (@eval_rename _ _ _ (@wk _ s) (val_ext rho (canon s 0)) (sigma _ x)).
        apply eval_ext. intros r y. unfold wk. rewrite val_ext_vs. reflexivity.
Qed.

Lemma eval_subst0 : forall Gamma s u (N : tm Gamma s) (M : tm (s :: Gamma) u)
    (rho : Val Gamma),
  eval rho (subst0 N M) = eval (val_ext rho (eval rho N)) M.
Proof.
  intros. unfold subst0. rewrite eval_subst.
  apply eval_ext. intros q x. dependent destruction x.
  - rewrite sub0_vz. simpl. reflexivity.
  - rewrite sub0_vs. simpl. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Admissible valuations and monotonicity of term denotations.             *)

Definition ValAdm Gamma (rho : Val Gamma) : Prop :=
  forall t (x : var Gamma t), adm t (rho t x).

Definition ValGe Gamma (rho rho' : Val Gamma) : Prop :=
  forall t (x : var Gamma t), ge t (rho t x) (rho' t x).

Arguments ValAdm Gamma rho : clear implicits.
Arguments ValGe Gamma rho rho' : clear implicits.

Lemma ValAdm_ext : forall Gamma s (rho : Val Gamma) a,
  ValAdm Gamma rho -> adm s a -> ValAdm (s :: Gamma) (val_ext rho a).
Proof.
  intros Gamma s rho a Hr Ha t x. dependent destruction x.
  - rewrite val_ext_vz. exact Ha.
  - rewrite val_ext_vs. apply Hr.
Qed.

Lemma ValGe_ext : forall Gamma s (rho rho' : Val Gamma) a b,
  ValGe Gamma rho rho' -> ge s a b ->
  ValGe (s :: Gamma) (val_ext rho a) (val_ext rho' b).
Proof.
  intros Gamma s rho rho' a b Henv Hab t x. dependent destruction x.
  - repeat rewrite val_ext_vz. exact Hab.
  - repeat rewrite val_ext_vs. apply Henv.
Qed.

Lemma ValGe_refl : forall Gamma (rho : Val Gamma),
  ValAdm Gamma rho -> ValGe Gamma rho rho.
Proof.
  intros Gamma rho Hr t x. apply ge_refl. apply Hr.
Qed.

Lemma eval_adm_ge : forall Gamma t (M : tm Gamma t),
  (forall rho, ValAdm Gamma rho -> adm t (eval rho M)) /\
  (forall rho rho', ValAdm Gamma rho -> ValAdm Gamma rho' -> ValGe Gamma rho rho' ->
     ge t (eval rho M) (eval rho' M)).
Proof.
  induction M; split; simpl; intros.
  - apply H.
  - apply H1.
  - destruct IHM1 as [IH1adm IH1ge]. destruct IHM2 as [IH2adm IH2ge].
    specialize (IH1adm rho H) as HF. simpl in HF.
    destruct HF as [HFadm _]. apply HFadm. apply IH2adm; assumption.
  - destruct IHM1 as [IH1adm IH1ge]. destruct IHM2 as [IH2adm IH2ge].
    set (F := eval rho M1). set (G := eval rho' M1).
    set (A := eval rho M2). set (B := eval rho' M2).
    assert (HadmA : adm s A) by (subst A; apply IH2adm; assumption).
    assert (HadmB : adm s B) by (subst B; apply IH2adm; assumption).
    assert (HFG : ge (s ~~> u) F G) by (subst F G; apply IH1ge; assumption).
    assert (HGadm : adm (s ~~> u) G) by (subst G; apply IH1adm; assumption).
    assert (HAB : ge s A B) by (subst A B; apply IH2ge; assumption).
    simpl in HFG. destruct HFG as [_ Hpoint]. simpl in HGadm.
    destruct HGadm as [_ [HGge _]].
    eapply ge_trans.
    + apply Hpoint; assumption.
    + apply HGge; assumption.
  - destruct IHM as [IHadm IHge]. apply lam_adm.
    + intros a Ha. apply IHadm. apply ValAdm_ext; assumption.
    + intros a b Ha Hb Hab. apply IHge.
      * apply ValAdm_ext; assumption.
      * apply ValAdm_ext; assumption.
      * apply ValGe_ext; [apply ValGe_refl; assumption | assumption].
  - destruct IHM as [IHadm IHge]. simpl. split.
    + assert (Hc : adm s (canon s 0)) by apply canon_adm.
      pose proof (IHge (val_ext rho (canon s 0)) (val_ext rho' (canon s 0))) as Hbody.
      assert (HVA : ValAdm (s :: Gamma) (val_ext rho (canon s 0))) by
        (apply ValAdm_ext; assumption).
      assert (HVB : ValAdm (s :: Gamma) (val_ext rho' (canon s 0))) by
        (apply ValAdm_ext; assumption).
      assert (HVG : ValGe (s :: Gamma) (val_ext rho (canon s 0)) (val_ext rho' (canon s 0))) by
        (apply ValGe_ext; [assumption|apply ge_refl; assumption]).
      specialize (Hbody HVA HVB HVG). apply ge_star in Hbody. exact Hbody.
    + intros a Ha. apply add_ge_same.
      * apply IHadm. apply ValAdm_ext; assumption.
      * apply IHadm. apply ValAdm_ext; assumption.
      * apply IHge.
        -- apply ValAdm_ext; assumption.
        -- apply ValAdm_ext; assumption.
        -- apply ValGe_ext; [assumption|apply ge_refl; assumption].
Qed.

Lemma eval_adm : forall Gamma t (M : tm Gamma t) rho,
  ValAdm Gamma rho -> adm t (eval rho M).
Proof.
  intros. exact (proj1 (eval_adm_ge M) rho H).
Qed.

Lemma eval_ge : forall Gamma t (M : tm Gamma t) rho rho',
  ValAdm Gamma rho -> ValAdm Gamma rho' -> ValGe Gamma rho rho' ->
  ge t (eval rho M) (eval rho' M).
Proof.
  intros. exact (proj2 (eval_adm_ge M) rho rho' H H0 H1).
Qed.

(* ---------------------------------------------------------------------- *)
(* Full contextual beta-reduction.                                        *)

Inductive step : forall Gamma t, tm Gamma t -> tm Gamma t -> Prop :=
| step_beta : forall Gamma s u (M : tm (s :: Gamma) u) (N : tm Gamma s),
    @step Gamma u (TApp (TLam M) N) (subst0 N M)
| step_app_l : forall Gamma s u (M M' : tm Gamma (s ~~> u)) (N : tm Gamma s),
    @step Gamma (s ~~> u) M M' ->
    @step Gamma u (TApp M N) (TApp M' N)
| step_app_r : forall Gamma s u (M : tm Gamma (s ~~> u)) (N N' : tm Gamma s),
    @step Gamma s N N' ->
    @step Gamma u (TApp M N) (TApp M N')
| step_lam : forall Gamma s u (M M' : tm (s :: Gamma) u),
    @step (s :: Gamma) u M M' ->
    @step Gamma (s ~~> u) (TLam M) (TLam M').

Theorem step_decreases : forall Gamma t (M N : tm Gamma t),
  @step Gamma t M N ->
  forall rho, ValAdm Gamma rho -> gt t (eval rho M) (eval rho N).
Proof.
  intros Gamma t M N Hstep.
  induction Hstep; simpl; intros rho Hrho.
  - rewrite eval_subst0. unfold appD, dot, lamD. simpl.
    apply add_positive.
    + apply eval_adm. apply ValAdm_ext.
      * assumption.
      * apply eval_adm; assumption.
    + rewrite Nat.add_1_r. apply Nat.lt_0_succ.
  - specialize (IHHstep rho Hrho) as Hfun.
    simpl in Hfun. destruct Hfun as [_ Hpoint].
    apply Hpoint. apply eval_adm; assumption.
  - specialize (IHHstep rho Hrho) as Harg.
    pose proof (@eval_adm Gamma (s ~~> u) M rho Hrho) as Hfun_adm. simpl in Hfun_adm.
    destruct Hfun_adm as [_ [_ Hstrict]].
    apply Hstrict.
    + apply eval_adm; assumption.
    + apply eval_adm; assumption.
    + assumption.
  - simpl. split.
    + assert (Hc : adm s (canon s 0)) by apply canon_adm.
      specialize (IHHstep (val_ext rho (canon s 0))).
      assert (Hext : ValAdm (s :: Gamma) (val_ext rho (canon s 0))) by
        (apply ValAdm_ext; assumption).
      specialize (IHHstep Hext). apply gt_star in IHHstep. exact IHHstep.
    + intros a Ha. apply add_gt_same.
      * apply eval_adm. apply ValAdm_ext; assumption.
      * apply eval_adm. apply ValAdm_ext; assumption.
      * apply IHHstep. apply ValAdm_ext; assumption.
Qed.

Corollary star_decreases : forall Gamma t (M N : tm Gamma t) rho,
  ValAdm Gamma rho -> @step Gamma t M N ->
  star t (eval rho M) > star t (eval rho N).
Proof.
  intros Gamma t M N rho Hrho Hstep. apply gt_star. eapply (@step_decreases Gamma t M N); eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Strong normalization from the decreasing natural-number measure.        *)

Definition SN {Gamma t} (M : tm Gamma t) : Prop :=
  Acc (fun N M => @step Gamma t M N) M.

Theorem strong_normalization : forall Gamma t (M : tm Gamma t) rho,
  ValAdm Gamma rho -> SN M.
Proof.
  unfold SN. intros Gamma t M rho Hrho.
  remember (star t (eval rho M)) as n eqn:Hn.
  revert Gamma t M rho Hrho Hn.
  induction n as [n IH] using lt_wf_ind; intros Gamma t M rho Hrho Hn.
  constructor. intros N Hstep.
  refine (IH (star t (eval rho N)) _ Gamma t N rho Hrho eq_refl).
  pose proof (@star_decreases Gamma t M N rho Hrho Hstep) as Hlt.
  rewrite <- Hn in Hlt. exact Hlt.
Qed.


Definition canon_val (Gamma : list ty) : Val Gamma :=
  fun t _ => canon t 0.

Lemma canon_val_adm : forall Gamma, ValAdm Gamma (@canon_val Gamma).
Proof.
  intros Gamma t x. apply canon_adm.
Qed.

Theorem strong_normalization_all : forall Gamma t (M : tm Gamma t), SN M.
Proof.
  intros Gamma t M. apply (@strong_normalization Gamma t M (@canon_val Gamma)).
  apply canon_val_adm.
Qed.

Definition empty_val : Val [] :=
  fun t x => match x with end.

Lemma empty_val_adm : ValAdm [] empty_val.
Proof.
  intros t x. dependent destruction x.
Qed.

Corollary strong_normalization_closed : forall t (M : tm [] t), SN M.
Proof.
  intros t M. apply (@strong_normalization [] t M empty_val). apply empty_val_adm.
Qed.

(* ---------------------------------------------------------------------- *)
(* The running example from the paper.                                    *)

Definition oo : ty := base ~~> base.

Definition id_o_tm : tm [] oo :=
  TLam (TVar vz).

Definition eta_o_tm : tm [] (oo ~~> oo) :=
  TLam (TLam (TApp (TVar (vs vz)) (TVar vz))).

Definition ex_tm : tm [] oo :=
  TApp eta_o_tm id_o_tm.

Example ex_star : star oo (eval empty_val ex_tm) = 2.
Proof. cbv. reflexivity. Qed.

Example ex_one : exists N, @step [] oo ex_tm N.
Proof.
  eexists. constructor.
Qed.

Example ex_sn : SN ex_tm.
Proof.
  apply strong_normalization_closed.

Qed.
