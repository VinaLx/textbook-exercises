Require Import References.language.
Require Import List.
Require Import Omega.

Definition store := list tm.

Definition ty_store := list ty.

Definition store_lookup (n : nat) (st : store) := nth n st unit.
Definition ty_store_lookup (n : nat) (st : ty_store) := nth n st Unit.

Fixpoint replace {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
      match n with
      | O => x :: t
      | S n' => h :: replace n' x t
      end
  end
.

Lemma replace_nil : ∀ A n (x : A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : ∀ A x (l : list A) n,
  length (replace n x l) = length l.
Proof.
  induction l; intros.
  - now rewrite replace_nil.
  - destruct n.
    + easy.
    + simpl. now rewrite IHl.
Qed.

Lemma lookup_replace_eq : ∀ st l t,
  l < length st → store_lookup l (replace l t st) = t.
Proof.
  unfold store_lookup.
  induction st; intros.
  - simpl in H. inversion H.
  - simpl. destruct l.
    + easy.
    + apply IHst. simpl in H. omega.
Qed.

Lemma lookup_replace_neq : ∀ st n n0 t,
  n0 ≠ n → store_lookup n0 (replace n t st) = store_lookup n0 st.
Proof.
  unfold store_lookup.
  induction st; intros n n0 t NE; simpl.
  - destruct n0.
    + destruct n; reflexivity.
    + destruct n; reflexivity.
  - destruct n0.
    + now destruct n.
    + destruct n. reflexivity. simpl. auto.
Qed.

Inductive extends : ty_store → ty_store → Prop :=
| extends_nil : ∀ ST, extends ST nil
| extends_cons : ∀ T ST' ST,
    extends ST' ST → extends (T :: ST') (T :: ST)
.

Lemma extends_lookup : ∀ ST ST' n,
  n < length ST →
  extends ST' ST →
  ty_store_lookup n ST' = ty_store_lookup n ST.
Proof.
  induction ST; intros.
  - inversion H.
  - inversion H0. subst.
    unfold ty_store_lookup. destruct n; simpl.
    + reflexivity.
    + apply IHST.
      simpl in H. omega.
      assumption.
Qed.

Lemma length_extends : ∀ ST ST' n,
  n < length ST →
  extends ST' ST →
  n < length ST'.
Proof.
  induction ST; intros.
  - inversion H.
  - inversion H0. subst.
    destruct n; simpl.
    + omega.
    + apply le_n_S.
      apply IHST.
      apply le_S_n. simpl in H. apply H.
      assumption.
Qed.

Lemma extends_app : ∀ ST ST',
  extends (ST ++ ST') ST.
Proof.
  induction ST; intros; simpl.
  - constructor.
  - constructor. apply IHST.
Qed.

Lemma extends_refl : ∀ ST,
  extends ST ST.
Proof.
  induction ST; constructor. assumption.
Qed.
