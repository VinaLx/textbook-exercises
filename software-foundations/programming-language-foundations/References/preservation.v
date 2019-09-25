Require Import String.
Require Import LF.Maps.
Require Import Equality.
Require Import PeanoNat.

Require Import List.
Import ListNotations.

Require Import References.language.
Require Import References.semantics.
Require Import References.store.

Require Import Omega.

Inductive appears_free : string → tm → Prop :=
| AF_Var : ∀ x, appears_free x (var x)
| AF_App1 : ∀ x f a,
    appears_free x f → appears_free x (app f a)
| AF_App2 : ∀ x f a,
    appears_free x a → appears_free x (app f a)
| AF_Abs : ∀ x y T b,
    y ≠ x →
    appears_free x b →
    appears_free x (abs y T b)
| AF_Succ : ∀ x t,
    appears_free x t →
    appears_free x (scc t)
| AF_Pred : ∀ x t,
    appears_free x t →
    appears_free x (prd t)
| AF_Mlt1 : ∀ x l r,
    appears_free x l →
    appears_free x (mlt l r)
| AF_Mlt2 : ∀ x l r,
    appears_free x r →
    appears_free x (mlt l r)
| AF_Test1 : ∀ x n t f,
    appears_free x n →
    appears_free x (test0 n t f)
| AF_Test2 : ∀ x n t f,
    appears_free x t →
    appears_free x (test0 n t f)
| AF_Test3 : ∀ x n t f,
    appears_free x f →
    appears_free x (test0 n t f)
| AF_Ref : ∀ x t,
    appears_free x t → appears_free x (ref t)
| AF_Deref : ∀ x t,
    appears_free x t → appears_free x (deref t)
| AF_Assign1 : ∀ x v a,
    appears_free x v → appears_free x (assign v a)
| AF_Assign2 : ∀ x v a,
    appears_free x a → appears_free x (assign v a)
.

Hint Constructors appears_free.

Lemma free_in_context : ∀ x t T Γ ST,
  appears_free x t →
  Γ ; ST ⊢ t ∈ T →
  ∃ T', Γ x = Some T'.
Proof.
  intros x t T Γ ST AF.
  generalize dependent T.
  generalize dependent Γ.
  generalize dependent ST.
  induction AF; intros ST Γ Tp Typing; inversion Typing; subst;
  try solve [eapply IHAF; eauto].
  - now exists Tp.
  - apply IHAF in H6. rewrite update_neq in H6; assumption.
Qed.

Lemma context_invariance : ∀ Γ Γ' ST t T,
  Γ  ; ST ⊢ t ∈ T →
  (∀ x, appears_free x t → Γ x = Γ' x) →
  Γ' ; ST ⊢ t ∈ T.
Proof.
  intros Γ Γ' ST t T Typing.
  generalize dependent Γ'.
  induction Typing; intros Γ' HE; eauto; try solve [econstructor; eauto].
  - apply T_Var. rewrite <- HE; auto.
  - apply T_Abs. apply IHTyping.
    intros x AF. unfold update, t_update.
    destruct (beq_string a x) eqn: E.
    + reflexivity.
    + apply HE. constructor. now apply beq_string_false_iff. assumption.
Qed.

Lemma substitution_preserves_typing : ∀ t Γ ST x s S T,
  empty ; ST ⊢ s ∈ S →
  Γ & {{ x ==> S }} ; ST ⊢ t ∈ T →
  Γ ; ST ⊢ [x := s] t ∈ T.
Proof.
  induction t; intros Γ ST x a A T TypingS TypingT;
  inversion TypingT; subst; simpl; eauto.
  - unfold update, t_update in H2.
    destruct (beq_string x s) eqn: E.
    + inversion H2. subst.
      apply context_invariance with empty. assumption.
      intros x0 AF.
      eapply free_in_context in AF.
      2: eassumption. destruct AF as [T' contra].
      inversion contra.
    + apply T_Var. assumption.
  - destruct (beq_string x s) eqn: Exs.
    + apply T_Abs. apply beq_string_true_iff in Exs. subst.
      rewrite update_shadow in H5. assumption.
    + apply T_Abs. eapply IHt. eassumption.
      apply beq_string_false_iff in Exs.
      rewrite update_permute; auto.
Qed.

Lemma assign_store_typing : ∀ ST st n t,
  n < length st →
  store_well_typed ST st →
  empty ; ST ⊢ t ∈ ty_store_lookup n ST →
  store_well_typed ST (replace n t st).
Proof.
  unfold store_well_typed.
  intros ST st n t LT StWellTyped TypingT.
  split.
  - rewrite length_replace. now destruct StWellTyped.
  - intros n0 LT0.
    destruct (Nat.eq_dec n0 n).
    + subst. rewrite lookup_replace_eq; auto.
    + rewrite lookup_replace_neq.
      apply StWellTyped. now rewrite length_replace in LT0. assumption.
Qed.

Lemma nth_eq_last : ∀ {A} (l: list A) x d,
  nth (length l) (l ++ x :: nil) d = x.
Proof.
  induction l; intros x d.
  - reflexivity.
  - apply IHl.
Qed.

Lemma store_weakening : ∀ Γ ST ST' t T,
  extends ST' ST →
  Γ ; ST ⊢ t ∈ T → Γ ; ST' ⊢ t ∈ T.
Proof.
  intros Γ ST ST' t T Extends Typing.
  induction Typing; eauto.
  - erewrite <- extends_lookup; eauto.
    apply T_Loc. now apply length_extends with ST.
Qed.

Hint Unfold ty_store_lookup store_lookup.
Hint Resolve extends_refl.
Hint Resolve nth_eq_last.
Hint Resolve store_weakening.
Hint Resolve extends_app.

Lemma lt_dec : ∀ {x} {y},
  x < S y → x < y ∨ x = y.
Proof.
  unfold lt. intros x y LT. omega.
Qed.

Lemma nth_shrink : ∀ {A} (xs ys : list A) n  d,
  n < length xs → nth n (xs ++ ys) d = nth n xs d.
Proof.
  induction xs; intros.
  + inversion H.
  + destruct n.
    - reflexivity.
    - simpl. apply IHxs. now apply le_S_n.
Qed.
  

Theorem preservation : ∀ ST t t' st st' T,
  empty ; ST ⊢ t ∈ T →
  t / st --> t' / st' →
  store_well_typed ST st →
  ∃ ST', (empty ; ST' ⊢ t' ∈ T ∧
     extends ST' ST ∧ store_well_typed ST' st').
Proof.
  intros ST t t' st st' T Typing.
  generalize dependent t'.
  generalize dependent st.
  generalize dependent st'.
  dependent induction Typing; intros st' st t' Step StWellTyped;
  inversion Step; subst; try solve [exists ST; eauto].
  - exists ST. destruct StWellTyped. repeat split; auto.
    apply substitution_preserves_typing with A; auto.
    inversion Typing1. now subst.
  - apply IHTyping1 in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping2 in H5 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping1 in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping2 in H5 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping1 in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto 6.
  - apply IHTyping in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - exists (ST ++ T :: nil).
    destruct StWellTyped as [ELength WellTyped]. 
    repeat split; auto.
    + assert (Ref T = Ref (ty_store_lookup (length st) (ST ++ T :: nil))). {
        rewrite <- ELength. unfold ty_store_lookup.
        now rewrite (nth_eq_last ST T Unit).
      } 
      rewrite H. apply T_Loc. rewrite <- ELength. rewrite app_length.
      rewrite plus_comm. constructor.
    + repeat rewrite app_length. now rewrite ELength.
    + intros n LTn. rewrite app_length, plus_comm in LTn.
      apply store_weakening with ST. apply extends_app.
      unfold store_lookup, ty_store_lookup.
      destruct (lt_dec LTn).
      ++ repeat rewrite nth_shrink.
         now apply WellTyped.
         now rewrite ELength. trivial.
      ++ rewrite H. rewrite nth_eq_last.
         rewrite <- ELength. now rewrite nth_eq_last.
  - apply IHTyping in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - exists ST. split; auto.
    destruct StWellTyped.
    inversion Typing. subst. now apply H1.
  - apply IHTyping1 in H0 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - apply IHTyping2 in H5 as [ST' [Typing' [ExtendsST' StWellTyped']]]; auto.
    exists ST'. eauto.
  - exists ST. split. auto. split. auto.
    apply assign_store_typing; auto.
    inversion Typing1. now subst.
Qed.
    
    
  

    
