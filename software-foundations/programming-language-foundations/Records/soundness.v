Require Import Records.language.
Require Import Records.typing.
Require Import Equality.

Theorem progress : ∀ t T,
  empty ⊢ t ∈ T →
  value t ∨ ∃ t', t --> t'.
Proof.
  intros t T Typing.
  dependent induction Typing.
  - auto.
  - right.
    destruct IHTyping1; auto.
    destruct IHTyping2; auto.
    + apply canonical_forms_of_arrow_types in Typing1. 
      destruct Typing1 as [x [A' [B' Ef]]].
      subst. eauto. assumption.
    + destruct H0 as [a' Step]; eauto.
    + destruct H as [f' Step]; eauto.
  - right. destruct IHTyping. auto.  
    + eapply lookup_field_in_value in H; eauto.
      destruct H as [t [ELookup TypingT]].
      eauto.
    + destruct H0 as [r' Step]. eauto.
  - now apply IHTyping.
  - auto.
  - destruct IHTyping1. auto.
    destruct IHTyping2. auto.
    + auto.
    + destruct H2. eauto.
    + destruct H1. eauto.
Qed.

Lemma typing_inversion_var : ∀ Γ x T,
  Γ ⊢ var x ∈ T →
  ∃ S, Γ x = Some S ∧ S <: T.
Proof.
  intros Γ x T Typing.
  dependent induction Typing.
  - exists T. eauto.
  - destruct (IHTyping x eq_refl) as [SS [E SubSS]].
    exists SS. eauto.
Qed.

Lemma typing_inversion_app : ∀ Γ f a B,
  Γ ⊢ app f a ∈ B →
  ∃ A, Γ ⊢ f ∈ Arrow A B ∧ Γ ⊢ a ∈ A.
Proof.
  intros.
  dependent induction H.
  - exists A. auto.
  - destruct (IHhas_type f a eq_refl) as [A [TypingF TypingA]].
    exists A. split.
    eapply T_Sub. eassumption. eauto. eauto.
Qed.

Lemma typing_inversion_abs : ∀ Γ x A b T,
  Γ ⊢ abs x A b ∈ T →
  ∃ B, Arrow A B <: T ∧ Γ & {{ x ==> A }} ⊢ b ∈ B.
Proof.
  intros.
  dependent induction H.
  - exists B. eauto.
  - destruct (IHhas_type x A b eq_refl) as [B [SubB TypingB]].
    exists B. eauto.
Qed.

Lemma typing_inversion_proj : ∀ Γ r i T,
  Γ ⊢ rproj r i ∈ T →
  ∃ R S, Tlookup i R = Some S ∧ S <: T ∧ Γ ⊢ r ∈ R.
Proof.
  intros. dependent induction H.
  - exists T, Ti. split; eauto.
  - destruct (IHhas_type r i eq_refl) as [R [S' [ELookup [SubS TypingR]]]].
    exists R, S'. split; eauto.
Qed.

Lemma typing_inversion_rcons : ∀ Γ i ti r T,
  Γ ⊢ rcons i ti r ∈ T →
  ∃ Ti R, RCons i Ti R <: T ∧ Γ ⊢ ti ∈ Ti ∧ record_tm r ∧ Γ ⊢ r ∈ R.
Proof.
  intros.
  dependent induction H.
  - destruct (IHhas_type i ti r eq_refl) as
      [Ti [R [SubS [TypingTi [Record TypingR]]]]].
    exists Ti, R. split; eauto.
  - exists T, R. split; eauto.
Qed.

Lemma abs_arrow : ∀ x A' b A B,
  empty ⊢ abs x A' b ∈ Arrow A B →
  A <: A' ∧ (update empty x A') ⊢ b ∈ B.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - apply sub_inversion_arrow in H0 as [SA [SB [ES [SubA SubB]]]].
    destruct (IHhas_type x A' b SA SB); auto.
    eauto.
Qed.

Inductive appears_free : string → tm → Prop :=
| AF_Var : ∀ x,
    appears_free x (var x)
| AF_App1 : ∀ x f a,
    appears_free x f → appears_free x (app f a)
| AF_App2 : ∀ x f a,
    appears_free x a → appears_free x (app f a)
| AF_Abs : ∀ x y A b,
    y ≠ x →
    appears_free x b →
    appears_free x (abs y A b)
| AF_Proj : ∀ x r i,
    appears_free x r →
    appears_free x (rproj r i)
| AF_Rhead : ∀ x i t r,
    appears_free x t →
    appears_free x (rcons i t r)
| AF_Rtail : ∀ x i t r,
    appears_free x r →
    appears_free x (rcons i t r).

Hint Constructors appears_free.

Lemma context_invariance : ∀ Γ Γ' t T,
  Γ ⊢ t ∈ T →
  (∀ x, appears_free x t → Γ x = Γ' x) →
  Γ' ⊢ t ∈ T.
Proof.
  intros Γ Γ' t T Typing. generalize dependent Γ'.
  induction Typing; intros Γ' Invariance.
  - constructor. rewrite <- Invariance. all: auto.
  - constructor. assumption.
    apply IHTyping. intros x0 AF. unfold update, t_update.
    destruct (beq_string x x0) eqn: Ex.
    + auto.
    + apply Invariance. constructor. now apply beq_string_false_iff.
      auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - apply T_Sub with S; eauto.
  - eauto.
  - constructor; eauto.
Qed.

Lemma free_in_context : ∀ Γ a t T,
  appears_free a t →
  Γ ⊢ t ∈ T →
  ∃ A, Γ a = Some A.
Proof.
  intros Γ a t T AF Typing.
  induction Typing; inversion AF; subst;
  try solve
    [ now apply IHTyping
    | now apply IHTyping1
    | now apply IHTyping2].
  - now exists T.
  - rewrite update_neq in IHTyping.
    now apply IHTyping. exact H3.
Qed.

Lemma record_subst : ∀ r x a,
  record_tm r → record_tm ([x := a] r).
Proof.
  intros. destruct H; simpl.
  - constructor.
  - auto.
Qed.

Hint Resolve record_subst.

Lemma substitution_preserves_typing : ∀ Γ x a A t T,
  Γ & {{ x ==> A }} ⊢ t ∈ T →
  empty ⊢ a ∈ A →
  Γ ⊢ [ x := a ] t ∈ T.
Proof.
  intros. rename H into Typing. rename H0 into TypingA.
  dependent induction Typing; simpl; eauto.
  - unfold update, t_update in H.
    destruct (beq_string x x0) eqn: Ex.
    + inversion H. subst. apply context_invariance with empty.
      exact TypingA.
      intros x1 AF.
      eapply free_in_context in AF; eauto.
      destruct AF. inversion H1.
    + constructor; auto.
  - destruct (beq_string x x0) eqn: Ex.
    + apply beq_string_true_iff in Ex. subst.
      rewrite update_shadow in Typing.
      eauto.
    + apply T_Abs; auto.
      eapply IHTyping. rewrite update_permute. auto.
      now apply beq_string_false_iff. exact TypingA.
Qed.


Theorem preservation : ∀ t t' T,
  empty ⊢ t ∈ T →
  t --> t' →
  empty ⊢ t' ∈ T.
Proof.
  intros t t' T Typing.
  generalize dependent t'.
  dependent induction Typing; intros t'; intros Step; inversion Step; subst; eauto.
  - apply typing_inversion_abs in Typing1 as
      [SB [SubArrow TypingSB]].
    apply sub_inversion_arrow in SubArrow as
      [T' [SB' [EArrow [SubA SubB]]]].
    inversion EArrow. subst.
    apply substitution_preserves_typing with T'.
    eauto. eauto.
  - eapply lookup_field_in_value in H2; eauto.
    destruct H2 as [t [E TypingT]].
    rewrite E in H4. inversion H4. subst.
    exact TypingT.
  - apply T_RCons; auto.
    apply step_preserves_record_tm with r; auto.
Qed.
