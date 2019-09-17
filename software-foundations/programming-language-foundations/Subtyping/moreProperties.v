Require Import Subtyping.language.
Require Import Subtyping.properties.
Require Import LF.Maps.
Require Import Equality.

Inductive appears_free : string → tm → Prop :=
| AF_Var : ∀ x, appears_free x (var x)
| AF_App1 : ∀ x f a,
    appears_free x f → appears_free x (app f a)
| AF_App2 : ∀ x f a,
    appears_free x a → appears_free x (app f a)
| AF_Abs : ∀ x y T t,
    y ≠ x →
    appears_free x t → appears_free x (abs y T t)
| AF_test1 : ∀ x b t f,
    appears_free x b → appears_free x (test b t f)
| AF_test2 : ∀ x b t f,
    appears_free x t → appears_free x (test b t f)
| AF_test3 : ∀ x b t f,
    appears_free x f → appears_free x (test b t f)
| AF_pair1 : ∀ x a b,
    appears_free x a → appears_free x (pair a b)
| AF_pair2 : ∀ x a b,
    appears_free x b → appears_free x (pair a b)
| AF_fst : ∀ x p,
    appears_free x p → appears_free x (fst p)
| AF_snd : ∀ x p,
    appears_free x p → appears_free x (snd p)
.

Hint Constructors appears_free.

Lemma context_invariance : ∀ Γ Γ' t S,
  Γ ⊢ t ∈ S →
  (∀ x, appears_free x t → Γ x = Γ' x) →
  Γ' ⊢ t ∈ S.
Proof.
  intros Γ Γ' t S Typing.
  generalize dependent Γ'.
  induction Typing; intros Γ' Invariant.
  - cut (Γ x = Γ' x).
    + intro E. rewrite E in H. auto.
    + apply Invariant. auto.
  - apply T_Abs.
    apply IHTyping. intros x AF.
    unfold update, t_update.
    destruct (beq_string a x) eqn: Exa.
    + reflexivity.
    + apply Invariant. apply AF_Abs.
      now apply beq_string_false_iff.
      trivial.
  - apply T_App with A; 
    [> apply IHTyping1 | apply IHTyping2];
        intros; apply Invariant; auto.
  - auto.
  - auto.
  - apply T_Test;
    [> apply IHTyping1 | apply IHTyping2 | apply IHTyping3];
        intros; apply Invariant; auto.
  - auto.
  - apply T_Pair;
    [> apply IHTyping1 | apply IHTyping2];
        intros; apply Invariant; auto.
  - apply T_Fst with B.
    apply IHTyping. intros. apply Invariant. auto.
  - apply T_Snd with A.
    apply IHTyping. intros. apply Invariant. auto.
  - apply T_Sub with S.
    apply IHTyping. intros. apply Invariant. auto.
    auto.
Qed.

Lemma free_in_context : ∀ x t T Γ,
  appears_free x t →
  Γ ⊢ t ∈ T →
  ∃ X, Γ x = Some X.
Proof.
  intros x t T Γ Free Typing.
  induction Typing; inversion Free; subst; eauto.
  - destruct (IHTyping H4) as [X E]. exists X.
    unfold update, t_update in E.
    apply beq_string_false_iff in H2. now rewrite H2 in E.
Qed.

Lemma empty_context_typing : ∀ t T,
  empty ⊢ t ∈ T → (∀ Γ, Γ ⊢ t ∈ T).
Proof.
  intros t T Typing Γ.
  apply context_invariance with empty.
  - assumption.
  - intros x Free.
    assert (∃ X: ty, empty x = Some X) as contra.
    + eapply free_in_context; eauto.
    + destruct contra as [X contra]. inversion contra.
Qed.

Lemma substitution_preserves_typing : ∀ t Γ x A a T,
  Γ & {{ x ==> A }} ⊢ t ∈ T →
  empty ⊢ a ∈ A →
  Γ ⊢ [x := a] t ∈ T.
Proof.
  induction t; intros Γ x A a T TypingT TypingA; simpl.
  - apply typing_inversion_var in TypingT as [S [EΓ Sub]].
    unfold update, t_update in EΓ.
    destruct (beq_string x s) eqn: Exs.
    + inversion EΓ. subst. apply T_Sub with S.
      now apply empty_context_typing.
      assumption.
    + eauto.
  - apply typing_inversion_app in TypingT as [X [TypingArrow TypingArg]].
    apply T_App with X.
    + now apply IHt1 with A.
    + now apply IHt2 with A.
  - apply typing_inversion_abs in TypingT as [B [Sub TypingT0]].
    destruct (beq_string x s) eqn: E.
    + apply beq_string_true_iff in E. subst.
      rewrite update_shadow in TypingT0.
      eauto.
    + apply T_Sub with (Arrow t B); auto.
      apply T_Abs. eapply IHt. 
      rewrite update_permute in TypingT0.
      eauto. now apply beq_string_false_iff. auto.
  - apply typing_inversion_true in TypingT. eauto.
  - apply typing_inversion_false in TypingT. eauto.
  - apply typing_inversion_if in TypingT as [TypingB [TypingT TypingF]].
    eauto.
  - apply typing_inversion_unit in TypingT. eauto.
  - apply typing_inversion_pair in TypingT as
      [A' [B [SubPair [Typing1 Typing2]]]].
    eauto.
  - apply typing_inversion_fst in TypingT as [A' [B [SubA' TypingP]]]. eauto.
  - apply typing_inversion_snd in TypingT as [A' [B' [SubB' TypingP]]]. eauto.
Qed.

Theorem preservation : ∀ t t' T,
  empty ⊢ t ∈ T →
  t --> t' →
  empty ⊢ t' ∈ T.
Proof.
  intros t t' T Typing.
  generalize dependent t'.
  dependent induction Typing; intros t' Step; inversion Step; subst; eauto.
  - apply typing_inversion_abs in Typing1.
    destruct Typing1 as [Sb [SubArrow Typing12]].
    apply sub_inversion_arrow in SubArrow.
    destruct SubArrow as [T₁ [S₂ [E [SubA SubB]]]].
    inversion E. subst.
    apply substitution_preserves_typing with T₁; eauto.
  - apply typing_inversion_pair in Typing.
    destruct Typing as [Sa [Sb [SubP [TypingSa TypingSb]]]].
    apply sub_inversion_pair in SubP.
    destruct SubP as [Sa' [Sb' [E [SubA SubB]]]].
    inversion E. subst.
    eauto.
  - apply typing_inversion_pair in Typing.
    destruct Typing as [Sa [Sb [SubP [TypingSa TypingSb]]]].
    apply sub_inversion_pair in SubP.
    destruct SubP as [Sa' [Sb' [E [SubA SubB]]]].
    inversion E. subst.
    eauto.
Qed.

