Require Import Subtyping.language.
Require Import Coq.Program.Equality.
Require Import LF.Maps.

Lemma sub_inversion_Bool :
  ∀ T, T <: Bool → T = Bool.
Proof.
  intros S Hsub.
  remember Bool as T eqn: ETBool.
  induction Hsub; try solve [inversion ETBool].
  - reflexivity.
  - assert (B = C) as Ebc by now apply IHHsub2.
    rewrite ETBool in *.
    rewrite Ebc in *.
    now apply IHHsub1.
Qed.

Lemma sub_inversion_arrow : ∀ A S₁ T₂,
  A <: Arrow S₁ T₂ →
  ∃ T₁ S₂, A = Arrow T₁ S₂ ∧ S₁ <: T₁ ∧ S₂ <: T₂.
Proof.
  intros A S₁ T₂ Sub.
  dependent induction Sub.
  - exists S₁, T₂. auto.
  - assert (∃ T₁ S₂ : ty, B = Arrow T₁ S₂ ∧ S₁ <: T₁ ∧ S₂ <: T₂)
      as [Tb₁ [Sb₂ [Eb [Sub₁ Sub₂]]]] by now apply IHSub2.
    assert (∃ T₁ S₂ : ty, A = Arrow T₁ S₂ ∧ Tb₁ <: T₁ ∧ S₂ <: Sb₂)
      as [Ta₁ [Sa₂ [Ea [Suba₁ Suba₂]]]] by now apply IHSub1.
    exists Ta₁, Sa₂.
    eauto.
  - exists T₁, S₂. auto.
Qed.

Lemma sub_inversion_pair : ∀ S A B,
  S <: Pair A B →
  ∃ Sa Sb, S = Pair Sa Sb ∧ Sa <: A ∧ Sb <: B.
Proof.
  intros S A B Sub.
  dependent induction Sub.
  - exists A, B. auto.
  - set (IH2 := IHSub2 A B eq_refl).
    destruct IH2 as [Sa [Sb [Eb [SubSa SubSb]]]]. subst.
    set (IH1 := IHSub1 Sa Sb eq_refl).
    destruct IH1 as [SSa [SSb [Ea [SubSSa SubSSb]]]]. subst.
    exists SSa, SSb.
    eauto.
  - exists S₁, S₂. auto.
Qed.

Lemma canonical_forms_arrow : ∀ Γ f A B,
  Γ ⊢ f ∈ Arrow A B → value f →
  ∃ a A b, f = abs a A b.
Proof.
  intros Γ f A B Tp. 
  dependent induction Tp;
  intros ValueF; try solve [inversion ValueF].
  - now exists a, A, b.
  - apply sub_inversion_arrow in H
      as [Sa [Sb [Es [Sub1 Sub2]]]].
    eapply IHTp; eauto.
Qed.

Lemma canonical_forms_bool : ∀ Γ s,
  Γ ⊢ s ∈ Bool → value s → s = tru ∨ s = fls.
Proof.
  intros Γ s Tp.
  dependent induction Tp;
  intros ValueS; try solve [inversion ValueS]; auto.
  - apply IHTp.
    + now apply sub_inversion_Bool.
    + assumption.
Qed.

Lemma canonical_forms_pair : ∀ {Γ} {p} {A} {B},
  Γ ⊢ p ∈ Pair A B → value p →
  ∃ a b, p = pair a b.
Proof.
  intros Γ p A B Typing.
  dependent induction Typing; intros ValueP;
  try solve [inversion ValueP]; auto.
  - exists a, b. auto.
  - apply sub_inversion_pair in H as [Sa [Sb [E [SubA SubB]]]].
    subst. eapply IHTyping; eauto.
Qed.

Theorem progress : ∀ t T,
  empty ⊢ t ∈ T → value t ∨ ∃ t', t --> t'.
Proof.
  intros t T Typing.
  dependent induction Typing; auto.
  - right.
    assert (value f ∨ (∃ f', f --> f')) as [ValueF | [f' StepF']]
      by now apply IHTyping1.
    assert (value a ∨ (∃ a', a --> a')) as [ValueA | [a' StepA']]
      by now apply IHTyping2.
      + assert (∃ x A' b, f = abs x A' b) as [x [A' [b E]]]. {
          eapply canonical_forms_arrow; eauto.
        }
        rewrite E. exists ([x := a] b). auto.
      + exists (app f a'). auto.
      + exists (app f' a). auto.
  - right.
    assert (value b ∨ (∃ b', b --> b')) as [ValueB | [b' StepB]]
      by now apply IHTyping1.
      + assert (b = tru ∨ b = fls) as [E | E].
        { eapply canonical_forms_bool; eauto. }
        all: rewrite E; [> exists t | exists f]; auto.
      + exists (test b' t f). auto.
  - set (IH1 := IHTyping1 JMeq_refl).
    set (IH2 := IHTyping2 JMeq_refl).
    destruct IH1 as [ValueA | [a' StepA]]. 
    + destruct IH2 as [ValueB | [b' StepB]].
      -- auto.
      -- right. exists (pair a b'). auto.
    + right. exists (pair a' b). auto.
  - right.
    set (IH := IHTyping JMeq_refl).
    destruct IH as [ValueP | [p' StepP]].
    + set (CanonicalPair := canonical_forms_pair Typing ValueP).
      destruct CanonicalPair as [a [b E]]. rewrite E.
      exists a. auto.
    + exists (fst p'). auto.
  - right.
    set (IH := IHTyping JMeq_refl).
    destruct IH as [ValueP | [p' StepP]].
    + set (CanonicalPair := canonical_forms_pair Typing ValueP).
      destruct CanonicalPair as [a [b E]]. rewrite E.
      exists b. auto.
    + exists (snd p'). auto.
Qed. 

Lemma typing_inversion_abs : ∀ Γ a A b F,
  Γ ⊢ abs a A b ∈ F →
  ∃ B, Arrow A B <: F ∧ Γ & {{ a ==> A }} ⊢ b ∈ B.
Proof.
  intros Γ a A b F Typing.
  dependent induction Typing.
  - exists B. auto.
  - edestruct IHTyping as [B [Sub TypingB]]. reflexivity.
    exists B. eauto.
Qed.

Lemma typing_inversion_var : ∀ Γ x T,
  Γ ⊢ var x ∈ T →
  ∃ S, Γ x = Some S ∧ S <: T.
Proof.
  intros Γ x T Typing.
  dependent induction Typing.
  - exists T. auto.
  - edestruct IHTyping as [SS [H1 H2]]. reflexivity.
    exists SS. eauto.
Qed.

Lemma typing_inversion_app : ∀ Γ f a B,
  Γ ⊢ app f a ∈ B →
  ∃ A, Γ ⊢ f ∈ Arrow A B ∧ Γ ⊢ a ∈ A.
Proof.
  intros Γ f a B Typing.
  dependent induction Typing.
  - exists A. auto.
  - edestruct IHTyping as [A [HF HA]]. reflexivity.
    exists A. eauto.
Qed.

Lemma typing_inversion_true : ∀ Γ T,
  Γ ⊢ tru ∈ T → Bool <: T.
Proof.
  intros Γ T Typing.
  dependent induction Typing.
  - auto.
  - eapply S_Trans. now apply IHTyping. trivial.
Qed.

Lemma typing_inversion_false : ∀ Γ T,
  Γ ⊢ fls ∈ T → Bool <: T.
Proof. 
  intros Γ T Typing.
  dependent induction Typing.
  - auto.
  - eapply S_Trans. now apply IHTyping. trivial.
Qed.

Lemma typing_inversion_unit : ∀ Γ T,
  Γ ⊢ unit ∈ T → Unit <: T.
Proof.
  intros Γ T Typing.
  dependent induction Typing.
  - auto.
  - eapply S_Trans. now apply IHTyping. trivial.
Qed.

Lemma typing_inversion_if : ∀ Γ b t f T,
  Γ ⊢ test b t f ∈ T →
  Γ ⊢ b ∈ Bool ∧ Γ ⊢ t ∈ T ∧ Γ ⊢ f ∈ T.
Proof.
  intros. dependent induction H.
  - auto.
  - edestruct IHhas_type.
    + reflexivity.
    + destruct H2. repeat split; eauto.
Qed.

Lemma typing_inversion_pair : ∀ Γ a b P,
  Γ ⊢ pair a b ∈ P →
  ∃ A B, Pair A B <: P ∧ Γ ⊢ a ∈ A ∧ Γ ⊢ b ∈ B.
Proof.
  intros Γ a b P Typing.
  dependent induction Typing.
  - exists A, B. auto.
  - edestruct IHTyping as [A [B [E [TypingA TypingB]]]].
    reflexivity.
    exists A, B.
    eauto.
Qed.

Lemma typing_inversion_fst : ∀ Γ p A,
  Γ ⊢ fst p ∈ A →
  ∃ A' B, A' <: A ∧ Γ ⊢ p ∈ Pair A' B.
Proof.
  intros Γ p A Typing.
  dependent induction Typing.
  - exists A, B. auto.
  - destruct (IHTyping p eq_refl) as [A' [B [SubA TypingP]]].
    exists A', B. eauto.
Qed.

Lemma typing_inversion_snd : ∀ Γ p B,
  Γ ⊢ snd p ∈ B →
  ∃ A B', B' <: B ∧ Γ ⊢ p ∈ Pair A B'.
Proof.
  intros Γ p A Typing.
  dependent induction Typing.
  - exists A, B. auto.
  - destruct (IHTyping p eq_refl) as [A [B' [SubB TypingP]]].
    exists A, B'. eauto.
Qed.
