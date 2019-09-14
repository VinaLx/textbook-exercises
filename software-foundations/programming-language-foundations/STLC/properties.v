Require Import STLC.language.
Require Import STLC.semantics.
Require Import STLC.typing.
Require Import LF.Maps.
Require Import Relations.

Lemma canonical_forms_bool : ∀ t,
  empty ⊢ t ∈ Bool → value t → (t = tru) ∨ (t = fls).
Proof.
  intros t H V.
  inversion V; subst.
  - inversion H.
  - now left.
  - now right.
Qed.

Lemma canonical_forms_func : ∀ t A B,
  empty ⊢ t ∈ Arrow A B →
  value t →
  ∃ a b, t = abs a A b.
Proof.
  intros t A B H V.
  inversion V; subst; inversion H.
  subst. now exists x, t0.
Qed.

Theorem progress : ∀ t T,
  empty ⊢ t ∈ T → value t ∨ ∃ t', t --> t'.
Proof.
  induction t; intros T Ht; auto; inversion Ht; subst; right.
  - inversion H1.
  - apply IHt1 in H2 as [Hv1 | [t1' Ht1]].
    + apply IHt2 in H4 as [Hv2 | [t2' Ht2]].
      -- clear A IHt1 IHt2. inversion Ht. subst.
         inversion Hv1; subst; try solve [inversion H2].
         exists ([x := t2] t). auto.
      -- exists (app t1 t2'). auto.
    + exists (app t1' t2). auto.
  - pose H3. apply IHt1 in h as [Hv1 | [t1' Ht1]].
    + inversion Hv1; subst; try solve [inversion H3].
      -- exists t2. auto.
      -- exists t3. auto.
    + exists (test t1' t2 t3). auto.
Qed.

Inductive appears_free : string → tm → Prop :=
| AF_Var : ∀ x, appears_free x (var x)
| AF_App1 : ∀ x op arg,
    appears_free x op →
    appears_free x (app op arg)
| AF_App2 : ∀ x op arg,
    appears_free x arg →
    appears_free x (app op arg)
| AF_Abs : ∀ x y Y t,
    y ≠ x →
    appears_free x t →
    appears_free x (abs y Y t)
| AF_Test1 : ∀ x b t f,
    appears_free x b →
    appears_free x (test b t f)
| AF_Test2 : ∀ x b t f,
    appears_free x t →
    appears_free x (test b t f)
| AF_Test3 : ∀ x b t f,
    appears_free x f →
    appears_free x (test b t f)
.

Hint Constructors appears_free.

Definition closed (t : tm) := ∀ x, ¬ appears_free x t.

Lemma free_in_context : ∀ x t T Γ,
  appears_free x t → Γ ⊢ t ∈ T →
  ∃ T', Γ x = Some T'.
Proof.
  intros x t T Γ H.
  generalize dependent Γ.
  generalize dependent T.
  induction H; intros T Γ Ht; inversion Ht; subst;
    try solve [eapply IHappears_free; eassumption].
  - now exists T.
  - apply IHappears_free in H6. 
    assert (Γ & {{ y ==> Y }} x = Γ x) as E. {
      unfold update, t_update.
      apply beq_string_false_iff in H. now rewrite H.
    }
    now rewrite E in H6.
Qed.

Corollary typable_empty__closed : ∀ t T,
  empty ⊢ t ∈ T → closed t.
Proof.
  intros t T Ht.
  remember empty as Γ. 
  induction Ht; intros v Haf; inversion Haf; subst.
  - discriminate H.
  - assert (∃ V, empty & {{ a ==> A }} v = Some V) as [V E] by
      now apply free_in_context with b B.
    unfold update, t_update in E.
    apply beq_string_false_iff in H2. rewrite H2 in E.
    discriminate E.
  - assert (closed f) by auto.
    now apply H with v.
  - assert (closed a) by auto.
    now apply H with v.
  - assert (closed b) by auto.
    now apply H with v.
  - assert (closed t) by auto.
    now apply H with v.
  - assert (closed f) by auto.
    now apply H with v.
Qed.

Lemma context_invariance : ∀ Γ Γ' t T,
  Γ  ⊢ t ∈ T →
  (∀ x, appears_free x t → Γ x = Γ' x) →
  Γ' ⊢ t ∈ T.
Proof.
  intros Γ Γ' t T Ht. generalize dependent Γ'.
  induction Ht; intros Γ' Hf.
  - apply T_Var.
    rewrite <- H. symmetry. apply Hf. auto.
  - apply T_Abs.
    apply IHHt. intros x Haf.
    unfold update, t_update.
    destruct (beq_string a x) eqn: Exa.
    + reflexivity.
    + apply Hf. apply AF_Abs.
      -- now apply beq_string_false_iff.
      -- assumption.
  - eapply T_App;
    [> apply IHHt1 | apply IHHt2];
    intros x Haf; apply Hf; auto.
  - constructor.
  - constructor.
  - apply T_Test;
    [> apply IHHt1 | apply IHHt2 | apply IHHt3];
    intros x Haf; apply Hf; auto.
Qed.

Lemma relax_empty_context : ∀ Γ t T,
  empty ⊢ t ∈ T → Γ ⊢ t ∈ T.
Proof.
  intros Γ t T Ht.
  apply context_invariance with empty.
  + trivial.
  + intros x Haf.
    apply typable_empty__closed in Ht.
    set (contra := Ht x Haf).
    contradiction.
Qed.
  

Lemma substitution_preserves_typing : ∀ Γ x u U t T,
  Γ & {{ x ==> U }} ⊢ t ∈ T →
  empty ⊢ u ∈ U →
  Γ ⊢ [x := u] t ∈ T.
Proof.
  intros until t.
  generalize dependent U.
  generalize dependent u.
  generalize dependent x.
  generalize dependent Γ.
  induction t; simpl; intros Γ x u U T Htt Htu;
  inversion Htt; subst.
  - destruct (eqb x s) eqn: Esx;
    apply beq_eqb_iff in Esx; unfold update, t_update in H1;
      rewrite Esx in H1.
    + inversion H1. rewrite <- H0.
      now apply relax_empty_context.
    + now apply T_Var.
  - eapply T_App;
    [> eapply IHt1 | eapply IHt2]; eauto.
  - apply T_Abs.
    destruct (eqb x s) eqn: Esx.
    + apply eqb_eq in Esx. rewrite Esx in H4.
        rewrite update_shadow in H4.
      assumption.
    + eapply IHt. rewrite update_permute in H4.
      -- eassumption.
      -- now apply eqb_neq.
      -- trivial.
  - constructor.
  - constructor. 
  - apply T_Test;
    [> eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
Qed.

Theorem preservation : ∀ t t' T,
  empty ⊢ t  ∈ T → t --> t' →
  empty ⊢ t' ∈ T.
Proof.
  intros t t' T Ht. generalize dependent t'.
  remember (@empty ty) as Γ eqn: Γempty.
  induction Ht; intros t'; intros Hstep; inversion Hstep; subst.
  - apply substitution_preserves_typing with A.
    + inversion Ht1. subst. assumption.
    + assumption.
  - apply T_App with A.
    + now apply IHHt1.
    + assumption.
  - apply T_App with A.
    + assumption.
    + now apply IHHt2.
  - assumption.
  - assumption.
  - apply T_Test; try assumption.
    apply IHHt1; auto.
Qed.

Definition normal_form
  {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Definition stuck (t : tm) : Prop :=
  (normal_form step) t ∧ ¬ value t.

Corollary soundness : ∀ t t' T,
  empty ⊢ t ∈ T → t -->* t' →
  ¬ (stuck t').
Proof.
  intros t t' T Ht Hmstep.
  unfold stuck.
  intros [Hnf Hnv]. unfold normal_form in Hnf.
  induction Hmstep.
  - apply progress in Ht as [Hv | Hstep]; contradiction.
  - apply IHHmstep; try assumption.
    eapply preservation; eauto.
Qed.

Theorem unique_types : ∀ Γ t T1 T2,
  Γ ⊢ t ∈ T1 → Γ ⊢ t ∈ T2 → T1 = T2.
Proof.
  intros Γ t T1 T2 Ht1. generalize dependent T2.
  induction Ht1; intros T2 Ht2; inversion Ht2; subst; auto.
  - congruence.
  - cut (B = B0).
    + intro E. now rewrite E.
    + now apply IHHt1.
  - assert (A = A0) by
      now apply IHHt1_2.
    rewrite <- H in H2.
    assert (Arrow A B = Arrow A T2) by
      now apply IHHt1_1.
    now inversion H0.
Qed.
