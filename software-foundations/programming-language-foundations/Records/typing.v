Require Import Records.language.
Require Import Equality.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty → ty → Prop :=
| S_Refl : ∀ T, well_formed_ty T → T <: T
| S_Trans : ∀ S U T, S <: U → U <: T → S <: T
| S_Top : ∀ S, well_formed_ty S → S <: Top
| S_Arrow : ∀ S1 S2 T1 T2,
    T1 <: S1 → S2 <: T2 → Arrow S1 S2 <: Arrow T1 T2

| S_RcdWidth : ∀ i T R,
    well_formed_ty (RCons i T R) → RCons i T R <: RNil
| S_RcdDepth : ∀i S T SR TR,
    S <: T → SR <: TR →
    record_ty SR → record_ty TR →
    RCons i S SR <: RCons i T TR
| S_RcdPerm : ∀ x y A B R,
    well_formed_ty (RCons x A (RCons y B R)) →
    x ≠ y →
    RCons x A (RCons y B R) <: RCons y B (RCons x A R)

where "T '<:' U" := (subtype T U).
Hint Constructors subtype.

Lemma subtype_wellform : ∀ S T,
  S <: T → well_formed_ty S ∧ well_formed_ty T.
Proof.
  intros S T Sub.
  induction Sub; try easy.
  - destruct IHSub1. destruct IHSub2. auto.
  - destruct IHSub1. destruct IHSub2. auto.
  - inversion H. subst.
    split. easy.
    inversion H5. subst. auto.
Qed.

Lemma wellformed_record_lookup : ∀ i T Ti,
  well_formed_ty T → Tlookup i T = Some Ti →
  well_formed_ty Ti.
Proof.
  induction T; intros Ti WF E; try solve [inversion E].
  simpl in E.
  inversion WF. subst.
  destruct (beq_string i s) eqn: Eis.
  - inversion E. now subst.
  - apply IHT2; trivial.
Qed.

Hint Resolve wellformed_record_lookup subtype_wellform.

Lemma record_types_match : ∀ S T i Ti,
  subtype S T →
  Tlookup i T = Some Ti →
  ∃ Si, Tlookup i S = Some Si ∧ subtype Si Ti.
Proof.
  intros S T i Ti SubST.
  generalize dependent Ti.
  induction SubST; intros Ti E; try solve [inversion E].
  - exists Ti. eauto.
  - apply IHSubST2 in E as [Ui [EU SubUT]].
    apply IHSubST1 in EU as [Si [ES SubSU]].
    eauto.
  - simpl in E.
    destruct (beq_string i i0) eqn: Ei.
    + exists S. inversion E. subst. simpl. rewrite Ei. auto.
    + apply IHSubST2 in E as [Si [ESR SubSTi]].
      exists Si. simpl. rewrite Ei. auto.
  - simpl in E.
    destruct (beq_string i y) eqn: Ey; destruct (beq_string i x) eqn: Ex;
    inversion H; inversion H5; subst.
    + apply beq_string_true_iff in Ey.
      apply beq_string_true_iff in Ex.
      subst. contradiction.
    + exists B. simpl. rewrite Ex, Ey. inversion E. subst. eauto.
    + exists A. simpl. rewrite Ex. inversion E. subst. eauto.
    + exists Ti. simpl. rewrite Ex, Ey. eauto.
Qed.

Lemma sub_inversion_arrow : ∀ S T1 T2,
  S <: Arrow T1 T2 →
  ∃ S1 S2, S = Arrow S1 S2 ∧ T1 <: S1 ∧ S2 <: T2.
Proof.
  intros S T1 T2 Sub.
  dependent induction Sub.
  - exists T1, T2. inversion H. subst.
    auto.
  - edestruct IHSub2 as [U1 [U2 [EU [SubTU SubUT]]]]. eauto.
    apply IHSub1 in EU as [S1 [S2 [ES [SubUS SubSU]]]].
    exists S1, S2. eauto.
  - exists S1, S2. eauto.
Qed.

Definition context := partial_map ty.
Reserved Notation "Γ '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
| T_Var : ∀ Γ x T,
    Γ x = Some T → well_formed_ty T → Γ ⊢ var x ∈ T
| T_Abs : ∀ Γ x A B b,
    well_formed_ty A → update Γ x A ⊢ b ∈ B →
    Γ ⊢ abs x A b ∈ Arrow A B
| T_App : ∀ Γ A B f a,
    Γ ⊢ f ∈ Arrow A B → Γ ⊢ a ∈ A →
    Γ ⊢ app f a ∈ B
| T_Proj : ∀ Γ i r T Ti,
    Γ ⊢ r ∈ T → Tlookup i T = Some Ti →
    Γ ⊢ rproj r i ∈ Ti
| T_Sub : ∀ Γ t S T,
    Γ ⊢ t ∈ S → S <: T → Γ ⊢ t ∈ T
| T_RNil : ∀ Γ,
    Γ ⊢ rnil ∈ RNil
| T_RCons : ∀ Γ i t T r R,
    Γ ⊢ t ∈ T →
    Γ ⊢ r ∈ R →
    record_ty R →
    record_tm r →
    Γ ⊢ rcons i t r ∈ RCons i T R

where "Γ '⊢' t '∈' T" := (has_type Γ t T).
Hint Constructors has_type.

Lemma has_type_wellform : ∀ Γ t T,
  Γ ⊢ t ∈ T → well_formed_ty T.
Proof.
  intros Γ t T H. induction H.
  - assumption.
  - now constructor.
  - now inversion IHhas_type1.
  - eapply wellformed_record_lookup; eauto.
  - now apply subtype_wellform in H0 as [WFS WFT].
  - constructor.
  - now constructor.
Qed.

Hint Resolve has_type_wellform.

Lemma step_preserves_record_tm : ∀ r r',
  record_tm r → r --> r' → record_tm r'.
Proof.
  intros r r' R Step.
  generalize dependent R.
  induction Step; intros R; inversion R; subst.
  - constructor.
  - constructor.
Qed.

Lemma lookup_field_in_value : ∀ r R i T,
  value r → empty ⊢ r ∈ R → Tlookup i R = Some T →
  ∃ t, tlookup i r = Some t ∧ empty ⊢ t ∈ T.
Proof.
  intros r R i T ValueR Typing.
  generalize dependent T.
  generalize dependent i.
  induction Typing; intros x' Tx' E; try solve [inversion E | inversion ValueR].
  - eapply record_types_match in H as [Si [ES SubST]]; eauto.
    eapply IHTyping in ValueR. 2: apply ES.
    destruct ValueR as [s [LookupS TypingS]].
    eauto.
  - simpl in *. destruct (beq_string x' i) eqn: Exi.
    + exists t. inversion E. subst. auto.
    + apply IHTyping2 in E; eauto.
      inversion ValueR. auto.
Qed.

Lemma canonical_forms_of_arrow_types : ∀ Γ f A B,
   Γ ⊢ f ∈ Arrow A B → value f →
   ∃ x A' B', f = abs x A' B'.
Proof.
  intros Γ f A B Typing ValueF.
  dependent induction Typing; inversion ValueF; subst.
  - eauto.
  - eauto.
  - apply sub_inversion_arrow in H as [SA [SB [E Subs]]].
    subst.
    eapply IHTyping; eauto.
  - apply sub_inversion_arrow in H as [SA [SB [E Subs]]].
    eapply IHTyping; eauto.
Qed.
