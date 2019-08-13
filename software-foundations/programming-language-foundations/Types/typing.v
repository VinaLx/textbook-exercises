Require Import Types.language.
Require OperationalSemantics.multistep.

Inductive ty : Type :=
| Bool : ty
| Nat : ty
.

Reserved Notation "'⊢' t '∈' T" (at level 40).

Inductive has_type : tm → ty → Prop :=
| T_Tru : ⊢ tru ∈ Bool
| T_Fls : ⊢ fls ∈ Bool
| T_Test : ∀ ttest tt tf T,
    ⊢ ttest ∈ Bool →
    ⊢ tt ∈ T → ⊢ tf ∈ T →
    ⊢ test ttest tt tf ∈ T
| T_Zro : ⊢ zro ∈ Nat
| T_Scc : ∀ t, ⊢ t ∈ Nat → ⊢ scc t ∈ Nat
| T_Prd : ∀ t, ⊢ t ∈ Nat → ⊢ prd t ∈ Nat
| T_Iszro : ∀ t, ⊢ t ∈ Nat → ⊢ iszro t ∈ Bool

where "'⊢' t '∈' T" := (has_type t T)
.

Hint Constructors has_type.

Example scc_hastype_nat__has_type_nat :
  ∀ t, ⊢ scc t ∈ Nat → ⊢ t ∈ Nat.
Proof.
  intros t T.
  now inversion T.
Qed.

Lemma bool_canonical :
  ∀ t, ⊢ t ∈ Bool → value t → bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical :
  ∀ t, ⊢ t ∈ Nat → value t → nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

Theorem progress : ∀ t T,
  ⊢ t ∈ T → value t ∨ ∃ t', t --> t'.
Proof.
  intros t T Ht.
  induction Ht.
  - auto.
  - auto.
  - destruct IHHt1 as [Vtest | [ttest' Stest]].
    + assert (bvalue ttest) as BVtest by now apply bool_canonical.
      inversion BVtest.
      ++ right. exists tt. auto.
      ++ right. exists tf. auto.
    + right. exists (test ttest' tt tf). auto.
  - auto.
  - destruct IHHt as [V | [t' S]].
    + left. right.
      assert (nvalue t) as NV by now apply nat_canonical.
      now apply nv_scc.
    + right. exists (scc t'). auto.
  - destruct IHHt as [V | [t' S]].
    + assert (nvalue t) as NV by now apply nat_canonical.
      right. inversion NV; subst.
      ++ exists zro. auto.
      ++ exists t0. auto.
    + right. exists (prd t'). auto.
  - destruct IHHt as [V | [t' S]].
    + assert (nvalue t) as NV by now apply nat_canonical.
      right. inversion NV; subst.
      ++ exists tru. auto.
      ++ exists fls. auto.
    + right. exists (iszro t'). auto.
Qed.

Lemma nvalue_nat : ∀ t, nvalue t → ⊢ t ∈ Nat.
Proof.
  intros t NV. induction NV; auto.
Qed.

Theorem Preservation : ∀ t t' T,
  ⊢ t ∈ T → t --> t' → ⊢ t' ∈ T.
Proof.
  intros t t' T HT HS.
  generalize dependent t'.
  induction HT; intros t' HS; inversion HS; subst; auto.
  + now apply nvalue_nat.
Qed.

Definition multistep := multistep.multi step.

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : ∀ t t' T,
  ⊢ t ∈ T → t -->* t' → ¬ stuck t'.
Proof.
  unfold stuck.
  intros t t' T HT HS.
  induction HS.
  - intros [NF NV].
    apply progress in HT as [V | [t' S]].
    + contradiction.
    + now assert (¬ x --> t') as contra by now apply normal_form_no_step.
  - assert (⊢ y ∈ T) as HIH by now apply Preservation with x.
    now apply IHHS.
Qed.
