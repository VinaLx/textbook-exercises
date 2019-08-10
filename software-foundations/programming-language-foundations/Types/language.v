Require Export Utf8.
Require OperationalSemantics.relations.

Inductive tm : Type :=
| tru : tm
| fls : tm
| test : tm → tm → tm → tm
| zro : tm
| scc : tm → tm
| prd : tm → tm
| iszro : tm → tm
.

Inductive bvalue : tm → Prop :=
| bv_tru : bvalue tru
| bv_fls : bvalue fls
.

Inductive nvalue : tm → Prop :=
| nv_zro : nvalue zro
| nv_scc : ∀ t, nvalue t → nvalue (scc t)
.

Definition value (t : tm) := bvalue t ∨ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm → tm → Prop :=
| ST_TestTru : ∀ t1 t2, test tru t1 t2 --> t1
| ST_TestFls : ∀ t1 t2, test fls t1 t2 --> t2
| ST_Test : ∀ t1 t1' t2 t3, t1 --> t1' → test t1 t2 t3 --> test t1' t2 t3
| ST_Scc : ∀ t1 t1', t1 --> t1' → scc t1 --> scc t1'
| ST_PrdZro : prd zro --> zro
| ST_PrdScc : ∀ t, nvalue t → prd (scc t) --> t
| ST_Prd : ∀ t1 t1', t1 --> t1' → prd t1 --> prd t1'
| ST_IszroZro : iszro zro --> tru
| ST_IszroScc : ∀ t1, nvalue t1 → iszro (scc t1) --> fls
| ST_Iszro : ∀ t1 t1', t1 --> t1' → iszro t1 --> iszro t1'

where "t1 '-->' t2" := (step t1 t2)
.

Hint Constructors step.

Notation step_normal_form := (relations.normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t ∧ ¬ value t.

Example some_term_is_stuck : ∃ t, stuck t.
Proof.
  exists (scc tru).
  split.
  - intros [t' S]. inversion S. inversion H0.
  - intros [BV | NV].
    + inversion BV.
    + inversion NV. inversion H0.
Qed.

Lemma value_is_nf : ∀ t,
  value t → step_normal_form t.
Proof.
  intros t [BV | NV].
  - inversion BV; intros [t' S]; inversion S.
  - induction NV; intros [t' S].
    + inversion S.
    + inversion S.
      apply IHNV. exists t1'. assumption.
Qed.

