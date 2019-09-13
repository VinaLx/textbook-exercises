Require Export LF.Maps.
Require Export STLC.language.
Require Import STLC.semantics.

Definition context := partial_map ty.

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
| T_Var : ∀ Γ x T, Γ x = Some T → Γ ⊢ var x ∈ T
| T_Abs : ∀ Γ a A b B,
    Γ & {{ a ==> A }} ⊢ b ∈ B →
    Γ ⊢ abs a A b ∈ Arrow A B
| T_App : ∀ Γ f A B a,
    Γ ⊢ f ∈ Arrow A B →
    Γ ⊢ a ∈ A →
    Γ ⊢ app f a ∈ B
| T_Tru : ∀ Γ, Γ ⊢ tru ∈ Bool
| T_Fls : ∀ Γ, Γ ⊢ fls ∈ Bool
| T_Test : ∀ Γ b t f T,
    Γ ⊢ b ∈ Bool →
    Γ ⊢ t ∈ T →
    Γ ⊢ f ∈ T →
    Γ ⊢ test b t f ∈ T

where "Gamma '⊢' t '∈' T" := (has_type Gamma t T).

Lemma update_type_exact : ∀ Γ x T, update Γ x T ⊢ var x ∈ T.
Proof.
  intros Γ x T.
  apply T_Var.
  unfold update, t_update.
  now rewrite <- beq_string_refl.
Qed.

Example typing_example_2_full :
  empty ⊢
  (abs x Bool (abs y (Arrow Bool Bool)
    (app (var y) (app (var y) (var x))))) ∈
  (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof.
  apply T_Abs.
  apply T_Abs.
  apply T_App with Bool.
  - apply update_type_exact.
  - apply T_App with Bool.
    + apply update_type_exact.
    + rewrite update_permute. apply update_type_exact. easy.
Qed.

Example typing_example_3 :
  ∃ T,
    empty ⊢
    (abs x (Arrow Bool Bool) (abs y (Arrow Bool Bool) (abs z Bool
      (app (var y) (app (var x) (var z)))))) ∈
    T.
Proof.
  exists (Arrow (Arrow Bool Bool) (Arrow (Arrow Bool Bool) (Arrow Bool Bool))).
  repeat apply T_Abs.
  apply T_App with Bool.
  - rewrite update_permute.
    apply update_type_exact. easy.
  - apply T_App with Bool.
    + apply T_Var. now unfold update, t_update.
    + apply update_type_exact.
Qed.

Lemma arrow_not_itself : ∀ A B, A ≠ Arrow A B.
Proof.
  induction A; intros.
  - discriminate.
  - intro E. injection E. intros A2B contra.
    apply IHA1 in contra.
    auto.
Qed.

Example typing_nonexample_3 :
  ¬ (∃ S T, empty ⊢ abs x S (app (var x) (var x)) ∈ T).
Proof.
  intros [S [T H]].
  inversion H. subst.
  inversion H5. subst.
  inversion H3. inversion H6. subst.
  rewrite H9 in H2.
  injection H2.
  apply arrow_not_itself.
Qed.

