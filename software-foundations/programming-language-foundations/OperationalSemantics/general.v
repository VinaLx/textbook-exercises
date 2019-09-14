Require Import Utf8.
Require Import Relations.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : ∀ (x : X), multi R x x
| multi_step : ∀ (x y z : X), R x y → multi R y z → multi R x z.


Theorem multi_R : ∀ {X : Type} (R : relation X) (x y : X),
  R x y → multi R x y.
Proof.
  intros X R x y Rxy.
  apply multi_step with y.
  - assumption.
  - constructor.
Qed.

Theorem multi_trans : ∀ {X : Type} (R : relation X) (x y z : X),
  multi R x y → multi R y z → multi R x z.
Proof.
  intros X R x y z Rxy Ryz.
  induction Rxy.
  - assumption.
  - eapply multi_step; eauto.
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  ∀ t, ∃ t', multi R t t' ∧ normal_form R t'.

