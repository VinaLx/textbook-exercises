Require Export OperationalSemantics.tm.
Require Import Relations.
Require Import OperationalSemantics.general.

Ltac solve_by_inverts n :=
  match goal with
  | H : ?T |- _ =>
      match type of T with Prop =>
        solve [
          inversion H;
          match n with S (S (?n')) =>
            subst; solve_by_inverts (S n')
          end
        ]
      end
  end
.

Ltac solve_by_invert := solve_by_inverts 1.

Theorem step_deterministic : deterministic step.
Proof.
  intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + inversion H2.
    + inversion H3.
  - inversion Hy2; subst. 
    + inversion Hy1.
    + apply IHHy1 in H2. now rewrite H2.
    + inversion H1. subst. inversion Hy1.
  - inversion Hy2; subst.
    + inversion Hy1.
    + inversion H. subst. inversion H3.
    + apply IHHy1 in H4. now rewrite H4.
Qed.

Theorem strong_progress :
  ∀ t, value t ∨ (∃ t', t --> t').
Proof.
  induction t.
  - left. constructor.
  - right. destruct IHt1.
    + destruct IHt2.
      ++ inversion H. inversion H0.
         exists (C (n + n0)).
         constructor.
      ++ destruct H0 as [t' H0].
         exists (P t1 t').
         now apply ST_Plus2.
    + destruct H as [t' H].
      exists (P t' t2).
      now apply ST_Plus1.
Qed.

Lemma value_is_nf :
  ∀ v, value v → normal_form step v.
Proof.
  intros v V.
  inversion V.
  intros [t S].
  inversion S.
Qed.

Lemma nf_is_value :
  ∀ v, normal_form step v → value v.
Proof.
  unfold normal_form.
  intros t H.
  assert (value t ∨ ∃ t', t --> t') by apply strong_progress.
  destruct H0.
  - assumption.
  - contradiction.
Qed.

Corollary nf_same_as_value :
  ∀ t, normal_form step t ↔ value t.
Proof.
  intros t.
  split; solve [apply value_is_nf | apply nf_is_value].
Qed.
