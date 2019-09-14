Require Export STLC.language.
Require Import OperationalSemantics.general.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tru => tru
  | fls => fls
  | abs x' T body =>
      abs x' T (if eqb x x' then body else [x := s] body)
  | var x' => if eqb x x' then s else t
  | app t1 t2 => app ([x := s] t1) ([x := s] t2)
  | test b t f => test ([x := s] b) ([x := s] t) ([x := s] f)
  end

where "'[' x ':=' s ']' t" := (subst x s t)
.

Inductive substi (s : tm) (x : string) : tm → tm → Prop :=
| s_var1 : substi s x (var x) s
| s_var2 : ∀ y : string, x <> y → substi s x (var y) (var y)
| s_tru : substi s x tru tru
| s_fls : substi s x fls fls
| s_abs1 : ∀ T body, substi s x (abs x T body) (abs x T body)
| s_abs2 : ∀ y T body body', x <> y → substi s x body body' → 
    substi s x (abs y T body) (abs y T body')
| s_app : ∀ operator operator' operand operand',
    substi s x operator operator' → substi s x operand operand' →
    substi s x (app operator operand) (app operator' operand')
| s_test : ∀ b b' t t' f f',
    substi s x b b' → substi s x t t' → substi s x f f' →
    substi s x (test b t f) (test b' t' f')
.

Lemma subst_substi : ∀ s x t t', [x := s]t = t' → substi s x t t'.
Proof.
  induction t; simpl; intros; rewrite <- H.
  - destruct (eqb x s0) eqn: E.
    + apply eqb_eq in E. subst.
      apply s_var1.
    + apply s_var2.
      now apply eqb_neq.
  - apply s_app.
    + now apply IHt1.
    + now apply IHt2.
  - destruct (eqb x s0) eqn: E.
    + apply eqb_eq in E. rewrite E.
      apply s_abs1.
    + apply s_abs2.
      now apply eqb_neq.
      now apply IHt.
  - apply s_tru.
  - apply s_fls.
  - apply s_test.
    + now apply IHt1.
    + now apply IHt2.
    + now apply IHt3.
Qed.

Lemma substi_subst : ∀ s x t t', substi s x t t' → [x := s]t = t'.
Proof.
  intros. induction H; simpl.
  + now rewrite eqb_refl.
  + apply eqb_neq in H. now rewrite H.
  + reflexivity.
  + reflexivity.
  + now rewrite eqb_refl.
  + apply eqb_neq in H. now rewrite H, IHsubsti.
  + now rewrite IHsubsti1, IHsubsti2.
  + now rewrite IHsubsti1, IHsubsti2, IHsubsti3.
Qed.

Theorem substi_correct : ∀ s x t t', [x := s]t = t' ↔ substi s x t t'.
Proof.
  intros. split;
  [> apply subst_substi | apply substi_subst].
Qed.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : tm → tm → Prop :=
| ST_AppAbs : ∀ x T body v,
    value v → app (abs x T body) v --> [x := v] body
| ST_App1 : ∀ t1 t1' t2,
    t1 --> t1' → app t1 t2 --> app t1' t2
| ST_App2 : ∀ v t2 t2',
    value v → t2 --> t2' → app v t2 --> app v t2'
| ST_TestTru : ∀ t1 t2, test tru t1 t2 --> t1
| ST_TestFls : ∀ t1 t2, test fls t1 t2 --> t2
| ST_Test : ∀ b b' t f, b --> b' → test b t f --> test b' t f
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Notation idB := (abs x Bool (var x)).
Notation idBB := (abs x (Arrow Bool Bool) (var x)).
Notation idBBBB := (abs x (Arrow (Arrow Bool Bool) (Arrow Bool Bool)) (var x)).
Notation k := (abs x Bool (abs y Bool (var x))).
Notation notB := (abs x Bool (test (var x) fls tru)).

Lemma step_example5 :
  app (app idBBBB idBB) idB -->* idB.
Proof.
  eapply multi_step.
  apply ST_App1.
  apply ST_AppAbs.
  auto.
  simpl.
  eapply multi_step.
  apply ST_AppAbs.
  auto.
  apply multi_refl.
Qed.
