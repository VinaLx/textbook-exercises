Require Export Utf8.
Require Import LF.Maps.

Inductive ty : Type :=
| Top : ty
| Bool : ty
| Base : string → ty
| Arrow : ty → ty → ty
| Unit : ty
| Pair : ty → ty → ty
.

Inductive tm : Type :=
| var : string → tm
| app : tm → tm → tm
| abs : string → ty → tm → tm
| tru : tm
| fls : tm
| test : tm → tm → tm → tm
| unit : tm
| pair : tm → tm → tm
| fst : tm → tm
| snd : tm → tm
.

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y => if beq_string x y then s else t
  | abs y T b =>
      abs y T (if beq_string x y then b else (subst x s b))
  | app f a =>
      app (subst x s f) (subst x s a)
  | tru => tru
  | fls => fls
  | test b tr fl =>
      test (subst x s b) (subst x s tr) (subst x s fl)
  | unit => unit
  | pair a b => pair (subst x s a) (subst x s b)
  | fst a => fst (subst x s a)
  | snd a => snd (subst x s a)
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm → Prop :=
| v_abs   : ∀ x T t, value (abs x T t)
| v_true  : value tru
| v_false : value fls
| v_unit  : value unit
| v_pair  : ∀ a b, value a → value b → value (pair a b)
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : tm → tm → Prop :=
| ST_AppAbs : ∀x T t12 v2,
    value v2 →
    app (abs x T t12) v2 --> [x := v2] t12
| ST_App1 : ∀ f f' a,
    f --> f' →
    app f a --> app f' a
| ST_App2 : ∀ v a a',
    value v →
    a --> a' →
    app v a --> app v a'
| ST_TestTrue : ∀ t f,
    test tru t f --> t
| ST_TestFalse : ∀ t f,
    test fls t f --> f
| ST_Test : ∀ b b' t f,
    b --> b' →
    test b t f --> test b' t f
| ST_Pair1 : ∀ a a' b,
    a --> a' →
    pair a b --> pair a' b
| ST_Pair2 : ∀ v b b',
    value v → b --> b' →
    pair v b --> pair v b'
| ST_Fst1 : ∀ p p',
    p --> p' → fst p --> fst p'
| ST_Fst2 : ∀ a b,
    fst (pair a b) --> a
| ST_Snd1 : ∀ p p',
    p --> p' → snd p --> snd p'
| ST_Snd2 : ∀ a b,
    snd (pair a b) --> b

where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty → ty → Prop :=
| S_Refl  : ∀ T, T <: T
| S_Trans : ∀ A B C, A <: B → B <: C → A <: C
| S_Top   : ∀ T, T <: Top
| S_Arrow : ∀ S₁ S₂ T₁ T₂,
    S₁ <: T₁ → S₂ <: T₂ → Arrow T₁ S₂ <: Arrow S₁ T₂
| S_Pair  : ∀ S₁ S₂ T₁ T₂,
    S₁ <: T₁ → S₂ <: T₂ → Pair S₁ S₂ <: Pair T₁ T₂
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

Definition context := partial_map ty.

Reserved Notation "Γ '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
| T_Var : ∀ Γ x T, Γ x = Some T → Γ ⊢ var x ∈ T
| T_Abs : ∀ Γ a A B b,
    Γ & {{ a ==> A }} ⊢ b ∈ B →
    Γ ⊢ abs a A b ∈ Arrow A B
| T_App : ∀ Γ A B f a,
    Γ ⊢ f ∈ Arrow A B → Γ ⊢ a ∈ A →
    Γ ⊢ app f a ∈ B
| T_True  : ∀ Γ, Γ ⊢ tru ∈ Bool
| T_False : ∀ Γ, Γ ⊢ fls ∈ Bool
| T_Test : ∀ b t f T Γ,
    Γ ⊢ b ∈ Bool →
    Γ ⊢ t ∈ T → Γ ⊢ f ∈ T →
    Γ ⊢ test b t f ∈ T
| T_Unit : ∀ Γ, Γ ⊢ unit ∈ Unit
| T_Pair : ∀ Γ a A b B,
    Γ ⊢ a ∈ A → Γ ⊢ b ∈ B →
    Γ ⊢ pair a b ∈ Pair A B
| T_Fst : ∀ Γ p A B,
    Γ ⊢ p ∈ Pair A B →
    Γ ⊢ fst p ∈ A
| T_Snd : ∀ Γ p A B,
    Γ ⊢ p ∈ Pair A B →
    Γ ⊢ snd p ∈ B
(* Subsumption *)
| T_Sub : ∀ Γ t S T, Γ ⊢ t ∈ S → S <: T → Γ ⊢ t ∈ T

where "Γ '⊢' t '∈' T" := (has_type Γ t T).
Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.
