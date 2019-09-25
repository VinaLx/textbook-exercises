Require Export Utf8.
Require Import String.
Require Import LF.Maps.

Inductive ty : Type :=
| Nat : ty
| Unit : ty
| Arrow : ty → ty → ty
| Ref : ty → ty
.

Inductive tm : Type :=
| var : string → tm
| app : tm → tm → tm
| abs : string → ty → tm → tm
| const : nat → tm
| scc : tm → tm
| prd : tm → tm
| mlt : tm → tm → tm
| test0 : tm → tm → tm → tm
| unit : tm
| ref    : tm → tm
| deref  : tm → tm
| assign : tm → tm → tm
| loc : nat → tm
.

Inductive value : tm → Prop :=
| v_abs : ∀ a A b, value (abs a A b)
| v_nat : ∀ n, value (const n)
| v_unit : value unit
| v_loc : ∀ l, value (loc l)
.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' => if beq_string x x' then s else t
  | app f a => app (subst x s f) (subst x s a)
  | abs a A b => if beq_string x a then t else abs a A (subst x s b)
  | const n => t
  | scc t' => scc (subst x s t')
  | prd t' => prd (subst x s t')
  | mlt l r => mlt (subst x s l) (subst x s r)
  | test0 n t f => test0 (subst x s n) (subst x s t) (subst x s f)
  | unit => t
  | ref t' => ref (subst x s t')
  | deref t' => deref (subst x s t')
  | assign v a => assign (subst x s v) (subst x s a)
  | loc l => t
  end
.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Definition tseq t₁ t₂ := app (abs "x" Unit t₂) t₁.


