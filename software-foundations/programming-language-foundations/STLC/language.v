Require Export Utf8.
Require Export String.

Inductive ty : Type :=
| Bool : ty
| Arrow : ty → ty → ty
.

Inductive tm : Type :=
| var : string → tm
| app : tm → tm → tm
| abs : string → ty → tm → tm
| tru : tm
| fls : tm
| test : tm → tm → tm → tm
.

Inductive value : tm → Prop :=
| v_abs : ∀ x T t, value (abs x T t)
| v_tru : value tru
| v_fls : value fls
.

Hint Constructors value.
