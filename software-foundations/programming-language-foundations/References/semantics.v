Require Import References.store.
Require Import OperationalSemantics.general.
Require Import LF.Maps.

Require Import List.
Import ListNotations.

Require Import References.language.

Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : tm * store → tm * store → Prop :=
| ST_AppAbs : ∀ x A b a st,
    value a →
    app (abs x A b) a / st --> [x := a] b / st
| ST_App1 : ∀ f f' st st' a,
    f / st --> f' / st' →
    app f a / st --> app f' a / st'
| ST_App2 : ∀ f a a' st st',
    value f →
    a / st --> a' / st' →
    app f a / st --> app f a' / st'
| ST_SccConst : ∀ n st,
    scc (const n) / st --> scc (const (S n)) / st
| ST_Scc : ∀ t t' st st',
    t / st --> t' / st' →
    scc t / st --> scc t' / st'
| ST_PrdConst : ∀ n st,
    prd (const n) / st --> prd (const (pred n)) / st
| ST_Prd : ∀ t t' st st',
    t / st --> t' / st' →
    prd t / st --> prd t' / st'
| ST_MultConsts : ∀ n1 n2 st,
    mlt (const n1) (const n2) / st --> const (mult n1 n2) / st
| ST_Mult1 : ∀ l l' st st' r,
    l / st --> l' / st' →
    mlt l r / st --> mlt l' r / st'
| ST_Mult2 : ∀ l r r' st st',
    value l →
    r / st --> r' / st' →
    mlt l r / st --> mlt l r' / st'
| ST_If0 : ∀ n n' st st' t f,
    n / st --> n' / st' →
    test0 n t f / st --> test0 n' t f / st'
| ST_If0True : ∀ t f st,
    test0 (const 0) t f / st --> t / st
| ST_If0False : ∀ n t f st,
    test0 (const (S n)) t f / st --> f / st
| ST_Ref : ∀ t t' st st',
    t / st --> t' / st' →
    ref t / st --> ref t' / st'
| ST_RefValue: ∀ t st,
    value t →
    ref t / st --> loc (length st) / (st ++ t :: nil)
| ST_Deref : ∀ t t' st st',
    t / st --> t' / st' →
    deref t / st --> deref t' / st'
| ST_DerefLoc : ∀ n st,
    n < length st →
    deref (loc n) / st --> store_lookup n st / st
| ST_Assign1 : ∀ v v' st st' a,
    v / st --> v' / st' →
    assign v a / st --> assign v' a / st'
| ST_Assign2 : ∀ v a a' st st',
    value v →
    a / st --> a' / st' →
    assign v a / st --> assign v a' / st'
| ST_Assign : ∀ n a st,
    value a → n < length st →
    assign (loc n) a / st --> unit / replace n a st

where  "t1 '/' st1 '-->' t2 '/' st2" := (step (t1, st1) (t2, st2))
.

Hint Constructors step.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" := (multistep (t, st) (t', st'))
  (at level 40, st at level 39, t' at level 39).

Reserved Notation "Γ ';' ST '⊢' t '∈' T" (at level 40).

Definition context := partial_map ty.

Inductive has_type : context → ty_store → tm → ty → Prop :=
| T_Var : ∀ Γ ST x T,
    Γ x = Some T → Γ; ST ⊢ var x ∈ T
| T_Abs : ∀ Γ ST a A b B,
    Γ & {{ a ==> A }} ; ST ⊢ b ∈ B →
    Γ ; ST ⊢ abs a A b ∈ Arrow A B
| T_App : ∀ Γ ST A B f a,
    Γ ; ST ⊢ f ∈ Arrow A B →
    Γ ; ST ⊢ a ∈ A →
    Γ ; ST ⊢ app f a ∈ B
| T_Nat : ∀ Γ ST n, Γ ; ST ⊢ const n ∈ Nat
| T_Scc : ∀ Γ ST t,
    Γ ; ST ⊢ t ∈ Nat → Γ ; ST ⊢ scc t ∈ Nat
| T_Prd : ∀ Γ ST t,
    Γ ; ST ⊢ t ∈ Nat → Γ ; ST ⊢ prd t ∈ Nat
| T_Mlt : ∀ Γ ST l r,
    Γ ; ST ⊢ l ∈ Nat → Γ ; ST ⊢ r ∈ Nat →
    Γ ; ST ⊢ mlt l r ∈ Nat
| T_Test0 : ∀ Γ ST n t f T,
    Γ ; ST ⊢ n ∈ Nat →
    Γ ; ST ⊢ t ∈ T → Γ ; ST ⊢ f ∈ T →
    Γ ; ST ⊢ test0 n t f ∈ T
| T_Unit : ∀ Γ ST, Γ ; ST ⊢ unit ∈ Unit
| T_Loc : ∀ Γ ST n,
    n < length ST →
    Γ ; ST ⊢ loc n ∈ Ref (ty_store_lookup n ST)
| T_Ref : ∀ Γ ST t T,
    Γ ; ST ⊢ t ∈ T → Γ ; ST ⊢ ref t ∈ Ref T
| T_Deref : ∀ Γ ST t T,
    Γ ; ST ⊢ t ∈ Ref T → Γ ; ST ⊢ deref t ∈ T
| T_Assign : ∀ Γ ST v t T,
    Γ ; ST ⊢ v ∈ Ref T →
    Γ ; ST ⊢ t ∈ T →
    Γ ; ST ⊢ assign v t ∈ Unit

where "Γ ';' ST '⊢' t '∈' T" := (has_type Γ ST t T)
.

Hint Constructors has_type.

Definition store_well_typed (ST : ty_store) (st : store) :=
  length ST = length st ∧
  ∀ n, n < length st → empty ; ST ⊢ store_lookup n st ∈ ty_store_lookup n ST. 

