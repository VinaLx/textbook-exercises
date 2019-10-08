Require Export Utf8.
Require Export String.
Require Export LF.Maps.

Inductive ty : Type :=
| Top : ty
| Base : string → ty
| Arrow : ty → ty → ty
| RNil : ty
| RCons : string → ty → ty → ty.

Inductive tm : Type :=
| var : string → tm
| app : tm → tm → tm
| abs : string → ty → tm → tm
| rproj : tm → string → tm
| rnil : tm
| rcons : string → tm → tm → tm
.

Inductive record_ty : ty → Prop :=
| RTNil : record_ty RNil
| RTCons : ∀ x T R, record_ty (RCons x T R)
.

Inductive record_tm : tm → Prop :=
| rtnil : record_tm rnil
| rtcons : ∀ x r rs, record_tm (rcons x r rs)
.

Inductive well_formed_ty : ty → Prop :=
| WFTop : well_formed_ty Top
| WFBase : ∀ x, well_formed_ty (Base x)
| WFArrow : ∀ T1 T2,
    well_formed_ty T1 →
    well_formed_ty T2 →
    well_formed_ty (Arrow T1 T2)
| WFRNil : well_formed_ty RNil
| WFRCons : ∀ x T R,
    well_formed_ty T →
    well_formed_ty R →
    record_ty R →
    well_formed_ty (RCons x T R)
.

Hint Constructors record_ty record_tm well_formed_ty.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var y => if beq_string x y then s else t
  | abs y T b =>
      abs y T (if beq_string x y then b else (subst x s b))
  | app f a => app (subst x s f) (subst x s a)
  | rproj t1 i => rproj (subst x s t1) i
  | rnil => rnil
  | rcons i t r => rcons i (subst x s t) (subst x s r)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm → Prop :=
| v_abs : ∀ x T t, value (abs x T t)
| v_rnil : value rnil
| v_rcons : ∀ i v vr, value v → value vr → value (rcons i v vr).

Hint Constructors value.

Fixpoint Tlookup (i : string) (Tr : ty) : option ty :=
  match Tr with
  | RCons i' T Tr' =>
      if beq_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end
.

Fixpoint tlookup (i : string) (tr : tm) : option tm :=
  match tr with
  | rcons i' t tr' =>
      if beq_string i i' then Some t else tlookup i tr'
  | _ => None
  end
.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm → tm → Prop :=
| ST_AppAbs : ∀ x T b a,
     value a →
     (app (abs x T b) a) --> [x := a] b
| ST_App1 : ∀ f f' a,
     f --> f' → (app f a) --> (app f' a)
| ST_App2 : ∀ f a a',
     value f → a --> a' →
     (app f a) --> (app f a')
| ST_Proj1 : ∀ r r' i,
    r --> r' →
    (rproj r i) --> (rproj r' i)
| ST_ProjRcd : ∀ r i vi,
    value r →
    tlookup i r = Some vi →
   (rproj r i) --> vi
| ST_Rcd1 : ∀ i t t' r,
    t --> t' →
    (rcons i t r) --> (rcons i t' r)
| ST_Rcd2 : ∀ i t r r',
    value t → r --> r' →
    (rcons i t r) --> (rcons i t r')

where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step.

