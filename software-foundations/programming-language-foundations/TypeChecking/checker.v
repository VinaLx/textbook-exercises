Require Export STLC.typing.
Require Import Bool.
Require Import LF.Maps.

Fixpoint eqb_ty (lhs rhs : ty) : bool :=
  match lhs, rhs with
  | Bool, Bool => true
  | Arrow f1 a1, Arrow f2 a2 => andb (eqb_ty f1 f2) (eqb_ty a1 a2)
  | _, _ => false
  end
.

Lemma eqb_ty_refl :
  ∀ T, eqb_ty T T = true.
Proof.
  induction T.
  - reflexivity.
  - simpl. rewrite IHT1, IHT2.
    reflexivity.
Qed.

Lemma arrow_eqb_inversion : ∀ T1 T2 T3 T4,
  eqb_ty (Arrow T1 T2) (Arrow T3 T4) = true → eqb_ty T1 T3 = true ∧ eqb_ty T2 T4 = true.
Proof.
  intros.
  simpl in H.
  now apply andb_true_iff.
Qed.

Lemma eqb_ty_true_iff : ∀ T1 T2,
  eqb_ty T1 T2 = true ↔ T1 = T2.
Proof.
  split.
  - generalize dependent T2.
    induction T1; intros T2 H.
    + destruct T2. reflexivity. inversion H.
    + destruct T2. inversion H.
      simpl in H.
      apply andb_true_iff in H as [E1 E2].
      apply IHT1_1 in E1.
      apply IHT1_2 in E2.
      congruence.
  - intros. rewrite H. apply eqb_ty_refl.
Qed.

Notation "x <- e1 ;; e2" := (
  match e1 with
  | Some x => e2
  | None => None
  end)
  (right associativity, at level 60).

Notation "'return' e" := (Some e) (at level 60).
Notation "'fail'" := None.

Fixpoint type_check (Γ : context) (t : tm) : option ty :=
  match t with
  | var x => Γ x
  | abs a A b =>
      B <- type_check (Γ & {{ a ==> A }}) b ;;
      return (Arrow A B)
  | app f a =>
      F <- type_check Γ f ;;
      A <- type_check Γ a ;;
      match F with
      | Arrow A' B => if eqb_ty A A' then return B else fail
      | _ => fail
      end
  | tru => return Bool
  | fls => return Bool
  | test b t f =>
      B <- type_check Γ b ;;
      match B with
      | Bool =>
          T <- type_check Γ t ;;
          F <- type_check Γ f ;;
          if eqb_ty T F then return T else fail
      | _ => fail
      end
  end
.

Theorem type_checking_sound : ∀ t Γ T,
  type_check Γ t = Some T → Γ ⊢ t ∈ T.
Proof.
  induction t; intros Γ T H; simpl in H.
  - now apply T_Var.
  - destruct (type_check Γ t1) eqn: Et1; destruct (type_check Γ t2) eqn: Et2;
    try solve [inversion H].
    destruct t. inversion H.
    destruct (eqb_ty t0 t3) eqn: EA.
    + apply IHt1 in Et1. apply IHt2 in Et2.
      apply eqb_ty_true_iff in EA. inversion H. subst.
      eapply T_App; eauto.
    + inversion H.
  - destruct (type_check (update Γ s t) t0) eqn: Et; inversion H.
    apply IHt in Et. now apply T_Abs.
  - inversion H. apply T_Tru.
  - inversion H. apply T_Fls.
  - destruct (type_check Γ t1) eqn: E1. 2: inversion H.
    destruct t; 
    destruct (type_check Γ t2) eqn: E2; destruct (type_check Γ t3) eqn: E3;
    inversion H.
    destruct (eqb_ty t t0) eqn: ET; inversion H.
    apply eqb_ty_true_iff in ET. subst.
    apply T_Test; auto.
Qed.

Theorem type_checking_complete : ∀ Γ t T,
  Γ ⊢ t ∈ T → type_check Γ t = Some T.
Proof.
  intros Γ t T H.
  induction H; simpl.
  - easy.
  - now rewrite IHhas_type.
  - rewrite IHhas_type1, IHhas_type2.
    now rewrite eqb_ty_refl.
  - reflexivity.
  - reflexivity.
  - rewrite IHhas_type1, IHhas_type2, IHhas_type3.
    now rewrite eqb_ty_refl.
Qed.

