(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

From Coq Require Import Ring.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Lia.
From Coq Require Import Classes.SetoidClass.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.
From Crypto Require Import Curves.Weierstrass.Jacobian.
From Crypto Require Import Curves.Weierstrass.Affine.
From Crypto Require Import Curves.Weierstrass.AffineProofs.

From EC Require Import CommutativeGroup.

(* An elliptic curve over a finite field. *)
Class Curve
  (F : Type)(Feq: F -> F -> Prop)
  {Fzero Fone : F}
  {Fadd Fsub Fmul Fdiv : F -> F -> F}
  {Fopp Finv : F -> F}
  `{F_field : field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
  {a b : F}
:=
{
  a_is_minus_3 : Feq a (Fopp (Fadd (Fadd Fone Fone) Fone));
  (* Field has characteristic at least 28 enables a simple proof that the discriminant is nonzero. *)
  Fchar_28 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28;
  (* Discriminant is non-zero follows from a=-3 and b<>2 and b<>-2 when characteristic is large*)
  b_ne_plus_minus_2 : 
    ~((Feq b (Fadd Fone Fone)) \/ (Feq b (Fopp (Fadd Fone Fone))))
}.

(* The field must have characteristic at least 12 in order for the base point to generate a group. *)
Global Instance Fchar_12 : forall `{Curve}, @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12.
  intros.
  eapply char_ge_weaken.
  apply Fchar_28.
  lia.

Defined.

(* Point addition requires the field to have characteristic at least 3. *)
Global Instance Fchar_3 : forall `{Curve}, @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3.

  intros.
  eapply char_ge_weaken.
  apply Fchar_12.
  lia.

Qed.

Definition point `{Curve}{Feq_dec : DecidableRel Feq} : Type := @Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec.
Definition double_minus_3 `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.double_minus_3 F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Feq_dec a_is_minus_3.
Definition double `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.double F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Feq_dec.
Definition add `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Fchar_3 Feq_dec.
Definition to_affine `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Feq_dec.
Definition opp `{Curve}{Feq_dec : DecidableRel Feq} : point -> point := Jacobian.opp.

Definition is_jacobian `{Curve}{Feq_dec : DecidableRel Feq} (p : F * F * F) :=
  let '(X, Y, Z) := p in
  if dec (Feq Z Fzero)
    then True
    else
     Feq (Fmul Y Y)
       (Fadd
          (Fadd (Fmul (Fmul X X) X)
             (Fmul 
                (Fmul a X)
                (Fmul 
                 (Fmul Z Z) 
                 (Fmul Z Z))))
          (Fmul b
             (Fmul 
                (Fmul (Fmul Z Z) Z)
                (Fmul (Fmul Z Z) Z)))).

Definition zero_point_h`{Curve} : F * F * F := (Fzero, Fone, Fzero).
Theorem zero_point_is_jacobian : forall `{Curve}{Feq_dec : DecidableRel Feq} , is_jacobian zero_point_h.

  intros.
  unfold is_jacobian, zero_point_h.
  destruct (dec (Feq Fzero Fzero)); intuition.
  exfalso.
  eapply n.
  nsatz.

Qed.

Definition zero_point`{Curve}{Feq_dec : DecidableRel Feq}  : point :=
  exist _  zero_point_h zero_point_is_jacobian.

(* Weierstrass curve is used to produce commutative group *)
Definition wpoint`{Curve} := @WeierstrassCurve.W.point F Feq Fadd Fmul a b.
Definition W_opp`{Curve}{Feq_dec : DecidableRel Feq}  : wpoint -> wpoint := W.opp.
Definition W_eq`{Curve} : wpoint -> wpoint -> Prop := WeierstrassCurve.W.eq.
Definition W_add`{Curve}{Feq_dec : DecidableRel Feq}  : wpoint -> wpoint -> wpoint := WeierstrassCurve.W.add.
Definition wzero`{Curve} : wpoint := WeierstrassCurve.W.zero.

Section DiscriminantNonzero.

  Context `{curve: Curve}.
  Context {Feq_dec : DecidableRel Feq}.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

    
  Theorem discriminant_nonzero : 
    ~
  Feq
  ((1 + 1 + 1 + 1) * a * a * a +
   ((1 + 1 + 1 + 1) ^ 2 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) 0.

    intros.
    repeat rewrite a_is_minus_3.

    assert (Feq ((1 + 1 + 1 + 1) * Fopp (1 + 1 + 1) * Fopp (1 + 1 + 1) * Fopp (1 + 1 + 1)) (((1 + 1 + 1)^3) * (Fopp (1 + 1 + 1 + 1)))).
    nsatz.
    rewrite H.
    assert (Feq  (((1 + 1 + 1 + 1) ^ 2 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) (((1 + 1 + 1)^3) * (b^2))).
    nsatz.
    rewrite H0.
    unfold Logic.not.
    intros.

    assert (~ Feq (1 + (1 + 1) * (1 + (1 + 1) * ((1 + 1) * (1 + (1 + 1))))) 0).
    assert (Feq (1 + (1 + 1) * (1 + (1 + 1) * ((1 + 1) * (1 + (1 + 1))))) (@Ring.of_Z F 0 1 Fopp Fadd  (Z.pos 27))).
    simpl.
    nsatz.
    rewrite H2.

    eapply Fchar_28.
    lia.

    assert (Feq ((b + (1 + 1)) * (b  + (Fopp (1 + 1)))) 0).
    nsatz.
    destruct (dec (Feq b (1+1))).
    apply b_ne_plus_minus_2.
    left.
    trivial.
    apply b_ne_plus_minus_2.
    right.
    assert (Feq ((b + (1 + 1)) * ((Finv (b + Fopp (1 + 1)))* ( (b + Fopp (1 + 1))))) 0).
    nsatz.
    rewrite left_multiplicative_inverse in H4.
    nsatz.
    intuition idtac.
    eapply n.
    nsatz.

  Qed.
End DiscriminantNonzero.

Global Instance W_commutative_group : 
  forall `{Curve}{Feq_dec : DecidableRel Feq},
  @commutative_group wpoint
  WeierstrassCurve.W.eq
  WeierstrassCurve.W.add
  WeierstrassCurve.W.zero
  W.opp.

  intros.
  apply W.commutative_group.
  apply Fchar_12.
  unfold Datatypes.id.
  apply discriminant_nonzero.  

Defined.

Global Instance jac_eq_setoid : forall `{Curve}{Feq_dec : DecidableRel Feq}, Setoid point := {equiv := Jacobian.eq}.
Global Instance w_eq_setoid : forall `{Curve}{Feq_dec : DecidableRel Feq}, Setoid wpoint := {equiv := WeierstrassCurve.W.eq}.


Section CurveFacts.

  Context `{curve : Curve}.
  Context {Feq_dec : DecidableRel Feq}.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

  (* Additional field facts *)
  Theorem fmul_same_r : forall x v1 v2,
    Feq v1 v2 ->
    Feq (v1 * x) (v2 * x).

    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem fadd_same_r : forall x v1 v2,
    Feq v1 v2 ->
    Feq (v1 + x) (v2 + x).

    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem f_zero_absorb : forall (x : F),
    Feq (x * 0) 0.

    intros.
    symmetry.
    rewrite <- (right_identity (x * 0)).
    rewrite <- (right_inverse (x * 0)) at 1.
    rewrite <- (right_inverse (x * 0)) at 4.
    rewrite (associative (x * 0)).
    apply fadd_same_r.
    rewrite <- left_distributive.
    rewrite right_identity.
    reflexivity.

  Qed.

  Theorem square_nz : forall (x : F),
    ~(Feq x 0) ->
    ~(Feq (x ^ 2 ) 0).

    intuition idtac.
    eapply (@fmul_same_r (Finv x)) in H0.
    rewrite <- (associative x) in H0.
    rewrite (commutative _ (Finv x)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite (commutative 0) in H0.
    rewrite f_zero_absorb in H0.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem cube_nz : forall (x : F),
    ~(Feq x 0) ->
    ~(Feq (x ^ 3) 0).

    intuition idtac.
    eapply (@fmul_same_r (Finv x)) in H0.
    rewrite <- (associative x) in H0.
    rewrite (commutative _ (Finv x)) in H0.
    rewrite (associative (Finv x)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite left_identity in H0.
    rewrite (commutative 0) in H0.
    rewrite f_zero_absorb in H0.

    eapply (@fmul_same_r (Finv x)) in H0.
    rewrite <- (associative x) in H0.
    rewrite (commutative _ (Finv x)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite (commutative 0) in H0.
    rewrite f_zero_absorb in H0.
    intuition idtac.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem square_mul_eq : forall (x y : F),
    Feq ((x * y)^2) (x^2 * y^2).
  
    intros.
    repeat rewrite associative.
    apply ring_mul_Proper.
    rewrite <- (associative x x).  
    rewrite <- associative.
    apply ring_mul_Proper.
    reflexivity.
    apply commutative.
    reflexivity.
  Qed.

  Theorem cube_mul_eq : forall (x y : F),
    Feq ((x * y)^3) (x^3 * y^3).

    intros.
    rewrite square_mul_eq.
    repeat rewrite <- (associative (x^2)).
    apply ring_mul_Proper.
    reflexivity.
    rewrite (commutative x (y^3)).
    rewrite <- (associative (y^2)).
    apply ring_mul_Proper.
    reflexivity.
    apply commutative.
  Qed.

  
  Theorem fmul_same_r_if : forall (x y z : F),
    ~ (Feq x 0) ->
    Feq (y * x) (z * x) ->
    Feq y z.

    intros.
    eapply (fmul_same_r (Finv x)) in H0.
    rewrite <- associative in H0.
    rewrite (commutative x) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite <- associative in H0.
    rewrite (commutative x) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    trivial.
    trivial.
    trivial.

  Qed.

  Theorem fadd_same_r_if : forall (x y z : F),
    Feq (y + x) (z + x) ->
    Feq y z.

    intros.
    eapply (fadd_same_r (Fopp x)) in H.
    rewrite <- associative in H.
    rewrite (commutative x) in H.
    rewrite left_inverse in H.
    rewrite right_identity in H.
    rewrite <- associative in H.
    rewrite (commutative x) in H.
    rewrite left_inverse in H.
    rewrite right_identity in H.
    trivial.

  Qed.

  Theorem mul_nz : forall (x y : F),
    ~(Feq x 0) ->
    ~(Feq y 0) ->
    ~(Feq (x * y) 0).

    intuition idtac.
    
    eapply (@fmul_same_r (Finv y)) in H1.
    rewrite <- (associative x) in H1.
    rewrite (commutative _ (Finv y)) in H1.
    rewrite left_multiplicative_inverse in H1.
    rewrite right_identity in H1.
    rewrite (commutative 0) in H1.
    rewrite f_zero_absorb in H1.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem inv_mul_eq : forall (x y : F),
    ~(Feq y 0) ->
    ~(Feq x 0) ->
    Feq (Finv (x*y)) ((Finv x) * (Finv y)).

    intros.
    eapply (@fmul_same_r_if y).
    trivial.
    rewrite <- associative.
    rewrite left_multiplicative_inverse; trivial.
    rewrite right_identity.
    
    eapply (@fmul_same_r_if x).
    trivial.
    rewrite left_multiplicative_inverse; trivial.
    rewrite <- associative.
    rewrite (commutative y).
    apply left_multiplicative_inverse.
    apply mul_nz; eauto.
 
  Qed.

  Theorem inv_square_eq : forall (x : F),
    ~(Feq x 0) ->
    Feq ((Finv x)^2) (Finv (x^2)).

    symmetry.
    apply inv_mul_eq; eauto.

  Qed.

  Theorem inv_cube_eq : forall (x : F),
    ~(Feq x 0) ->
    Feq ((Finv x)^3) (Finv (x^3)).

    symmetry.
    rewrite inv_mul_eq; eauto.
    rewrite inv_square_eq; eauto.
    reflexivity.
    apply square_nz; trivial.

  Qed.

  Theorem cube_square_eq : forall (x : F),
    Feq ((x^3)^2) ((x^2)^3).

    intros.
    repeat rewrite associative.
    reflexivity.

  Qed.

  Theorem opp_mul_eq : forall (x : F),
    Feq (Fopp x) (Fmul (Fopp 1) x).

    intros.
    eapply (@fadd_same_r_if x).
    rewrite left_inverse.
    assert (Feq x (1 * x)).
    nsatz.
    rewrite H at 2.
    rewrite <- right_distributive.
    rewrite left_inverse.
    symmetry.
    rewrite commutative.
    apply f_zero_absorb.

  Qed.

  Theorem fmul_same_l:
    forall [x y z : F],
    Feq y z ->
    Feq (x * y) (x * z).

    intros.
    rewrite H.
    reflexivity.
  Qed.


  Theorem double_minus_3_eq_double : forall P,
      Jacobian.eq (double P) (double_minus_3 P).

    intros.
    eapply Jacobian.double_minus_3_eq_double.
  Qed.

  Theorem to_affine_add: forall `{Curve}`{DecidableRel Feq} P Q,
    W_eq (to_affine (add P Q)) (W_add (to_affine P) (to_affine Q)).

    intros.
    apply Jacobian.to_affine_add.

  Qed.

  Theorem jac_eq_from_affine : forall (x y : point),
    W_eq (to_affine x) (to_affine y) ->
    x == y.
  
    intros.
    rewrite <- Jacobian.of_affine_to_affine.
    symmetry.
    rewrite <- Jacobian.of_affine_to_affine.
    symmetry.
    apply Jacobian.Proper_of_affine.
    trivial.
  Qed.

  Theorem jac_add_assoc : forall (x y z : point),
    Jacobian.eq (add (add x y) z) (add x (add y z)).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_add.
    rewrite associative.
    reflexivity.

  Qed.

  Theorem jac_add_comm : forall (a b : point),
    Jacobian.eq (add a b) (add b a).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_add.
    apply commutative.

  Qed.

  Theorem to_affine_zero : W_eq (to_affine zero_point) WeierstrassCurve.W.zero.

    unfold W_eq, WeierstrassCurve.W.eq, to_affine, Jacobian.to_affine, zero_point.
    simpl.
    destruct (dec (Feq 0 0)); trivial.
    intuition idtac.
    eapply n.
    reflexivity.
  Qed.

  Theorem jac_add_id_l : forall (a : point),
    Jacobian.eq (add zero_point a)  a.

    intros.
    apply jac_eq_from_affine.
    rewrite to_affine_add.
    rewrite to_affine_zero.  
    apply left_identity.

  Qed.

  Theorem jac_double_correct : forall (a : point),
    Jacobian.eq (double a) (add a a).

    intros.
    apply jac_eq_from_affine.
    rewrite to_affine_add.
    unfold double, to_affine.
    rewrite Jacobian.to_affine_double.
    reflexivity.

  Qed.

  Theorem Proper_opp : Proper (Jacobian.eq ==> Jacobian.eq) opp.
  
    intros.
    unfold Proper, respectful, Jacobian.eq, Jacobian.opp.
    intros.
    simpl in *.
    destruct (proj1_sig x). destruct p.
    destruct (proj1_sig y). destruct p.
    destruct (dec (Feq f 0)).
    trivial.
    intuition idtac.
    rewrite opp_mul_eq.
    rewrite (opp_mul_eq f4).
    repeat rewrite <- (associative (Fopp 1)).
    eapply fmul_same_l; eauto.
  Qed.

  Theorem to_affine_opp : forall x, 
    W_eq (to_affine (opp x)) (W_opp (to_affine x)).

    intros.

    unfold W_eq, WeierstrassCurve.W.eq, to_affine, Jacobian.to_affine, Jacobian.opp, W_opp.
    simpl.
    destruct x.
    simpl.
    destruct x.
    destruct p.
    destruct (dec (Feq f 0)); intuition idtac.
    reflexivity.
    repeat rewrite field_div_definition.
    rewrite (@opp_mul_eq (f1 * Finv (f ^ 3))).
    rewrite (opp_mul_eq).
    symmetry.
    apply associative.
  Qed.

  Theorem jac_opp_correct : forall (a : point),
    Jacobian.eq (add a (opp a)) zero_point.

    intros.
    apply jac_eq_from_affine.
    rewrite to_affine_add.
    rewrite to_affine_zero.
    rewrite to_affine_opp.
    apply right_inverse.
  Qed.

  Theorem w_add_same_r : forall (z x y : wpoint),
    WeierstrassCurve.W.eq x y ->
    WeierstrassCurve.W.eq (WeierstrassCurve.W.add x z) (WeierstrassCurve.W.add y z).

    intros.
    rewrite H.
    reflexivity.

  Qed.

  Theorem w_add_same_r_if : forall (z x y : wpoint),
    WeierstrassCurve.W.eq (WeierstrassCurve.W.add x z) (WeierstrassCurve.W.add y z) ->
    WeierstrassCurve.W.eq x y.

    intros.
    apply (@w_add_same_r (W_opp z)) in H.
    repeat rewrite <- associative in H.
    rewrite right_inverse in H.
    repeat rewrite right_identity in H.
    trivial.
  Qed.

  Theorem w_opp_add_distr : forall (x y : wpoint),
    WeierstrassCurve.W.eq (W_opp (WeierstrassCurve.W.add x y)) (WeierstrassCurve.W.add (W_opp x) (W_opp y)).

    intros.
    eapply (@w_add_same_r_if (WeierstrassCurve.W.add x y)).
    rewrite left_inverse.
    rewrite (commutative x).
    rewrite <- associative.
    rewrite (associative (W_opp y)).
    rewrite left_inverse.
    rewrite left_identity.
    rewrite left_inverse.
    reflexivity.
  Qed.


  Theorem jac_opp_add_distr : forall (a b : point),
   Jacobian.eq (opp (add a b)) (add (opp a) (opp b)).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_opp.
    repeat rewrite to_affine_add.
    repeat rewrite to_affine_opp.
    apply w_opp_add_distr.

  Qed.

  Theorem w_opp_involutive  : forall (x : wpoint),
    WeierstrassCurve.W.eq (W_opp (W_opp x)) x.

    intros.
    apply (@w_add_same_r_if (W_opp x)).
    rewrite left_inverse.
    rewrite right_inverse.
    reflexivity.

  Qed.

  Theorem jac_opp_involutive  : forall (a : point),
    Jacobian.eq (opp (opp a)) a.

    intros.
    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_opp.
    apply w_opp_involutive.
  Qed.

End CurveFacts.

Global Instance EC_CommutativeGroup : forall `{Curve}{Feq_dec : DecidableRel Feq}, 
  (CommutativeGroup point jac_eq_setoid).

  econstructor; intros.
  apply Jacobian.Proper_add.
  eapply jac_add_assoc.
  eapply jac_add_comm.
  apply jac_add_id_l.
  apply Proper_opp.
  apply jac_opp_correct.
Defined.

Global Instance EC_CommutativeGroupWithDouble : forall `{Curve}{Feq_dec : DecidableRel Feq},
  (CommutativeGroupWithDouble EC_CommutativeGroup).

  econstructor.
  apply Jacobian.Proper_double. 
  intros.
  apply jac_double_correct.

Defined.

