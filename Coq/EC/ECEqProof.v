(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Proof of equivalence and correctness for extracted scalar/point multiplication operation. *)

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import BinPos.
From Coq Require Import Ring.
From Coq Require Import Setoid.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import Lia.

From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.

From CryptolToCoq Require Import SAWCoreBitvectors.

From Bits Require Import operations.
From Bits Require Import operations.properties.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.

From Crypto Require Import Curves.Weierstrass.Jacobian.
From Crypto Require Import Curves.Weierstrass.Affine.
From Crypto Require Import Curves.Weierstrass.AffineProofs.


From EC Require Import Curve.
From EC Require Import GroupMulWNAF.
From EC Require Import EC_P384_5.
From EC Require Import EC_P384_Abstract.
From EC Require Import CryptolToCoq_equiv.
From EC Require Import EC_P384_Abstract_5_equiv.
From EC Require Import EC_P384_Abstract_Model_equiv.

From EC Require Import WindowedMulMachine.
From EC Require Import GeneratorMul.

Set Implicit Arguments.

Require Import CryptolToCoq.SAWCoreVectorsAsCoqVectors.

Section ECEqProof.

  Definition F := Vec 6 (Vec 64 Bool).
  Definition Feq := (@eq F).
  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).
  Definition Fone := p384_felem_one.

  Instance Feq_dec : DecidableRel Feq.

    unfold Decidable.
    intros.
    apply Vector_eq_dec.
    intros.
    apply Vector_eq_dec.
    intros.
    decide equality.
  Defined.

  Context `{curve : Curve F Feq Fzero Fone}.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

  Theorem felem_nz_eq_0 : 
    (felem_nz 0) = (intToBv 64 0).

    reflexivity.

  Qed.

  Theorem felem_nz_neq_0 : forall x,
    x <> 0 ->
    (felem_nz x) <> (intToBv 64 0).

    intuition.
    eapply H.
    eapply fold_or_impl_0; eauto.

  Qed.

  Theorem felem_nz_0 : forall x, 
    felem_nz x = intToBv 64 0 ->
    x = 0.

    intros.
    destruct (dec (Feq x 0)).
    eapply f.
    exfalso.
    eapply felem_nz_neq_0.
    intuition idtac.
    eapply n.
    eapply H0.
    trivial.

  Qed.
  
  Theorem felem_nz_not_0 : forall x, 
    ~(felem_nz x = intToBv 64 0) ->
    x <> 0.

    intros.
    intuition idtac.
    subst.
    eapply H.
    reflexivity.

  Qed.

  Definition point := Curve.point.

  Definition Fsquare x := Fmul x x.
  Local Opaque Fsquare.

  Definition point_add := @point_add Fadd Fsub Fmul.
  Definition point_add_jac := point_add false.

  Definition point_add_jac_prod (p1 p2 : (F * F * F)) : (F * F * F) :=
    let p3 := point_add_jac (prodToSeq p1) (prodToSeq p2) in
    (seqToProd p3).

  (* Prove that squaring satisifes its spec. *)
  Theorem felem_sqr_spec : forall (x : F), Fsquare x = Fmul x x.

    intros. reflexivity.
  Qed.

  (* Now, we can prove that the extracted Cryptol code computes the
     same point (up to strict equality) as the specialized (for a = -3)
     point-doubling procedure from fiat-crypto.
  *)
  Definition point_double := @point_double Fadd Fsub Fmul. 

  Lemma double_eq_minus_3_h : forall p:point,
      fromPoint (Curve.double_minus_3 p) =
      seqToProd (point_double (prodToSeq (fromPoint p))).

      intros [ [[x y] z] Hp ]; simpl.
      unfold prodToSeq, seqToProd, fromPoint, point_double, EC_P384_Abstract_5_equiv.point_double, EC_P384_5.point_double; simpl.      
      unfold nth_order, nth. simpl.
      unfold sawAt, atWithDefault. simpl.
      unfold EC_P384_Abstract_5_equiv.Fsquare.
      f_equal.
      nsatz.
  
  Qed.

  Theorem double_eq_minus_3 : forall p:point,
      prodToSeq (fromPoint (Curve.double_minus_3 p)) =
      (point_double (prodToSeq (fromPoint p))).

    intros.
    rewrite double_eq_minus_3_h.
    rewrite prodToSeq_inv.
    reflexivity.

  Qed.

  Theorem point_double_minus_3_jac_eq : 
    forall (p0 : Curve.point) (p' : t EC_P384_Abstract.F 3),
    jac_eq (fromPoint p0) (seqToProd p') -> jac_eq (fromPoint (double_minus_3 p0)) (seqToProd (point_double p')).

    intros.
    destruct (jac_eq_point_ex _ _ H).
    replace p' with (prodToSeq (fromPoint x)).
    rewrite <- double_eq_minus_3.
    rewrite seqToProd_inv.
    eapply jacobian_eq_jac_eq.
    apply Proper_double_minus_3.
    eapply jac_eq_jacobian_eq.
    congruence.
    rewrite <- H0.
    apply prodToSeq_inv.

  Qed.

  Lemma point_add_jac_eq_h : forall (a b:point),
      jac_eq (fromPoint (Curve.add a b))
      (seqToProd (point_add_jac (prodToSeq (fromPoint a)) (prodToSeq (fromPoint b)))).

      intros [ [[xa ya] za] Ha ] [ [[xb yb] zb] Hb ]; simpl.
    
      unfold point_add_jac, fromPoint, point_add, EC_P384_Abstract_5_equiv.point_add, EC_P384_5.point_add, ecNotEq, ecEq, ecZero, ecAnd, ecOr, ecCompl, felem_cmovznz; simpl.
      unfold EC_P384_Abstract_5_equiv.Fsquare.
      unfold sawAt, atWithDefault. simpl.
      
      match goal with
      | [|- jac_eq (if ?a then _ else _) _ ] => 
      replace a with    
        (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
         (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya)))
      end.

      case_eq (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
         (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))); intros.
      replace (xa, ya, za) with (fromPoint
       (exist (fun '(X, Y, Z) => if dec (Z = 0) then True else Y ^ 2 = X ^ 3 + a * X * (Z ^ 2) ^ 2 + b * (Z ^ 3) ^ 2)
          (xa, ya, za) Ha)).
      match goal with
      | [|- context[EC_P384_5.point_double ?a ?b ?c ?d (prodToSeq (fromPoint ?p))]] =>
        replace (EC_P384_5.point_double a b c d (prodToSeq (fromPoint p))) with (prodToSeq (fromPoint (double_minus_3 p)))
      end.
      rewrite seqToProd_inv.
      eapply jac_eq_trans; [idtac | apply jacobian_eq_jac_eq; apply Curve.double_minus_3_eq_double].
      apply jac_eq_refl_abstract.
   
      unfold Jacobian.double, fromPoint; simpl.
      reflexivity.
      apply double_eq_minus_3.
      trivial.

      apply jac_eq_refl_abstract.
      unfold Feq, seqToProd, nth_order, nth. simpl.
      destruct (dec (zb = 0)); subst.
      rewrite felem_nz_eq_0.
      rewrite ecEq_bv_true.
      trivial.
      destruct (dec (za = 0)); subst.
      rewrite felem_nz_eq_0.
      rewrite ecEq_bv_true.
      rewrite ecEq_bv_false.
      trivial.
      eapply felem_nz_neq_0.
      trivial.
      repeat rewrite ecEq_bv_false; simpl.
      reflexivity.
      eapply felem_nz_neq_0. trivial.
      eapply felem_nz_neq_0. trivial.

      unfold testForDouble.
      destruct (dec (Feq (xb * za ^ 2 - xa * zb ^ 2) 0)).
      simpl.
      rewrite f.
      rewrite <- rep_false_eq_int_bv.
      
      rewrite ecEq_vec_bv_true.
      unfold ecAnd. simpl.
      destruct (dec (Feq (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya)) 0)).
      rewrite f0.
      rewrite ecEq_vec_bv_true.
      simpl.
      destruct (dec (Feq za 0)).
      rewrite f1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      simpl.
      destruct (dec (Feq zb 0)).
      rewrite f1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      rewrite ecEq_vec_bv_false; intuition.

      simpl.
      rewrite ecEq_vec_bv_false; intuition.

  Qed.

  Definition point_add_mixed := point_add true.

  Definition isAffine (p : point) :=
    (snd (proj1_sig p) = Fone).

  Lemma point_add_mixed_eq_h : forall (a b:point),
      isAffine b -> 
      jac_eq (fromPoint (Curve.add a b))
      (seqToProd (point_add_mixed (prodToSeq (fromPoint a)) (prodToSeq (fromPoint b)))).

    intros [ [[xa ya] za] Ha ] [ [[xb yb] zb] Hb ]; intros; simpl.
    unfold point_add_mixed, fromPoint, point_add, EC_P384_Abstract_5_equiv.point_add, EC_P384_5.point_add, ecNotEq, ecEq, ecZero, ecAnd, ecOr, ecCompl, felem_cmovznz; simpl.
      repeat rewrite felem_sqr_spec.
      unfold sawAt, atWithDefault. simpl.
    
      replace ((negb (if dec (xb * za ^ 2 - xa * zb ^ 2 = Fzero) then 0 else 1) &&
     negb (if dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = Fzero) then 0 else 1) &&
     (if dec (za = Fzero) then 0 else 1) && (if dec (zb = Fzero) then 0 else 1))%bool) with 
      (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
    (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))).
      unfold isAffine in *.
      simpl in *.
      subst zb.
      replace (xb * za ^ 2 - xa * 1 ^ 2) with (xb * za ^ 2 - xa); try nsatz.
      replace (yb * (za * za ^ 2) - 1 * 1 ^ 2 * ya + (yb * (za * za ^ 2) - 1 * 1 ^ 2 * ya)) with
        (yb * (za * za ^ 2) - ya + (yb * (za * za ^ 2) - ya)); try nsatz.
      case_eq (testForDouble za 1 (xb * za ^ 2 - xa) (yb * (za * za ^ 2) - ya + (yb * (za * za ^ 2) - ya))); intros.

      replace (xa, ya, za) with (fromPoint
       (exist (fun '(X, Y, Z) => if dec (Z = 0) then True else Y ^ 2 = X ^ 3 + a * X * (Z ^ 2) ^ 2 + b * (Z ^ 3) ^ 2)
          (xa, ya, za) Ha)).
      rewrite <- double_eq_minus_3.
      rewrite seqToProd_inv.

      eapply jac_eq_trans; [idtac | apply jacobian_eq_jac_eq; apply Curve.double_minus_3_eq_double].
      apply jac_eq_refl_abstract.
   
      unfold Jacobian.double, fromPoint; simpl.
      reflexivity.
      trivial.

      apply jac_eq_refl_abstract.
      destruct (dec (Feq 1 0)).
      exfalso.
      eapply Fone_ne_Fzero.
      eauto.
      rewrite ecEq_bv_false.
      destruct (dec (Feq za 0)).
      unfold Feq in *.
      rewrite f.
      rewrite felem_nz_eq_0.
      unfold ecZero.
      rewrite ecEq_bv_true. 
      reflexivity.
      rewrite ecEq_bv_false.  
      unfold seqToProd, nth_order.
      simpl.
      repeat rewrite left_identity.
      rewrite right_identity.
      f_equal.
      nsatz.
      eapply felem_nz_neq_0.
      intuition idtac.
      eapply felem_nz_neq_0.
      intuition idtac.

      unfold testForDouble.
      destruct (dec (xb * za ^ 2 - xa * zb ^ 2 = 0)).
      simpl.
      rewrite e.
      rewrite <- rep_false_eq_int_bv.
      
      rewrite ecEq_vec_bv_true.
      unfold ecAnd. simpl.
      destruct (dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = 0)).
      rewrite e0.
      rewrite ecEq_vec_bv_true.
      simpl.
      destruct (dec (za = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      simpl.
      destruct (dec (zb = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      rewrite ecEq_vec_bv_false; intuition.

      simpl.
      rewrite ecEq_vec_bv_false; intuition.
  Qed.
 
  (* A more general form the point add/double correctness using Jacobian equality *)
  Lemma point_add_jac_eq : forall (a b:point) a' b',
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Curve.add a b)) (seqToProd (point_add_jac a' b')).

    intros.  
    edestruct (jac_eq_point_ex _ _ H).
    edestruct (jac_eq_point_ex _ _ H0).
    
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    eapply jac_eq_jacobian_eq.
    rewrite H1 in H.
    eauto.
    eapply jac_eq_jacobian_eq.
    rewrite H2 in H0.
    eauto.
    eapply jac_eq_trans.
    eapply point_add_jac_eq_h.
    rewrite <- H1.
    rewrite <- H2.
    repeat rewrite prodToSeq_inv.
    apply jac_eq_refl.
 
  Qed.

  Lemma point_add_mixed_eq : forall (a b:point) a' b',
    nth_order b' two_lt_three = Fone -> 
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Curve.add a b)) (seqToProd (point_add_mixed a' b')).

    intros.  
    edestruct (jac_eq_point_ex _ _ H0).
    edestruct (jac_eq_point_ex _ _ H1).
    
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    eapply jac_eq_jacobian_eq.
    rewrite H2 in H0.
    eauto.
    eapply jac_eq_jacobian_eq.
    rewrite H3 in H1.
    eauto.
    eapply jac_eq_trans.
    eapply point_add_mixed_eq_h.
    unfold isAffine in *.
    destruct x0.
    simpl in *.
    subst.
    destruct (Vec_S_cons _ _ b'). destruct H3.
    destruct (Vec_S_cons _ _ x1). destruct H4.
    destruct (Vec_S_cons _ _ x3). destruct H5.
    subst.
    rewrite (Vec_0_nil _ x5).
    simpl.
    eauto.
    
    rewrite <- H2.
    rewrite <- H3.
    repeat rewrite prodToSeq_inv.
    apply jac_eq_refl.
 
  Qed.

  Lemma point_double_eq : forall (a:point) a',
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint (Curve.double a)) (seqToProd (point_double a')).

    intros.
    rewrite <- (prodToSeq_inv a').
    edestruct (jac_eq_point_ex _ _ H).

    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_double.
    eapply jac_eq_jacobian_eq.
    rewrite <- H0.
    eapply H.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    apply double_minus_3_eq_double.
    rewrite double_eq_minus_3_h.
    rewrite <- H0.
    apply jac_eq_refl.

  Qed.

  Definition seqToList(A : Type)(n : nat)(s : seq n A) : list A :=
    to_list s.

  Fixpoint preCompTable_fix (p : point) n prev :=
    match n with
    | O => prev :: List.nil
    | S n' => prev :: (preCompTable_fix p n'(Jacobian.add (Jacobian.double p) prev))
    end.

  Theorem seqTolist_cons : forall (A : Type)(n : nat) (x : A) (s : Vector.t A n),
    seqToList (cons _ x _ s) = List.cons x (seqToList s).

    intros.
    unfold seqToList, to_list. simpl.
    reflexivity.

  Qed.

  Local Opaque Jacobian.double Jacobian.add EC_P384_5.point_double EC_P384_5.point_add.

  Local Opaque sbvToInt.


  Definition conditional_subtract_if_even := @conditional_subtract_if_even Fadd Fsub Fmul Fopp.
  Definition point_opp_abstract := (@point_opp_abstract Fopp).

  Theorem conditional_subtract_if_even_jac_eq_ite : forall n p1 p2,
    jac_eq (seqToProd (conditional_subtract_if_even p1 n p2)) (seqToProd (if (Nat.even (bvToNat _ n)) then (point_add false p1 (point_opp_abstract p2)) else p1)).
  
    intros.
    unfold conditional_subtract_if_even.
    rewrite conditional_subtract_if_even_equiv.
    eapply jac_eq_refl.
  Qed.

  Theorem felem_cmovznz_equiv : forall x y z,
    felem_cmovznz x y z = if (bvEq _ x (intToBv 64 0)) then y else z.

    intros.
    reflexivity.

  Qed.

  Theorem bvXor_bvEq : forall n y w,
    bvEq n (bvXor _ y w) (intToBv _ 0)  = bvEq _ y w.
  
    induction n; intros; simpl in *.
    reflexivity.
    destruct (@Vec_S_cons _ _  y). destruct H.
    destruct (@Vec_S_cons _ _ w). destruct H0. 
    subst.
    rewrite bvXor_cons.
    rewrite intToBv_0_S.
    repeat rewrite bvEq_cons.
    destruct x; destruct x1; simpl; trivial.

  Qed.

  Theorem select_point_loop_body_equiv : forall w x y z,
    select_point_loop_body w x y z = 
       if (bvEq _ y w) then z else x.

    intros. 
    unfold select_point_loop_body.
    simpl.
    unfold ecXor.
    simpl.
    repeat rewrite felem_cmovznz_equiv.
    case_eq (bvEq 64 (bvXor 64 y w) (intToBv 64 0)); intros;
    rewrite sawAt_3_equiv;
    case_eq (bvEq _ y w); intros; 
    trivial;
    rewrite bvXor_bvEq in H; 
    congruence.

  Qed.


  Theorem sawAt_2_equiv : forall A (inh : Inhabited A) (v : Vector.t A 2),
  Vector.cons _ (sawAt 2%nat A v 0%nat) _
    (Vector.cons _ (sawAt 2%nat A v 1%nat) _ (Vector.nil A))
    = v.

    intros.
    destruct (Vec_S_cons _ _ v). destruct H. subst.
    destruct (Vec_S_cons _ _ x0). destruct H. subst.
    repeat rewrite sawAt_nth_equiv; try lia.
    repeat rewrite to_list_cons.
    simpl.
    specialize (Vec_0_nil _ x2); intros; subst.
    reflexivity.

  Qed.

  Theorem select_point_affine_loop_body_equiv : forall w x y z,
    select_point_affine_loop_body w x y z = 
       if (bvEq _ y w) then z else x.

    intros. 
    unfold select_point_affine_loop_body.
    simpl.
    unfold ecXor.
    simpl.
    repeat rewrite felem_cmovznz_equiv.
    case_eq (bvEq 64 (bvXor 64 y w) (intToBv 64 0)); intros;
    rewrite sawAt_2_equiv;
    case_eq (bvEq _ y w); intros; 
    trivial;
    rewrite bvXor_bvEq in H; 
    congruence.

  Qed.

  Local Opaque shiftR.

  Definition conditional_point_opp_abstract := @conditional_point_opp_abstract Fopp.
       
  Theorem sbvToInt_sign_extend_16_64_equiv : forall x,
    sbvToInt _ (sign_extend_16_64 x) = sbvToInt _ x.

    intros.
    unfold sign_extend_16_64.
    simpl.
    apply (@sbvToInt_sign_extend_equiv 16 48).
    lia.

  Qed.

  Definition point_mul_abstract := @point_mul_abstract Fopp point_double point_add sign_extend_16_64 felem_cmovznz select_point_loop_body conditional_subtract_if_even.
(*
  Section PointMulAbstract.
  Variable wsize : nat.
  Hypothesis wsize_range : (1 < wsize < 16)%nat.
  Variable nw : nat.
  Hypothesis nw_range : nw <> 0%nat.

  Definition point_mul_base := @point_mul_base Fadd Fsub Fmul Fopp.
  Definition base_precomp_table : list (list affine_point) := List.map to_list (to_list p384_g_pre_comp).
  Local Opaque p384_g_pre_comp.
  Hypothesis base_precomp_table_length : List.length base_precomp_table = (wsize * (Nat.pred wsize))%nat.
  Definition numPrecompExponentGroups : nat := (Nat.pred wsize).
  Definition precompTableSize : nat := List.length base_precomp_table.
  Hypothesis base_precomp_table_entry_length : 
    forall ls, List.In ls base_precomp_table -> List.length ls = Nat.pow 2 numPrecompExponentGroups.
  Definition affine_g := 
    List.nth 0 (List.nth 0 base_precomp_table (inhabitant (list affine_point))) (inhabitant affine_point).
  (* We need a default point for some lookup operations. It simplifies the proof a bit if this point is on the curve. *)
  Definition affine_default : affine_point := affine_g.

  Variable g : point. 
  Definition affineToJac := @affineToJac p384_felem_one.
  Hypothesis g_affine_jac_equiv :   
    jac_eq (seqToProd (affineToJac affine_g)) (fromPoint g).
*)

(*
  (* Assume the base point table passes validation, and then prove that it is correct.*)
  Definition validate_base_table_abstract := @validate_base_table_abstract Fadd Fsub Fmul.
  Hypothesis base_precomp_table_validated : validate_base_table_abstract wsize base_precomp_table = true.

  Definition jacobian_affine_eq_abstract :=  @jacobian_affine_eq_abstract Fsub Fmul.
  Definition validateGeneratorTable := validateGeneratorTable g (fun p => jacobian_affine_eq_abstract (prodToSeq (fromPoint p))) affine_default.
*)

(*
  Definition jacobian_affine_eq_abstract := @jacobian_affine_eq_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ felem_nz.
  Definition jacobian_affine_eq_point (p : point) :=
    jacobian_affine_eq_abstract (prodToSeq (fromPoint p)).

  Theorem jacobian_affine_eq_point_correct : 
  forall (p : point) (t : affine_point),
    Feq p384_felem_one 1 ->
    jacobian_affine_eq_point p t = 1%bool <-> jac_eq (seqToProd (affineToJac t)) (fromPoint p).

    intros.
    eapply jacobian_affine_eq_abstract_correct; eauto.
    apply felem_nz_0.
    apply felem_nz_not_0.
    apply felem_nz_neq_0.

  Qed.
 

  Theorem base_precomp_table_correct  : forall n1 n2,
    Feq p384_felem_one 1 -> 
    (n1 < precompTableSize)%nat ->
    (n2 < Nat.pow 2 numPrecompExponentGroups)%nat-> 
    jac_eq (seqToProd (affineToJac (List.nth n2 (List.nth n1 base_precomp_table List.nil) affine_default))) (fromPoint (groupMul ((2 * n2 + 1) * (Nat.pow 2 (n1 * numPrecompExponentGroups * wsize))) g)).
 
    intros.
    eapply validateGeneratorTable_correct.
    lia.
    intros.
    eapply jacobian_affine_eq_point_correct.
    trivial.
    intros.
    eapply jac_eq_trans; eauto.
    rewrite validate_base_table_abstract_model_equiv in base_precomp_table_validated.
    eapply base_precomp_table_validated.
    unfold validate_base_table_abstract, EC_P384_Abstract.validate_base_table_abstract in *.
    trivial.

    eauto.
    unfold numPrecompExponentGroups.
    rewrite NPeano.Nat.mul_comm.
    rewrite base_precomp_table_length.
    destruct wsize; simpl in *; reflexivity.

    apply base_precomp_table_entry_length.

  Qed.
*)


(*
  Hypothesis p384_felem_one_correct : Feq p384_felem_one 1.
*)

 (*
  
  Theorem affineToJac_cons_eq : forall z,
      affineToJac z =
      cons (seq 6 (seq 64 bool)) (nth_order z zero_lt_two) 2
        (cons (seq 6 (seq 64 bool)) (nth_order z one_lt_two) 1
           (cons (seq 6 (seq 64 bool)) 1 0 (nil (seq 6 (seq 64 bool))))).

    intros.
    unfold affineToJac. 
    destruct (Vec_S_cons _ _ z). destruct H.
    destruct (Vec_S_cons _ _ x0). destruct H0.
    subst.
    rewrite (Vec_0_nil _ x2).
    unfold nth_order.
    simpl.
    
    rewrite p384_felem_one_correct.
    reflexivity.

  Qed.
*)

(*
  Definition add_base_abstract := @add_base_abstract Fadd Fsub Fmul Fopp 1.
*)


  (*

  Local Opaque jac_eq.

  Definition groupedMul_scalar_precomp := @groupedMul_scalar_precomp Fone Fadd Fsub Fmul Fdiv Fopp Finv _  a b _ 
    5 wsize_range nw nw_range base_precomp_table base_precomp_table_length base_precomp_table_entry_length g base_precomp_table_correct.

  Theorem groupedMul_scalar_precomp_Some_P384_concrete : forall n, exists x, 
    groupedMul_scalar_precomp 4 5 77 1 n = Some x.

    intros.
    unfold groupedMul_scalar_precomp.
    unfold groupedMul_precomp.

    assert  (exists x, permuteAndDouble_grouped (recode_rwnaf 5 77 (Z.of_nat n)) 1 (groupIndices 77 4) = Some x /\
        List.Forall (List.Forall (wmIsMultiple 4)) x).
    eapply permuteAndDouble_grouped_Some.
    apply groupIndices_all_lt.
    rewrite groupIndices_length. reflexivity.
    reflexivity.
    repeat econstructor.

    destruct H.
    destruct H.
    erewrite permuteAndDouble_grouped_equiv; eauto.
    edestruct (groupMul_signedWindows_precomp_Some).
    eapply Forall_flatten.
    intros.
    eapply (@List.Forall_forall _ _ x).
    trivial.
    eauto.
    
    unfold idElem.
    simpl.
    rewrite H1.
    destruct (Nat.even n); econstructor; eauto.

  Qed.

  End PointMulAbstract.
*)


   (**
  The point multiplication spec extracted from Cryptol is equivalent to the basic group
  multiplication operation on points. 
  *)
  Definition point_mul := @point_mul Fadd Fsub Fmul Fopp.
  Theorem point_mul_correct : forall (p : point) (n : seq 384 Bool),
      jac_eq (fromPoint (groupMul (bvToNat _ n) p))
      (seqToProd (point_mul (prodToSeq (fromPoint p)) n)).

    intros.
    unfold point_mul.
    rewrite point_mul_abstract_equiv.
    unfold EC_P384_Abstract_5_equiv.point_mul_abstract.
    eapply jac_eq_trans.
    apply point_mul_abstract_correct.
    apply sign_extend_16_64.
    apply felem_cmovznz_equiv.
    apply select_point_loop_body_equiv.
    apply point_add_jac_eq.
    apply point_double_minus_3_jac_eq.
    apply sbvToInt_sign_extend_16_64_equiv.   
    apply conditional_subtract_if_even_jac_eq_ite.
    assert (1 < 5 < 16)%nat by lia.
    eauto.
    assert (74 <> 0)%nat by lia.
    eauto.
    lia.
    eapply jac_eq_refl.

  Qed.
    
  (**
  The base point multiplication spec extracted from Cryptol is equivalent to the basic group
  multiplication operation on the base point. 
  *)

  Definition validate_base_table := @validate_base_table Fadd Fsub Fmul.
  (* Assume that the hard-coded table containing multiples of the base point has been validated.
  This validation can occur during testing using a C program that is verified against this functional spec. *)
  Hypothesis validate_base_table_true : validate_base_table p384_g_pre_comp = true.

  Definition preCompTable := (List.map (fun x => to_list x) (to_list p384_g_pre_comp)).

  Definition validate_base_table_abstract := @validate_base_table_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ 
    point_double point_add felem_nz.
  Theorem validate_preCompTable_true : validate_base_table_abstract 5 preCompTable = true.

    match goal with
    | [H : ?a = true |- ?b = true] => rewrite <- H
    end.
    symmetry.

    apply validate_base_table_equiv.

  Qed.

  Section PointMulBase.

  Theorem preCompTable_entry_length : forall ls,
    List.In ls preCompTable ->
    Datatypes.length ls = Nat.pow 2 (Nat.pred 5).

    intros.
    unfold preCompTable in *.
    erewrite to_list_entry_length; eauto.

  Qed.

  Theorem preCompTable_length : 
    Datatypes.length preCompTable = 20%nat.

    intros.
    reflexivity.

   Qed.

  (* Assume the multiplicative identity element of the field is equal to the hard-coded "one" value in the code. *)
  Hypothesis Fone_eq : 
    p384_felem_one = 1.
  Local Opaque p384_felem_one.
  Local Opaque felem_nz.

  (* The base point multiplication operation using a hard-coded table is equivalent to multiplication by the base point. *)

  Local Opaque groupedMul_scalar_precomp.

  Hypothesis g_point : Curve.point.
  Variable g_point_eq : jac_eq (seqToProd g) (fromPoint g_point).
  Variable g_point_affine_jac_equiv : jac_eq (seqToProd (affineToJac (affine_g base_precomp_table))) (fromPoint g_point).

  Definition point_mul_base := @point_mul_base Fadd Fsub Fmul Fopp.  
  Theorem point_mul_base_correct : forall (n : seq 384 Bool),
      jac_eq 
        (fromPoint (groupMul (bvToNat _ n) g_point))
        (seqToProd (point_mul_base n)).

    intros.
    specialize (@groupedMul_scalar_precomp_Some_P384_5 Fone Fadd Fsub Fmul Fdiv Fopp Finv _  a b _  
      point_double point_add point_add_jac_eq point_double_minus_3_jac_eq
      felem_nz felem_nz_0 felem_nz_not_0 felem_nz_eq_0 felem_nz_neq_0 base_precomp_table
      g_point g_point_affine_jac_equiv 
      preCompTable_length preCompTable_entry_length validate_preCompTable_true
      (bvToNat _ n)); intros.
    destruct H.
    unfold point_mul_base.
    assert (List.Forall2 (fun (x : list affine_point) (y : t affine_point 16) => x = to_list y) preCompTable
         (to_list p384_g_pre_comp)).
    unfold preCompTable.
    eapply Forall2_map_l.
    eapply Forall2_same_Forall.
    eapply List.Forall_impl; [idtac | eapply Forall_I].
    intros.
    trivial.

    rewrite point_mul_base_abstract_equiv.
    rewrite Fone_eq.
    specialize (@point_mul_base_abstract_correct
      Fone Fadd Fsub Fmul Fdiv Fopp Finv _  a b _  
      point_double point_add sign_extend_16_64 point_id_to_limb
      felem_cmovznz felem_cmovznz_equiv
      point_add_jac_eq point_add_mixed_eq
      point_double_minus_3_jac_eq
      sbvToInt_sign_extend_16_64_equiv
      felem_nz felem_nz_0 felem_nz_not_0 felem_nz_eq_0 felem_nz_neq_0 base_precomp_table
      g_point g_point_affine_jac_equiv 
      wsize wsize_range nw nw_range
      preCompTable_length preCompTable_entry_length validate_preCompTable_true
      select_point_affine_loop_body
      select_point_affine_loop_body_equiv
    ); intros.
    eapply H1.
    eapply Z.lt_le_trans.
    eapply bvToInt_bound.
    apply Z.pow_le_mono_r.
    lia.
    simpl.
    lia.

    unfold numPrecompExponentGroups, wsize, nw.
    match goal with 
    | [ |- (_ < _ * ?a)%nat] => replace a with 20%nat
    end.
    simpl; lia.
    lia.
    apply H.

  Qed.

  End PointMulBase.


End ECEqProof.



