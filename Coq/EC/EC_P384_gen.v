
(* Generalized low-level specification for NIST prime curve arithmetic. These functions
are equivalent to the functions extracted from Crypto, and the folloing changes are made:
* Operations using Cryptol sequences are replaced with equivalent operations on vectors. 
* Vectors are replaced with lists in situations where a list is more natural (e.g. folding 
  over a list).
* Definitions are abstracted over window size, number of windows, word size, number of bits 
    used to represent the field, etc. 
*)

Set Implicit Arguments.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import Vectors.VectorSpec.
From Coq Require Import Lia.


From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import Everything.


From EC Require Import CryptolToCoq_equiv.
From EC Require Import EC_P384_5.


Definition append_comm (m n : Nat) (a : Type) (Inh_a : Inhabited a) 
  (x : Vec m a) (y : Vec n a) :=
gen (addNat n m) a
  (fun i : Nat =>
   if ltNat i m then sawAt m a x i else sawAt n a y (subNat i m)).


Local Arguments cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments append_comm [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.


Definition mul_scalar_rwnaf_odd_loop_body_gen (wsize : nat)(s : bitvector 384) :=
(drop Bool 368 16
   (bvSub
      (bvURem 384 s
         (bvMul 384 (bvNat 384 2)
            (shiftL 384 bool false (bvNat 384 1) wsize)))
      (shiftL 384 bool false (bvNat 384 1) wsize)),
shiftR 384 bool false
  (bvSub s
     (bvSub
        (bvURem 384 s
           (bvMul 384 (bvNat 384 2)
              (shiftL 384 bool false (bvNat 384 1) wsize)))
        (shiftL 384 bool false (bvNat 384 1) wsize))) wsize).

Theorem mul_scalar_rwnaf_odd_loop_body_gen_equiv : forall s,
  mul_scalar_rwnaf_odd_loop_body_gen 5 s = mul_scalar_rwnaf_odd_loop_body s.

  intros.
  unfold mul_scalar_rwnaf_odd_loop_body, mul_scalar_rwnaf_odd_loop_body_gen.
  removeCoerce.
  simpl.
  reflexivity.

Qed.

From EC Require Import GroupMulWNAF.
From EC Require Import CryptolToCoq_equiv.
Require Import ZArith.BinInt.
Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.

Definition mul_scalar_rwnaf_odd_gen wsize numWindows s :=
  List.map (fun x : bitvector 16 * bitvector 384 => fst x)
  (scanl
     (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
      mul_scalar_rwnaf_odd_loop_body_gen wsize (snd __p2)) (toN_int numWindows)
     (mul_scalar_rwnaf_odd_loop_body_gen wsize s)) ++
[drop Bool 368%nat 16%nat
   (snd
      (hd (inhabitant (Inhabited_prod (bitvector 16) (bitvector 384)))
         (rev
            (scanl
               (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
                mul_scalar_rwnaf_odd_loop_body_gen wsize (snd __p2)) 
               (toN_int numWindows) (mul_scalar_rwnaf_odd_loop_body_gen wsize s)))))].


Local Open Scope Z_scope.

Definition recode_rwnaf_odd_scanl_fix_body wsize n :=
      let k_i := (n mod (Z.double (twoToWsize wsize))) - (twoToWsize wsize) in
      let n' := (n - k_i) / (twoToWsize wsize) in
      (k_i, n').

Theorem recode_rwnaf_odd_scanl_equiv : forall wsize nw (n : Z),
  recode_rwnaf_odd wsize (S nw) n = 
  scanl_fix 
    (fun p => recode_rwnaf_odd_scanl_fix_body wsize (snd p))
    (fun p => fst p)
    (fun p => snd p)
    (S nw) (recode_rwnaf_odd_scanl_fix_body wsize n).

  induction nw; intros; simpl in *.
  reflexivity.
  rewrite IHnw.
  reflexivity.
Qed.

Require Import Coq.ZArith.Zdigits.

Theorem mul_scalar_rwnaf_odd_gen_equiv : forall s,
  to_list (mul_scalar_rwnaf_odd s) = (mul_scalar_rwnaf_odd_gen 5 74 s).

  intros.
  unfold mul_scalar_rwnaf_odd.
  repeat removeCoerce.

  Local Opaque append of_list ecFromTo.
  simpl.

  match goal with
  | [|- context[to_list (append ?v1 ?v2 )]] =>
    replace (to_list (append v1 v2 )) with (List.app (to_list v1) (to_list v2)); [idtac | symmetry; apply toList_append_equiv]
  end.

  rewrite toList_map_equiv.
  match goal with
  | [|- context[to_list (SAWCoreVectorsAsCoqVectors.scanl ?t1 ?t2 ?n ?f ?a ?v)]] =>
    replace (to_list (SAWCoreVectorsAsCoqVectors.scanl t1 t2 n f a v)) with (scanl f (to_list v) a); [idtac | symmetry; apply toList_scanl_equiv]
  end.

  rewrite to_list_of_list_opp.
  rewrite ecFromTo_0_n_equiv.
  rewrite sawAt_nth_equiv.
  rewrite toList_reverse_equiv.
  rewrite nth_0_hd_equiv.
  match goal with
  | [|- context[to_list (SAWCoreVectorsAsCoqVectors.scanl ?t1 ?t2 ?n ?f ?a ?v)]] =>
    replace (to_list (SAWCoreVectorsAsCoqVectors.scanl t1 t2 n f a v)) with (scanl f (to_list v) a); [idtac | symmetry; apply toList_scanl_equiv]
  end.

  rewrite <- mul_scalar_rwnaf_odd_loop_body_gen_equiv.
  rewrite (scanl_ext _ (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
      mul_scalar_rwnaf_odd_loop_body_gen 5 (snd __p2))).

  rewrite ecFromTo_0_n_equiv.
  reflexivity.

  intros.
  symmetry.
  apply mul_scalar_rwnaf_odd_loop_body_gen_equiv.

  lia.

Qed.

Definition mul_scalar_rwnaf_gen wsize nw s := 
  mul_scalar_rwnaf_odd_gen wsize nw
    (bvOr s (intToBv 384%nat 1)).

Theorem mul_scalar_rwnaf_equiv : forall s,
  to_list (mul_scalar_rwnaf s) = mul_scalar_rwnaf_gen 5 74 s.

  intros.
  unfold mul_scalar_rwnaf.
  rewrite mul_scalar_rwnaf_odd_gen_equiv.
  Local Opaque mul_scalar_rwnaf_odd_gen.
  simpl.
  reflexivity.

Qed.

Definition select_point_ct_gen x t :=
  fold_left
  (fun acc p =>
   select_point_loop_body x acc (fst p) (snd p))
  (combine (toN_excl_bv 64%nat (length t)) t) (of_list [zero_felem; zero_felem; zero_felem]).

Theorem to_list_length : forall (A : Type)(n : nat)(x : Vector.t A n),
  (List.length (to_list x)) = n.

  induction x; intros. 
  simpl in *; trivial.
  rewrite to_list_cons.
  simpl.
  rewrite IHx.
  trivial.

Qed.


Theorem select_point_ct_gen_equiv : forall x t,
  select_point_ct x t = select_point_ct_gen x (to_list t).

  intros.
  unfold select_point_ct, select_point_ct_gen.
  removeCoerce.
  rewrite ecFoldl_foldl_equiv.
  rewrite toList_zip_equiv. 

  replace ((to_list
        (ecFromTo 0%nat 15%nat (CryptolPrimitivesForSAWCore.seq 64%nat Bool)
           (PLiteralSeqBool 64%nat))))
  with (toN_excl_bv 64%nat (length (to_list t))).
  reflexivity.
  rewrite to_list_length.
  symmetry.
  apply (@ecFromTo_0_n_bv_excl_equiv 64%nat 15%nat).
Qed.

Require Import Coq.Logic.EqdepFacts.

Section PointMul.

  Definition felem := Vector.t (bitvector 64) 6.
  Definition prodPoint := (felem * felem * felem)%type.
  Definition point := Vector.t felem 3.
  Variable felem_sqr : felem -> felem.
  Variable felem_mul felem_sub felem_add : felem -> felem -> felem.
  Variable field_opp : felem -> felem.

  Definition point_opp (p : point) : point :=
    Vector.cons (sawAt _ _ p 0%nat) 
      (Vector.cons (field_opp (sawAt _ _ p 1%nat) ) 
        (Vector.cons (sawAt _ _ p 2%nat)  (Vector.nil felem))).

  Definition point_mul := point_mul felem_sqr felem_mul felem_sub felem_add field_opp.
 
  Definition conditional_subtract_if_even_ct := 
    conditional_subtract_if_even_ct felem_sqr felem_mul felem_sub felem_add field_opp.

  Definition point_add := 
    point_add felem_sqr felem_mul felem_sub felem_add.

  Theorem conditional_subtract_if_even_ct_equiv : forall (p1 : point) n (p2 : point),
    conditional_subtract_if_even_ct p1 n p2 = 
    if (even (bvToNat _ n)) then (point_add false p1 (point_opp p2)) else p1.

    intros.
    unfold conditional_subtract_if_even_ct, EC_P384_5.conditional_subtract_if_even_ct.
    unfold felem_cmovznz.
    match goal with
    | [|- context[of_list [if ?a then _ else _; _; _]]] =>
      case_eq a; intros
    end.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    case_eq (even (bvToNat 384%nat n)); intros.
    (* both even *)
    simpl.
    Local Transparent of_list.
    unfold of_list.
    apply sawAt_3_equiv.

    (* contradiction *)
    assert (pred 384 < 384)%nat by lia.
    erewrite (lsb_0_even _ H1) in H0.
    discriminate.
    eapply bvEq_nth_order in H.
    erewrite (@nth_order_append_eq _ _ 8%nat _ 56%nat) in H.
    erewrite nth_order_bvAnd_eq in H.
    erewrite nth_order_drop_eq in H.
    rewrite H.
    apply nth_order_0.
 
    case_eq (even (bvToNat 384%nat n)); intros.
    (* contradiction *)
    simpl in *.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    assert (pred 384 < 384)%nat by lia.
    erewrite (lsb_1_not_even _ H1) in H0.
    discriminate.
    apply bvEq_false_ne in H.
    destruct H.
    destruct H.
    rewrite nth_order_0 in H.
    destruct (lt_dec x 56).
    erewrite (@nth_order_append_l_eq _ _ 8%nat _ 56%nat) in H.
    rewrite nth_order_0 in H.
    intuition idtac.
    assert (exists x', x = addNat x' 56)%nat.
    exists (x - 56)%nat.
    rewrite <- addNat_equiv.
    lia.
    destruct H2.
    subst.

    assert (x1 < 8)%nat.
    clear H.
    rewrite <- addNat_equiv in x0.
    lia.
    erewrite (@nth_order_append_eq _ _ 8%nat _ 56%nat _ _ _ H2) in H. 
    destruct (lt_dec x1 7)%nat. 
    erewrite nth_order_bvAnd_l_eq in H.
    intuition idtac.
    trivial.
    assert (x1 = (pred 8))%nat.
    rewrite <- addNat_equiv in x0.
    lia.
    subst.
    erewrite nth_order_bvAnd_eq in H.
    erewrite nth_order_drop_eq in H.
    apply ne_false_impl_true.
    eauto.

    (* both odd. *)
    unfold of_list.
    apply sawAt_3_equiv.

    Unshelve.
    rewrite <- addNat_equiv.
    lia.
    lia.
    trivial.

  Qed.

  Definition pre_comp_table := pre_comp_table felem_sqr felem_mul felem_sub felem_add .

  Definition pre_comp_table_gen pred_tsize p :=
    scanl
  (fun
     (z : CryptolPrimitivesForSAWCore.seq 3%nat
            (CryptolPrimitivesForSAWCore.seq 6%nat
               (CryptolPrimitivesForSAWCore.seq 64%nat Bool))) 
     (_ : Integer) =>
   EC_P384_5.point_add felem_sqr felem_mul felem_sub felem_add
     (ecNumber 0%nat Bool PLiteralBit)
     (point_double felem_sqr felem_mul felem_sub felem_add p) z)
  (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int pred_tsize)) p .

  Theorem pre_comp_table_gen_equiv : forall p,
    to_list (pre_comp_table p) = pre_comp_table_gen 14%nat p.

    intros. 
    unfold pre_comp_table_gen, pre_comp_table, EC_P384_5.pre_comp_table.
    removeCoerce.
    removeCoerce.
    rewrite toList_scanl_equiv.
    replace (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int 14))
      with (to_list (ecFromTo (TCNum 1%nat) (TCNum 15%nat) Integer PLiteralInteger)).
    reflexivity.
    apply ecFromTo_m_n_equiv.
  Qed.

  
  Definition double_add_body := 
    double_add_body felem_sqr felem_mul felem_sub felem_add field_opp.
  

  Definition conditional_point_opp (t : bitvector 64) (p : point): point :=
    Vector.cons (sawAt _ _ p 0%nat) (Vector.cons (felem_cmovznz t (sawAt _ _ p 1%nat) (field_opp (sawAt _ _ p 1%nat))) (Vector.cons (sawAt _ _ p 2%nat) (Vector.nil _))).

  Definition double_add_body_gen pred_wsize t p id :=
    EC_P384_5.point_add felem_sqr felem_mul felem_sub
  felem_add false
  (fold_left
     (fun
        (x : CryptolPrimitivesForSAWCore.seq 3%nat
               (CryptolPrimitivesForSAWCore.seq 6%nat
                  (CryptolPrimitivesForSAWCore.seq 64%nat Bool)))
        (_ : Integer) =>
      point_double felem_sqr felem_mul felem_sub felem_add x)
     (toN_int pred_wsize) p)
  (conditional_point_opp
     (point_id_to_limb
        (shiftR 16 bool false id 15))
     (select_point_ct_gen
        (sign_extend_16_64
           (bvSShr 15%nat
              (bvAdd 16
                  (shiftR 16 bool false id 15)


                 (bvXor 16%nat id
                      (bvSShr 15%nat id 15)
)) 1%nat)) t)).

  Theorem double_add_body_gen_equiv : forall t p id,
    double_add_body t p id = double_add_body_gen 4 (to_list t) p id.

    intros.
    unfold double_add_body, EC_P384_5.double_add_body.
    removeCoerce.
    rewrite ecFoldl_foldl_equiv.

    replace (to_list (ecFromTo 0%nat 4%nat Integer PLiteralInteger))
      with (toN_int 4%nat).
    repeat rewrite select_point_ct_gen_equiv.
    reflexivity.

    symmetry.
    apply ecFromTo_0_n_equiv.

  Qed.

  Definition point_mul_gen wsize nw pred_tsize p s : point := 
    EC_P384_5.conditional_subtract_if_even_ct felem_sqr felem_mul
  felem_sub felem_add field_opp
  (fold_left
     (double_add_body_gen (pred wsize) (pre_comp_table_gen pred_tsize p))
     (skipn 1 (rev (mul_scalar_rwnaf_gen wsize nw s)))
     (select_point_ct_gen
        (sign_extend_16_64
           (bvSShr 15
              (nth (S (S nw)) (mul_scalar_rwnaf_gen wsize nw s)
                 (bvNat 16%nat 0%nat))
              1%nat) )
        (pre_comp_table_gen pred_tsize p))) s
  (nth 0 (pre_comp_table_gen pred_tsize p)
     (inhabitant (ecNumber 0%nat Integer PLiteralInteger))).

  Theorem point_mul_gen_equiv : forall p s,
    point_mul p s = point_mul_gen 5 74 14 p s.

    intros.
    unfold point_mul, EC_P384_5.point_mul.

    rewrite ecFoldl_foldl_equiv.

    Local Opaque fold_left.
    simpl.
    rewrite (fold_left_ext _
      (double_add_body_gen 4%nat
        (pre_comp_table_gen 14%nat p))
    ).
    rewrite toList_drop_equiv.
    rewrite toList_reverse_equiv.
    rewrite mul_scalar_rwnaf_equiv.

    rewrite select_point_ct_gen_equiv.
    rewrite pre_comp_table_gen_equiv.

    unfold point_mul_gen.
    rewrite sawAt_nth_equiv.
    rewrite mul_scalar_rwnaf_equiv.

    rewrite sawAt_nth_equiv.
    rewrite pre_comp_table_gen_equiv.

    reflexivity.

    lia.
    lia.

    intros.
    rewrite <- pre_comp_table_gen_equiv.
    unfold pre_comp_table.
  
    rewrite <- double_add_body_gen_equiv.
    reflexivity.

  Qed.

End PointMul.
