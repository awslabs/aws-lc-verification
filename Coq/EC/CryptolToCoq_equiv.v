
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
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import CoqVectorsExtra.
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCoreScaffolding.


From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import Everything.

From Bits Require Import operations.
From Bits Require Import operations.properties.
From Bits Require Import spec.properties.

(*
Require Import CryptolToCoq.SAWCoreBitvectorsZifyU64.
*)

(*
Axioms on which the main proof depend. If you prove something in this file, remove it from the list. 

sbvToInt_sign_extend_equiv
  : forall (n1 : Nat) (n2 : nat) (x : bitvector n1),
    sbvToInt (addNat n2 n1)
      (append n2 n1 Bool (if sawAt n1 Bool x 0%nat then ecCompl (bitvector n2) (PLogicWord n2) (ecZero (bitvector n2) (intToBv n2 0)) else ecZero (bitvector n2) (intToBv n2 0)) x) =
    sbvToInt n1 x


sbvToInt_intToBv_id : forall (n : nat) (v : Z), (- 2 ^ BinInt.Z.of_nat (Nat.pred n) <= v < 2 ^ BinInt.Z.of_nat (Nat.pred n))%Z -> sbvToInt n (intToBv n v) = v
sbvToInt_drop_equiv_h
  : forall (n1 : Nat) (n2 : nat) (x : bitvector (addNat n1 (S n2))),
    (- 2 ^ BinInt.Z.of_nat n2 <= sbvToInt (addNat n1 (S n2)) x < 2 ^ BinInt.Z.of_nat n2)%Z -> spec.toZ (bvToBITS (drop Bool n1 (S n2) x)) = sbvToInt (addNat n1 (S n2)) x
sbvToInt_bvToInt_id : forall (n : nat) (x : bitvector n), n > 0 -> intToBv n (sbvToInt n x) = x
sbvToInt_bvSub_equiv
  : forall (n : nat) (v1 v2 : bitvector n),
    n > 1 ->
    (- 2 ^ BinInt.Z.of_nat (Nat.pred (Nat.pred n)) <= sbvToInt n v1 < 2 ^ BinInt.Z.of_nat (Nat.pred (Nat.pred n)))%Z ->
    (- 2 ^ BinInt.Z.of_nat (Nat.pred (Nat.pred n)) <= sbvToInt n v2 < 2 ^ BinInt.Z.of_nat (Nat.pred (Nat.pred n)))%Z ->
    sbvToInt n (bvSub n v1 v2) = (sbvToInt n v1 - sbvToInt n v2)%Z
sbvToInt_bvNeg_equiv : forall (n : Nat) (v : bitvector n), sbvToInt n (bvNeg n v) = (- sbvToInt n v)%Z
sbvToInt_0_replicate : forall (n : Nat) (b2 : bitvector n), sbvToInt n b2 = 0%Z -> b2 = replicate n bool 0%bool
sawAt_nth_order_equiv : forall (A : Type) (inh : Inhabited A) (n1 n2 : nat) (v : Vec n1 A) (ltpf : n2 < n1), sawAt n1 A v n2 = nth_order v ltpf
sawAt_3_equiv : forall (A : Type) (inh : Inhabited A) (v : t A 3), cons A (sawAt 3 A v 0%nat) 2 (cons A (sawAt 3 A v 1%nat) 1 (cons A (sawAt 3 A v 2) 0 (nil A))) = v
rep_false_eq_int_bv : forall n : Nat, replicate n bool 0%bool = intToBv n 0
nth_order_shiftR_all_eq : forall (A : Type) (n2 len : nat) (v : Vec len A) (nlt : n2 < len) (zlt : 0 < len) (a : A), nth_order (shiftR len A a v n2) nlt = nth_order v zlt
nth_order_drop_eq
  : forall (A : Type) (inh : Inhabited A) (n1 n2 : Nat) (v : Vec (addNat n1 n2) A) (n' : Nat) (lt1 : addNat n1 n' < addNat n1 n2) (lt2 : n' < n2),
    nth_order (drop A n1 n2 v) lt2 = nth_order v lt1
nth_order_bvAnd_l_eq : forall (n : nat) (v : bitvector n) (n' : nat) (plt : n' < n), n' < Nat.pred n -> nth_order (bvAnd n v (intToBv n 1)) plt = 0%bool
nth_order_bvAnd_eq : forall (n : nat) (v : bitvector n) (plt : Nat.pred n < n), nth_order (bvAnd n v (intToBv n 1)) plt = nth_order v plt
nth_order_append_l_eq
  : forall (A : Type) (inh : Inhabited A) (n1 : nat) (v1 : Vec n1 A) (n2 : nat) (v2 : Vec n2 A) (n' : nat) (nlt2 : n' < addNat n2 n1) (nlt1 : n' < n2),
    nth_order (append n2 n1 A v2 v1) nlt2 = nth_order v2 nlt1
nth_order_append_eq
  : forall (A : Type) (inh : Inhabited A) (n1 : nat) (v1 : Vec n1 A) (n2 : nat) (v2 : Vec n2 A) (n' : Nat) (nlt2 : addNat n' n2 < addNat n2 n1) (nlt1 : n' < n1),
    nth_order (append n2 n1 A v2 v1) nlt2 = nth_order v1 nlt1
nth_order_0 : forall (n1 n2 : nat) (nlt : n2 < n1), nth_order (intToBv n1 0) nlt = 0%bool
intToBv_eq_pos : forall (n : nat) (x y : Z), (0 <= x < 2 ^ BinInt.Z.of_nat n)%Z -> (0 <= y < 2 ^ BinInt.Z.of_nat n)%Z -> intToBv n x = intToBv n y -> x = y
intToBv_add_equiv : forall (n : Nat) (x y : Z), intToBv n (x + y) = bvAdd n (intToBv n x) (intToBv n y)
intToBv_0_eq_replicate : forall n : Nat, intToBv n 0 = replicate n bool 0%bool
intToBv_0_S : forall n : nat, intToBv (S n) 0 = cons bool 0%bool n (intToBv n 0)
holds_up_to_3 : forall P : nat -> Prop, P 0%nat -> P 1%nat -> P 2 -> P 3 -> forall n : nat, P n
error : forall a : Type, Inhabited a -> string -> a
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
ecOr_0_if : forall (n : nat) (x y : bitvector n), ecOr (bitvector n) (PLogicWord n) x y = replicate n bool 0%bool -> x = replicate n bool 0%bool /\ y = replicate n bool 0%bool
ecNotEq_vec_bv_true : forall (n1 n2 : nat) (v1 v2 : Vec n1 (bitvector n2)), v1 <> v2 -> ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2 = 1%bool
ecNotEq_vec_bv_false : forall (n1 n2 : nat) (v : Vec n1 (bitvector n2)), ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v = 0%bool
ecFromTo_m_n_equiv : forall m n : Nat, to_list (ecFromTo m n Integer PLiteralInteger) = List.map (Z.add (Z.of_nat m)) (toN_int (n - m))
ecFromTo_0_n_equiv : forall n : Nat, to_list (ecFromTo 0%nat n Integer PLiteralInteger) = toN_int n
ecFromTo_0_n_bv_excl_equiv : forall (s : nat) (n : Nat), to_list (ecFromTo 0%nat n (seq s Bool) (PLiteralSeqBool s)) = toN_excl_bv s (S n)
ecFoldl_foldl_equiv : forall (A B : Type) (inhB : Inhabited B) (f : A -> B -> A) (n : Nat) (ls : seq n B) (a : A), ecFoldl n A B f a ls = List.fold_left f (to_list ls) a
ecEq_vec_bv_true : forall (n1 n2 : nat) (v : Vec n1 (bitvector n2)), ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v = 1%bool
ecEq_vec_bv_false : forall (n1 n2 : nat) (v1 v2 : Vec n1 (bitvector n2)), v1 <> v2 -> ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2 = 0%bool
bvToNat_toZ_equiv : forall (n : Nat) (x : bitvector n), BinInt.Z.of_nat (bvToNat n x) = bvToInt n x
bvToNat_lt_word : forall (n : Nat) (x : bitvector n), (BinInt.Z.of_nat (bvToNat n x) < 2 ^ BinInt.Z.of_nat n)%Z
bvToNat_Z_to_nat_equiv : forall (n : Nat) (x : bitvector n) (z : Z), (0 <= z)%Z -> sbvToInt n x = z -> bvToNat n x = BinInt.Z.to_nat z
bvToInt_shiftR_lt : forall (n : Nat) (v : bitvector n) (s : nat) (b : Z), (bvToInt n v < 2 ^ (BinInt.Z.of_nat s + b))%Z -> (bvToInt n (shiftR n bool 0%bool v s) < 2 ^ b)%Z
bvToInt_shiftR_equiv : forall (n s : nat) (x : t bool n), s >= 0 -> bvToInt n (shiftR n bool 0%bool x s) = BinInt.Z.shiftr (bvToInt n x) (BinInt.Z.of_nat s)
bvToInt_shiftL_1_equiv : forall n s : nat, s < n -> bvToInt n (shiftL n bool 0%bool (intToBv n 1) s) = BinInt.Z.shiftl 1 (BinInt.Z.of_nat s)
bvToInt_sbvToInt_range : forall (n : Nat) (v : bitvector n) (x : Z), (bvToInt n v < 2 ^ (1 + x))%Z -> (- 2 ^ x <= sbvToInt n v < 2 ^ x)%Z
bvToInt_sbvToInt_equiv : forall (n : nat) (v : bitvector n), n > 0 -> (bvToInt n v < 2 ^ BinInt.Z.of_nat (Nat.pred n))%Z -> sbvToInt n v = bvToInt n v
bvToInt_nonneg : forall (n : Nat) (v : bitvector n), (0 <= bvToInt n v)%Z
bvToInt_intToBv_id : forall (n : Nat) (v : Z), bvToInt n (intToBv n v) = v
bvToInt_bvAdd_small_equiv
  : forall (n : nat) (v1 v2 : bitvector n), (0 <= bvToInt n v1 + sbvToInt n v2 < 2 ^ BinInt.Z.of_nat n)%Z -> bvToInt n (bvAdd n v1 v2) = (bvToInt n v1 + sbvToInt n v2)%Z
bvToInt_bound : forall (n : Nat) (v : bitvector n), (0 <= bvToInt n v < 2 ^ BinInt.Z.of_nat n)%Z
bvToBits_eq_inv : forall (n : nat) (b1 b2 : bitvector n), bvToBITS b1 = bvToBITS b2 -> b1 = b2
bvToBITS_z_equiv : forall (n : Nat) (z : Z), bvToBITS (intToBv n z) = spec.fromZ z
bvToBITS_xor_eq : forall (n : Nat) (v1 v2 : bitvector n), bvToBITS (bvXor n v1 v2) = xorB (bvToBITS v1) (bvToBITS v2)
bvToBITS_ones_eq : forall n : Nat, bvToBITS (replicate n bool 1%bool) = spec.ones n
bvToBITS_bitsToBv_id : forall (n : nat) (v : spec.BITS n), bvToBITS (bitsToBv v) = v
bvSShr_all_nonneg : forall (n1 : nat) (v : bitvector (S n1)), (0 <= sbvToInt (S n1) v)%Z -> bvSShr n1 v n1 = replicate (S n1) bool 0%bool
bvSShr_all_neg : forall (n1 : nat) (v : bitvector (S n1)), (sbvToInt (S n1) v < 0)%Z -> bvSShr n1 v n1 = replicate (S n1) bool 1%bool
bvSShr_Z_shiftr_equiv
  : forall (n : nat) (x1 : bitvector (S n)) (x2 : Z) (y1 : nat) (y2 : Z),
    BinInt.Z.of_nat y1 = y2 -> sbvToInt (S n) x1 = x2 -> sbvToInt (S n) (bvSShr n x1 y1) = BinInt.Z.shiftr x2 y2
bvOr_bvToInt_equiv : forall (n : Nat) (x y : bitvector n), bvToInt n (bvOr n x y) = BinInt.Z.lor (bvToInt n x) (bvToInt n y)
bvNat_bvToNat_id : forall (n : Nat) (x : bitvector n), Eq (bitvector n) (bvNat n (bvToNat n x)) x
bvMul_2_shiftl_equiv : forall (n : nat) (v : bitvector n), bvMul n (intToBv n 2) v = shiftL n bool 0%bool v 1
bvEq_nth_order : forall (n : nat) (v1 v2 : bitvector n), bvEq n v1 v2 = 1%bool -> forall (n' : nat) (pf : n' < n), nth_order v1 pf = nth_order v2 pf
bvEq_false_ne : forall (n : nat) (v1 v2 : bitvector n), bvEq n v1 v2 = 0%bool -> exists (n' : nat) (nlt : n' < n), nth_order v1 nlt <> nth_order v2 nlt
bits_cons_decomp : forall (n : nat) (v : spec.BITS (S n)), exists (b : bool) (v' : spec.BITS n), v = spec.consB b v'
bitsToBv_cons_eq : forall (n : nat) (x : spec.BITS n) (h : Bool), VectorDef.cons Bool h n (bitsToBv x) = bitsToBv (spec.consB h x)
append_nil_eq : forall (A : Type) (inh : Inhabited A) (n : nat) (v : Vec n A), append 0%nat n A (nil A) v = v
adcB_0_1_equiv : forall (n : nat) (a : spec.BITS n), adcB 1 (spec.fromZ 0) a = adcB 0 (spec.fromZ 1) a
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y

*)

Ltac ecSimpl_one :=
  match goal with
    | [ |- context[ecNumber (TCNum ?a) ?t (PLiteralSeqBool (TCNum ?s))]] =>
        replace (ecNumber (TCNum a) t (PLiteralSeqBool (TCNum s))) with (bvNat s a); [idtac | reflexivity] 
    | [ |- context[ecNumber (TCNum ?a) ?t PLiteralInteger]] =>
        replace (ecNumber (TCNum a) t PLiteralInteger) with (Z.of_nat a); [idtac | reflexivity] 
    | [|- context[ecCat ?s1 ?s2 ?t ?a ?b]] =>
        replace (ecCat s1 s2 t a b) with (append a b); [idtac | reflexivity]
    | [|- context[map ?s ?t1 ?t2 ?f ?ls]] =>
        replace (map s t1 t2 f ls) with (SAWCorePrelude.map f _ ls); [idtac | reflexivity]
    | [ |- context[ecPlus Integer ?r (Z.of_nat ?a) (Z.of_nat ?b)]] =>
        replace (ecPlus Integer r (Z.of_nat a) (Z.of_nat b)) with (ecNumber (a + b) Integer PLiteralInteger); [idtac | reflexivity]
    | [ |- context[ecMinus ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecMinus t (PRingSeqBool s) a b) with (bvSub a b); [idtac | reflexivity]
    | [ |- context[ecPlus ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecPlus t (PRingSeqBool s) a b) with (bvAdd a b); [idtac | reflexivity]
    | [ |- context[ecAnd ?t (PLogicSeqBool ?s) ?a ?b]] => 
        replace (ecAnd t (PLogicSeqBool s) a b) with (bvAnd a b); [idtac | reflexivity]
    | [ |- context[ecMul ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecMul t (PRingSeqBool s) a b) with (bvMul _ a b); [idtac | reflexivity]
    | [ |- context[ecMod ?t (PIntegralSeqBool ?s) ?a ?b]] => 
        replace (ecMod t (PIntegralSeqBool s) a b) with (bvURem _ a b); [idtac | reflexivity]
    | [ |- context[ecDrop (TCNum ?s1) (TCNum ?s2) ?t ?a]] => 
        replace (ecDrop (TCNum s1) (TCNum s2) t a) with (drop _ s1 s2 a); [idtac | reflexivity]
    | [ |- context[ecShiftL ?s ?t Bool ?r PZeroBit ?a (Z.of_nat ?b)]] => 
        replace (ecShiftL s t Bool r PZeroBit a (Z.of_nat b)) with (shiftL _ _ false a b); [idtac | reflexivity]
    | [ |- context[ecShiftR ?s1 ?t Bool ?r PZeroBit ?a (bvNat ?s2 ?b)]] => 
        replace (ecShiftR s1 t Bool r PZeroBit a (bvNat s2 b)) with (shiftR _ _ false a b); [idtac | reflexivity]
    | [ |- context[ecShiftR ?s ?t Bool ?r PZeroBit ?a (Z.of_nat ?b)]] => 
        replace (ecShiftR s t Bool r PZeroBit a (Z.of_nat b)) with (shiftR _ _ false a b); [idtac | reflexivity]
  end.

Ltac removeCoerce :=
  match goal with
  | [ |- context[coerce ?t1 ?t2 ?p ?a]] => 
    replace (coerce t1 t2 p a) with a; [idtac | reflexivity]
  end.

Theorem Vec_0_nil : forall (A : Type)(v : Vec O A),
  v = @Vector.nil A.

  intros.
  eapply (@case0 _ (fun v => v = Vector.nil A)).
  reflexivity.

Qed.

Theorem Vec_S_cons : forall (A : Type) n (v : Vec (S n) A),
  exists x y, v = @Vector.cons A x n y.

  intros.
  eapply (@VectorDef.caseS' _ _ _ (fun v => exists x y, v = Vector.cons A x n y)).
  intros.
  econstructor.
  econstructor.
  reflexivity.

Qed.


Theorem empty_Vec_eq : forall (A : Type)(v1 v2 : Vec O A),
  v1 = v2.

  intros.
  rewrite (@Vec_0_nil _ v1).
  rewrite (@Vec_0_nil _ v2).
  reflexivity.
Qed.


Theorem ecScanl_vec_ext : forall t1 t2 (f1 f2 : t1 -> t2 -> t1) n (ls : Vec n t2) x,
  (forall x y, f1 x y = f2 x y) ->
  (ecScanl n t1 t2 f1 x ls) = (ecScanl n t1 t2 f2 x ls).

  induction ls; intros.
  reflexivity.

  simpl.
  rewrite H.
  f_equal.
  eapply IHls; eauto.

Qed.

Fixpoint toN_excl_int n :=
  match n with 
  | 0 => List.nil
  | S n' => (toN_excl_int n') ++ (Z.of_nat n') :: List.nil
  end.

Definition toN_int n :=
  (toN_excl_int n) ++ ((Z.of_nat n) :: List.nil).

Theorem ecFromTo_0_n_equiv : forall n,
  to_list (ecFromTo 0 (TCNum n) Integer PLiteralInteger) = 
  (toN_int n).

  intros.
  unfold ecFromTo, toN_int.
  simpl.

Admitted.

Fixpoint toN_excl_bv s n :=
  match n with 
  | 0 => List.nil
  | S n' => (toN_excl_bv s n') ++ (bvNat s n') :: List.nil
  end.

Definition toN_bv s n :=
  (toN_excl_bv s n) ++ ((bvNat s n) :: List.nil).

Theorem ecFromTo_0_n_bv_excl_equiv : forall (s : nat) n,
  to_list (ecFromTo 0 (TCNum n) (CryptolPrimitivesForSAWCore.seq (TCNum s) Bool)
           (PLiteralSeqBool (TCNum s))) = 
  (toN_excl_bv s (S n)).

Admitted.

Theorem ecFromTo_0_n_bv_equiv : forall (s : nat) n,
  to_list (ecFromTo 0 (TCNum n) (CryptolPrimitivesForSAWCore.seq (TCNum s) Bool)
           (PLiteralSeqBool (TCNum s))) = 
  (toN_bv s n).

Admitted.

Theorem ecFromTo_m_n_equiv : forall m n,
  to_list (ecFromTo (TCNum m) (TCNum n) Integer PLiteralInteger) = 
  (List.map (Z.add (Z.of_nat m)) (toN_int (n-m))).

Admitted.

Theorem toList_ecDrop_equiv : forall A (inh : Inhabited A) n m (v : Vec (addNat n m) A),
  to_list (ecDrop n m _ v) = skipn n (to_list v).

Admitted.


Theorem toList_cons : forall A n (v : Vec n A) a,
  to_list (Vector.cons A a n v) = List.cons a (to_list v).

  intros.
  reflexivity.

Qed.

Theorem map_cons : forall A B n (v : Vec n A) (f : A -> B) a,
  map _ _ f _ (VectorDef.cons _ a _ v) = Vector.cons _ (f a) _ (map _ _ f _ v).

  intros.
  reflexivity.

Qed.

Theorem toList_map_equiv : forall A (inh : Inhabited A) B n (v : Vec n A) (f : A -> B),
  to_list (SAWCorePrelude.map _ _ f _ v) = List.map f (to_list v).

  induction v; intros.
  reflexivity.

  rewrite toList_cons.
  simpl.
  match goal with
  | [|- to_list (map ?A ?B ?f (S ?n) (VectorDef.cons ?A ?h ?n ?v)) = _] =>
    assert ((map A B f (S n) (VectorDef.cons A h n v)) = (Vector.cons _ (f h) _ (map _ _ f _ v)))
  end.
  reflexivity.
  rewrite H.
  rewrite toList_cons.
  f_equal.
  eauto.

Qed.



Fixpoint scanl (A B : Type)(f : A -> B -> A)(ls : list B)(a : A) :=
  match ls with 
  | List.nil => a :: List.nil 
  | b :: ls' => a :: scanl f ls' (f a b)
  end.

Theorem toList_scanl_equiv : forall (A B : Type)(f : A -> B -> A) n (v : Vec n B)(a : A),
  to_list (ecScanl (TCNum n) A B f a v) = scanl f (to_list v) a.

  induction v; intros.
  simpl. reflexivity.

  simpl.
  rewrite toList_cons.
  f_equal.
  eapply IHv.

Qed.

Theorem ecAtBack_0_equiv : forall n A (inh : Inhabited A)(def : A) r (v : seq (TCNum n) A),
  (@ecAtBack (TCNum n) A inh _ r v 0) = List.hd def (List.rev (to_list v)).
    
  intros.
  unfold ecAtBack.

Abort.

Fixpoint scanl_fix (A C : Type)(f : A -> A)(f1 f2 : A -> C) n a := 
  match n with
  | 0 => List.nil
  | 1 => (f1 a) :: (f2 a) :: List.nil
  | S n' => (f1 a) :: (scanl_fix f f1 f2 n' (f a))
  end.

Theorem hd_app_eq : forall (A : Type)(defA: A)(ls1 ls2 : list A),
  List.length ls1 <> O ->
  List.hd defA (ls1 ++ ls2) = List.hd defA ls1.

  intros.
  destruct ls1; simpl in *.
  intuition.
  trivial.
Qed.

Theorem scanl_length : forall (A B : Type)(ls : list A)(f : B -> A -> B)(b : B),
  Datatypes.length (scanl f ls b) <> O.

  intros.
  destruct ls; simpl; intuition.

Qed.


Theorem scanl_fix_equiv : forall (A B C: Type) (defA : A) (f : A -> A) (ls : list B) (n : nat) (f1 f2 : A -> C) a,
  List.length ls = n ->  
  (List.map f1 (scanl (fun x y => f x) ls a)) ++ (f2 (List.hd defA (List.rev (scanl (fun x y => f x) ls a))))::List.nil = 
  scanl_fix f f1 f2 (S n) a.

  induction ls; destruct n; intros; simpl in *.
  reflexivity.
  discriminate.
  discriminate.
  
  f_equal.

  rewrite hd_app_eq.
  eapply IHls.
  lia.

  rewrite rev_length.
  eapply scanl_length.
Qed.

Require Import ZArith.BinInt.

Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Zdigits.


Theorem ecCat_equiv : forall s1 s2 t (inh : Inhabited t)(a : Vec s1 t) (b : Vec s2 t),
  (ecCat (TCNum s1) (TCNum s2) t a b) = (SAWCorePrelude.append _ _ _ a b).

  intros.
  reflexivity.
Qed.


Theorem sawAt_nth_equiv : forall (A : Type)(inh : Inhabited A)(n1 : nat)(ls : Vec n1 A)(n2 : nat),
   (n2 < n1)%nat ->
   (sawAt _ _ ls n2) = (nth n2 (to_list ls) (inhabitant inh)).

  induction ls; intros; simpl in *.
  lia.

  destruct n2; simpl in *.
  trivial.

  unfold sawAt in *. simpl.
  rewrite IHls.
  reflexivity.
  lia.
Qed.

Theorem to_list_cons : forall (A : Type)(n : Nat)(ls : Vec n A) x,
  to_list (VectorDef.cons _ x _ ls) = List.cons x (to_list ls).

  intros.
  reflexivity.

Qed.

(*
Theorem toList_reverse_cons_eq : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A) a,
  to_list (SAWCorePrelude.reverse _ _ (Vector.cons _ a _ ls)) =  (to_list (SAWCorePrelude.reverse _ _ ls)) ++ (a :: nil).
  
  intros.
  unfold SAWCorePrelude.reverse.
  Search gen.
  specialize (gen_add n 1%nat _ (fun i : Nat => sawAt (S n) A (Vector.cons A a n ls) (subNat (subNat (S n) 1%nat) i))). intros.
  assert (ssrnat.addn n 1 = S n) by admit.
  rewrite H0 in H.
  replace (ssrnat.addn n 1) with (S n).
  rewrite H.


  induction n; intros; simpl in *.
  rewrite (Vec_0_nil ls).
  reflexivity.
  destruct (Vec_S_cons ls).
  destruct H.
  subst.
  simpl.
  Search Vec S.

Qed.
*)

Print rev_ind.

Section NatPlusInd.

  Variable P : nat -> Prop.
  Hypothesis base : P O.
  Hypothesis step : forall n, P n -> P (n + 1)%nat.

  Theorem nat_plus_ind : forall n, P n.
    induction n; intros; simpl in *; trivial.
    specialize (@step n).
    replace (S n )%nat with (n + 1)%nat.
    eauto.
    lia.
  Qed.

End NatPlusInd.

Theorem Vec_plus_app : forall (A : Type) n m (v : Vec (n + m)%nat A),
  exists (v1 : (Vec n A))(v2 : (Vec m A)),
    v = Vector.append v1 v2.

  induction n; intros; simpl in *.
  exists (Vector.nil A).
  exists v.
  reflexivity.

  destruct (Vec_S_cons v).
  destruct H.
  subst.
  destruct (IHn _ x0). destruct H. subst.
  exists (Vector.cons A x _ x1).
  exists x2.
  simpl.
  reflexivity.

Qed.

(*
Require Import Eqdep.

Check eq_dep.

Theorem Vec_rev_append_eq : forall (A : Type) n1 (v1 : Vec n1 A) n2 (v2 : Vec n2 A),
  eq_dep nat (fun n => Vec n A) _ (Vector.rev (Vector.append v1 v2)) _ (Vector.append (Vector.rev v2) (Vector.rev v1)).

Abort.

Definition Vec_eq_length (A : Type) (n m : nat) (len_eq : n = m) v :=
  eq_rect _ (fun k => @Vec k A) v _ len_eq.
*)


Fixpoint gen_ls (n : nat)(A : Type)(f : nat -> A) : list A :=
  match n with
  | O => nil
  | S p => cons (f 0%nat) (gen_ls p (fun i => f (S i)))
  end.

Theorem to_list_gen_sawAt_eq : forall (A : Type)(inh : Inhabited A) n n' (ls : Vec n' A)(f : nat-> nat),
  (forall i, i < n -> f i < n')%nat -> 
  to_list (gen n _ (fun i => sawAt n' _ ls (f i) )) = gen_ls n (fun i => nth (f i) (to_list ls) inhabitant). 

  induction n; intros; simpl in *.
  reflexivity.

  rewrite to_list_cons.
  rewrite (@IHn _ ls (fun x => (f (S x)))).
  f_equal.
  apply sawAt_nth_equiv.
  eapply H.
  lia.
  intros.
  eapply H.
  lia.

Qed.

Theorem gen_ls_ext : forall (A : Type) n (f1 f2 : nat -> A),
  (forall i, (i < n)%nat -> f1 i = f2 i) ->
  gen_ls n f1 = gen_ls n f2.

  induction n; intros; simpl in *.
  trivial.

  f_equal.
  eapply H.
  lia.
  eapply IHn.
  intros.
  eapply H.
  lia.

Qed.


Theorem gen_ls_reverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : list A) , 
  length ls = n ->
  gen_ls n (fun i : nat => nth ((n - 1) - i)%nat ls inhabitant) = rev ls.

  induction n; intuition; simpl in *.
  destruct ls; simpl in *; trivial; try discriminate.

  destruct ls using rev_ind.
  simpl in *. discriminate.
  rewrite app_length in H.
  assert (n = Datatypes.length ls).
  simpl in *. lia.
  subst.
  rewrite rev_app_distr.
  simpl.
  f_equal.
  rewrite app_nth2.
  simpl in *.
  repeat rewrite Nat.sub_0_r.
  rewrite minus_diag. trivial.
  lia.

  specialize (IHn ls).
  rewrite <- IHn; trivial.
  eapply gen_ls_ext.
  intros.
  repeat rewrite Nat.sub_0_r.
  replace (Datatypes.length ls - 1 - i)%nat with (Datatypes.length ls - (S i))%nat.
  rewrite app_nth1.
  trivial.
  lia.
  lia.
 
Qed.

Theorem gen_ls_reverse_subNat_equiv : forall (A : Type)(inh : Inhabited A) n (ls : list A) , 
  length ls = n ->
  gen_ls n (fun i : nat => nth (subNat (subNat n 1%nat) i) ls inhabitant) = rev ls.

  intros.
  erewrite gen_ls_ext.
  apply gen_ls_reverse_equiv; eauto.
  intros.  
  repeat rewrite subNat_sub.
  reflexivity.
Qed.


Theorem to_list_length : forall (A : Type) n (ls : Vec n A),
  List.length (to_list ls) = n.

  induction ls; intros.
  trivial.
  rewrite to_list_cons.
  simpl.
  f_equal; eauto.

Qed.

Theorem toList_reverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A),
  to_list (SAWCorePrelude.reverse _ _ ls) = rev (to_list ls).

  intros.
  unfold reverse.
  rewrite to_list_gen_sawAt_eq.
  apply gen_ls_reverse_subNat_equiv.
  apply to_list_length.
  intros.
  repeat rewrite subNat_sub.
  lia.

Qed.

Theorem nth_0_hd_equiv : forall (A : Type)(defA : A)(ls : list A),
  nth 0 ls defA = hd defA ls.

  destruct ls; trivial.

Qed.

Theorem scanl_ext : forall (A B : Type)(f1 f2 : A -> B -> A) ls a,
    (forall a b, f1 a b = f2 a b) ->
    (scanl f1 ls a) = (scanl f2 ls a).

  induction ls; intuition idtac; simpl in *.
  f_equal.
  rewrite H.
  eapply IHls.
  eauto.

Qed.

Theorem sawAt_3_equiv : forall A (inh : Inhabited A) (v : Vector.t A 3),
  Vector.cons _ (sawAt 3%nat A v 0%nat) _
    (Vector.cons _ (sawAt 3%nat A v 1%nat) _
      (Vector.cons _ (sawAt 3%nat A v 2%nat) _ (Vector.nil A)))
  = v.
Admitted.

Theorem sawAt_3_equiv_gen : forall A (inh : Inhabited A) (v1 v2 : Vector.t A 3),
  v1 = v2 ->
  Vector.cons _ (sawAt 3%nat A v1 0%nat) _
    (Vector.cons _ (sawAt 3%nat A v1 1%nat) _
      (Vector.cons _ (sawAt 3%nat A v1 2%nat) _ (Vector.nil A)))
  = v2.
  
  intros.
  subst.
  apply sawAt_3_equiv.

Qed.

Theorem ecFoldl_foldl_equiv : forall (A B : Type)(inhB : Inhabited B)(f : A -> B -> A) n ls a,
    ecFoldl (TCNum n) _ _ f a ls = fold_left f (to_list ls) a.

Admitted.

Theorem toList_ecReverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A),
  to_list (ecReverse (TCNum n) _ ls) = rev (to_list ls).
    
  intros.
  simpl.
  apply toList_reverse_equiv.
Qed.

(* zip is in the generated code. It is reproduced here to allow us to reason about it without importing
generated code. *)

Definition zip (n : CryptolPrimitivesForSAWCore.Num) (a : Type) {Inh_a : SAWCoreScaffolding.Inhabited a} (b : Type) {Inh_b : SAWCoreScaffolding.Inhabited b} (xs : CryptolPrimitivesForSAWCore.seq n a) (ys : CryptolPrimitivesForSAWCore.seq n b)  :=
  let var__0   := prod a b in
  CryptolPrimitivesForSAWCore.seqMap var__0 var__0 n (SAWCorePrelude.uncurry a b var__0 (fun (x : a) (y : b) => pair x y)) (CryptolPrimitivesForSAWCore.seqZipSame a b n xs ys).

Theorem zip_cons_equiv : forall A B (inha : Inhabited A)(inhb : Inhabited B) n (lsa: Vec n A) (lsb: Vec n B) h h0,
  (@zip (TCNum (S n)) A inha B inhb (VectorDef.cons A h n lsa)
     (VectorDef.cons B h0 n lsb)) = VectorDef.cons _ (h, h0) _ (@zip (TCNum n) A inha B inhb lsa lsb).

  intros.
  reflexivity.

Qed.

Theorem toList_zip_equiv : forall (A B : Type)(inha : Inhabited A)(inhb: Inhabited B) n (lsa: Vec n A) (lsb : Vec n B),
  to_list (zip (TCNum n) lsa lsb) = List.combine (to_list lsa) (to_list lsb).

  induction lsa; intros.
  rewrite (@Vec_0_nil _ lsb0).
  simpl.
  reflexivity.
  destruct (Vec_S_cons lsb0).
  destruct H. subst.
  rewrite zip_cons_equiv.
  repeat rewrite to_list_cons.
  rewrite IHlsa.
  reflexivity. 
Qed.

Theorem ecAt_equiv : forall A s (ls : Vec s A) (n : Z) def,
    (Z.to_nat n < s)%nat ->
    ecAt (TCNum s) A _ PIntegralInteger ls n = nth (Z.to_nat n) (to_list ls) def.

Admitted.

Theorem fold_left_ext : forall (A B : Type)(f1 f2 : A -> B -> A) ls a,
    (forall a b, f1 a b = f2 a b) ->
    fold_left f1 ls a = fold_left f2 ls a.

  induction ls; intuition idtac; simpl in *.
  rewrite H.
  apply IHls.
  intuition idtac.  
Qed.

Theorem drop_cons_eq : forall (A : Type)(inh : Inhabited A) n1 n2 ls a,
  drop A (S n1) n2 (Vector.cons _ a _ ls) = drop A n1 n2 ls.

  intros.
  reflexivity.

Qed.

Theorem toList_drop_equiv : forall A (inh : Inhabited A) n1 n2 ls,
  to_list (drop A n1 n2 ls) = skipn n1 (to_list ls).

  induction n1; intros; simpl in *.
  unfold drop.
  erewrite gen_domain_eq.
  rewrite gen_sawAt.
  reflexivity.
  intros.
  simpl.
  reflexivity.

  destruct (Vec_S_cons ls). destruct H.
  subst.
  rewrite drop_cons_eq.
  rewrite IHn1.
  rewrite to_list_cons.
  reflexivity.

Qed.

Theorem nth_order_S_cons : forall (A : Type) a n (v : Vec n A) n' (pf : (S n' < S n)%nat)(pf' : (n' < n)%nat),
  nth_order (Vector.cons _ a _ v) pf = nth_order v pf'.

  intros.
  unfold nth_order.
  simpl.
  eapply Vector.eq_nth_iff; trivial.
  apply Fin.of_nat_ext.
Qed.

Theorem ssr_addn_even : forall n1 n2,
  even n1 = true ->
  even n2 = true ->
  even (ssrnat.addn n1 n2) = true.

  intros.
  rewrite <- ssrnat.plusE.
  rewrite Nat.even_add_even; trivial.
  apply Nat.even_spec; trivial.

Qed.


Theorem ssr_double_even : forall n,
  even (ssrnat.double n) = true.

  induction n; intros; simpl in *; trivial.

Qed.

Theorem nth_order_0_cons : forall (A : Type) a n (v : Vec n A) (pf : (0 < S n)%nat),
  nth_order (Vector.cons _ a _ v) pf = a.

  intros.
  reflexivity.
Qed.

Theorem lsb_0_even_h : forall n (v : Vec n _) acc (pf : (pred n < n)%nat),
  nth_order v pf = false -> 
  even (Vector.fold_left bvToNatFolder acc v)  = true.

  induction n; intros; simpl in *.
  lia.

  unfold bvToNat in *.
  destruct (Vec_S_cons v).
  destruct H0.
  subst.
  simpl.
  destruct n.
  rewrite nth_order_0_cons in H.
  subst.
  rewrite (@Vec_0_nil _ x0).
  simpl.
  unfold bvToNatFolder.
  simpl.
  (* double anything is even, 0 is even, even plus even is even*)
  apply ssr_addn_even.
  reflexivity.
  apply ssr_double_even.

  assert (n < S n)%nat by lia.
  rewrite (@nth_order_S_cons _ _ _ _ _ _ H0) in H.
  eapply IHn.
  eauto.

Qed.

Theorem lsb_0_even : forall n (v : Vec n _) (pf : (pred n < n)%nat),
  nth_order v pf = false -> 
  even (bvToNat _ v) = true.

  intros. 
  eapply lsb_0_even_h; eauto.

Qed.

Theorem lsb_1_not_even_h : forall n (v : Vec n _) acc (pf : (pred n < n)%nat),
  nth_order v pf = true -> 
  even (Vector.fold_left bvToNatFolder acc v)  = false.

  induction n; intros; simpl in *.
  lia.

  unfold bvToNat in *.
  destruct (Vec_S_cons v).
  destruct H0.
  subst.
  simpl.
  destruct n.
  rewrite nth_order_0_cons in H.
  subst.
  rewrite (@Vec_0_nil _ x0).
  simpl.
  case_eq (ssrnat.double acc); intros; trivial.
  rewrite <- Nat.negb_odd.
  rewrite <- Nat.even_succ.
  rewrite <- H.
  rewrite ssr_double_even.
  reflexivity.

  assert (n < S n)%nat by lia.
  rewrite (@nth_order_S_cons _ _ _ _ _ _ H0) in H.
  eapply IHn.
  eauto.

Qed.

Theorem lsb_1_not_even : forall n (v : Vec n _) (pf : (pred n < n)%nat),
  nth_order v pf = true -> 
  even (bvToNat _ v) = false.

  intros. 
  eapply lsb_1_not_even_h; eauto.

Qed.


Theorem bvAnd_cons : forall n a1 a2 (v1 v2 : Vec n _),
  bvAnd _ (Vector.cons _ a1 _ v1) (Vector.cons _ a2 _ v2) = 
  Vector.cons _ (andb a1 a2) _ (bvAnd _ v1 v2).
Admitted.

Theorem addNat_equiv : forall n1 n2,
  (n1 + n2)%nat = addNat n1 n2.

  induction n1; intros; simpl in *; trivial.
  rewrite IHn1.
  reflexivity.
Qed.

Theorem drop_0_equiv : forall (A : Type)(inh : Inhabited A) n2 (v : Vector.t A (addNat O n2)),
  drop _ O n2 v = v.

Admitted.

Theorem append_nil_eq : forall (A : Type)(inh : Inhabited A) n (v : Vec n A),
  SAWCorePrelude.append _ _ _ (@Vector.nil A) v = v.

Admitted.

Theorem bvZipWith_cons : forall f n2 a b (v2a v2b : Vec n2 _),
  bvZipWith f _ (Vector.cons _ a _ v2a) (Vector.cons _ b _ v2b) = 
  Vector.cons _ (f a b) _ (bvZipWith f _ v2a v2b).

  intros.
  reflexivity.

Qed.

Local Arguments Vector.cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.



Theorem bvZipWith_append : forall f n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvZipWith f _ (append v1a v2a) (append v1b v2b) = 
  append (bvZipWith f _ v1a v1b) (bvZipWith f _ v2a v2b).

  induction n1; intros; simpl in *.
  rewrite (@Vec_0_nil _ v1a).
  rewrite (@Vec_0_nil _ v1b).
  repeat rewrite append_nil_eq.
  reflexivity.

  destruct (Vec_S_cons v1a).
  destruct H.
  destruct (Vec_S_cons v1b).
  destruct H0.
  subst.
  repeat rewrite SAWCorePrelude_proofs.append_cons.
  unfold Succ.
  repeat rewrite bvZipWith_cons.
  rewrite IHn1.
  rewrite SAWCorePrelude_proofs.append_cons.
  reflexivity.
Qed.

Theorem bvAnd_append : forall n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvAnd (append v1a v2a) (append v1b v2b) = 
  append (bvAnd v1a v1b) (bvAnd v2a v2b).

  intros.
  apply bvZipWith_append.
Qed.

Theorem bvZipWith_append' : forall f n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvZipWith f _ (Vector.append v1a v2a) (Vector.append v1b v2b) = 
  Vector.append (bvZipWith f _ v1a v1b) (bvZipWith f _ v2a v2b).

  induction n1; intros; simpl in *.
  rewrite (@Vec_0_nil _ v1a).
  rewrite (@Vec_0_nil _ v1b).
  reflexivity.

  destruct (Vec_S_cons v1a).
  destruct H.
  destruct (Vec_S_cons v1b).
  destruct H0.
  subst.
  simpl.
  repeat rewrite bvZipWith_cons.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem bvAnd_append' : forall n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvAnd (Vector.append v1a v2a) (Vector.append v1b v2b) = 
  Vector.append (bvAnd v1a v1b) (bvAnd v2a v2b).

  intros.
  apply bvZipWith_append'.

Qed.


Theorem Vec_addNat_append : forall (A : Type)(inh : Inhabited A) n1 n2 (v : Vec (addNat n1 n2) A),
  exists v1 v2,
  v = append v1 v2.

  induction n1; intros; simpl in *.
  exists (@Vector.nil A).
  exists v.
  symmetry.
  apply append_nil_eq.
  destruct (Vec_S_cons v).
  destruct H.
  subst.
  destruct (IHn1 _ x0).
  destruct H.
  subst.
  exists (Vector.cons x x1).
  exists x2.
  rewrite SAWCorePrelude_proofs.append_cons.
  reflexivity.

Qed.

Theorem drop_S_cons : forall (A : Type)(inh : Inhabited A) a n1 n2 (v : Vec (addNat n1 n2) A),
  drop _ (S n1) n2 (Vector.cons a v) = drop _ n1 n2 v.

  intros.
  reflexivity.

Qed.

Theorem drop_append_eq : forall (A : Type)(inh : Inhabited A) n1 n2 (v1 : Vec n1 A)(v2 : Vec n2 A),
  drop _ n1 n2 (append v1 v2) = v2.

  induction n1; intros; simpl in *.
  rewrite drop_0_equiv.
  rewrite (@Vec_0_nil _ v1).
  rewrite append_nil_eq.
  reflexivity.
  destruct (Vec_S_cons v1).
  destruct H.
  subst.
  rewrite SAWCorePrelude_proofs.append_cons.
  rewrite drop_S_cons.
  eauto.  
Qed.

Theorem bvAnd_drop_equiv: forall n1 n2 v1 v2,
  (bvAnd (drop _ n1 n2 v1) (drop _ n1 n2 v2)) = 
  drop _ _ _ (bvAnd v1 v2).

  intros.
  destruct (Vec_addNat_append _ _ _ v1).
  destruct H.
  destruct (Vec_addNat_append _ _ _ v2).
  destruct H0.
  subst.
  rewrite bvAnd_append.
  repeat rewrite drop_append_eq.
  reflexivity.

Qed.


Theorem intToBv_1_append_eq : forall n1 n2,
  (n1 > 0)%nat ->
  append (intToBv n2 0) (intToBv n1 1) = intToBv (addNat n2 n1) 1.
Admitted.

Theorem intToBv_1_append_eq' : forall n1 n2,
  (n1 > 0)%nat ->
  Vector.append (intToBv n2 0) (intToBv n1 1) = intToBv (n2 + n1)%nat 1.
Admitted.

Theorem bvAnd_lsb_drop_equiv: forall n1 n2 v,
  (bvAnd (@drop _ _ n2 n1 v) (intToBv _ 1)) = 
  drop _ _ _ (bvAnd v (intToBv _ 1)).

  intros.
  replace (intToBv n1 1) with (drop _ n2 n1 (append (intToBv n2 0) (intToBv n1 1))).
  rewrite bvAnd_drop_equiv.
  destruct n1.
  apply empty_Vec_eq.
  f_equal.
  f_equal.
  apply intToBv_1_append_eq.
  lia.
  rewrite drop_append_eq.
  trivial.

Qed.



Theorem bvAnd_0 : forall n (v : Vec n _),
  bvAnd v (intToBv n 0) = (intToBv n 0).
Admitted.

Theorem bvAnd_lsb_drop_append_equiv: forall n1 n2 v,
  (n1 > 0)%nat ->
  (bvAnd v (intToBv _ 1)) = 
  (append (intToBv _ 0) (bvAnd (@drop _ _ n2 n1 v) (intToBv _ 1))).

  intros.
  destruct (Vec_addNat_append _ _ _ v).
  destruct H0.
  subst.
  rewrite <- intToBv_1_append_eq; trivial.
  rewrite bvAnd_append.
  f_equal.
  apply bvAnd_0.
  rewrite drop_append_eq.
  reflexivity.

Qed.

Theorem bvEq_append_same : forall n1 n2 (v1 : Vec n1 _) (v2a v2b : Vec n2 _),
  bvEq _ (append v1 v2a) (append v1 v2b) = bvEq _ v2a v2b.

Admitted.

Theorem append_0_320_56 : forall n3 (v : Vec n3 _),
  (append (intToBv 320%nat 0)
       (append (intToBv 56%nat 0) v)) = append (intToBv 376%nat 0) v.

Admitted.

Theorem bvEq_nth_order : forall n (v1 v2 : Vec n _),
  bvEq _ v1 v2 = true ->
  forall n' (pf : (n' < n)%nat),
  nth_order v1 pf = nth_order v2 pf.
Admitted.

Theorem nth_order_append_eq : forall (A : Type)(inh : Inhabited A) n1 (v1 : Vec n1 A) 
  n2 (v2 : Vec n2 A)  n' (nlt2 : (addNat n' n2 < addNat n2 n1)%nat) (nlt1 : (n' < n1)%nat),
  nth_order (append v2 v1) nlt2 = nth_order v1 nlt1.
Admitted.

Theorem nth_order_append_l_eq : forall (A : Type)(inh : Inhabited A) n1 (v1 : Vec n1 A) 
  n2 (v2 : Vec n2 A)  n' (nlt2 : (n' < addNat n2 n1)%nat) (nlt1 : (n' < n2)%nat),
  nth_order (append v2 v1) nlt2 = nth_order v2 nlt1.
Admitted.

Theorem nth_order_append_r_eq : forall (A : Type)(inh : Inhabited A) n1 (v1 : Vec n1 A) 
  n2 (v2 : Vec n2 A)  n' (nlt2 : (n' < addNat n2 n1)%nat) (nlt1 : (n'-n2 < n1)%nat),
  (n' >= n2)%nat ->
  nth_order (append v2 v1) nlt2 = nth_order v1 nlt1.
Admitted.

Theorem nth_order_drop_eq : forall (A : Type)(inh : Inhabited A) n1 n2 (v : Vec (addNat n1 n2) A)
  n' (lt1 : (addNat n1 n' < addNat n1 n2)%nat)(lt2 : (n' < n2)%nat),
  nth_order (drop _ n1 n2 v) lt2 = nth_order v lt1.

Admitted.

Theorem nth_order_bvAnd_eq : forall n (v : Vec n _)(plt : (pred n < n)%nat),
  nth_order (bvAnd v (intToBv n 1)) plt = nth_order v plt.
Admitted.

Theorem nth_order_bvAnd_l_eq : forall n (v : Vec n _) n' (plt : (n' < n)%nat),
  (n' < pred n)%nat ->
  nth_order (bvAnd v (intToBv n 1)) plt = false.
Admitted.

Theorem nth_order_ext : forall (A : Type) n1 n2 (v : Vec n1 A)(lt1 lt2 : (n2 < n1)%nat),
  nth_order v lt1 = nth_order v lt2.

  intros.
  unfold nth_order.
  f_equal.
  apply Fin.of_nat_ext.
Qed.

Theorem nth_order_0 : forall n1 n2 (nlt : (n2 < n1)%nat),
  nth_order (intToBv n1 0) nlt = false.
Admitted.

Theorem bvEq_false_ne : forall n (v1 v2 : Vec n _ ),
  bvEq _ v1 v2 = false -> 
  exists n' (nlt : (n' < n)%nat),
  nth_order v1 nlt <> nth_order v2 nlt.

Admitted.

Theorem ne_false_impl_true : forall a,
  a <> false ->   
  a = true.

  intros.
  destruct a; trivial.
  intuition idtac.

Qed.

Theorem bvToNat_toZ_equiv : forall n x,
  (BinInt.Z.of_nat (bvToNat n x)) = bvToInt n x.
Admitted.


Theorem sbvToInt_bvToInt_id : forall n x,
  (n > 0)%nat -> 
  intToBv n (sbvToInt n x) = x.

  intros.
  unfold intToBv, sbvToInt.
  destruct n.
  lia.
  Print spec.toZ.
Admitted.


Theorem ecEq_bv_true : forall n v,  
  ecEq (bitvector n) (PEqWord n) v v = true.

  intros.
  apply bvEq_refl.

Qed.

Theorem ecEq_bv_false : forall n v1 v2,
  v1 <> v2 ->
  ecEq (bitvector n) (PEqWord n) v1 v2 = false.

  intros.
  unfold ecEq.
  simpl.
  case_eq (bvEq n v1 v2); intros; trivial.
  apply bvEq_eq in H0.
  intuition.
Qed.

Theorem ecEq_vec_bv_true : forall n1 n2 v,
  (ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v) = true.

  intros.
  unfold ecEq.
  simpl.
  unfold vecEq.

Admitted.

Theorem ecEq_vec_bv_false : forall n1 n2 v1 v2,
  v1 <> v2 ->
  (ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2) = false.

Admitted.

Theorem ecNotEq_vec_bv_false : forall n1 n2 v,
  (ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v) = false.

    intros.
  unfold ecNotEq.
  

Admitted.

Theorem ecNotEq_vec_bv_true : forall n1 n2 v1 v2,
  v1 <> v2 ->
  (ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2) = true.
Admitted.

Theorem rep_false_eq_int_bv : forall n, (replicate n _ false) = (intToBv n 0).

Admitted.

Theorem ecOr_0_if : forall n x y, 
    ecOr (bitvector n) (PLogicWord n) x y = (replicate n _ false) ->
    (x = (replicate n _ false) /\ y = (replicate n _ false)).
Admitted.

Theorem fold_or_impl_0 : forall (n1 n2 : nat) x y,
  ecFoldl n1 (CryptolPrimitivesForSAWCore.seq n2 Bool) (CryptolPrimitivesForSAWCore.seq n2 Bool) (ecOr (CryptolPrimitivesForSAWCore.seq n2 Bool) (PLogicSeqBool n2))
     y x = intToBv n2 0 ->
  (x = (replicate n1 _ (replicate n2 _ false)) /\ y = (replicate n2 _ false)).

  induction n1; intros; simpl in *.
  unfold replicate. simpl in *.
  generalize H.
  eapply (case0 (fun x => foldl (bitvector n2) (bitvector n2) 0%nat (ecOr (bitvector n2) (PLogicWord n2)) y x = intToBv n2 0 ->
x = @Vector.nil (Vec n2 bool) /\ y = gen n2 bool (fun _ : Nat => false))); eauto; intuition.
  simpl in *; subst.
  rewrite <- rep_false_eq_int_bv.
  trivial.

  unfold replicate in *. simpl.
  generalize H.
  eapply (caseS' x); intuition;
  simpl in *;
  edestruct IHn1; eauto;
  subst.
  f_equal.
  edestruct ecOr_0_if; eauto.
  edestruct ecOr_0_if; eauto.

Qed.

Theorem scanl_gen_equiv : forall A n f1 f2 z1 x,
  (SAWCoreVectorsAsCoqVectors.scanl Integer A n
         (fun (z : A) (_ : Integer) =>
          z1 z) x
         (gen n Integer f1))
  = 
  (SAWCoreVectorsAsCoqVectors.scanl Integer A n
         (fun (z : A) (_ : Integer) =>
          z1 z) x
         (gen n Integer f2)).

  induction n; intuition; simpl in *.
  f_equal.
  apply IHn.
Qed.

Fixpoint bv64Nats_h (n : nat) v :=
  match n with
  | 0%nat => List.nil
  | S n' => (intToBv 64%nat (Z.of_nat v)) :: (bv64Nats_h n' (S v))
  end.

Definition bv64Nats n := bv64Nats_h n 0.

Theorem gen_nat_seq_eq_h : forall n v,
  (to_list
      (gen n (bitvector 64)
         (fun i : nat => intToBv 64%nat (Z.of_nat (addNat i v%nat)))))
  = bv64Nats_h n v.

  induction n; intuition; simpl in *.
  rewrite to_list_cons.
  f_equal.
  rewrite <- IHn.
  f_equal.  
  eapply gen_domain_eq.
  intros.
  rewrite (eqNatAddComm _ (S v)).
  simpl.
  rewrite eqNatAddComm.
  trivial.
Qed.

Theorem gen_nat_seq_eq : forall n,
  (to_list
      (gen n (bitvector 64)
         (fun i : nat => intToBv 64%nat (Z.of_nat (addNat i 0%nat)))))
  = bv64Nats n.

  intros.
  apply gen_nat_seq_eq_h.    
Qed.

Fixpoint nats_h n v :=
  match n with
  | 0%nat => List.nil
  | S n' => v :: (nats_h n' (S v))
  end.

Definition nats n := nats_h n 0.

Theorem toN_int_excl_length : forall n, 
  List.length (toN_excl_int n) = n.

  induction n; intuition idtac; simpl in *.

  rewrite app_length.
  rewrite IHn.
  simpl.
  lia.

Qed.

Theorem toN_int_length : forall n, 
  List.length (toN_int n) = (S n).

  intros.
  unfold toN_int.
  rewrite app_length.
  rewrite toN_int_excl_length.
  simpl.
  lia.

Qed.

Theorem scanl_fix_convert : forall (A1 A2 B1 B2: Type)
  (conva : A2 -> A1)(convb : B2 -> B1)
  (f1 : A1 -> A1)(f2 : A2 -> A2)
  (fb1 : A1 -> B1)(fb2 : A2 -> B2)
  (fc1 : A1 -> B1)(fc2 : A2 -> B2),
  (forall a, fb1 (conva a) = convb (fb2 a)) ->
  (forall a, (exists b, a = (f2 b)) -> fc1 (conva a) = convb (fc2 a)) ->
  (forall a, (exists b, a = (f2 b)) -> f1 (conva a) = conva (f2 a)) ->
  forall n a1 a2,
  (exists b, a2 = (f2 b)) ->
  a1 = (conva a2) ->
  List.Forall2 (fun b1 b2 => b1 = convb b2)
  (scanl_fix f1 fb1 fc1 n a1)
  (scanl_fix f2 fb2 fc2 n a2).

  induction n; intros; simpl in *; subst.
  econstructor.

  destruct n.
  econstructor.
  eauto.
  econstructor.
  eauto.
  econstructor.

  econstructor.
  eauto.
  eapply IHn.
  eauto.
  eauto.

Qed.


Theorem mod_drop_equiv : forall s1 m a,
  (Z.modulo (bvToInt _ a) (Z.shiftl 1 (Z.of_nat m))) =
  (bvToInt _ (drop Bool s1 m a)).

  intros.
  

Admitted.


Theorem bvToInt_sbvToInt_equiv : forall n v,
  (n > 0)%nat ->
  (bvToInt n v < Z.pow 2 (Z.of_nat (pred n)))%Z ->
  (sbvToInt n v = bvToInt n v).

  intros.
  unfold sbvToInt, bvToInt, spec.toZ, spec.toPosZ.
  destruct n. lia.
  case_eq (spec.splitmsb (bvToBITS v)); intros.
  destruct b0.

Admitted.

Theorem shiftR_bvToInt_nonneg : 
  forall n s x,
  (s > 0)%nat ->
  (VectorDef.hd (shiftR (S n) bool false x s) = false).

Admitted.



Theorem bvToInt_drop_equiv : forall n1 n2 x,
  ((bvToInt _ x) < Z.pow 2 (Z.of_nat n2))%Z ->
  bvToInt _ (drop _ n1 n2 x) = bvToInt _ x.

Admitted.


Theorem sbvToInt_drop_equiv_h : forall n1 n2 x,
  (-(Z.pow 2 (Z.of_nat (n2))) <= (sbvToInt _ x) < Z.pow 2 (Z.of_nat (n2)))%Z ->
  spec.toZ (bvToBITS (drop _ n1 (S n2) x)) = sbvToInt _ x.

Admitted.

Theorem sbvToInt_drop_equiv : forall n1 n2 x,
  (n2 > 0)%nat -> 
  (-(Z.pow 2 (Z.of_nat (pred n2))) <= (sbvToInt _ x) < Z.pow 2 (Z.of_nat (pred n2)))%Z ->
  sbvToInt _ (drop _ n1 n2 x) = sbvToInt _ x.

  intros.
  destruct n2.
  lia.
  unfold sbvToInt.
  simpl in *.
  rewrite sbvToInt_drop_equiv_h; trivial.

Qed.

Theorem sbvToInt_bvSub_equiv : forall n (v1 v2 : Vec n _),
  (n > 1)%nat -> 
    (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v1) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
   (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v2) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
  sbvToInt _ (bvSub v1 v2) = ((sbvToInt _ v1) - (sbvToInt _ v2))%Z.

Admitted.

Theorem bvToInt_intToBv_id : forall n v,
  bvToInt n (intToBv n v) = v.

Admitted.

Theorem sbvToInt_bvURem_equiv : forall n v1 v2,
  (n > 0)%nat ->
  (0 < bvToInt _ v2)%Z ->
  (bvToInt _ v2 <= Z.pow 2 (Z.of_nat (pred n)))%Z ->
  sbvToInt n (bvURem _ v1 v2) = Z.modulo (bvToInt _ v1) (bvToInt _ v2).

  intros.
  Local Transparent bvURem.
  unfold bvURem.
  destruct n. lia.
  rewrite bvToInt_sbvToInt_equiv.
  apply bvToInt_intToBv_id.
  trivial.
  rewrite bvToInt_intToBv_id.
  eapply Z.lt_le_trans.
  eapply Z.mod_pos_bound.
  trivial.
  trivial.
Qed.

Theorem bvToInt_drop_le : forall n1 n2 v,
  (bvToInt _ (drop _ n1 n2 v) <= bvToInt _ v)%Z.

Admitted.

Theorem bvMul_2_shiftl_equiv : forall n v,
  bvMul n (intToBv _ 2) v = shiftL _ _ false v 1.
Admitted.

Theorem shiftL1_shiftL : forall (A : Type) n (b : A) v n1,
  (shiftL1 n _ b (shiftL n _ b v n1)) = shiftL n _ b v (S n1).

  induction n1; intros; simpl in *.
  reflexivity.
  reflexivity.

Qed.

Theorem shiftL_shiftL1 : forall (A : Type) n (b : A) v n1,
  (shiftL n _ b (shiftL1 n _ b v) n1) = shiftL n _ b v (S n1).

  induction n1; intros; simpl in *.
  reflexivity.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem shiftL_shiftL : forall (A : Type) n (b : A) v n1 n2,
  (shiftL n _ b (shiftL n _ b v n1) n2) = shiftL n _ b v (n1 + n2).

  induction n1; intros; simpl in *; trivial.
  rewrite shiftL_shiftL1.
  rewrite IHn1.
  rewrite shiftL1_shiftL.
  f_equal.
  lia.

Qed.

Theorem bvToInt_shiftL_1_equiv : forall n s,
  (s < n)%nat ->
  bvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
  Z.shiftl 1 (Z.of_nat s).
Admitted.

Theorem bvToInt_bvSub_nonneg_equiv : forall n v1 v2,
  (bvToInt _ v2 <= bvToInt _ v1)%Z ->
  (bvToInt n (bvSub v1 v2)) =
  ((bvToInt _ v1) - (bvToInt _ v2))%Z.
Admitted.

Theorem bvToBITS_bitsToBv_id : forall n v,
  bvToBITS (@bitsToBv n v) = v.
Admitted.

Theorem toZ_toPosZ_equiv : forall n (v : spec.BITS (S n)),
  (spec.toZ v mod 2 ^ Z.of_nat (S n) = spec.toPosZ v mod 2 ^ Z.of_nat (S n))%Z.
Admitted.

Theorem toPosZ_addB_equiv: forall n (v1 v2 : spec.BITS (S n)),
  (0 <= spec.toPosZ v1 + spec.toZ v2 < Z.pow 2 (Z.of_nat (S n)))%Z ->
  spec.toPosZ (addB v1 v2) =
  (spec.toPosZ v1 + spec.toZ v2)%Z.

  intros.
  erewrite <- (@Zdiv.Zmod_small (spec.toPosZ v1 + spec.toZ v2)); eauto.
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite toZ_toPosZ_equiv.
  rewrite Zdiv.Zplus_mod_idemp_r.
 
  rewrite addB_def.
Admitted.


Theorem sbvToInt_bvNeg_equiv : forall n v,
  sbvToInt n (bvNeg _ v) = Z.opp (sbvToInt _ v).
Admitted.

Theorem bvToInt_bvAdd_small_equiv : forall n (v1 v2 : bitvector n),
  (* (sbvToInt _ v2 <= bvToInt _ v1)%Z -> *)
  (0 <= (bvToInt _ v1) + (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
  (bvToInt n (bvAdd _ v1 v2)) =
  ((bvToInt _ v1) + (sbvToInt _ v2))%Z.

  intros.
  unfold bvToInt, sbvToInt in *.
  destruct n.
  (* empty bit vectors *)
  admit.

  Local Transparent bvAdd operations.adcB.
  unfold bvAdd.
  rewrite bvToBITS_bitsToBv_id.
  apply toPosZ_addB_equiv.
  apply H.

Admitted.



Theorem bvToInt_bvSub_small_equiv : forall n v1 v2,
  (0 <= (bvToInt _ v1) - (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
  (bvToInt n (bvSub v1 v2)) =
  ((bvToInt _ v1) - (sbvToInt _ v2))%Z.

  intros.
  rewrite bvSub_eq_bvAdd_neg.
  rewrite <- Z.add_opp_r.
  rewrite bvToInt_bvAdd_small_equiv.
  rewrite sbvToInt_bvNeg_equiv.
  reflexivity.
  
  rewrite sbvToInt_bvNeg_equiv.
  rewrite Z.add_opp_r.
  trivial.
Qed.


Theorem bvToInt_shiftR_lt : forall n v s b,
  ((bvToInt n v) < (Z.pow 2 (Z.of_nat s + b)))%Z ->
  ((bvToInt n (shiftR _ _ false v s)) < Z.pow 2 b)%Z.

Admitted.

Theorem bvToInt_nonneg : forall n v,
  (0 <= bvToInt n v)%Z.
Admitted.

Theorem forall2_symm : forall (A B : Type)(P : B -> A -> Prop) lsa lsb,
  List.Forall2 (fun a b => P b a) lsa lsb ->
  List.Forall2 P lsb lsa.

  induction 1; intros;
  econstructor; eauto.

Qed.

Theorem forall2_trans : forall ( A B C : Type)(R1 : A -> B -> Prop)(R2 : B -> C -> Prop)(R3 : A -> C -> Prop)
  lsa lsb lsc,
  List.Forall2 R1 lsa lsb ->
  (forall a b c, R1 a b -> R2 b c -> R3 a c) ->
  List.Forall2 R2 lsb lsc ->
  List.Forall2 R3 lsa lsc.

  induction lsa; intuition; simpl in *.
  inversion H; subst.
  inversion H1; subst.
  econstructor.

  inversion H; subst.
  inversion H1; subst.
  econstructor.
  eauto.
  eapply IHlsa; eauto.

Qed.

Theorem forall2_eq : forall (A : Type)(ls1 ls2 : list A),
  ls1 = ls2 ->
  List.Forall2 eq ls1 ls2.

  induction ls1; intros; simpl in *; subst.
  econstructor.

  econstructor; trivial.
  eauto.

Qed.

Theorem forall2_map_eq : forall (A B : Type)(f : B -> A) lsa lsb,
  List.Forall2 (fun a b => a = f b) lsa lsb ->
  lsa = List.map f lsb.

  induction 1; intros; simpl in *; trivial.
  congruence.

Qed.

Theorem bvOr_bvToInt_equiv : forall n x y,
  bvToInt n (bvOr x y) =
  BinInt.Z.lor (bvToInt n x) (bvToInt n y).
Admitted.

Theorem bvSShr_intToBv_equiv : forall n z v,
  bvSShr _ (intToBv (S n) z) v = intToBv (S n) (Z.shiftr z (Z.of_nat v)).
Admitted.

Theorem fold_left_unroll_one : forall (A B : Type) def (f : A -> B -> A) (ls : list B) a,
  (List.length ls > 0)%nat ->
  List.fold_left f ls a = List.fold_left f (List.tl ls) (f a (List.hd def ls)).

  destruct ls; intros; simpl in *.
  lia.
  reflexivity.

Qed.

Theorem fold_left_R : forall (A1 A2 B1 B2 : Type)(RA : A1 -> A2 -> Prop)(RB : B1 -> B2 -> Prop)(f1 : A1 -> B1 -> A1)(f2: A2 -> B2 -> A2) ls1 ls2 a1 a2,
  RA a1 a2 ->
  List.Forall2 RB ls1 ls2 ->
  (forall a1 a2 b1 b2, RA a1 a2 -> RB b1 b2 -> In b1 ls1 -> In b2 ls2 -> RA (f1 a1 b1) (f2 a2 b2)) ->
  RA (List.fold_left f1 ls1 a1) (List.fold_left f2 ls2 a2).

  induction ls1; destruct ls2; intros; simpl in *; trivial.
  inversion H0.
  inversion H0.
  inversion H0; subst; clear H0.
  eapply IHls1.
  eapply H1; eauto.
  trivial.
  eauto.

Qed.

Theorem hd_rev_eq_last : forall (A : Type)(ls : list A)(def : A),
  List.hd def (List.rev ls) = List.last ls def.

  induction ls using rev_ind; intros; simpl in *; trivial.
  rewrite rev_unit.
  simpl.
  rewrite last_last.
  reflexivity.
Qed.

Theorem fold_left_scanl_app_equiv : forall (A B : Type) (f : A -> B -> A) ls def a1 a2,
  a2 <> List.nil ->
  List.fold_left
(fun (x : list A) (y : B) =>
 x ++ [f (List.last x def) y]) ls 
(List.cons a1 a2) =
  a1 :: (List.fold_left (fun (x : list A) (y : B) =>
 x ++ [f (List.last x def) y]) ls 
a2 ).

  induction ls; intros; simpl in *; trivial.
  rewrite (@IHls _ a1).
  destruct a2.
  intuition idtac.
  reflexivity.
  f_equal.
  intuition idtac.
  apply app_eq_nil in H0.
  intuition idtac.

Qed.

Theorem fold_left_scanl_equiv : forall (A B : Type) def (f : A -> B -> A) ls a,
  List.fold_left (fun x y => x ++ (f (List.last x def) y)::List.nil) ls [a] = 
  CryptolToCoq_equiv.scanl f ls a.

  induction ls; intros; simpl in *; trivial.
  rewrite <- IHls.
  rewrite fold_left_scanl_app_equiv.
  reflexivity.
  congruence.
Qed.

Theorem Forall2_scanl : forall (A1 A2 B1 B2 : Type)(PA : A1 -> A2 -> Prop)(PB : B1 -> B2 -> Prop)
  (f1 : A1 -> B1 -> A1)(f2 : A2 -> B2 -> A2) ls1 ls2 a1 a2,
  List.Forall2 PB ls1 ls2 ->
  (forall a1 a2 b1 b2, PA a1 a2 -> PB b1 b2 -> PA (f1 a1 b1) (f2 a2 b2)) ->
  PA a1 a2 ->
  List.Forall2 PA (scanl f1 ls1 a1) (scanl f2 ls2 a2).

  induction ls1; destruct ls2; simpl in *; intros.
  econstructor; eauto.
  inversion H.
  inversion H.
  inversion H; clear H; subst.
  econstructor; eauto.

Qed.

Theorem Forall2_I : forall (A B : Type)(ls1 : list A)(ls2 : list B),
  List.length ls1 = List.length ls2 ->
  List.Forall2 (fun a b => True) ls1 ls2.

  induction ls1; destruct ls2; intros; simpl in *; try lia.
  econstructor.
  econstructor; eauto; econstructor.

Qed.

Theorem Forall2_nth : forall (A B : Type)(P : A -> B -> Prop) lsa lsb,
  List.Forall2 P lsa lsb ->
  forall n defA defB,
  P defA defB ->
  P (List.nth n lsa defA) (List.nth n lsb defB).

  induction 1; intros; simpl in *.
  destruct n; trivial.
  destruct n; trivial.
  eapply IHForall2; trivial.

Qed.

Theorem Forall2_nth_lt : forall (A B : Type)(P : A -> B -> Prop) lsa lsb,
  List.Forall2 P lsa lsb ->
  forall n defA defB,
  (n < List.length lsa)%nat ->
  P (List.nth n lsa defA) (List.nth n lsb defB).

  induction 1; intros; simpl in *.
  destruct n; try lia.
  destruct n; trivial.
  eapply IHForall2; trivial; lia.

Qed.

Theorem bvNat_Z_to_nat_eq_intToBv : forall n (z : Z),
  (0 <= z)%Z ->
  bvNat n (Z.to_nat z) = intToBv n z.
Admitted.

Theorem skipn_1_eq_tl : forall (A : Type)(ls : list A),
  skipn 1 ls = List.tl ls.

  intros.
  destruct ls; trivial.

Qed.

Theorem Forall2_tl : forall (A B : Type)(P : A -> B -> Prop) ls1 ls2,
  List.Forall2 P ls1 ls2 ->
  List.Forall2 P (List.tl ls1) (List.tl ls2).

  intros.
  inversion H; clear H; subst;
  simpl.
  econstructor.
  trivial.

Qed.

Theorem Forall2_rev : forall (A B : Type)(P : A -> B -> Prop) ls1 ls2,
  List.Forall2 P ls1 ls2 ->
  List.Forall2 P (List.rev ls1) (List.rev ls2).

  induction 1; intros; simpl in *.
  econstructor.
  eapply Forall2_app.
  eauto.
  econstructor.
  trivial.  
  econstructor.

Qed.

Theorem bvToNat_Z_to_nat_equiv : forall n x z,
  (0 <= z)%Z ->
  sbvToInt n x = z ->
  bvToNat n x = Z.to_nat z.

Admitted.

Theorem bvSShr_Z_shiftr_equiv : forall n x1 x2 y1 y2,
  Z.of_nat y1 = y2 ->
  sbvToInt _ x1 = x2 ->
  sbvToInt _ (bvSShr n x1 y1) = Z.shiftr x2 y2.
Admitted.

Theorem sbvToInt_shiftR_equiv:
  forall [n s : nat] x,
  (s >= 0)%nat ->
  sbvToInt n (shiftR n bool false x s) =
  BinInt.Z.shiftr (sbvToInt _ x) (BinInt.Z.of_nat s).

Admitted.


Theorem bvToInt_sbvToInt_range : forall n v x,
  (bvToInt n v < 2^(1 + x) ->
  -2^x <= sbvToInt _ v < 2^x)%Z.
Admitted.

Theorem bvToInt_shiftR_equiv
   : forall (n s : nat) (x : Vector.t bool n),
     (s >= 0)%nat ->
     bvToInt n (shiftR n bool false x s) =
     BinInt.Z.shiftr (bvToInt n x)
       (BinInt.Z.of_nat s).

Admitted.

Theorem bvToInt_bound : forall n v,
    (0 <= bvToInt n v < 2^(Z.of_nat n))%Z.

Admitted.

Theorem bvXor_cons : forall n x y u v,
  bvXor (S n) (Vector.cons u x) (Vector.cons v y) = 
  Vector.cons (xor u v) (bvXor _ x y).

  intros.
  reflexivity.

Qed.

Theorem bvEq_cons : forall n x y u v,
  bvEq (S n) (Vector.cons u x) (Vector.cons v y) = 
  andb (Bool.eqb u v) (bvEq _ x y).

  intros.
  reflexivity.
Qed.

Theorem intToBv_0_S : forall n,
  intToBv (S n) 0 = Vector.cons false (intToBv n 0).

 Admitted.

(*
Theorem intToBv_add_equiv_64 : forall x y,
  intToBv 64%nat (x + y) = bvAdd 64%nat (intToBv 64%nat x) (intToBv 64%nat y).

  intros.
  lia.

Qed.
*)

Theorem intToBv_add_equiv : forall n x y,
  intToBv n (x + y) = bvAdd n (intToBv n x) (intToBv n y).

Admitted.

Theorem intToBv_eq_pos : forall n x y,
  (0 <= x < 2^(Z.of_nat n))%Z ->
  (0<= y < 2^(Z.of_nat n))%Z ->
  intToBv n x = intToBv n y ->
  x = y.
Admitted.

Theorem bvToNat_lt_word : forall n x,
    (Z.of_nat (bvToNat n x)) < 2^(Z.of_nat n).
Admitted.

(*
Theorem sign_extend_equiv : forall n1 n2 z,
    (-2^(Z.of_nat n1) <= z < 2^(Z.of_nat n1)) ->
    append 
  (if sawAt (S n1) Bool (intToBv (S n1) z) 0%nat
   then ecCompl (bitvector n2) (PLogicWord n2) (ecZero (bitvector n2) (intToBv n2 0))
   else ecZero (bitvector n2) (intToBv n2 0)) (intToBv (S n1) z) = intToBv _ z.
Admitted.
*)

Theorem sbvToInt_sign_extend_equiv : forall n1 n2 x,
    sbvToInt _
  (append
     (if sawAt n1 Bool x 0%nat
      then
       ecCompl (bitvector n2) (PLogicWord n2)
         (ecZero (bitvector n2) (intToBv n2 0))
      else ecZero (bitvector n2) (intToBv n2 0)) x) = 
sbvToInt n1 x.
Admitted.

Theorem sbvToInt_0_replicate: forall n b2,
    sbvToInt n b2 = 0%Z ->
    b2 = replicate _ _ false.
Admitted.

Theorem bvNeg_replicate_0 : forall n,
    bvNeg _ (replicate n bool false) = replicate n bool false.
Admitted.

Theorem shiftR_small_nonneg : forall n1 n2 v,
  (0 <= sbvToInt _ v < 2^(Z.of_nat n2))%Z ->
  (shiftR n1 bool false v n2) = replicate n1 bool false.
Admitted.



Theorem bvSShr_all_nonneg : forall n1 v,
  (0 <= sbvToInt _ v)%Z ->
  bvSShr n1 v n1 = replicate (S n1) bool false.
Admitted.

Theorem bvNeg_1_replicate : forall n,
    bvNeg n (intToBv n 1) = replicate n bool true.
Admitted.

Theorem replicate_S_cons : forall (A : Type) n (a : A),
  replicate (S n) _ a = Vector.cons a (replicate n _ a).

  intros.
  reflexivity.

Qed.

(*
Theorem bvXor_bvSub_equiv : forall n v,
    bvXor n (replicate n bool true) v = bvSub (replicate n bool true) v.

  intros.
  Print sbbB.
  Print invB.
  Locate bvSub_eq_bvAdd_neg.
  Print bvNeg.
  Search bvSub bvAdd.

  induction n; intros; simpl in *.
  reflexivity.

  destruct (Vec_S_cons v).
  destruct H. subst.  
  rewrite replicate_S_cons.
  rewrite bvXor_cons.
  rewrite bvSub_cons.

Qed.

Theorem bvAdd_one_rollover : forall n,
  bvAdd n (intToBv n 1) (replicate n Bool true) = intToBv n 0.
Admitted.


Theorem adcB_1_carry_eq_h : forall n v,
  adcB 0 (spec.joinlsb (spec.zero n, 1%bool)) v =
  adcB 1 (spec.joinlsb (spec.zero n, 0%bool)) v.

  intros.
  destruct v.
  destruct tval.
  inversion i.

  unfold adcB.
Admitted.


Theorem adcB_1_carry_eq : forall n v, 
  (n > 0)%nat ->
  @adcB n 0 (spec.fromZ 1) v = 
  @adcB n 1 (spec.fromZ 0) v.

  intros.

  destruct n; simpl.
  lia.
Admitted.
*)

(*
  rewrite adcB_1_carry_eq_h.

  destruct v.
  destruct tval.
  simpl in *.
  inversion i.

  


  simpl in *.
  unfold spec.zero. spec.copy.
  simpl.
  simpl.

  unfold adcB.
  simpl.

  unfold intToBv.

  unfold intToBv.
  simpl.
  repeat rewrite bvToBITS_bitsToBv_id.
  unfold tuple.nil_tuple.
  simpl.
    unfold adcB.
  simpl.
  Search bvToBITS bitsToBv.

  Print spec.zero.

Qed.

*)

(* maybe use tuple.tcast and/or spec.getBit?*)
(*
Definition bitsEq (n : nat)(b1 b2 : spec.BITS n) := 
  match b1 with
  | tuple.Tuple t1 _ =>
    match b2 with
    | tuple.Tuple t2 _ => t1 = t2
    end
  end.
*)
(*
Theorem bitsToBv_cons : forall n b tval i,
  bitsToBv (tuple.Tuple (n:=S n) (tval:=b :: tval) i)  = 
  Vector.cons b (tuple.Tuple (n:=n) (tval:=b :: tval) i)
*)

Search spec.BITS.

Search spec.joinmsb.
Search spec.getBit.

(*
Theorem bitsToBv_bitsEq_mono : forall n (b1 b2 : spec.BITS n), 
  bitsEq b1 b2 -> bitsToBv b1  = bitsToBv b2.

  induction n; intros; simpl in *.
  admit.
  


  destruct b1, b2.
  destruct tval.
  destruct tval0.
  reflexivity.

  inversion i0.
  inversion i.

  destruct b1, b2.
  destruct tval.
  inversion i.
  destruct tval0.
  inversion i0.
  Search bitsToBv Vector.cons.
  
  unfold bitsToBv in *.
  simpl.
  unfold tuple.thead.
  simpl.
  Search tuple_foldl_dep.
  destruct tval0.
  

  intros.
  unfold bitsToBv.
  unfold tuple_foldl_dep.

Qed.
*)

Theorem adcB_0_1_equiv : forall n (a : spec.BITS n),
  (adcB 1 (spec.fromZ 0) a) = 
  (adcB 0 (spec.fromZ 1) a).
Admitted.

Theorem bvToBITS_z_equiv : forall n z,
  (bvToBITS (intToBv n z)) = spec.fromZ z.
Admitted.

Search tuple.tuple_of eq.

Theorem ssr_addn_comm : forall n1 n2, 
  ssrnat.addn n1 n2 = (n2 + n1)%nat.
Admitted.

(*
Theorem foldl_dep_tuple_cat : forall n1 (x : Vector.t bool n1) n2 (v : tuple.tuple_of n2 bool),
  foldl_dep bool 
    (fun n0 : Nat => tuple.tuple_of (n2 + n0) bool) 
    n1
    (fun (n0 : Nat) (bs : tuple.tuple_of (n2 + n0) bool) (b0 : bool) =>
      tuple.cons_tuple b0 bs) 
    v
    x
  =
  foldl_dep bool 
    (fun n0 : Nat => tuple.tuple_of (n2 + n0) bool) 
    n1
    (fun (n0 : Nat) (bs : tuple.tuple_of (n2 + n0) bool) (b0 : bool) =>
      tuple.cons_tuple b0 bs) 
    v
    x.

Admitted.
*)

(*
Theorem foldl_dep_tuple_cons : forall n (x : Vector.t bool n) b,
  foldl_dep bool (fun n0 : Nat => tuple.tuple_of (S n0) bool) n
  (fun (n0 : Nat) (bs : tuple.tuple_of (S n0) bool) (b0 : bool) =>
   tuple.cons_tuple b0 bs) (tuple.cons_tuple b (tuple.nil_tuple bool)) x
  =
  tuple.cons_tuple b (
  foldl_dep bool (fun n0 : Nat => tuple.tuple_of n0 bool) n
  (fun (n0 : Nat) (bs : tuple.tuple_of n0 bool) (b0 : bool) =>
   tuple.cons_tuple b0 bs) (tuple.nil_tuple bool) x).

  induction x; intros; simpl in *.
  reflexivity.

  

Qed.

Theorem bvToBITS_cons_eq : forall n (x : Vector.t bool n) b,
  bvToBITS (Vector.cons b x) =
  spec.consB b (bvToBITS x).

  intros.

  unfold spec.consB.
  unfold bvToBITS.
  simpl.
  unfold spec.joinlsb.
  unfold spec.BITS.
  simpl.
  apply foldl_dep_tuple_cons.

Qed.

*)

Theorem xorB_cons : forall n (v1 v2 : spec.BITS n) b1 b2,
  xorB (spec.consB b1 v1) (spec.consB b2 v2) = spec.consB (xorb b1 b2) (xorB v1 v2).

  intros.
  apply liftBinOpCons.
Qed.

(*

Theorem bvToBITS_xor_eq : forall n v1 v2, 
  bvToBITS (bvXor n v1 v2) = xorB (bvToBITS v1) (bvToBITS v2).

  induction n; intros; simpl in *.
  apply trivialBits.

  destruct (Vec_S_cons v1).
  destruct H.
  subst.
  destruct (Vec_S_cons v2).
  destruct H.
  subst.
  rewrite bvXor_cons.
  repeat rewrite bvToBITS_cons_eq.
  rewrite IHn.
  unfold xorB.
  rewrite liftBinOpCons.
  reflexivity.

Qed.

*)

Theorem bvToBITS_xor_eq : forall n v1 v2, 
  bvToBITS (bvXor n v1 v2) = xorB (bvToBITS v1) (bvToBITS v2).

Admitted.

Theorem bvToBITS_ones_eq : forall n,
  bvToBITS (replicate n bool true) = spec.ones n.

Admitted.

(*

Theorem bvToBITS_ones_eq : forall n,
  bvToBITS (replicate n bool true) = spec.ones n.

  induction n; intros; simpl in *.
  apply trivialBits.

  rewrite ones_decomp.
  rewrite <- IHn.
  rewrite replicate_S_cons.
  apply bvToBITS_cons_eq.

Qed.

*)


Theorem twos_complement_equiv : forall n v,
    (n > 0)%nat ->
    sbvToInt n (bvAdd n (bvXor n v (replicate n bool true)) (intToBv n 1)) = Z.opp (sbvToInt _ v).

  intros.

  rewrite <- sbvToInt_bvNeg_equiv.
  unfold bvNeg.
  f_equal.
  Local Transparent bvAdd bvSub sbbB.
  unfold bvAdd, bvSub, sbbB.
  simpl.
  f_equal.
  repeat rewrite bvToBITS_z_equiv.  
  rewrite adcB_0_1_equiv.
  rewrite addBC.
  f_equal.
  f_equal.
  rewrite <- xorBN.
  rewrite bvToBITS_xor_eq.
  f_equal.
  apply bvToBITS_ones_eq.
Qed.


Theorem sawAt_nth_order_equiv : forall (A : Type)(inh : Inhabited A)(n1 n2 : nat)(v : Vec n1 A)(ltpf : (n2 < n1)%nat),
  @sawAt n1 A inh v n2 = nth_order v ltpf.
Admitted.

Theorem shiftR_shiftR_eq : forall (A : Type)(n1 n2 len : nat)(v : Vec len A) a,
    shiftR _ _ a (shiftR _ _ a v n1) n2 = shiftR _ _ a v (n1 + n2)%nat.
Admitted.

Theorem shiftR1_eq : forall (A : Type)(len : nat)(v : Vec len A) a,
  shiftR1 _ _ a v = shiftR _ _ a v 1.
Admitted.



Theorem nth_order_shiftR_eq : forall (A : Type)(n1 n2 len : nat)(v : Vec len A) (nlt : (n2 < len)%nat)(nlt' : (n2-n1 < len)%nat) a,
  (n1 <= n2)%nat ->
  nth_order (shiftR _ _ a v n1) nlt = nth_order v nlt'.

Admitted.

Theorem nth_order_shiftR_all_eq : forall (A : Type)(n2 len : nat)(v : Vec len A) (nlt : (n2 < len)%nat)(zlt : (0 < len)%nat) a,
  nth_order (shiftR _ _ a v n2) nlt = nth_order v zlt.

Admitted.

Theorem sbvToInt_neg_bits_set : forall n wsize b2 n' (ltpf : (n' < n)%nat),
    (n' <= n - wsize)%nat ->
    (- 2 ^ Z.of_nat wsize <= sbvToInt n b2 < 0)%Z ->
    nth_order b2 ltpf = true.
Admitted.

Theorem sbvToInt_nonneg_bits_clear : forall n wsize b2 n' (ltpf : (n' < n)%nat),
    (n' <= n - wsize)%nat ->
    (0 <= sbvToInt n b2 < 2 ^ Z.of_nat wsize )%Z ->
    nth_order b2 ltpf = false.
Admitted.

Theorem sbvToInt_z_nth:
  forall [n : nat] (v : Vec n bool),
  (forall [n' : nat] (nlt : (n' < n)%nat), nth_order v nlt = false) -> sbvToInt n v = 0%Z.
Admitted.

Theorem bitsToBv_cons_eq : forall n (x : @spec.BITS n) h,
  VectorDef.cons h (bitsToBv x) =
  bitsToBv (spec.consB h x).
Admitted.

Theorem bitsEx : forall (n : nat)(v : bitvector n), 
  exists y, v = bitsToBv y.

  induction v; intros; simpl in *.
  exists (@tuple.nil_tuple Bool).
  reflexivity.

  destruct IHv.
  subst.
  exists (spec.consB h x).
  apply bitsToBv_cons_eq.

Qed.

Theorem bitsToBv_bvToBITS_id : forall (n : nat) (v : bitvector n),
       bitsToBv (bvToBITS v) = v.

  intros.
  assert (exists y, v = bitsToBv y).
  apply bitsEx.
  destruct H.
  subst.
  rewrite bvToBITS_bitsToBv_id.
  reflexivity.
  
Qed.

Theorem bvAdd_replicate_0 : forall n v,
  bvAdd _ (replicate n bool false) v = v.

  intros.
  unfold bvAdd.
  Search replicate.
  Search adcB.
  Search bvToBITS.
  Search replicate.
  rewrite rep_false_eq_int_bv.
  Search bvToBITS.
  replace (intToBv n 0) with (@bitsToBv n (spec.fromNat 0)).
  rewrite bvToBITS_bitsToBv_id.
  rewrite add0B.
  apply bitsToBv_bvToBITS_id.
  unfold intToBv.
  f_equal.
  rewrite fromNat0.
  reflexivity.
 
Qed.


Theorem bits_cons_decomp : forall n (v : spec.BITS (S n)),
  exists b, exists v',
  v = spec.consB b v'.

  intros.

  Search tuple.thead.

  exists (tuple.thead v).
  exists (tuple.behead_tuple v).
 
Admitted.

Theorem bitsToBv_eq_inv : forall n (b1 b2 : spec.BITS n),
  bitsToBv b1 = bitsToBv b2 ->
  b1 = b2.

  induction n; intros; simpl in *.
  apply trivialBits.

  destruct (bits_cons_decomp b1).
  destruct H0.
  destruct (bits_cons_decomp b2).
  destruct H1.
  subst.
  repeat rewrite <- bitsToBv_cons_eq in H.
  apply cons_inj in H.
  intuition; subst.
  f_equal.
  eauto.

Qed.

(*
Theorem bvToBits_eq_inv : forall n (b1 b2 : bitvector n),
  bvToBITS b1 = bvToBITS b2 ->
  b1 = b2.

  induction n; intros; simpl in *.
  rewrite Vec_0_nil.
  symmetry.
  rewrite Vec_0_nil.
  reflexivity.

  destruct (Vec_S_cons b1).
  destruct H0.
  destruct (Vec_S_cons b2).
  destruct H1.
  subst.
  repeat rewrite bvToBITS_cons_eq in H.
  apply tuple.splitTuple in H.
  intuition idtac; subst.
  f_equal.
  eauto.

Qed.
*)
Theorem bvToBits_eq_inv : forall n (b1 b2 : bitvector n),
  bvToBITS b1 = bvToBITS b2 ->
  b1 = b2.

Admitted.

Theorem addb_same_l : forall n (x y1 y2 : spec.BITS n),
  y1 = y2 ->
  addB x y1 = addB x y2.

  intros. subst. trivial.
Qed.

Theorem addb_same_l_if : forall n (x y1 y2 : spec.BITS n),
  (addB x y1) = (addB x y2) ->
  y1 = y2.

  intros.
  apply (@addb_same_l n (negB x)) in H.
  repeat rewrite addBA in H.
  repeat rewrite addBN in H.
  rewrite addBC in H.
  rewrite addB0 in H.
  rewrite addBC in H.
  rewrite addB0 in H.
  trivial.

Qed.

Theorem bvAdd_same_l_if : forall n x y1 y2,
  (bvAdd n x y1) = (bvAdd n x y2) ->
  y1 = y2.

  intros.
  unfold bvAdd in *.
  apply bitsToBv_eq_inv in H.
  apply addb_same_l_if in H.
  eapply bvToBits_eq_inv; eauto.

Qed.

Theorem vec_0_eq : forall (A : Type)(v1 v2 : Vector.t A 0%nat),
  v1 = v2.

  intros.
  specialize (Vec_0_nil v1); intros.
  specialize (Vec_0_nil v2); intros.
  subst.
  reflexivity.

Qed.

Theorem zipWith_cons : forall (A B C: Type)(inha : Inhabited A)(inhb : Inhabited B) f n (v1 : Vec n A)(v2 : Vec n B) a b,
  zipWith A B C f _ (Vector.cons a v1) (Vector.cons b v2) = Vector.cons (f a b) (zipWith A B C f _ v1 v2).

  intros.
  reflexivity.

Qed.

Theorem zipWith_comm : forall (A B : Type)(inha : Inhabited A) (f : A -> A -> B) n (v1 v2 : Vec n A),
  (forall a1 a2, f a1 a2 = f a2 a1) ->
  zipWith A A B f n v1 v2 = zipWith A A B f n v2 v1.

  induction n; intros; simpl in *.
  apply vec_0_eq.

  destruct (Vec_S_cons v1).
  destruct H0.
  destruct (Vec_S_cons v2).
  destruct H1.  
  subst.
  repeat rewrite zipWith_cons.
  f_equal; eauto.

Qed.

Theorem bvAnd_comm : forall n v1 v2,
    @bvAnd n v1 v2 = bvAnd v2 v1.

  intros.
  apply zipWith_comm.
  intros.
  destruct a1; destruct a2; reflexivity.

Qed.

Theorem bvAnd_replicate_0 : forall n v,
    bvAnd (replicate n bool false) v = replicate n bool false.

  intros.
  repeat rewrite rep_false_eq_int_bv.
  rewrite bvAnd_comm.
  apply bvAnd_0.

Qed.

Theorem bvAnd_bitsToBv_eq : forall n v1 v2,
  bvAnd (@bitsToBv n v1) (@bitsToBv n v2) = bitsToBv (andB v1 v2).

  induction n; intros; simpl in *.
  apply vec_0_eq.
  destruct (bits_cons_decomp v1).
  destruct H.
  destruct (bits_cons_decomp v2).
  destruct H0.
  subst.
  repeat rewrite <- bitsToBv_cons_eq.
  unfold bvAnd, andB, bvZipWith.
  rewrite liftBinOpCons.
  rewrite zipWith_cons.
  repeat rewrite <- bitsToBv_cons_eq.
  f_equal.
  eapply IHn.
  
Qed.

Theorem bvAnd_replicate_1 : forall n v,
  bvAnd (replicate n _ true) v = v.

  induction v; intros; simpl in *.
  apply vec_0_eq.
  rewrite replicate_S_cons.
  unfold bvAnd, bvZipWith.
  rewrite zipWith_cons.
  simpl.
  f_equal.
  eapply IHv.
Qed.


Theorem vec_split_append_eq : forall (A : Type) n1 n2  (v : Vec (n1 + n2) A),
  Vector.append (fst (Vector.splitat n1 v)) (snd (splitat n1 v)) = v.
Admitted.

Theorem nth_order_eq_impl_eq : forall (A : Type) n (v1 v2 : Vec n A),
  (forall n1 (n1lt : (n1 < n)%nat), nth_order v1 n1lt = nth_order v2 n1lt) ->
  v1 = v2.

  intros.
  apply Vector.eq_nth_iff.
  intros.
  subst.
  unfold nth_order in *.
  rewrite <- (@Fin.of_nat_to_nat_inv _ p2).
  eapply H.
Qed.


Theorem bvSShr_all_neg : forall n1 v,
  (sbvToInt _ v < 0)%Z ->
  (bvSShr n1 v n1) = replicate (S n1) bool true.

Admitted.

Theorem toList_append_equiv : forall A (inh : Inhabited A) n m (v1 : Vec n A)(v2 : Vec m A),
  to_list (SAWCorePrelude.append v1 v2) = 
  List.app (to_list v1) (to_list v2).

  induction n; intros; simpl in *.
  
  rewrite (Vec_0_nil v1).
  simpl.
  rewrite append_nil_eq.
  reflexivity.

  destruct (Vec_S_cons v1). destruct H. subst.
  rewrite append_cons.
  repeat rewrite to_list_cons.
  rewrite IHn.
  simpl.
  reflexivity.

Qed.


Theorem to_list_ecCAt_equiv : forall (s1 s2 : nat) t (inh : Inhabited t)(a : Vec s1 t) (b : Vec s2 t),
  (to_list (ecCat (TCNum s1) (TCNum s2) t a b)) = (List.app (to_list a) (to_list b)).

  intros.
  rewrite ecCat_equiv.
  apply toList_append_equiv.

Qed.

Theorem shiftout_cons : forall (A : Type)(a : A) n (v : Vec (S n) A),
  shiftout (Vector.cons a v) = Vector.cons a (shiftout v).

  intros.
  reflexivity.

Qed.

Theorem shiftR1_false_0 : forall n1, 
    (shiftR1 n1 bool false (replicate n1 bool false)) = (replicate n1 bool false).

  induction n1; intros; simpl in *.
  apply vec_0_eq.

  repeat rewrite replicate_S_cons.
  unfold shiftR1.
  rewrite shiftout_cons.
  f_equal.
  eapply IHn1.

Qed.

Theorem shiftR_false_0 : forall n2 n1, 
    (shiftR n1 bool false (replicate n1 bool false) n2) = (replicate n1 bool false).

  induction n2; intros; simpl in *; trivial.
  rewrite IHn2.
  eapply shiftR1_false_0.

Qed.

Theorem eq_if_to_list_eq : forall (A : Type) n (v1 v2 : Vector.t A n),
  to_list v1 = to_list v2 ->
  v1 = v2.

  induction n; intros; simpl in *.
  eapply vec_0_eq.
  destruct (Vec_S_cons v1). destruct H0. subst.
  destruct (Vec_S_cons v2). destruct H0. subst.
  repeat rewrite to_list_cons in H.
  inversion H; clear H; subst.
  f_equal.
  eapply IHn.
  eauto.

Qed.

Theorem toNegZ_nonneg : 
  forall n (b : spec.BITS n),
  0 <= spec.toNegZ b.

  induction n; intros; simpl in *.
  destruct b.
  destruct tval.
  unfold spec.toNegZ.
  simpl.
  lia.
  inversion i.

  destruct (bits_cons_decomp b). destruct H. subst.
  unfold spec.toNegZ in *.
  simpl in *.
  destruct x.
  specialize (IHn x0).
  lia.
  specialize (IHn x0).
  lia.

Qed.

(*

Theorem msb_hd_eq : forall n (v : bitvector (S n)),
  spec.msb (bvToBITS v) = Vector.hd v.

  intros; simpl in *.
  destruct (Vec_S_cons v). destruct H. subst.
  simpl.
  Print spec.msb.
  unfold bvToBITS.
  Search foldl_dep Vector.cons.
  simpl.

Qed.

Theorem sbvToInt_nonneg_sign_bit_clear:
  forall [n : nat] (b2 : bitvector n) (ltpf : (0 < n)%nat), 0 <= sbvToInt n b2 -> nth_order b2 ltpf = 0%bool.

  intros.
  unfold sbvToInt in *.
  destruct b2; simpl in *.
  lia.
  unfold spec.toZ in *.
  case_eq (spec.splitmsb (bvToBITS (VectorDef.cons h b2))); intros.
  rewrite H0 in H.
  destruct b.
  specialize (toNegZ_nonneg b0); intros.
  lia.

  Search spec.splitmsb.
  rewrite splitmsb_msb in H0.
  Search spec.splitmsb.
  Print spec.toNegZ.
  admit.
  Search spec.toNegZ.
  Check spec.toNegZ.

  induction b2; intros.
  lia.

  simpl in *.
  unfold nth_order.
  simpl.
  unfold spec.toZ in *.
  unfold bvToBITS in *.
  simpl.

Qed.
*)

Theorem replicate_repeat_eq : forall n (A  : Type)(v : A),
  repeat v n = to_list (replicate n A v).

  induction n; intros; simpl in *.
  rewrite (Vec_0_nil (replicate 0%nat A v)).
  reflexivity.
  rewrite replicate_S_cons.
  rewrite to_list_cons.
  f_equal.
  eauto.

Qed.

Definition shiftout_ls (A : Type)(ls : list A):=
  (firstn (pred (length ls)) ls).

Definition shiftR1_ls (A : Type)(a : A)(ls : list A) :=
  shiftout_ls (cons a ls).

Theorem shiftR1_ls_equiv : forall (A : Type) n  (v : Vector.t A n) a,
  to_list (shiftR1 n A a v) = shiftR1_ls a (to_list v).

  induction v; intros; simpl in *.
  reflexivity.

  unfold shiftR1 in *.
  rewrite shiftout_cons.
  rewrite to_list_cons.
  rewrite IHv.
  reflexivity.

Qed.

Definition shiftR_ls (A : Type) (x : A) (v :list A) (i : nat) := 
  ssrnat.iter i (shiftR1_ls x) v.

Theorem shiftR_ls_equiv : forall (A : Type) n2  n (v : Vector.t A n) a,
  to_list (shiftR n A a v n2) = shiftR_ls a (to_list v) n2.

  induction n2; intros; simpl in *; trivial.

  rewrite shiftR1_ls_equiv.
  rewrite IHn2.
  reflexivity.

Qed.

Theorem shiftR1_ls_length : forall (A: Type) a (ls : list A),
  length (shiftR1_ls a ls) = length ls.

  intros.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite firstn_length.
  simpl.
  lia.

Qed.

Theorem shiftR_ls_length : forall (A: Type) a n (ls : list A),
  length (shiftR_ls a ls n) = length ls.

  induction n; intros; simpl in *; trivial.
  rewrite shiftR1_ls_length.
  eapply IHn.

Qed.

Theorem firstn_app_1 : forall (A : Type)(ls1 ls2 : list A) n,
  (n <= length ls1)%nat -> 
  firstn n (ls1 ++ ls2) = firstn n ls1.

  induction ls1; intros; destruct n; simpl in *; trivial.
  lia.
  f_equal.
  eapply IHls1.
  lia.

Qed.

Theorem shiftR1_ls_firstn : forall (A : Type) n (ls : list A) a,
  (n <= length ls)%nat ->
  firstn n (shiftR1_ls a ls) = shiftR1_ls a (firstn n ls).

  intros. 
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite firstn_length.
  rewrite Nat.min_l; trivial.
  rewrite firstn_firstn.
  rewrite Nat.min_l; trivial.
  destruct n.
  simpl in *; trivial.
  repeat rewrite firstn_cons.
  f_equal.
  rewrite firstn_firstn.
  rewrite Nat.min_l; trivial; lia.

Qed.


Theorem shiftR_ls_firstn : forall (A : Type) n2 n (ls : list A) a,
  (n <= length ls)%nat ->
  firstn n (shiftR_ls a ls n2) = shiftR_ls a (firstn n ls) n2.

  induction n2; intros; simpl in *; trivial.
  rewrite shiftR1_ls_firstn.
  rewrite IHn2.
  reflexivity.
  trivial.
  rewrite shiftR_ls_length.
  trivial.

Qed.


Theorem shiftR_ls_eq_repeat : forall (A : Type) n (ls : list A) a,
  (n <= length ls)%nat -> 
  shiftR_ls a ls n = (repeat a n) ++ (firstn (length ls - n)%nat ls).

  induction n; intros; simpl in *.
  rewrite Nat.sub_0_r.
  rewrite firstn_all. reflexivity.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite shiftR_ls_length.

  destruct ls using rev_ind.
  simpl in *. lia.
  rewrite app_length.
  simpl.
  rewrite plus_comm.
  simpl.
  f_equal.
  rewrite firstn_app_1; try lia.
  rewrite <- IHn.
  rewrite shiftR_ls_firstn.
  rewrite firstn_app_1; try lia.
  rewrite firstn_all.
  reflexivity.
  rewrite app_length.
  lia.
  rewrite app_length in H.
  simpl in *. lia.
Qed.

Definition joinlsb_ls(pair : (list bool) * bool) := (snd pair) :: (fst pair).

(*
This is not right---list is reversed
Definition bvToBITS_ls(n : nat)(v : Vec n bool) := to_list v.
*)

Theorem foldl_dep_conv_const_equiv : forall (A : Type) n (v : Vec n A)
  (B1 : nat -> Type)(B2 : Type)
  (conv : forall n, B1 n -> B2) b1
  (f1 : forall (n : nat), B1 n -> A -> B1 (S n))(f2 : B2 -> A -> B2),
  (forall n b a, conv _ (f1 n b a) = f2 (conv _ b) a) ->
  conv _ (foldl_dep A B1 n f1 b1 v) = foldl_dep A (fun _ => B2) n (fun _ => f2) (conv _ b1) v.

  induction v; intros; simpl in *.
  trivial.
  specialize (IHv (fun n => B1 (S n)) B2).
  specialize (IHv (fun n => conv (S n))).
  specialize (IHv (f1 _ b1 h)).
  
  specialize (IHv (fun n0 : nat => f1 (S n0)) f2).
  simpl in *.
  unfold Nat in *.
  rewrite IHv.
  rewrite H.
  reflexivity.

  intros.
  eapply H.

Qed.

Theorem fold_dep_ls_equiv : forall (A : Type) n (v : Vec n A)
  (B : Type)(f : B -> A -> B) b,
  foldl_dep A (fun _ => B) n (fun _ => f) b v = fold_left f (to_list v) b.

  induction v; intros.
  simpl in *.
  trivial.
  rewrite to_list_cons.
  simpl.
  rewrite IHv.
  reflexivity.

Qed.


Definition bvToBITS_ls_0 n (bs : Vec n bool) :=
  fold_left (fun (bs : list bool) (b : bool) => b ::bs)(to_list  bs) nil.


Theorem bvToBITS_ls_0_equiv : forall n (bs : Vec n bool),
  tuple.tval (bvToBITS bs) = bvToBITS_ls_0 bs.

  intros.
  unfold bvToBITS, bvToBITS_ls_0.
  rewrite <- fold_dep_ls_equiv.
  specialize (foldl_dep_conv_const_equiv bs spec.BITS (fun n b => tuple.tval b)); intros.
  simpl in *.
  eapply H.
  intros.
  simpl.
  reflexivity.
Qed.

Definition bvToBITS_ls n (bs : Vec n bool) := rev (to_list bs).

Theorem bvToBITS_ls_0_equiv' : forall n (bs : Vec n bool),
  bvToBITS_ls_0 bs = bvToBITS_ls bs.

  intros. 
  unfold bvToBITS_ls_0, bvToBITS_ls.
  generalize (to_list bs) as ls.
  induction ls using rev_ind; intros; simpl in *.
  reflexivity.

  rewrite rev_app_distr.
  rewrite fold_left_app.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem bvToBITS_ls_equiv : forall n (bs : Vec n bool),
  tuple.tval (bvToBITS bs) = bvToBITS_ls bs.

  intros.
  rewrite bvToBITS_ls_0_equiv.
  rewrite bvToBITS_ls_0_equiv'.
  reflexivity.
Qed.

Definition splitmsb_ls(ls : list bool):=
  match (seq.rev ls) with
  | nil => (false, nil)
  | b :: ls' => (b, seq.rev ls')
  end.

Definition toPosZ_ls bs :=
  seq.foldr (fun (b : bool) (z : Z) => if b then Z.succ (Z.double z) else Z.double z) 0 bs.

Definition toNegZ_ls bs :=
  seq.foldr (fun (b : bool) (z : Z) => if b then Z.double z else Z.succ (Z.double z)) 0 bs.

Definition toZ_ls bs :=
  let (b, bs') := splitmsb_ls bs in if b then - Z.succ (toNegZ_ls bs') else toPosZ_ls bs'.


Definition sbvToInt_ls n (v : Vec n bool) :=
  (match n as n0 return (bitvector n0 -> Z) with
    | 0%nat => fun _ : bitvector 0 => 0
    | S n0 => fun b0 : bitvector (S n0) => toZ_ls (bvToBITS_ls b0)
  end) v.


(*
Theorem bvToBITS_ls_eq : forall n (v : Vec n bool) n2 (bs : spec.BITS n2),
  tuple.tval
  (foldl_dep bool (fun n0 => spec.BITS (n0 + n2)) n (fun (n0 : Nat) (bs : spec.BITS (n0 + n2)) (b : bool) => spec.joinlsb (bs, b)) 
     bs v) = seq.rev (to_list v) ++ (tuple.tval bs).


Theorem bvToBITS_ls_eq_h : forall n (v : Vec n bool) n2 (bs : spec.BITS n2),
  tuple.tval
  (foldl_dep bool (fun n0 => spec.BITS (n0 + n2)) n (fun (n0 : Nat) (bs : spec.BITS (n0 + n2)) (b : bool) => spec.joinlsb (bs, b)) 
     bs v) = seq.rev (to_list v) ++ (tuple.tval bs).

  induction v; intros; simpl in *.
  reflexivity.
  rewrite to_list_cons.
  

  Check ((spec.joinlsb (tuple.nil_tuple bool, h))).
  Check (foldl_dep bool (fun n0 : Nat => spec.BITS (S n0)) n
     (fun (n0 : Nat) (bs : spec.BITS (S n0)) (b : bool) => spec.joinlsb (bs, b)) (spec.joinlsb (tuple.nil_tuple bool, h)) v).
  Check (foldl_dep bool (fun n0 : Nat => spec.BITS (S n0)) n
     (fun (n0 : Nat) (bs : spec.BITS (S n0)) (b : bool) => spec.joinlsb (bs, b)) ).
  Check (foldl_dep bool (fun n0 : Nat => spec.BITS (S n0))).

Qed.
*)

(*

Theorem foldl_dep_ls_equiv : forall (A : Type) n (v : Vec n A) (B1 : Nat->Type) b1 (f1 : forall (n : Nat), B1 n -> A -> B1 (S n))
    (B2 : Type)(convB : forall (n : Nat), B1 n -> B2)(f2 : B2 -> A -> B2), 
    (forall n (b : B1 n) a, convB _ (f1 _ b a) = f2 (convB _ b) a) ->
    convB _ (foldl_dep A B1 n f1 b1 v) = fold_left f2 (to_list v) (convB _ b1).

  induction v; intros. simpl in *.
  reflexivity.

  rewrite to_list_cons.
  simpl.
  rewrite <- H.
  rewrite <- IHv.

Qed.


Theorem foldl_dep_BITS_foldl_eq : forall n v (f1 : forall n, spec.BITS n -> bool -> spec.BITS (S n)) f2 acc,
  (forall n (bs : spec.BITS n) (b : bool), tuple.tval (f1 n bs b) = f2 (tuple.tval bs) b) ->
  tuple.tval (foldl_dep bool spec.BITS n f1 acc v) =
  fold_left f2 (to_list v)  (tuple.tval acc).

  induction v; intros; simpl in *.
  reflexivity.

  

  unfold to_list.
  unfold fold_left.
  simpl.
  Search to_list VectorDef.nil.
  reflexivity.
  

Qed.
  

Theorem bvToBITS_ls_eq : forall n (v : Vec n bool),
 tuple.tval (bvToBITS v) = seq.rev (to_list v).

  intros.
  unfold bvToBITS.
  Print foldl_dep.



  induction v; intros; simpl in *.
  reflexivity.

  Search seq.rev.

Qed.

Theorem bvToBITS_cons_eq : forall n (v : Vec n bool) h,
 tuple.tval (bvToBITS (VectorDef.cons h v)) = tuple.tval (bvToBITS v) ++ [h].

  induction v; intros; simpl in *; trivial.

  rewrite IHv.

  unfold bvToBITS.

Qed.

Theorem bvToBITS_ls_equiv : forall n (v : Vec n bool),
  bvToBITS_ls v = (tuple.tval (bvToBITS v)).

  intros.
  induction v; intros; simpl in *.
  reflexivity.

  unfold bvToBITS_ls in *.
  rewrite to_list_cons.
  rewrite IHv.
  rewrite bvToBITS_cons_eq.
  simpl.
  reflexivity.

Qed.
*)

Theorem splitmsb_ls_eq : forall n (b : spec.BITS (S n)),
  splitmsb_ls (tuple.tval b)  = 
    let p :=
      (spec.splitmsb b) in (fst p, (tuple.tval (snd p))).

  intros.
  remember (spec.splitmsb b) as z.
  destruct z.
  symmetry in Heqz.
  apply splitmsb_rev in Heqz.
  simpl.
  unfold splitmsb_ls.
  rewrite Heqz.
  rewrite seq.revK.
  reflexivity.
Qed.

Theorem toZ_ls_eq : forall n (b : spec.BITS (S n)),
  toZ_ls (tuple.tval b) = spec.toZ b.

  intros.
  unfold toZ_ls, spec.toZ.
  rewrite splitmsb_ls_eq.
  remember (spec.splitmsb b) as z.
  destruct z.
  simpl.
  destruct b0.
  reflexivity.
  reflexivity.

Qed.

Theorem sbvToInt_ls_equiv : forall n (v : Vec n bool),
  sbvToInt_ls v = sbvToInt n v.

  intros.
  destruct n; simpl in *; trivial.
  rewrite <- toZ_ls_eq.
  rewrite bvToBITS_ls_equiv.
  reflexivity.

Qed.

Theorem seq_rev_eq : forall (A : Type)(ls : list A),
  seq.rev ls = rev ls.

  induction ls; intros; simpl in *; trivial.
  rewrite <- IHls.
  rewrite seq.rev_cons.
  rewrite <- seq.cats1.
  reflexivity.

Qed.

Theorem toNegZ_ls_nonneg : forall ls,
  0 <= toNegZ_ls ls.

  induction ls; intros; simpl in *.
  lia.
  destruct a; simpl in *; lia.

Qed.

Theorem nonneg_sign_bit_clear :  forall n v h,
  0 <= sbvToInt (S n) (VectorDef.cons h v) ->
  h = false.

  intros. 
  rewrite <- sbvToInt_ls_equiv in *.
  simpl in *.
  unfold bvToBITS_ls in *.
  rewrite to_list_cons in H.
  simpl in *.
  
  unfold toZ_ls in *.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_app_distr in H.
  rewrite rev_involutive in *.
  simpl in *.
  destruct h; simpl in *; trivial.
  match goal with 
  | [H: 0 <= - Z.succ (toNegZ_ls ?a) |- _] =>
    remember a as z
  end.
  specialize (toNegZ_ls_nonneg z); intros.
  lia.
Qed.


Theorem shiftR_all_nonneg : forall n1 v,
  n1 <> O ->
  (0 <= sbvToInt _ v)%Z ->
  (shiftR n1 bool false v (pred n1)) = replicate n1 bool false.

  intros.
  apply eq_if_to_list_eq.
  rewrite <- replicate_repeat_eq.
  rewrite shiftR_ls_equiv.
  rewrite shiftR_ls_eq_repeat.
  match goal with 
  | [|- context[ (?a - ?b)%nat]] =>
  replace (a - b)%nat with 1%nat
  end.
  destruct v; simpl; trivial.
  erewrite (nonneg_sign_bit_clear _ h); eauto.
  replace [false] with (repeat false 1%nat); trivial.
  rewrite <- repeat_app.
  rewrite plus_comm.
  trivial.
  rewrite to_list_length.
  lia.
  rewrite to_list_length.
  lia.

Qed.

Theorem neg_sign_bit_set :  forall n v h,
  sbvToInt (S n) (VectorDef.cons h v) < 0 ->
  h = true.

Admitted.

Definition zero_ls n := repeat false n.


Fixpoint fromPosZ_ls n z :=
  match n with
    | 0%nat => nil
    | S n0 => joinlsb_ls (fromPosZ_ls n0 (Z.div2 z), negb (Z.even z))
  end.

Fixpoint fromNegZ_ls n z :=
  match n with
    | 0%nat => nil
    | S n0 => joinlsb_ls (fromNegZ_ls n0 (Z.div2 z), Z.even z)
  end.

Definition fromZ_ls n z :=
  match z with
     | 0 => zero_ls n
     | Z.pos _ => fromPosZ_ls n z
     | Z.neg _ => fromNegZ_ls n (Z.pred (- z))
   end.


Definition bitsToBv_ls (ls : list bool) := rev ls.

Definition bitsToBv_ls_0 size := 
tuple_foldl_dep bool (fun n : Nat => list bool) size
  (fun (n : Nat) ls (b : bool) => b::ls) (@nil bool).

Theorem tuple_S_ex : forall (A : Type) n (t : tuple.tuple_of (S n) A),
  exists a (t' : tuple.tuple_of n A),
  t = tuple.cons_tuple a t'.

  intros.
  exists (tuple.thead t).
  exists (tuple.behead_tuple t).
  apply tuple.tuple_eta.

Qed.

Theorem tuple_head_cons : forall (A: Type) n x (x0 : tuple.tuple_of n A),
  (tuple.thead (tuple.cons_tuple x x0)) = x.

  intros.
  apply tuple.theadCons.

Qed.

Theorem tuple_behead_cons : forall (A: Type) n x (x0 : tuple.tuple_of n A),
  (tuple.behead_tuple (tuple.cons_tuple x x0)) = x0.

  intros.
  apply tuple.beheadCons.

Qed.

Theorem tuple_tval_cons : forall (A: Type) n x (x0 : tuple.tuple_of n A),
  (tuple.tval (tuple.cons_tuple x x0)) = x :: (tuple.tval x0).

  intros.
  reflexivity.

Qed.

Theorem tuple_foldl_dep_conv_const_equiv : forall (A : Type) n (v : tuple.tuple_of n A)
  (B1 : nat -> Type)(B2 : Type)
  (conv : forall n, B1 n -> B2) b1
  (f1 : forall (n : nat), B1 n -> A -> B1 (S n))(f2 : B2 -> A -> B2),
  (forall n b a, conv _ (f1 n b a) = f2 (conv _ b) a) ->
  conv _ (tuple_foldl_dep A B1 n f1 b1 v) = tuple_foldl_dep A (fun _ => B2) n (fun _ => f2) (conv _ b1) v.

  induction n; intros; simpl in *; trivial.
  destruct (tuple_S_ex v).
  destruct H0.
  subst.
  
  specialize (IHn x0).
  specialize (IHn (fun n => B1 (S n)) B2).
  specialize (IHn (fun n => conv (S n))).
  specialize (IHn (f1 _ b1 x)).
  
  specialize (IHn (fun n0 : nat => f1 (S n0)) f2).
  simpl in *.
  unfold Nat in *.
  rewrite tuple_head_cons.
  rewrite tuple_behead_cons.
  rewrite IHn.
  rewrite H.
  reflexivity.

  intros.
  eapply H.

Qed.

Theorem tuple_fold_dep_ls_equiv : forall (A : Type) n (v : tuple.tuple_of n A)
  (B : Type)(f : B -> A -> B) b,
  tuple_foldl_dep A (fun _ => B) n (fun _ => f) b v = fold_left f (tuple.tval v) b.

  induction n; intros.
  simpl in *.
  destruct v.
  destruct tval; simpl in *; trivial.
  inversion i.

  destruct (tuple_S_ex v).
  destruct H.
  subst.
  simpl.
  rewrite tuple_behead_cons.
  rewrite tuple_head_cons.
  rewrite IHn.
  reflexivity.

Qed.

Theorem bitsToBv_ls_0_eq : forall n (bs : spec.BITS n),
  bitsToBv_ls_0 bs = to_list (bitsToBv bs).

  intros.
  symmetry.
  unfold bitsToBv_ls_0, bitsToBv.
  specialize (tuple_foldl_dep_conv_const_equiv bs (Vector.t bool) (@to_list bool)); intros.
  simpl in *.
  erewrite H.
  replace (to_list (Vector.nil Bool)) with (@nil bool).
  reflexivity.
  reflexivity.
  intros. simpl.
  rewrite to_list_cons.
  reflexivity.

Qed.

Theorem bitsToBv_ls_eq : forall n (bs : spec.BITS n),
  bitsToBv_ls (tuple.tval bs) = to_list (bitsToBv bs).

  intros.
  rewrite <- bitsToBv_ls_0_eq.

  unfold bitsToBv_ls_0, bitsToBv_ls.
  rewrite tuple_fold_dep_ls_equiv.
  generalize (tuple.tval bs) as ls.
  induction ls using rev_ind; intros; simpl in *; trivial.
  rewrite rev_app_distr.
  simpl.
  rewrite IHls.
  rewrite fold_left_app.
  simpl.
  reflexivity.

Qed.

Definition intToBv_ls n z:=
  bitsToBv_ls (fromZ_ls n z).


Theorem tuple_nseq_ls_eq : forall n (A : Type) (a: A), 
  repeat a n = tuple.tval (tuple.nseq_tuple n a).

  induction n; intros; simpl in *; trivial.

  f_equal; eauto.

Qed.

Theorem zero_ls_eq : forall n,
  zero_ls n = tuple.tval (spec.zero n).

  intros.
  eapply tuple_nseq_ls_eq.
Qed.

Theorem fromPosZ_ls_eq : forall n z,
  fromPosZ_ls n z = tuple.tval (@spec.fromPosZ n z).

  induction n; intros; simpl in *; trivial.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem fromNegZ_ls_eq : forall n z,
  fromNegZ_ls n z = tuple.tval (@spec.fromNegZ n z).

  induction n; intros; simpl in *; trivial.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem fromZ_ls_eq : forall n z,
  fromZ_ls n z = tuple.tval (@spec.fromZ n z).

  intros.
  unfold fromZ_ls, spec.fromZ.
  destruct z.
  apply zero_ls_eq.
  apply fromPosZ_ls_eq.
  apply fromNegZ_ls_eq.

Qed.

Theorem intToBv_ls_eq : forall n z,
  intToBv_ls n z = to_list (intToBv n z).

  intros.
  unfold intToBv, intToBv_ls.
  rewrite <- bitsToBv_ls_eq.
  f_equal.
  apply fromZ_ls_eq.

Qed.

Theorem fromPosZ_ls_0_eq : forall n,
  fromPosZ_ls n 0 = repeat 0%bool n.

  induction n; intros; simpl in *; trivial.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem fromZ_ls_1_eq :  forall n,
  fromZ_ls (S n) 1 = true :: repeat false n.

  intros.
  unfold fromZ_ls.
  simpl.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  apply fromPosZ_ls_0_eq.

Qed.

Theorem repeat_S_rev : forall (A : Type) n (a : A),
  repeat a (S n) = (repeat a n) ++ [a].

  induction n; intros; simpl in *; trivial.
  f_equal.
  eauto.

Qed.

Theorem rev_repeat_id : forall (A : Type) n (a : A),
  rev (repeat a n) = repeat a n.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  destruct n.
  simpl in *; trivial.
  rewrite repeat_S_rev at 2.
  simpl.
  reflexivity.

Qed.

Theorem intToBv_1_to_list_eq : forall n, 
  to_list (intToBv (S n) 1) = repeat 0%bool n ++ [true].

  intros.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls.
  unfold bitsToBv_ls.
  rewrite fromZ_ls_1_eq.
  simpl.
  rewrite rev_repeat_id.
  reflexivity.

Qed.

Theorem shiftR_all_neg : forall n1 v,
  n1 <> O ->
  (sbvToInt _ v < 0)%Z ->
  (shiftR n1 bool false v (pred n1)) = intToBv _ 1.

  intros.
  apply eq_if_to_list_eq.
  rewrite shiftR_ls_equiv.
  destruct v; simpl; trivial.
  rewrite intToBv_1_to_list_eq.  
  rewrite shiftR_ls_eq_repeat.
  match goal with 
  | [|- context[ (?a - ?b)%nat]] =>
  replace (a - b)%nat with 1%nat
  end.
 
  erewrite (neg_sign_bit_set _ h); eauto.
  rewrite to_list_length.
  lia.
  rewrite to_list_length.
  lia.

Qed.

Theorem intToBv_0_eq_replicate : forall n,
    intToBv n 0 = replicate n bool false.

  intros.
  apply eq_if_to_list_eq.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls.
  simpl.
  unfold bitsToBv_ls, zero_ls.
  rewrite rev_repeat_id.
  rewrite replicate_repeat_eq.
  reflexivity.

Qed.


Definition shiftin_ls(A : Type) a (ls : list A) :=
  ls ++ [a].

Definition shiftL1_ls (A : Type) (a : A) (ls : list A) :=
  tl (shiftin_ls a ls).

Definition shiftL_ls (A : Type) (x : A) (v : list A) (i : nat) := ssrnat.iter i (shiftL1_ls x) v.

Theorem to_list_tl_eq : forall (A : Type) n (ls : Vec (S n) A),
  to_list (Vector.tl ls) = tl (to_list ls).

  intros.
  destruct (Vec_S_cons ls).
  destruct H.
  subst.
  reflexivity.

Qed.

Theorem shiftin_ls_eq : forall n (A : Type) a (ls : Vec n A),
  to_list (shiftin a ls) = shiftin_ls a (to_list ls).

  intros.
  induction ls; intros; simpl in *.
  rewrite to_list_cons.
  reflexivity.

  rewrite to_list_cons.
  rewrite IHls.
  unfold shiftin_ls.
  rewrite to_list_cons.
  rewrite app_comm_cons.
  reflexivity.

Qed.

Theorem shiftL1_ls_eq : forall n (A : Type) a (ls : Vec n A),
  to_list (shiftL1 n A a ls) = shiftL1_ls a (to_list ls).

  intros.
  unfold shiftL1, shiftL1_ls.
  rewrite to_list_tl_eq.
  f_equal.
  apply shiftin_ls_eq.
  
Qed.


Theorem shiftL_to_list_eq : forall n n1 (A : Type)(a : A)(ls : Vec n A),
  to_list (shiftL n A a ls n1) = shiftL_ls a (to_list ls) n1.

  induction n1; intros; simpl in *; trivial.
  rewrite shiftL1_ls_eq.
  f_equal.
  eapply IHn1.

Qed.

(*

Theorem rev_shiftL_ls_eq_h : forall (A : Type) n1 n2 n (a b : A),
  (n < n1)%nat ->
  rev (shiftL_ls a (repeat a n1 ++ [b] ++ repeat a n2) n) = shiftR_ls a (repeat a n2 ++ b:: (repeat a n1))  n.

  induction n; intros; simpl in *.
  rewrite rev_app_distr.
  simpl.
  rewrite <- app_assoc.
  simpl.
  repeat rewrite rev_repeat_id.
  reflexivity.

  

  Search repeat rev.
  rewrite repeat_rev_eq.
  reflexivity.

Qed.

*)


(*

Theorem toZ_ls_shiftR_ls_eq_h : forall s n1 n2 a b,
  (s < n2)%nat -> 
  toZ_ls (shiftR_ls a (repeat a n1 ++ b :: repeat a n2) s) =  Z.shiftl (toZ_ls (repeat a n1 ++ b :: repeat a n2)) (Z.of_nat s).

  induction s; intros.
  simpl in *.
  reflexivity.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  rewrite <- (Z.shiftl_shiftl _ (Z.of_nat s) 1).
  rewrite <- IHs.
  simpl.
  Search Z.shiftl.

  Search toZ_ls shiftR1_ls.
  

Qed.
*)

Theorem shiftR1_ls_comm: forall (A : Type) (a : A) ls n1,
  shiftR1_ls a (shiftR_ls a ls n1) = shiftR_ls a (shiftR1_ls a ls) n1.

  induction n1; intros; simpl in *; trivial.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem shiftR1_app_repeat_eq : forall n1 (A : Type)(a b : A) ls,
  (n1 > 0)%nat ->
  shiftR1_ls a (ls ++ repeat b n1) = (a :: ls ++ repeat b (pred n1)).

  intros.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite app_length. 

  destruct n1.
  simpl in *; lia.

  rewrite repeat_S_rev at 2.
  simpl.
  rewrite plus_comm.
  simpl.
  f_equal.
  rewrite plus_comm.
  rewrite app_assoc.
  rewrite firstn_app_1.
  rewrite <- app_length.
  apply firstn_all.
  rewrite app_length.
  lia.

Qed.

Theorem shiftout_ls_app_rev : forall (A : Type)(ls : list A) a,
  shiftout_ls (ls ++ [a]) = ls.

  intros.
  unfold shiftout_ls.
  rewrite app_length.
  rewrite plus_comm.
  simpl.
  rewrite firstn_app_1.
  apply firstn_all.
  lia.

Qed.

Theorem splitmsb_ls_app_eq : forall ls a,
  splitmsb_ls (ls ++ [a])  = (a, ls).

  intros.
  unfold splitmsb_ls.
  rewrite seq_rev_eq.
  rewrite rev_app_distr.
  simpl.
  rewrite seq_rev_eq.
  rewrite rev_involutive.
  reflexivity.

Qed.

Theorem toPosZ_app_0_eq : forall ls,
  toPosZ_ls (ls ++ [0%bool]) = toPosZ_ls ls.

  induction ls; intros; simpl in *; trivial.
  destruct a.
  rewrite IHls.
  reflexivity.
  rewrite IHls.
  reflexivity.

Qed.

Theorem toPosZ_app_repeat_0_eq : forall n ls,
  toPosZ_ls (ls ++ (repeat false n)) = toPosZ_ls ls.

  induction n; intros; simpl in *.
  rewrite app_nil_r.
  reflexivity.
  replace (ls ++ 0%bool :: repeat 0%bool n)  with ((ls ++ [false]) ++ repeat 0%bool n).
  rewrite IHn.
  apply toPosZ_app_0_eq.
  rewrite <-  app_assoc.
  reflexivity.

Qed.


Theorem toPosZ_cons_0_eq : forall ls,
  toPosZ_ls (0%bool :: ls) = Z.double (toPosZ_ls ls).

  reflexivity.
Qed.

Theorem toZ_ls_shiftR1_ls_eq : forall ls,
  (length ls > 1)%nat ->
  last ls false = false ->
  last (removelast ls) false = false ->
  toZ_ls (shiftR1_ls false ls) = Z.shiftl (toZ_ls ls ) 1.

  destruct ls using rev_ind; intros; simpl in *.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  reflexivity.

  rewrite last_last in H0.
  subst.

  unfold shiftR1_ls.
  rewrite (app_comm_cons).
  rewrite shiftout_ls_app_rev.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  
  destruct ls using rev_ind.
  simpl in *.
  lia.

  rewrite app_comm_cons.
  rewrite splitmsb_ls_app_eq.
  rewrite removelast_last in H1.
  rewrite last_last in H1.
  subst.
  rewrite toPosZ_app_0_eq.
  rewrite toPosZ_cons_0_eq.
  remember (toPosZ_ls ls) as z.

  destruct z;
  lia.

Qed.

Theorem last_app_2 : forall (A : Type)(ls1 ls2 : list A) a,
  (length ls2 > 0)%nat ->
  last (ls1 ++ ls2) a = last ls2 a.


  intros.
  destruct ls2 using rev_ind.
  simpl in *.
  lia.

  rewrite app_assoc.
  rewrite last_last.
  rewrite last_last.
  reflexivity.

Qed.

Theorem last_repeat_eq : forall n (A : Type) (a : A),
  last (repeat a n) a = a.

  induction n; intros; simpl in *.
  trivial.
  rewrite IHn.
  destruct (repeat a n); trivial.

Qed.


Theorem removelast_repeat_eq : forall (A : Type)(a : A) n,
  (n > 0)%nat ->
  removelast (repeat a n) = repeat a (pred n).

  intros.
  destruct n.
  lia.
  rewrite repeat_S_rev.
  rewrite removelast_last.
  reflexivity.

Qed.

Theorem removelast_length : forall (A : Type)(ls : list A),
  ls <> nil ->
  List.length (removelast ls) = pred (List.length ls).

  induction ls using rev_ind; intros.
  intuition idtac.
  rewrite removelast_last.
  rewrite app_length.
  rewrite plus_comm.
  simpl.
  reflexivity.

Qed.

Theorem toZ_ls_shiftR_ls_eq : forall n n1 ls,
  (n < n1)%nat ->
  toZ_ls (shiftR_ls false (ls ++ repeat false n1) n) = Z.shiftl (toZ_ls (ls ++ repeat false n1) ) (Z.of_nat n).

  induction n; intros.
  simpl in *; trivial.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_l.

  simpl.
  rewrite shiftR1_ls_comm.
  rewrite shiftR1_app_repeat_eq.
  rewrite app_comm_cons.
  rewrite IHn; try lia.

  rewrite <- (Z.shiftl_shiftl _ 1 (Z.of_nat n)).
  f_equal.
  rewrite <- app_comm_cons.
  rewrite <- shiftR1_app_repeat_eq; try lia.
  rewrite toZ_ls_shiftR1_ls_eq.
  reflexivity.

  rewrite app_length.
  rewrite repeat_length.
  lia.
  rewrite last_app_2.
  apply last_repeat_eq.
  rewrite repeat_length.
  lia.
  rewrite removelast_app.
  rewrite last_app_2.
  rewrite removelast_repeat_eq; try lia.
  rewrite last_repeat_eq.
  trivial.
  rewrite removelast_length.
  rewrite repeat_length.
  lia.
  intuition idtac.
  apply length_zero_iff_nil in H0.
  rewrite repeat_length in *.
  lia.
  intuition idtac.
  apply length_zero_iff_nil in H0.
  rewrite repeat_length in *.
  lia.
  lia.
  lia.

Qed.

Theorem shiftL1_ls_shiftL_ls_comm : forall (A : Type) n (a : A) ls,
  shiftL1_ls a (shiftL_ls a ls n) = shiftL_ls a (shiftL1_ls a ls) n.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  reflexivity.

Qed.

Theorem shiftL1_ls_repeat_eq : forall n1 (A : Type)(a : A) b,
  (n1 > 0)%nat ->
  (shiftL1_ls a (repeat a n1 ++ b)) = (repeat a (pred n1) ++ b ++ [a]).

  intros.
  unfold shiftL1_ls.
  unfold shiftin_ls.
  destruct n1; simpl in *; try lia.
  rewrite app_assoc.
  reflexivity.

Qed.


Theorem rev_shiftL_ls_eq_h : forall (A : Type) n n1 (a : A) b,
  (n < n1)%nat ->
  rev (shiftL_ls a (repeat a n1 ++ b ) n) = shiftR_ls a ((rev b)++ (repeat a n1))  n.

  induction n;
  intros;
  simpl in *.
  rewrite rev_app_distr.
  rewrite rev_repeat_id.
  reflexivity.

  rewrite shiftL1_ls_shiftL_ls_comm.
  rewrite shiftL1_ls_repeat_eq.
  rewrite IHn.
  rewrite shiftR1_ls_comm.
  rewrite shiftR1_app_repeat_eq.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
  lia.
  lia.
  lia.

Qed.


Theorem rev_shiftL_ls_eq : forall (A : Type) n1 n (a b : A),
  (n < n1)%nat ->
  rev (shiftL_ls a (repeat a n1 ++ [b] ) n) = shiftR_ls a (b:: (repeat a n1))  n.

  intros.
  apply rev_shiftL_ls_eq_h.
  trivial.

Qed.

Theorem sbvToInt_shiftL_1_equiv : forall n s,
  (n > 0)%nat ->
  (s < pred n)%nat ->
  sbvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
  Z.shiftl 1 (Z.of_nat s).

  intros.
  rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n.
  lia.
  unfold bvToBITS_ls.
  rewrite shiftL_to_list_eq.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls, bitsToBv_ls.
  simpl in *.
  rewrite fromPosZ_ls_0_eq.
  rewrite rev_repeat_id.
  rewrite rev_shiftL_ls_eq.
  replace (1%bool :: repeat 0%bool n) with ([true] ++ (repeat false n)).
  rewrite toZ_ls_shiftR_ls_eq.
  unfold toZ_ls.
  Search splitmsb_ls app.
  destruct n.
  lia.
  rewrite repeat_S_rev.
  rewrite app_assoc.
  Search splitmsb_ls app.
  rewrite splitmsb_ls_app_eq.
  
  rewrite toPosZ_app_repeat_0_eq.
  simpl.
  reflexivity.
  lia.
  simpl.
  reflexivity.
  lia.

Qed.

Theorem toPosZ_ls_repeat_0 : forall n,
  toPosZ_ls (repeat 0%bool n) = 0.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  lia.

Qed.

Theorem sbvToInt_replicate_0 : forall n,
  sbvToInt _ (replicate n bool false) = 0.

  intros.
  rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n; simpl; trivial.
  unfold bvToBITS_ls.
  rewrite <- replicate_repeat_eq.
  rewrite rev_repeat_id.
  rewrite repeat_S_rev.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  apply toPosZ_ls_repeat_0.
  
Qed.

Theorem nth_to_list_eq : forall (A : Type) n (f : Fin.t n) (v : Vec n A) a,
  Vector.nth v f = nth (proj1_sig (Fin.to_nat f) ) (to_list v) a.

  induction f; intros; simpl in *; subst.
  destruct (Vec_S_cons v).
  destruct H. 
  subst.
  rewrite to_list_cons.
  simpl.
  reflexivity.

  remember (Fin.to_nat f ) as z.  
  destruct z.
  simpl.
  
  destruct (Vec_S_cons v).
  destruct H. 
  subst.
  rewrite to_list_cons.
  simpl in *.
  eapply IHf.

Qed.

Theorem nth_to_list_eq_gen : forall (A : Type) n (f : Fin.t n) (v : Vec n A) a n',
  n' = (proj1_sig (Fin.to_nat f) ) ->
  Vector.nth v f = nth n' (to_list v) a.

  intros.
  subst.
  apply nth_to_list_eq. 

Qed.


Theorem nth_order_to_list_eq : forall (A : Type) (a : A) n (v : Vec n A) n' (pf : (n' < n)%nat),
  nth_order v pf = nth n' (to_list v) a.

  intros.
  unfold nth_order.
  eapply nth_to_list_eq_gen.
  rewrite Fin.to_nat_of_nat.
  reflexivity.

Qed.

Theorem toPosZ_ls_nonneg : forall ls,
  0 <= toPosZ_ls ls.

  induction ls; intros; simpl in *; try lia.
  destruct a; lia.

Qed.

Theorem toPosZ_ls_In_true_nz : forall ls,
  In true ls ->
  toPosZ_ls ls <> 0%Z.

  induction ls; intros; simpl in *.
  intuition idtac.
  destruct H.
  subst.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.
  destruct a.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.
  intuition idtac.
  lia.
Qed.

Theorem toZ_ls_In_true_nz : forall ls,
  In true ls ->
  toZ_ls ls <> 0%Z.

  intros.
  destruct ls using rev_ind; intros; simpl in *.
  intuition idtac.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  apply in_app_or in H.

  destruct x.
  specialize (toNegZ_ls_nonneg ls); intros.
  lia.

  destruct H.
  eapply toPosZ_ls_In_true_nz; eauto.

  simpl in *.
  intuition idtac.
  discriminate.

Qed.

Theorem sbvToInt_nz_nth : forall n (v : Vec n _) n' (nlt : (n' < n)%nat),
  nth_order v nlt = true ->
  sbvToInt _ v <> 0%Z.

  intros.
  rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n.
  lia.
  
  unfold bvToBITS_ls.
  rewrite (@nth_order_to_list_eq _ false) in H.
  assert (In true (to_list v)).
  rewrite <- H.
  apply nth_In.
  rewrite to_list_length.
  trivial.
  apply toZ_ls_In_true_nz.
  apply (@in_rev _ (to_list v)).
  trivial.

Qed.

Theorem sbvToInt_neg_sign_bit_set : forall n  b2 (ltpf : (0 < n)%nat),
    (sbvToInt n b2 < 0)%Z ->
    nth_order b2 ltpf = true.

  intros.
  rewrite <- sbvToInt_ls_equiv in *.
  unfold sbvToInt_ls in *.
  destruct n.
  lia.
  unfold bvToBITS_ls in *.
  destruct (Vec_S_cons b2).
  destruct H0.
  subst.
  rewrite to_list_cons in *.
  unfold toZ_ls in *.
  simpl in *.
  rewrite splitmsb_ls_app_eq in *.
  destruct x.
  reflexivity.
  match goal with
  | [H : toPosZ_ls ?a < 0 |- _ ] =>
    specialize (toPosZ_ls_nonneg a); intros
  end.
  lia.

Qed.

Theorem toZ_ls_repeat_0: forall n : nat, 
  toZ_ls (repeat 0%bool n) = 0.

  intros.
  unfold toZ_ls.
  destruct n.
  simpl.
  reflexivity.

  rewrite repeat_S_rev.
  rewrite splitmsb_ls_app_eq.
  apply toPosZ_ls_repeat_0.

Qed.

Theorem splitmsb_ls_eq_app_if : forall ls a ls',
  (ls <> nil) ->
  splitmsb_ls ls = (a, ls') ->
  ls = ls' ++ [a].

  intros.
  destruct ls using rev_ind.
  intuition idtac.

  rewrite splitmsb_ls_app_eq in H0.
  inversion H0; clear H0; subst.
  reflexivity.

Qed.

Theorem Z_div_mul_eq : forall x y,
  x > 0 ->
  x * (y / x) = y - (y mod x).

  intros.
  specialize (Zdiv.Z_div_mod_eq y x); intuition idtac.
  lia.

Qed.

Theorem Z_mod_div_eq : forall x y z,
  z > 0 ->
  y > 0 ->
  y mod z = 0 ->
  Z.div (Z.modulo x y) z = Z.modulo (Z.div x z) (Z.div y z).

  intros.
  assert (exists y', y = y'*z).
  exists (y / z).
  rewrite (@Zdiv.Z_div_exact_full_2 y z); trivial; try lia.
  rewrite Z.mul_comm.
  rewrite Z.div_mul.
  reflexivity.
  lia.
  destruct H2.
  subst.

  destruct (Z.eq_decidable x0 0).
  subst.
  repeat rewrite Z.mul_0_l.
  repeat rewrite Z.div_0_l.
  repeat rewrite Zdiv.Zmod_0_r.
  apply Z.div_0_l.
  lia.
  lia.

  rewrite Zdiv.Z_div_mult; try lia.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_plus.
  rewrite Zdiv.Zmod_div.
  lia.
  lia.
  lia.
  lia.
Qed.


Theorem fromPosZ_ls_app : forall n1 n2 z, 
 
  fromPosZ_ls (n1 + n2) z = (fromPosZ_ls n1 (Z.modulo z (Z.pow 2 (Z.of_nat n1)))) ++ (fromPosZ_ls n2 (Z.div z (Z.pow 2 (Z.of_nat n1)))). 

  induction n1; intros.
  simpl in *.
  rewrite Z.div_1_r.
  reflexivity.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl in *.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  f_equal.
  repeat rewrite Zdiv.Zeven_mod.
  f_equal.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r.
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_mod_mult.
  rewrite Z.add_0_r.  
  rewrite Z.pow_1_r.
  rewrite Z.mod_mod.
  reflexivity.
  lia.
  lia.
  apply Z.pow_pos_nonneg; lia.
  lia.
  lia.

  rewrite IHn1.
  repeat rewrite Z.div2_div.
  f_equal.
  f_equal.
  replace (2 ^ (Z.of_nat n1 + 1)) with ((2 ^ (Z.of_nat n1))*2).
  rewrite Z_mod_div_eq; try lia.
  rewrite Zdiv.Z_div_mult.
  reflexivity.
  lia.
  apply Zorder.Zmult_gt_0_compat.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
  lia.
  apply Zdiv.Z_mod_mult.
  rewrite Z.pow_add_r.
  reflexivity.
  lia.
  lia.

  f_equal.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Zdiv_Zdiv; try lia.
  reflexivity.
  apply Z.pow_nonneg; lia.

Qed.

Theorem fromPosZ_ls_rev : forall n z, 
  (n > 0)%nat ->
  fromPosZ_ls n z = (fromPosZ_ls (pred n) (Z.modulo z (Z.pow 2 (Z.of_nat (pred n))))) ++ [negb (Z.even (Z.div z (Z.pow 2 (Z.of_nat (pred n)))))]. 

  intros.
  destruct n.
  lia.

  replace (S n) with (n + 1)%nat; try lia.
  rewrite fromPosZ_ls_app.
  rewrite plus_comm.
  simpl.
  reflexivity.

Qed.

Theorem toPosZ_ls_fromPosZ_ls_eq : forall n z,
  0 <= z < 2^(Z.of_nat n) ->
  toPosZ_ls (fromPosZ_ls n z) = z.

  induction n; intros.
  simpl in *.
  lia.

  rewrite Znat.Nat2Z.inj_succ in *.
  rewrite <- Z.add_1_r in *.
  simpl in *.
  case_eq (Z.even z); intros; simpl in *.
  assert (exists z', z = 2 * z').
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  simpl.
  rewrite Z.add_0_r.
  reflexivity.
  destruct H1. subst.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult; try lia.
  rewrite Z.double_spec.
  rewrite IHn.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  eapply Zorder.Zmult_lt_reg_r; eauto.
  lia.
  lia.
  lia.

  assert (exists z', z = 1 + z' *2 ).
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  unfold negb.
  lia.

  destruct H1. subst.
  rewrite <- Z.add_1_l.
  f_equal.
  rewrite Z.div2_div.
  rewrite Zdiv.Z_div_plus.
  simpl.
  rewrite IHn.
  rewrite Z.double_spec.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  lia.
  lia.
  lia.
  lia.
Qed.

Theorem fromNegZ_ls_app : forall n1 n2 z, 
 
  fromNegZ_ls (n1 + n2) z = (fromNegZ_ls n1 (Z.modulo z (Z.pow 2 (Z.of_nat n1)))) ++ (fromNegZ_ls n2 (Z.div z (Z.pow 2 (Z.of_nat n1)))). 

  induction n1; intros.
  simpl in *.
  rewrite Z.div_1_r.
  reflexivity.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl in *.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  repeat rewrite Zdiv.Zeven_mod.
  f_equal.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r.
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_mod_mult.
  rewrite Z.add_0_r.  
  rewrite Z.pow_1_r.
  rewrite Z.mod_mod.
  reflexivity.
  lia.
  lia.
  apply Z.pow_pos_nonneg; lia.
  lia.
  lia.

  rewrite IHn1.
  repeat rewrite Z.div2_div.
  f_equal.
  f_equal.
  replace (2 ^ (Z.of_nat n1 + 1)) with ((2 ^ (Z.of_nat n1))*2).
  rewrite Z_mod_div_eq; try lia.
  rewrite Zdiv.Z_div_mult.
  reflexivity.
  lia.
  apply Zorder.Zmult_gt_0_compat.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
  lia.
  apply Zdiv.Z_mod_mult.
  rewrite Z.pow_add_r.
  reflexivity.
  lia.
  lia.

  f_equal.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Zdiv_Zdiv; try lia.
  reflexivity.
  apply Z.pow_nonneg; lia.

Qed.


Theorem fromNegZ_ls_rev : forall n z, 
  (n > 0)%nat ->
  fromNegZ_ls n z = (fromNegZ_ls (pred n) (Z.modulo z (Z.pow 2 (Z.of_nat (pred n))))) ++ [(Z.even (Z.div z (Z.pow 2 (Z.of_nat (pred n)))))]. 

  intros.
  destruct n.
  lia.

  replace (S n) with (n + 1)%nat; try lia.
  rewrite fromNegZ_ls_app.
  rewrite plus_comm.
  simpl.
  unfold joinlsb_ls. simpl.
  reflexivity.

Qed.

Theorem toNegZ_ls_fromNegZ_ls_eq : forall n z,
  0 <= z < 2^(Z.of_nat n) ->
  toNegZ_ls (fromNegZ_ls n z) = z.

  induction n; intros.
  simpl in *.
  lia.

  rewrite Znat.Nat2Z.inj_succ in *.
  rewrite <- Z.add_1_r in *.
  simpl in *.
  case_eq (Z.even z); intros; simpl in *.
  assert (exists z', z = 2 * z').
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  simpl.
  rewrite Z.add_0_r.
  reflexivity.
  destruct H1. subst.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult; try lia.
  rewrite Z.double_spec.
  rewrite IHn.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  eapply Zorder.Zmult_lt_reg_r; eauto.
  lia.
  lia.
  lia.

  assert (exists z', z = 1 + z' *2 ).
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  unfold negb.
  lia.

  destruct H1. subst.
  rewrite <- Z.add_1_l.
  f_equal.
  rewrite Z.div2_div.
  rewrite Zdiv.Z_div_plus.
  simpl.
  rewrite IHn.
  rewrite Z.double_spec.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  lia.
  lia.
  lia.
  lia.
Qed.


Theorem sbvToInt_intToBv_id : forall n v,
  (n > 0)%nat ->
  (-Z.pow 2 (Z.of_nat (pred n)) <= v < Z.pow 2 (Z.of_nat (pred n)))%Z ->
  sbvToInt n (intToBv n v) = v.

  intros.
  rewrite <- sbvToInt_ls_equiv .
  unfold sbvToInt_ls .
  destruct n.
  lia.

  unfold bvToBITS_ls.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls, bitsToBv_ls.
  rewrite rev_involutive.
  simpl in *.
  unfold fromZ_ls.
  destruct v.
  unfold zero_ls.
  apply toZ_ls_repeat_0.

  rewrite fromPosZ_ls_rev.
  simpl.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  case_eq (Z.even (Z.pos p / 2^Z.of_nat n)); intros;
  simpl.
  rewrite Zdiv.Zmod_small.
  apply toPosZ_ls_fromPosZ_ls_eq; intuition idtac; lia.
  lia.
  rewrite Z.div_small in H1.
  simpl in *.
  discriminate.
  lia.
  lia.

  rewrite Pos2Z.opp_neg.
  rewrite fromNegZ_ls_rev.
  unfold pred.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  case_eq (Z.even (Z.pred (Z.pos p) / 2^Z.of_nat n)); intros.
  rewrite toNegZ_ls_fromNegZ_ls_eq.
  rewrite Zdiv.Zmod_small.
  lia.
  lia.
  apply Z.mod_bound_pos.
  lia.
  apply Z.pow_pos_nonneg; lia.
  rewrite Z.div_small in H1.
  simpl in *.
  discriminate.
  lia.
  lia.
Qed.




