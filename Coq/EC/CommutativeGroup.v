(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Definition of a group using additive notation, along with related definitions and theory. *)

Require Import SetoidClass.

Class CommutativeGroup(GroupElem : Type)(GroupElem_eq : Setoid GroupElem)
:=
{
  groupAdd : GroupElem -> GroupElem -> GroupElem;
  groupAdd_proper : Proper (equiv ==> equiv ==> equiv) groupAdd;
  idElem : GroupElem;
  groupAdd_assoc : forall a b c,
    groupAdd (groupAdd a b) c == groupAdd a (groupAdd b c);
  groupAdd_comm : forall a b,
    groupAdd a b == groupAdd b a;
  groupAdd_id : forall x, groupAdd idElem x == x;
  groupInverse : GroupElem -> GroupElem;
  groupInverse_proper : Proper (equiv ==> equiv) groupInverse;
  groupInverse_correct : forall e, groupAdd e (groupInverse e) == idElem;
}.

Global Existing Instance groupAdd_proper.
Global Existing Instance groupInverse_proper.

Section GroupFacts.

  Context `{CommutativeGroup}.

  Theorem groupInverse_id : groupInverse idElem == idElem.

    rewrite <- groupAdd_id.
    apply groupInverse_correct.
  Qed.

  Theorem groupAdd_ident_impl_inverse_eq : forall e1 e2,
    groupAdd e1 e2 == idElem ->
    groupInverse e1 == e2.

    intros.
    assert (groupAdd (groupAdd e1 e2)  (groupInverse e1) == (groupAdd idElem (groupInverse e1))).
    eapply groupAdd_proper.
    eauto.
    reflexivity.
    rewrite groupAdd_id in H1.
    rewrite <- H1.
    rewrite groupAdd_comm.
    rewrite <- groupAdd_assoc.
    rewrite (groupAdd_comm (groupInverse e1)).
    rewrite groupInverse_correct.
    apply groupAdd_id.

  Qed.

  Theorem groupInverse_add_distr : forall e1 e2, 
    groupInverse (groupAdd e1 e2) == groupAdd (groupInverse e1) (groupInverse e2).

    intros.
    apply groupAdd_ident_impl_inverse_eq.
    rewrite groupAdd_assoc.
    rewrite (groupAdd_comm (groupInverse e1)).
    rewrite <- (groupAdd_assoc e2).
    rewrite groupInverse_correct.
    rewrite groupAdd_id.
    apply groupInverse_correct.

  Qed.

  Theorem  groupInverse_involutive : forall e, 
    groupInverse (groupInverse e) == e.

    intros.
    apply groupAdd_ident_impl_inverse_eq.
    rewrite groupAdd_comm.
    apply groupInverse_correct.
    
  Qed.

End GroupFacts.

Section GroupMul.

  Context `{CommutativeGroup}.

  Fixpoint groupMul(x : nat)(e : GroupElem) :=
    match x with
    | 0 => idElem
    | S x' => (groupAdd e (groupMul x' e))
    end.

  Theorem groupMul_equiv_compat : forall n e1 e2,
    e1 == e2 ->
    groupMul n e1 == groupMul n e2.

    induction n; intuition; simpl in *.
    reflexivity.
    eapply groupAdd_proper; eauto.

  Qed.

  Instance groupMul_proper : Proper (eq ==> equiv ==> equiv) groupMul.

    unfold Proper, respectful; intros. subst.
    eapply groupMul_equiv_compat; eauto.

  Qed.

  Theorem groupMul_distr : forall a b x,
    groupMul (a + b) x == 
    (groupAdd (groupMul a x) (groupMul b x)).

    induction a; intuition; simpl in *.
    rewrite groupAdd_id.
    reflexivity.
    erewrite IHa.
    rewrite groupAdd_assoc.
    reflexivity.

  Qed.

End GroupMul.

Global Existing Instance groupMul_proper.

(* A commutative group with a distinct double operation that is equivalent to
(but not necessarily Lebniz equal to) adding an element with itself. *)
Class CommutativeGroupWithDouble`(grp : CommutativeGroup) 
:= {
  groupDouble : GroupElem -> GroupElem;
  groupDouble_proper : Proper (equiv ==> equiv) groupDouble;
  groupDouble_correct : forall x,
    groupDouble x == groupAdd x x
}.

Global Existing Instance groupDouble_proper.