(**********************************************************************)
(* Copyright 2024 Barry Jay                                           *)
(*                                                                    *) 
(* Permission is hereby granted, free of charge, to any person        *) 
(* obtaining a copy of this software and associated documentation     *) 
(* files (the "Software"), to deal in the Software without            *) 
(* restriction, including without limitation the rights to use, copy, *) 
(* modify, merge, publish, distribute, sublicense, and/or sell copies *) 
(* of the Software, and to permit persons to whom the Software is     *) 
(* furnished to do so, subject to the following conditions:           *) 
(*                                                                    *) 
(* The above copyright notice and this permission notice shall be     *) 
(* included in all copies or substantial portions of the Software.    *) 
(*                                                                    *) 
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,    *) 
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *) 
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              *) 
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT        *) 
(* HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,       *) 
(* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, *) 
(* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER      *) 
(* DEALINGS IN THE SOFTWARE.                                          *) 
(**********************************************************************)

(**********************************************************************)
(*          Type Derivation in Tree Calculus                          *) 
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)



Require Import String Arith Lia Bool List Nat Datatypes.
Require Import terms types subtypes.


Set Default Proof Using "Type".

Open Scope string_scope.
Open Scope nat_scope.




(* Type derivation *)


Inductive derive: list (string * dtype) -> Tree -> dtype -> Prop :=
| derive_ref : forall gamma x uty ty, get x gamma = Some uty -> subtype uty ty -> derive gamma (Ref x) ty
| derive_node : forall gamma uty, subtype Leaf uty -> derive gamma Node uty
| derive_app: forall gamma M N ty u, derive gamma M (Funty u ty) -> derive gamma N u -> derive gamma (M@N) ty
.

Global Hint Constructors derive: TreeHintDb.



Theorem derive_subtype:
  forall gamma M ty1, derive gamma M ty1 -> forall ty2, subtype ty1 ty2 -> derive gamma M ty2.
Proof.  intros gamma M ty1 d; induction d; intros; auto_t. Qed.


Lemma lift_rec_preserves_derive:
  forall gamma M ty, derive gamma M ty -> forall n k,  derive (lift_rec_context n k gamma) M (lift_rec ty n k).
Proof.
  intros gamma M ty d; induction d; intros; simpl; auto_t. 
  - eapply derive_ref; simpl; eauto; [
        rewrite get_lift_rec; rewrite H; eauto |
        eapply lift_rec_preserves_subtype; eauto].
  - eapply derive_node;
      replace Leaf with (lift_rec Leaf n k) by auto; eapply lift_rec_preserves_subtype; eauto.
  Qed. 
         
Lemma derive_subst_rec:
  forall gamma M ty,
    derive gamma M ty ->
    forall u k, derive (subst_rec_context u k gamma) M (subst_rec ty u k).
Proof.
  intros gamma M ty d; induction d; intros; simpl; auto_t.
  - eapply derive_ref; auto; [
        rewrite get_subst_rec; rewrite H;auto |
        eapply subst_rec_preserves_subtype; eauto].
  - eapply derive_node;
      replace Leaf with (subst_rec Leaf u k) by auto; eapply subst_rec_preserves_subtype; eauto.
Qed.


Theorem derive_generalisation:
  forall gamma M T, derive (lift_context 1 gamma)  M T -> derive gamma M (Quant T).
Proof.
  cut(forall gamma M T, derive gamma  M T ->
                        forall gamma1,  gamma = (lift_context 1 gamma1) -> derive gamma1 M (Quant T));
    [ intros; eapply H; eauto |];
    intros gamma M T d; induction d; intros; subst; auto.
  - unfold lift_context in *; rewrite get_lift_rec in *;
      caseEq (get x gamma1); intros; rewrite H1 in *.
    + eapply derive_ref; eauto;  inv_out H; eapply sub_trans; [ eapply sub_lift |];
        eapply sub_quant; eauto.
    + discriminate. 
  - eapply derive_node; eapply sub_trans; [ eapply sub_lift | eapply sub_quant; cbv; eauto]. 
  - eapply derive_app; [ eapply derive_subtype; [ eapply IHd1; auto | apply sub_dist] | eapply IHd2; auto].
Qed.

Corollary derive_generalisation_q:
  forall k gamma M T, derive (lift_context k gamma)  M T -> derive gamma M (quant k T).
Proof.
  induction k; intros.
  - rewrite lift_context_zero in *; auto.
  - simpl; replace (S k) with (k+1) in *; try lia; erewrite <- lift_rec_lift_context in *; [
    eapply IHk; eapply derive_generalisation; unfold lift_context; rewrite lift_rec_lift_context in *;
      replace (1+k) with (k+1) by lia; auto; lia |
        apply 0 | lia]. 
Qed.


Theorem derive_generalisation2:
  forall gamma M T, derive gamma M (Quant T) -> derive (lift_context 1 gamma)  M T.
Proof.
  intros; eapply derive_subtype.
  - eapply lift_rec_preserves_derive; eauto.
  - simpl;  subst_tac; rewrite subst_rec_lift_rec0; rewrite lift_rec_null; eapply sub_zero. 
Qed.

Corollary derive_generalisation2_q:
  forall k gamma M T, derive gamma M (quant k T) -> derive (lift_context k gamma)  M T.
Proof.
  induction k; intros; simpl in *.
  - rewrite lift_context_zero; auto.
  - assert(derive (lift_context k gamma) M (Quant T)).  eapply IHk; eauto. 
      replace (S k) with (1+k) by lia;  erewrite <- lift_rec_lift_context; [
  instantiate(1:= 0); eapply derive_generalisation2; eauto |
  apply 0 | lia]. 
Qed.
 

Theorem derive_K: forall gamma uty vty, derive gamma K (Funty uty (Funty vty uty)). 
Proof.
  intros; eapply derive_subtype; [
    eapply derive_app; eapply derive_node; [ eapply sub_leaf_fun | eapply sub_zero]
  | auto_t].
Qed.


Lemma derive_K1: forall gamma M uty vty, derive gamma M uty -> derive gamma (K@M) (Funty vty uty). 
Proof.  intros; eapply derive_app; [ eapply derive_K | eauto]. Qed. 


Theorem derive_S1 :  forall gamma f uty vty wty,
    derive gamma f (Funty uty (Funty vty wty)) -> 
    derive gamma (S1 f) (Funty (Funty uty vty) (Funty uty wty)). 
Proof.
  intros;  eapply derive_app. 
  - eapply derive_node; eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_funty_tac]; sub_fork2_tac. 
  - eapply derive_app; eauto; eapply derive_node; simpl; eapply sub_leaf_fun.
 Qed.

Theorem derive_S2 :  forall gamma f g uty vty wty,
    derive gamma f (Funty uty (Funty vty wty)) -> derive gamma g (Funty uty vty) -> 
    derive gamma (S1 f @ g) (Funty uty wty). 
Proof. intros;  eapply derive_app; eauto; eapply derive_S1; eauto. Qed. 

Theorem derive_S :  forall gamma uty vty wty,
    derive gamma Sop (Funty (Funty uty (Funty vty wty)) (Funty (Funty uty vty) (Funty uty wty))). 
Proof.
  intros; eapply derive_S2.
  - eapply derive_K1; eapply derive_node; auto_t.
  - eapply derive_node; auto_t. 
Qed.

Theorem derive_I: forall gamma uty, derive gamma I (Funty uty uty). 
Proof.  intros; eapply derive_S2; [eapply derive_K | auto_t].  Qed. 

  

Theorem derive_wait:
  forall gamma M N uty k vty wty,
    derive gamma M (Funty uty (quant k (Funty vty wty))) -> derive gamma N uty -> 
    derive gamma (wait M N) (quant k (Funty vty wty)). 
Proof.
  intros; unfold wait; eapply derive_generalisation_q; eapply derive_S2; [
    |
      eapply derive_K1;
      eapply derive_generalisation2_q;
      eapply derive_subtype; eauto; eapply subtype_lift];
    eapply derive_S2; [ | eapply derive_K];
    eapply derive_K1; eapply derive_S1; eapply derive_generalisation2_q;
    eapply derive_subtype; eauto;
    eapply sub_trans; [ eapply subtype_lift |];
    eapply subtype_quant; unfold lift; simpl; sub_fun_tac; eapply subtype_lift3.     
Qed.




Theorem derive_basic:
  (forall gamma uty vty, derive gamma K (Funty uty (Funty vty uty))) /\
  (forall gamma uty vty wty,
      derive gamma Sop (Funty (Funty uty (Funty vty wty)) (Funty (Funty uty vty) (Funty uty wty)))) /\
  (forall gamma uty, derive gamma I (Funty uty uty)) /\ 
  (forall gamma M N uty k vty wty,
    derive gamma M (Funty uty (quant k (Funty vty wty))) -> derive gamma N uty -> 
    derive gamma (wait M N) (quant k (Funty vty wty))).
Proof.
  repeat split;[ eapply derive_K | eapply derive_S | eapply derive_I | eapply derive_wait ].
Qed.

  
Theorem programs_have_types: forall p gamma, program p -> derive gamma p (program_type p).
Proof.
  cut (forall n p gamma, term_size p < n -> program p -> derive gamma p (program_type p)); [
      intros; eapply H; eauto |];
    induction n; intros; try lia;  inv_out H0; simpl; auto_t; simpl in *.
  -  assert(derive gamma M (program_type M)); [
         eapply IHn; eauto; lia | 
         eapply derive_app; eauto; eapply derive_node; eapply sub_leaf_fun].
  - assert(derive gamma M (program_type M)); [
        eapply IHn; eauto; lia |];
      assert(derive gamma N (program_type N)) by (eapply IHn; eauto; lia);
      repeat  eapply derive_app; eauto; eapply derive_node; eapply subtype_leaf_fork.
Qed.

