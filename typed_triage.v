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
(*                    Typed Triage                                    *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import String Arith Lia Bool List Nat Datatypes.
Require Import terms types subtypes derive typed_lambda typed_recursion.

Set Default Proof Using "Type".




Theorem derive_triage :
  forall gamma ty f0 f1 f2,
    covariant ty -> 
    derive gamma f0 (subst ty Leaf) ->
    derive gamma f1 (Quant (Funty (Var 0) (subst (lift_rec ty 1 1) (Stem (Var 0))))) -> 
    derive gamma f2 (Quant (Quant
                              (Funty (Var 1)
                                     (Funty (Var 0)
                                            (subst (lift_rec ty 1 2) (Fork (Var 1) (Var 0))))))) -> 
    derive gamma (triage f0 f1 f2) (Funty (Var 0) (subst_rec ty (Var 0) 0)). 
Proof.
  intros; repeat eapply derive_app; eauto; eapply derive_node.
  (eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_funty_tac]).
  eapply sub_trans. 2: eapply sub_tree;  auto_t.  eapply sub_zero. 
  eapply subtype_leaf_fork. 
Qed.


Theorem derive_query :
  forall gamma f0 f1 f2 vty,   
    derive gamma f0 (lift 1 vty) ->
    derive gamma f1 (Quant (Funty (Var 0) (lift 2 vty))) -> 
    derive gamma f2
           (Quant
              (Quant (Funty (Var 1)
                            (Funty (Var 0)
                                   (lift 3 vty))))) -> 
    derive gamma (triage f0 f1 f2) (Funty (Var 0) (lift 1 vty)). 
Proof.
  intros.
  replace (lift 1 vty) with (subst (lift 2 vty) (Var 0))
    by (unfold subst, lift; rewrite subst_rec_lift_rec; try lia; auto).
  eapply derive_triage. 
  unfold covariant, lift; eapply lift_rec_preserves_variant2.
  unfold subst, lift; rewrite subst_rec_lift_rec; try lia; auto_t.
  unfold subst, lift; rewrite lift_rec_lift_rec; try lia; rewrite subst_rec_lift_rec; try lia; auto_t.
  unfold subst, lift; rewrite lift_rec_lift_rec; try lia; simpl; rewrite subst_rec_lift_rec; try lia; auto.
Qed.



Theorem derive_update :
  forall gamma f0 f1 f2, 
    derive gamma f0 Leaf ->
    derive gamma f1 (Quant (Funty (Var 0) (Stem (Var 0)))) -> 
    derive gamma f2 (Quant (Quant (Funty (Var 1) (Funty (Var 0) (Fork(Var 1) (Var 0)))))) -> 
    derive gamma (triage f0 f1 f2) (Funty (Var 0) (Var 0)). 
Proof.
  intros; replace (Var 0) with (subst (Var 0) (Var 0)) at 2 by (cbv; auto).  
  eapply derive_triage; eauto; cbv; auto_t. 
Qed.



    
(* querying trees *) 

 
Definition isLeaf := triage K (K@ KI) (K @ (K @ KI)).
Definition isStem := triage KI (K@ K) (K @ (K @ KI)).
Definition isFork := triage KI (K@ KI) (K @ (K @ K)).


Theorem derive_isLeaf: forall gamma, derive gamma isLeaf (Quant (Funty (Var 0) Bool_ty)).
Proof.
  intros; eapply derive_generalisation.
  replace Bool_ty with (lift 1 Bool_ty) by (cbv; auto).
  eapply derive_query.
  eapply derive_true.
  eapply derive_generalisation;  eapply derive_app; [ eapply derive_K | eapply derive_false].
  repeat eapply derive_generalisation.  eapply derive_app. eapply derive_K.
  eapply derive_app. eapply derive_K.
  eapply derive_false.
Qed.

Theorem derive_isStem: forall gamma, derive gamma isStem (Quant (Funty (Var 0) Bool_ty)).
Proof.
  intros; eapply derive_generalisation.
  replace Bool_ty with (lift 1 Bool_ty) by (cbv; auto).
  eapply derive_query.
  eapply derive_false.
  eapply derive_generalisation;  eapply derive_app; [ eapply derive_K | eapply derive_true].
  repeat eapply derive_generalisation.  eapply derive_app. eapply derive_K.
  eapply derive_app. eapply derive_K.
  eapply derive_false.
Qed.
 

Theorem derive_isFork: forall gamma, derive gamma isFork (Quant (Funty (Var 0) Bool_ty)).
Proof.
  intros; eapply derive_generalisation.
  replace Bool_ty with (lift 1 Bool_ty) by (cbv; auto).
  eapply derive_query.
  eapply derive_false.
  eapply derive_generalisation;  eapply derive_app; [ eapply derive_K | eapply derive_false].
  repeat eapply derive_generalisation.  eapply derive_app. eapply derive_K.
  eapply derive_app. eapply derive_K.
  eapply derive_true.
Qed.

(*** Size *)

Theorem derive_size : forall gamma, derive gamma size (quant 1 (Funty (Var 0) Nat_ty)).
Proof.
  intros; eapply derive_Z. eapply derive_star. eapply derive_generalisation.  
  replace Nat_ty with (lift 1 Nat_ty) by (cbv; auto). 
  eapply derive_query.
  (* 3 *)
  replace (lift 1 Nat_ty) with Nat_ty by (cbv; auto).
  eapply derive_app. eapply derive_succ1. eapply derive_generalisation.
  eapply derive_app; [ eapply derive_K | eapply derive_I].
  (* 2 *)
  replace (lift 2 Nat_ty) with Nat_ty by (cbv; auto).
  eapply derive_generalisation. eapply derive_star. eapply derive_app. eapply derive_succ1.
  eapply derive_app; eapply derive_ref; simpl.  1,3: eauto. subst_tac.
  do 2 (replace (relocate 0 1 1) with 0 by (cbv; auto)). var_tac.
  (* 1 *)
  replace (lift 3 Nat_ty) with Nat_ty by (cbv; auto).
  do 2 eapply derive_generalisation. do 2 eapply derive_star.
  eapply derive_app. eapply derive_app.
  2,3: eapply derive_app; eapply derive_ref; simpl. 2,4,6,8: eauto. 3,5: eapply sub_zero.
  2,3: subst_tac; sub_fun_tac. 
  all: repeat (replace (relocate 0 1 1) with 0 by (cbv; auto)); var_tac.
  repeat (replace (relocate 0 2 1) with 0 by (cbv; auto)). var_tac.
  do 2 eapply derive_star.
  eapply derive_app. eapply derive_succ1.
  eapply derive_app. eapply derive_app.
  2,3: eapply derive_ref; simpl. 2,4: eauto. 2,3: eapply sub_zero.
  eapply derive_star. unfold prim_plus0.
  eapply derive_primrec; simpl.
  (* 3 *)
  eapply derive_I. 
  (* 2 *)
  do 2 eapply derive_K1.   eapply derive_S2. 2: eapply derive_I. eapply derive_K1.
  eapply derive_subtype with (Quant (Funty  (Funty (Funty (Var 0) (Var 0)) (Funty (Var 0) (Var 0)))
                                            (Funty (Funty (Var 0) (Var 0)) (Funty (Var 0) (Var 0))))). 
  2: eapply sub_dist. 
  eapply derive_generalisation.
  eapply derive_S1. eapply derive_S2. eapply derive_K1. eapply derive_node. 

  eapply sub_trans. eapply subtype_leaf_fork. do 2 sub_fun_tac.
  all: cycle 1.
  eapply derive_S2. eapply derive_K1. eapply derive_node. eapply sub_leaf_fun.
  eapply derive_K.
  all: cycle -1.
  sub_fork2_tac.
  eapply Forall_cons. 2: eapply Forall_nil. 
  eapply derive_ref; simpl; auto_t.
Qed.

 

(*** Equality *) 


Theorem derive_equal: forall gamma, derive gamma equal (quant 2 (Funty (Var 0) (Funty (Var 1) Bool_ty))).
Proof.
  intros; eapply derive_Z.
  eapply derive_subtype with
      (quant 2 (Funty (quant 2 (Funty (Var 0) (Funty (Var 1) Bool_ty)))
                      (Funty (Var 0) (Funty (Var 1) Bool_ty)))).
  2: dist_tac. 2: eapply sub_trans. 2: eapply (subtype_lift 2). 2: cbv; eapply sub_zero. 2: eapply sub_zero. 
  eapply derive_generalisation_q.  eapply derive_swap.
  replace (Funty (quant 2 (Funty (Var 0) (Funty (Var 1) Bool_ty))) (Funty (Var 1) Bool_ty))
    with (subst  (Funty (quant 2 (Funty (Var 0) (Funty (Var 1) Bool_ty))) (Funty (Var 2) Bool_ty)) (Var 0))
    by (cbv; auto).
  eapply derive_triage.
  (* 4 *)
  cbv; eauto. 
  (* 3 *)
  unfold subst; refold subst_rec. eapply derive_star. insert_Var_tac. unfold pred.
  eapply derive_subtype.   2: replace (subst_rec Bool_ty Leaf 0) with (subst Bool_ty (Var 1)) by (cbv; auto).
  2: eapply sub_tree; cbv; eauto.
  eapply derive_app. eapply derive_app. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_app. eapply derive_app. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_true.
  eapply derive_generalisation. eapply derive_K1. eapply derive_false. 
  eapply derive_generalisation_q. do 2 eapply derive_K1. eapply derive_false. 
  (* 2 *)
  unfold subst; refold lift_rec; refold subst_rec. eapply derive_generalisation; repeat eapply derive_star.
  var_tac; simpl; var_tac.
  eapply derive_subtype.
  2: replace (Quant (Funty (Var 0) (Funty (Var 0) (Var 0)))) with (subst Bool_ty (Var 2)) by (cbv; auto).
  2: eapply sub_tree.   2: cbv; auto. 
  eapply derive_app. eapply derive_app. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_app. eapply derive_app. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_false.
  eapply derive_generalisation.
  eapply derive_app; eapply derive_ref; simpl; eauto.
  var_tac. do 2 subst_tac. var_tac. 
  eapply derive_generalisation_q. do 2 eapply derive_K1. eapply derive_false. 
  (* 1 *)
  do 2 eapply derive_generalisation.
  unfold subst; refold lift_rec; refold subst_rec. repeat eapply derive_star.
  eapply derive_subtype. 
  2: var_tac; simpl; var_tac.
  eapply derive_subtype. 
  2: simpl; var_tac.
  eapply derive_subtype. 
  2: replace (Quant (Funty (Var 0) (Funty (Var 0) (Var 0)))) with (subst Bool_ty (Var 3)) by (cbv; auto).
  2: eapply sub_tree.   2: cbv; auto. 
  eapply derive_app. eapply derive_app. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_app. eapply derive_app. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_false.
  eapply derive_generalisation.
  eapply derive_K1.   eapply derive_false.
  do 2 eapply derive_generalisation. do 2 eapply derive_star. 
  eapply derive_app.  repeat eapply derive_app; eapply derive_ref; simpl; eauto; var_tac.
  cbv.   do 2 subst_tac. do 2 sub_fun_tac. subst_tac.
  cbv.   do 2 subst_tac.
  eapply derive_false.
Qed.

