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
(*                   Typed Recursion                                  *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)




Require Import String Arith Lia Bool List Nat Datatypes.
Require Import terms types subtypes derive typed_lambda.


Open Scope string_scope.
Open Scope nat_scope.



Set Default Proof Using "Type".


(*** Fixpoints *)



Theorem derive_Z:
  forall gamma f k uty vty,
    derive gamma f (Funty (quant k (Funty uty vty)) (quant k (Funty uty vty))) -> 
    derive gamma (Z f) (quant k (Funty uty vty)).
Proof.
  intros; eapply derive_subtype; [ | eapply sub_trans; [ | eapply sub_recursion; auto]; eapply sub_zero]; unfold Z, Zty, wait, S1.
  eapply derive_app.
  eapply derive_subtype; [ eapply programs_have_types; program_tac | cbv; eapply sub_stem_fun].
  eapply derive_app. eapply derive_app; eapply derive_node; auto_t.
  eapply derive_app. 2: eapply programs_have_types; program_tac.  
  eapply derive_app. eapply derive_node.
  eapply sub_trans. eapply subtype_leaf_fork. do 2 sub_funty_tac.
  eapply sub_fork. eapply sub_zero. 
  cbv; eapply sub_zero.
  eapply derive_app. eapply derive_node. eapply sub_leaf_fun.
  eapply derive_app. eapply derive_app; eapply derive_node; try eapply sub_zero; eapply subtype_leaf_fork.
  auto.
Qed.


Lemma derive_swap: forall gamma f uty vty ty, derive gamma f (Funty uty (Funty vty ty)) -> derive gamma (swap f) (Funty vty (Funty uty ty)). 
Proof.  intros; eapply derive_S2; [ eapply derive_K1; eapply derive_S1; eauto | eapply derive_K].  Qed. 
  
Theorem derive_Y2:
  forall gamma f uty vty,
    derive gamma f (Funty uty (Funty (Funty uty vty) vty)) ->
    derive gamma (Yop2 f) (Funty uty vty).
Proof.  intros; eapply derive_subtype; [ eapply (derive_Z _ _ 0); eapply derive_swap; eauto | apply sub_zero]. Qed. 



(*** Booleans and Arithmetic *)

Definition Bool_ty := Quant (Funty (Var 0) (Funty (Var 0) (Var 0))).

Lemma derive_true: forall gamma, derive gamma K Bool_ty.
Proof. intro; repeat eapply derive_generalisation; eapply derive_K. Qed. 

Lemma derive_false: forall gamma, derive gamma KI Bool_ty.
Proof.
  intro; repeat eapply derive_generalisation; eapply derive_app; [eapply derive_K | eapply derive_I].
Qed. 


Definition Nat_ty := Quant (Funty (Funty (Var 0) (Var 0)) (Funty (Var 0) (Var 0))).


Lemma derive_Kn : forall utys gamma ty, derive gamma (Kn (length utys)) (Funty ty (fold_right Funty ty utys)).
Proof.
  induction utys; intros; simpl.
  - eapply derive_I.
  - rewrite orb_true_r; eapply derive_S2; [
        eapply derive_K1; eapply derive_K | rewrite Kn_closed; auto]. 
Qed.

Lemma derive_compose1 :
  forall utys gamma vty wty,
    derive gamma (compose1 (length utys))
           (Funty (fold_right Funty (Funty vty wty) utys)
                  (Funty (fold_right Funty vty utys)
                         (fold_right Funty wty utys)
           )).
Proof.
  induction utys; intros; simpl. 
  - eapply derive_I.
  - rewrite ! orb_true_r; do 2  eapply derive_star; eapply derive_S2; [ 
    eapply derive_S2; [  eapply derive_star; eapply IHutys |] | ]; eapply derive_ref; simpl; auto_t.  
Qed.

Lemma derive_compose0 : 
  forall vtys gamma utys wty,
    derive gamma (compose0 (length vtys) (length utys))
           (Funty
              (fold_right Funty (fold_right Funty wty vtys) utys) (* type of g *) 
              (fold_right Funty (fold_right Funty wty utys)
                          (map (fun vty => fold_right Funty vty utys) vtys) (* types of fs *) 
           )). 
Proof.
  induction vtys; intros; simpl. 
  - eapply derive_I.
  - rewrite ! orb_true_r;
      rewrite compose1_closed; unfold orb;
      eapply derive_star; eapply derive_S2.   eapply derive_star; eauto.
      eapply derive_app; [ eapply derive_compose1 |
                           eapply derive_ref; simpl; eauto; eapply sub_zero].
Qed.


Theorem derive_compose : 
  forall gamma vtys utys wty,
    derive gamma (compose (length vtys) (length utys))
           (Funty
              (fold_right Funty wty vtys) (* type of g *) 
              (fold_right Funty (fold_right Funty wty utys)
                          (map (fun vty => fold_right Funty vty utys) vtys) (* types of fs *) 
           )). 
Proof.  intros; eapply derive_S2; [ eapply derive_K1; eapply derive_compose0 | eapply derive_Kn]. Qed.


Definition product uty vty :=
  Quant (Funty (Funty (lift 1 uty) (Funty (lift 1 vty) (Var 0))) (Var 0)).



Theorem derive_pairL : forall gamma m n uty vty,
    derive gamma m uty -> derive gamma n vty -> derive gamma (pairL m n) (product uty vty). 
Proof.
  intros; eapply derive_generalisation; eapply derive_S2; [ eapply derive_S2; [  eapply derive_I |] |]; eapply derive_K1; eapply lift_rec_preserves_derive; eauto.
  Qed. 


Theorem derive_fstL : forall gamma uty vty, derive gamma fstL (Funty (product uty vty) uty). 
Proof.
  intros; eapply derive_S2; [ eapply derive_subtype; [ eapply derive_I | sub_fun_tac; subst_tac] |
    eapply derive_K1; eapply derive_K].
Qed.

Theorem derive_sndL : forall gamma uty vty, derive gamma sndL (Funty (product uty vty) vty). 
Proof.
  intros; eapply derive_S2; [ eapply derive_subtype; [ eapply derive_I | sub_fun_tac; subst_tac] |
    eapply derive_K1; eapply derive_app; [ eapply derive_K | eapply derive_I]].
Qed.


Theorem derive_succ1: forall gamma, derive gamma succ1 (Funty Nat_ty Nat_ty).
Proof.
  intros; eapply derive_subtype with
    (quant 1 (Funty Nat_ty (Funty (Funty (Var 0) (Var 0)) (Funty (Var 0) (Var 0))))); [
    |
      dist_tac; [ eapply sub_trans; [ eapply sub_lift | cbv; eapply sub_zero] | eapply sub_zero]];
    eapply derive_generalisation;  eapply derive_app; [
    |
      eapply derive_app; [
        eapply derive_node; eapply sub_leaf_fun |
        repeat eapply derive_S2; repeat eapply derive_K1; [ | | eapply derive_K]; eapply derive_node; eapply sub_leaf_fun]];
    eapply derive_node; eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac; repeat sub_fork2_tac; [ | subst_tac]; auto_t]. 
Qed.




Lemma num_closed: forall k x, occurs x (num k) = false.
Proof. induction k; intros; simpl; auto; rewrite IHk; auto. Qed.                                 

Lemma derive_num: forall k gamma, derive gamma (num k) Nat_ty.
Proof.
  induction k; intros; unfold num; fold num; simpl.
  - eapply derive_generalisation; simpl; eapply derive_K1; eapply derive_I.
  - replace (iter k (fun x => succ1 @ x) zero) with (num k) by auto;  eapply derive_app; [ eapply derive_succ1 | eauto]. 
Qed.


Theorem derive_isZero: forall gamma, derive gamma isZero (Funty Nat_ty Bool_ty).
Proof.
  intros; eapply derive_star; eapply derive_app; [ eapply derive_app | ]; [
      eapply derive_subtype; [ eapply derive_ref; simpl; eauto; eapply sub_zero | subst_tac] | 
      eapply derive_K1;  eapply derive_false |
      eapply derive_true].
Qed.


Theorem derive_cond: forall gamma ty, derive gamma cond (Funty Bool_ty (Funty ty (Funty ty ty))).
Proof.
  intros; eapply derive_S2; [ eapply derive_subtype; [ eapply derive_K | do 2 sub_fun_tac; subst_tac] | auto_t]. 
Qed.   


Proposition derive_PZero : forall gamma, derive gamma PZero (product Nat_ty Nat_ty). 
Proof. intros; eapply derive_pairL; eapply derive_generalisation; eapply derive_K1; eapply derive_I. Qed.

Proposition derive_PSucc : forall gamma, derive gamma PSucc (Funty (product Nat_ty Nat_ty) (product Nat_ty Nat_ty)). 
Proof.
  intros; unfold PSucc; eapply derive_star;  eapply derive_pairL; [
    | eapply derive_app; [ eapply derive_succ1 |]];
    (eapply derive_app; [ eapply derive_sndL
                       | eapply derive_ref; simpl; eauto]; eapply sub_zero).
Qed.


               
Theorem derive_predN : forall gamma, derive gamma predN (Funty Nat_ty Nat_ty).
Proof.
  intros; unfold predN; eapply derive_star; eapply derive_app; [ 
  eapply derive_fstL |];
    eapply derive_app; [
      eapply derive_app; [
        eapply derive_ref; simpl; eauto; subst_tac |
        eapply derive_PSucc] |
      eapply derive_PZero]. 
Qed.


Proposition derive_primrec0:
  forall gamma g h, derive gamma g Nat_ty -> derive gamma h (Funty Nat_ty (Funty Nat_ty Nat_ty)) ->
                 derive gamma (primrec0 g h) (Funty Nat_ty Nat_ty). 
Proof.
  intros; unfold primrec0; eapply derive_Y2.
  do 2 eapply derive_S2.  eapply derive_K1; eapply derive_node.
  all: cycle 1.
  eapply derive_S2. eapply derive_K1. eapply derive_node. eapply sub_leaf_fun.
  eapply derive_S2. eapply derive_K1. eapply derive_K.
  eapply derive_S2. eapply derive_subtype. eapply derive_isZero. sub_funty_tac. subst_tac.
  eapply derive_K1. eauto.
  eapply derive_S2. eapply derive_K1. eapply derive_node. eapply subtype_leaf_fork.
  eapply derive_S2. eapply derive_K1. eapply derive_node. eapply sub_leaf_fun. 
  eapply derive_S2. eapply derive_K1. eapply derive_K. 
  eapply derive_S2. eapply derive_K1. eauto. eapply derive_predN. 
  eapply derive_S2. eapply derive_K1. eapply derive_S1. eapply derive_I. 
  eapply derive_S2. eapply derive_K1. eapply derive_K. eapply derive_predN. 
  eapply sub_trans. eapply subtype_leaf_fork. do 2 sub_funty_tac.   repeat sub_fork2_tac. 
Qed.


Theorem derive_primrec:
  forall gamma xs g h, derive gamma g (iter (length xs) (Funty Nat_ty) Nat_ty) ->
                 derive gamma h (iter (2 + length xs) (Funty Nat_ty) Nat_ty) ->
                 Forall (fun x => derive gamma x Nat_ty) xs -> 
                 derive gamma (primrec g h xs) (Funty Nat_ty Nat_ty). 
Proof.
  intros; unfold primrec; eapply derive_primrec0.
  - generalize g H H1; clear;  induction xs; intros; simpl in *; auto; eapply IHxs; [
        eapply derive_app; eauto; inv_out H1; auto |
        inv_out H1; auto].
  - generalize h H0 H1; clear;  induction xs; intros; simpl in *; auto; eapply IHxs; [
        eapply derive_app; eauto; inv_out H1; auto | inv_out H1; auto].
Qed.


Proposition derive_minrec0:
  forall gamma f, derive gamma f (Funty Nat_ty Bool_ty) ->
            derive gamma (minrec0 f) (Funty Nat_ty Nat_ty).
Proof.
  intros; eapply derive_Y2;  eapply derive_S2; [ 
    |
      eapply derive_S2; [
  eapply derive_app; [
      eapply derive_K |
      eapply derive_app; [
        eapply derive_node; eapply subtype_leaf_fork |
        eapply derive_app; [  eapply derive_node; eapply sub_leaf_fun | eapply derive_I]]] | ]]. 
  repeat eapply derive_S2; repeat eapply derive_K1; try eapply derive_K; try eapply derive_node.
  2,4: eapply sub_leaf_fun.
  eapply sub_trans. eapply subtype_leaf_fork. do 2 sub_funty_tac.   do 2 sub_fork2_tac.
  eapply derive_subtype; eauto.   sub_funty_tac. subst_tac.
  repeat eapply derive_S2; repeat eapply derive_K1; try eapply derive_K; try eapply derive_node.
  eapply derive_succ1.
Qed.
 
Theorem derive_minrec:
  forall gamma xs f, derive gamma f (iter (length xs) (Funty Nat_ty) (Funty Nat_ty Bool_ty)) ->
                 Forall (fun x => derive gamma x Nat_ty) xs -> 
                 derive gamma (minrec f xs) (Funty Nat_ty Nat_ty). 
Proof.
  intros; unfold minrec; eapply derive_minrec0;
    generalize f H H0; clear;  induction xs; intros; simpl in *; auto; eapply IHxs; [
      eapply derive_app; eauto; inv_out H0; auto |
      inv_out H0; auto]. 
Qed. 

 
 
