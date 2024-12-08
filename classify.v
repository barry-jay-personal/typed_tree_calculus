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
(*                Classifying Subtyping                               *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)




Require Import String Arith Lia Bool List Nat.
Require Import terms types subtypes. 

Open Scope string_scope.
Open Scope nat_scope.

Set Default Proof Using "Type".




Proposition variant_subst_rec_preserves_subtype:
  forall ty k uty vty,  
    (variant true k ty = true ->
    subtype uty vty ->
    subtype (subst_rec ty uty k) (subst_rec ty vty k))
.

Proof.
   cut (forall ty k uty vty,
    (variant true k ty = true ->
    subtype uty vty ->
    subtype (subst_rec ty uty k) (subst_rec ty vty k))
    /\
   (variant false k ty = true ->
    subtype vty uty ->
    subtype (subst_rec ty uty k) (subst_rec ty vty k)))
 .
 intros.  eelim (H ty k uty vty); intros. eapply H2; auto.
 induction ty; intros; simpl in *; auto 10 with TreeHintDb.
  (* 6 *)
  assert(k<n\/ k = n\/ k>n) by lia; disjunction_tac; subst; var_tac; split; intros; try eapply sub_zero.
  eapply lift_rec_preserves_subtype; eauto.   rewrite Nat.eqb_refl in *; discriminate.
  (* 5 *)
  eelim (IHty (S k)); intros; split; intros; eapply sub_quant; eauto.
  (* 4 *)
  intros; split; intros; rewrite ! andb_true_iff in *; split_all. 
  eapply sub_funty.  eapply IHty1; eauto.
  eelim IHty2; intros.  eapply H; eauto. 
  eapply sub_funty.  eelim IHty1; intros. eapply H; eauto. eapply IHty2; eauto. 
  (* 3 *)
  eelim (IHty k uty vty); intros; split; intros; eapply sub_stem; eauto. 
  (* 2 *)
  eelim IHty1; eelim IHty2; intros; split; intros; rewrite ! andb_true_iff in *; split_all;  auto_t.  
  (* 1 *)
  eelim (IHty k uty vty); intros; split; intros; eapply sub_asf; eauto. 
Qed.

 


(* bfff_aug *) 


Lemma subtype_preserves_bfff_aug: forall ty1 ty2, subtype ty1 ty2 -> subtype (bfff_aug ty1) (bfff_aug ty2).
Proof. intros; eapply sub_fork; [ eapply sub_zero | auto_t]. Qed. 
  
Lemma subtype_preserves_iter_bfff_aug:
  forall n ty1 ty2, subtype ty1 ty2 -> subtype (iter n bfff_aug ty1) (iter n bfff_aug ty2).
Proof. induction n; intros; simpl. eauto.
       eapply sub_trans. eapply subtype_preserves_bfff_aug. eauto. eapply sub_zero.
Qed.
  


Lemma subtype_quant_bfff_aug: forall n ty, subtype (quant n (bfff_aug ty)) (bfff_aug (quant n ty)).
Proof.
  intros; unfold bfff_aug.    
  eapply sub_trans. eapply subtype_quant_fork. eapply sub_fork.
  replace (Stem (Fork Leaf eval_ty)) with (lift n (Stem (Fork Leaf eval_ty))) by (cbv; auto). 
  eapply subtype_lift2.
  eapply subtype_quant_asf.
Qed.

Lemma subtype_quant_iter_bfff_aug:
  forall k n ty, subtype (quant n (iter k bfff_aug ty)) (iter k bfff_aug (quant n ty)).
Proof.
  induction k; intros; simpl. eapply sub_zero.
  eapply sub_trans. eapply subtype_quant_bfff_aug.
  eapply sub_fork. eapply sub_zero. eapply sub_asf. auto. 
Qed.


Lemma bfff_aug_of_binary_fun :
  forall uty vty wty, subtype (bfff_aug (Funty uty (Funty vty wty)))  (Funty uty (Funty vty wty)).
Proof.  intros; unfold bfff_aug; repeat sub_fork2_tac. 2: auto_t. subst_tac; sub_fun_tac; auto_t. Qed. 


Lemma iter_bfff_aug_of_binary_fun :
  forall n uty vty wty, subtype (iter n bfff_aug (Funty uty (Funty vty wty)))  (Funty uty (Funty vty wty)).
Proof.
  induction n; intros; simpl. eapply sub_zero.
  eapply sub_trans. eapply subtype_preserves_bfff_aug. eauto. eapply bfff_aug_of_binary_fun.
Qed.     

Lemma iter_bfff_aug_Quant: forall n ty, subtype (iter n bfff_aug (Quant ty)) (Quant (iter n bfff_aug ty)).
Proof.
  induction n; intros; simpl. eapply sub_zero. 
  eapply sub_trans. eapply subtype_preserves_bfff_aug. eauto. 
  unfold bfff_aug at 1 3.
  eapply sub_trans. eapply sub_lift. eapply sub_quant. unfold lift; simpl; var_tac.
  eapply sub_fork. eapply sub_zero. eapply sub_asf.
  replace  (Quant (lift_rec (iter n bfff_aug ty) 1 1)) with
      (lift 1 (quant 1 (iter n bfff_aug ty))) by (cbv; auto).
  eapply subtype_lift3.
Qed. 


(* bffs_aug *) 


Lemma subtype_preserves_bffs_aug: forall ty1 ty2, subtype ty1 ty2 -> subtype (bffs_aug ty1) (bffs_aug ty2).
Proof. intros; eapply sub_fork; [ eapply sub_zero | eapply subtype_preserves_bfff_aug; auto_t]. Qed. 
  
Lemma subtype_preserves_iter_bffs_aug:
  forall n ty1 ty2, subtype ty1 ty2 -> subtype (iter n bffs_aug ty1) (iter n bffs_aug ty2).
Proof. induction n; intros; simpl. eauto.
       eapply sub_trans. eapply subtype_preserves_bffs_aug. eauto. eapply sub_zero.
Qed.
  


Lemma subtype_quant_bffs_aug: forall n ty, subtype (quant n (bffs_aug ty)) (bffs_aug (quant n ty)).
Proof.
  intros; unfold bffs_aug.    
  eapply sub_trans. eapply subtype_quant_fork. eapply sub_fork.
  replace (Stem (Fork Leaf eager_ty)) with (lift n (Stem (Fork Leaf eager_ty))) by (cbv; auto). 
  eapply subtype_lift2.
  eapply subtype_quant_bfff_aug.
Qed.

Lemma subtype_quant_iter_bffs_aug:
  forall k n ty, subtype (quant n (iter k bffs_aug ty)) (iter k bffs_aug (quant n ty)).
Proof.
  induction k; intros; simpl. eapply sub_zero.
  eapply sub_trans. eapply subtype_quant_bffs_aug.
  eapply sub_fork. eapply sub_zero. eapply subtype_preserves_bfff_aug; auto. 
Qed.


Lemma bffs_aug_of_binary_fun :
  forall uty vty wty, subtype (bffs_aug (Funty uty (Funty vty wty)))  (Funty uty (Funty vty wty)).
Proof.
  intros; eapply sub_trans; [ eapply sub_fork; [ eapply sub_zero | eapply bfff_aug_of_binary_fun] |
  repeat sub_fork2_tac; do 2 subst_tac]. 
Qed. 

Lemma iter_bffs_aug_of_binary_fun :
  forall n uty vty wty, subtype (iter n bffs_aug (Funty uty (Funty vty wty)))  (Funty uty (Funty vty wty)).
Proof.
  induction n; intros; simpl. eapply sub_zero.
  eapply sub_trans. eapply subtype_preserves_bffs_aug. eauto. eapply bffs_aug_of_binary_fun.
Qed.     

Lemma iter_bffs_aug_Quant: forall n ty, subtype (iter n bffs_aug (Quant ty)) (Quant (iter n bffs_aug ty)).
Proof.
  induction n; intros; simpl. eapply sub_zero. 
  eapply sub_trans. eapply subtype_preserves_bffs_aug. eauto. 
  unfold bffs_aug at 1 3.
  eapply sub_trans. 2: eapply (fork_quant_commute 1). eapply sub_fork.
  eapply sub_trans. eapply sub_lift. cbv; eapply sub_zero. eapply (iter_bfff_aug_Quant 1). 
Qed. 


(* classification *)

Inductive isLeafty : dtype -> Prop :=
| leaf_isLeafty : isLeafty Leaf
| quant_is_leafty : forall ty, isLeafty ty -> isLeafty (Quant ty)
.

Inductive isStemty : dtype -> Prop :=
| stem_isStemty : forall ty, isStemty (Stem ty)
| quant_is_stemty : forall ty, isStemty ty -> isStemty (Quant ty)
.


Inductive isForkty : dtype -> Prop :=
| fork_isForkty : forall uty vty, isForkty (Fork uty vty)
| quant_is_forkty : forall ty, isForkty ty -> isForkty (Quant ty)
.


Inductive isFunty : dtype -> Prop :=
| fun_isFunty : forall uty vty, isFunty (Funty uty vty)
| quant_is_funty : forall ty, isFunty ty -> isFunty (Quant ty)
| asf_is_funty : forall ty, isFunty (Asf ty)
.


Inductive not_funty: dtype -> Prop :=
| fork_not_funty: forall uty vty, isFunty uty -> not_funty (Fork uty vty)
| quant_not_funty : forall ty, not_funty ty -> not_funty (Quant ty)
| asf_not_funty : forall ty, not_funty ty -> not_funty (Asf ty)
.

  
Hint Constructors isLeafty isStemty isForkty isFunty not_funty: TreeHintDb.

Lemma isLeafty_quant: forall n ty, isLeafty ty -> isLeafty (quant n ty).
Proof. induction n; intros; auto_t. Qed.

Lemma isStemty_quant: forall n ty, isStemty ty -> isStemty (quant n ty).
Proof. induction n; intros; auto_t. Qed.

Lemma isForkty_quant: forall n ty, isForkty ty -> isForkty (quant n ty).
Proof. induction n; intros; auto_t. Qed.

Lemma isFunty_quant: forall n ty, isFunty ty -> isFunty (quant n ty).
Proof. induction n; intros; auto_t. Qed.

Lemma isFunty_quanta: forall bs ty, isFunty ty -> isFunty (quanta bs ty).
Proof.  induction bs; intros; auto_t; simpl; caseEq a; intros; subst; eapply IHbs; auto_t. Qed. 


Lemma funty_not: forall ty, isFunty ty -> ~ isLeafty ty /\ ~ isStemty ty /\ ~ isForkty ty.
Proof.
  intros ty isf; induction isf; intros; split_all; intro; try (inv_out H; fail); inv_out H0; auto.
Qed. 
  
Lemma leafty_not: forall ty, isLeafty ty -> ~ isFunty ty /\ ~ isStemty ty /\ ~ isForkty ty.
Proof.
  intros ty isf; induction isf; intros; split_all; intro; try (inv_out H; fail); inv_out H0; auto.
Qed. 
  
Lemma stemty_not: forall ty, isStemty ty -> ~ isLeafty ty /\ ~ isFunty ty /\ ~ isForkty ty.
Proof.
  intros ty isf; induction isf; intros; split_all; intro; try (inv_out H; fail); inv_out H0; auto.
Qed. 
  
Lemma forkty_not: forall ty, isForkty ty -> ~ isLeafty ty /\ ~ isStemty ty /\ ~ isFunty ty.
Proof.
  intros ty isf; induction isf; intros; split_all; intro; try (inv_out H; fail); inv_out H0; auto.
Qed. 


Lemma lift_rec_preserves_leafty: forall ty, isLeafty ty -> forall n k, isLeafty (lift_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma subst_rec_preserves_leafty: forall ty, isLeafty ty -> forall n k, isLeafty (subst_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma lift_rec_preserves_stemty: forall ty, isStemty ty -> forall n k, isStemty (lift_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma subst_rec_preserves_stemty: forall ty, isStemty ty -> forall n k, isStemty (subst_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma lift_rec_preserves_forkty: forall ty, isForkty ty -> forall n k, isForkty (lift_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma subst_rec_preserves_forkty: forall ty, isForkty ty -> forall n k, isForkty (subst_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma lift_rec_preserves_funty: forall ty, isFunty ty -> forall n k, isFunty (lift_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.

Lemma subst_rec_preserves_funty: forall ty, isFunty ty -> forall n k, isFunty (subst_rec ty n k).
Proof.  intros ty isL; induction isL; intros; simpl; auto_t. Qed.


Lemma not_funty_quant: forall n ty, not_funty (quant n ty) -> not_funty ty.
Proof. induction n; intros; simpl in *; auto_t; assert(not_funty (Quant ty)) by auto; inv_out H0; auto.  Qed. 
       
Lemma lift_rec_preserves_not_funty: forall ty, not_funty ty -> forall n k, not_funty (lift_rec ty n k).
Proof.
  intros ty isfs; induction isfs; intros; simpl; auto_t.   
  eapply fork_not_funty; eapply lift_rec_preserves_funty; auto. 
Qed.

Lemma subst_rec_preserves_not_funty: forall ty, not_funty ty -> forall n k, not_funty (subst_rec ty n k).
Proof.
  intros ty isfs; induction isfs; intros; simpl; auto_t.   
  eapply fork_not_funty; eapply subst_rec_preserves_funty; auto. 
Qed.


Lemma subtype_from_funty: forall ty1 ty2, subtype ty1 ty2 -> isFunty ty1 -> isFunty ty2.
Proof.
  intros ty1 ty2 s; induction s; intros; auto_t; try (inv_out H; auto_t; inv_out H1; auto_t; fail). 
  inv_out H; unfold subst; eapply subst_rec_preserves_funty; auto.
  unfold lift; eapply quant_is_funty; eapply lift_rec_preserves_funty; auto.
Qed.



Lemma subtype_from_leafty:
  forall ty1 ty2, subtype ty1 ty2 -> isLeafty ty1 -> (isLeafty ty2 \/ isFunty ty2).
Proof.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; repeat no_quant; try discriminate; eauto;
   try (inv_out H; auto_t; fail). 
  (* 10 *)
  eelim IHs1; intros; eauto; disjunction_tac; no_quant; right.  eapply subtype_from_funty; eauto. 
  inv_out H.   eelim IHs; intros; eauto; split_all; auto_t.
  all: try (inv_out H; inv_out H1; auto_t; fail).
  inv_out H. left; unfold subst; eapply subst_rec_preserves_leafty; auto. 
  left; eapply quant_is_leafty. unfold lift; eapply lift_rec_preserves_leafty; eauto.
Qed.




Lemma subtype_from_stemty: forall ty1 ty2, subtype ty1 ty2 -> isStemty ty1 -> isStemty ty2 \/ isFunty ty2.
Proof.
  intros ty1 ty2 s; induction s; intros; auto_t; try (inv_out H; auto_t; inv_out H1; auto_t; fail). 
  (* 4 *)
  eelim IHs1; intros; eauto; split_all; right; eapply subtype_from_funty; eauto. 
  (* 3 *)
  inv_out H; eelim IHs; intros; eauto; split_all; auto_t.
  inv_out H; unfold subst; left; eapply subst_rec_preserves_stemty; auto.
  unfold lift; left; eapply quant_is_stemty; eapply lift_rec_preserves_stemty; auto.
Qed.


Lemma subtype_from_forkty: forall ty1 ty2, subtype ty1 ty2 -> isForkty ty1 -> isForkty ty2 \/ isFunty ty2.
Proof.
  intros ty1 ty2 s; induction s; intros; auto_t; try (inv_out H; auto_t; inv_out H1; auto_t; fail). 
  (* 4 *)
  eelim IHs1; intros; eauto; split_all; right; eapply subtype_from_funty; eauto. 
  (* 3 *)
  inv_out H; eelim IHs; intros; eauto; split_all; auto_t.
  inv_out H; unfold subst; left; eapply subst_rec_preserves_forkty; auto.
  unfold lift; left; eapply quant_is_forkty; eapply lift_rec_preserves_forkty; auto.
Qed.




Lemma subtype_not_funty: forall ty1 ty2, subtype ty1 ty2 -> not_funty ty1 -> not_funty ty2.
Proof.
  intros ty1 ty2 s; induction s; intros; inv_out H; auto_t; try (inv_out H1; auto_t; fail).
  (* 6 *)
  eapply fork_not_funty; eapply subtype_from_funty; eauto.
  inv_out H1. eapply subst_rec_preserves_not_funty; auto_t. 
  unfold subst; simpl; eapply quant_not_funty; eapply subst_rec_preserves_not_funty; auto.
  unfold subst; simpl; eapply asf_not_funty; eapply subst_rec_preserves_not_funty; auto.
  eapply quant_not_funty; eapply lift_rec_preserves_not_funty; auto. eapply fork_not_funty; eauto. 
  eapply quant_not_funty; eapply lift_rec_preserves_not_funty; auto_t.
  eapply quant_not_funty; eapply lift_rec_preserves_not_funty; auto_t.
  inv_out H0; inv_out H1. 
Qed.


Ltac not_funty_tac :=
  intros; intro; eelim subtype_from_funty; intros; eauto;
  split_all; disjunction_tac; split_all; no_quant2_tac.



Lemma subtype_funty_not_leafty :
  forall ty1 ty2, subtype ty1 ty2 -> isFunty ty1 -> ~ isLeafty ty2.
Proof.  intros; assert(isFunty ty2) by (eapply subtype_from_funty; eauto); eapply funty_not; auto. Qed. 

Lemma subtype_funty_not_stemty :
  forall ty1 ty2, subtype ty1 ty2 -> isFunty ty1 -> ~ isStemty ty2.
Proof.  intros; assert(isFunty ty2) by (eapply subtype_from_funty; eauto); eapply funty_not; auto. Qed. 

Lemma subtype_funty_not_forkty :
  forall ty1 ty2, subtype ty1 ty2 -> isFunty ty1 -> ~ isForkty ty2.
Proof.  intros; assert(isFunty ty2) by (eapply subtype_from_funty; eauto); eapply funty_not; auto. Qed. 

Lemma subtype_leafty_not_stemty :
  forall ty1 ty2, subtype ty1 ty2 -> isLeafty ty1 -> ~ isStemty ty2.
Proof.
  intros; assert(isLeafty ty2 \/ isFunty ty2)
    by (eapply subtype_from_leafty; eauto); disjunction_tac.  eapply leafty_not; auto.
  eapply funty_not; eauto. 
Qed. 

Lemma subtype_leafty_not_forkty :
  forall ty1 ty2, subtype ty1 ty2 -> isLeafty ty1 -> ~ isForkty ty2.
Proof.
  intros; assert(isLeafty ty2 \/ isFunty ty2)
    by (eapply subtype_from_leafty; eauto); disjunction_tac.  eapply leafty_not; auto.
  eapply funty_not; eauto. 
Qed. 

Lemma subtype_stemty_not_leafty :
  forall ty1 ty2, subtype ty1 ty2 -> isStemty ty1 -> ~ isLeafty ty2.
Proof.
  intros; assert(isStemty ty2 \/ isFunty ty2)
    by (eapply subtype_from_stemty; eauto); disjunction_tac.  eapply stemty_not; auto.
  eapply funty_not; eauto. 
Qed. 

Lemma subtype_stemty_not_forkty :
  forall ty1 ty2, subtype ty1 ty2 -> isStemty ty1 -> ~ isForkty ty2.
Proof.
  intros; assert(isStemty ty2 \/ isFunty ty2)
    by (eapply subtype_from_stemty; eauto); disjunction_tac.  eapply stemty_not; auto.
  eapply funty_not; eauto. 
Qed. 

Lemma subtype_forkty_not_leafty :
  forall ty1 ty2, subtype ty1 ty2 -> isForkty ty1 -> ~ isLeafty ty2.
Proof.
  intros; assert(isForkty ty2 \/ isFunty ty2)
    by (eapply subtype_from_forkty; eauto); disjunction_tac.  eapply forkty_not; auto.
  eapply funty_not; eauto. 
Qed. 

Lemma subtype_forkty_not_stemty :
  forall ty1 ty2, subtype ty1 ty2 -> isForkty ty1 -> ~ isStemty ty2.
Proof.
  intros; assert(isForkty ty2 \/ isFunty ty2)
    by (eapply subtype_from_forkty; eauto); disjunction_tac.  eapply forkty_not; auto.
  eapply funty_not; eauto. 
Qed. 





Ltac not_subtype_tac:=
  try (
      match goal with
  | H : subtype (Funty _ _) _ |- _ => rewrite quant0 in H at 1
  | H : subtype Leaf _ |- _ => rewrite quant0 in H at 1
  | H : subtype (Stem _) _ |- _ => rewrite quant0 in H at 1
  | H : subtype (Fork _ _) _ |- _ => rewrite quant0 in H at 1
      end);
     try (
         match goal with        
  | H : subtype _ (Funty ?uty ?vty) |- _ => replace (Funty uty vty) with (quant 0 (Funty uty vty)) in H by auto
  | H : subtype _ Leaf |- _ => replace Leaf with (quant 0 Leaf)  in H by auto
  | H : subtype _ (Stem ?uty) |- _ => replace (Stem uty) with (quant 0 (Stem uty))  in H by auto
  | H : subtype _ (Fork ?uty ?vty) |- _ => replace (Fork uty vty) with (quant 0 (Fork uty vty))  in H by auto
      end);
     cut False;[
       tauto |
       match goal with 
       | H : subtype (quant _ (Funty _ _)) (quant _ Leaf) |- _ => eapply subtype_funty_not_leafty
       | H : subtype (quant _ (Funty _ _)) (quant _ (Stem _)) |- _ =>  eapply subtype_funty_not_stemty
       | H : subtype (quant _ (Funty _ _)) (quant _ (Fork _ _)) |- _ => eapply subtype_funty_not_forkty
       | H : subtype (quant _ Leaf) (quant _ (Stem _)) |- _ =>  eapply subtype_leafty_not_stemty
       | H : subtype (quant _ Leaf) (quant _ (Fork _ _)) |- _ =>  eapply subtype_leafty_not_forkty
       | H : subtype (quant _ (Stem _)) (quant _ Leaf) |- _ =>  eapply subtype_stemty_not_leafty
       | H : subtype (quant _ (Stem _)) (quant _ (Fork _ _)) |- _ => eapply subtype_stemty_not_forkty
       | H : subtype (quant _ (Fork _ _)) (quant _ Leaf) |- _ =>  eapply subtype_forkty_not_leafty
       | H : subtype (quant _ (Fork _ _)) (quant _ (Stem _)) |- _ => eapply subtype_forkty_not_stemty
         end;
       eauto]. 



Lemma subst_rec_to_stem:
  forall ty uty k n rty,
    subst_rec ty uty k = quant n (Stem rty) ->
    ((exists m ty0, ty = quant m (Stem ty0)) \/ exists m, ty = quant m (Var (m+k))).
Proof.
  induction ty; intros; subst; simpl in *; try (no_quant; fail).
  (* 3 *)
  generalize H; assert(n < k \/ n = k \/ n > k) by lia;
    disjunction_tac; insert_Var_tac; intro; no_quant; right; exists 0; simpl; auto. 
  (* 2 *)
  eelim IHty; intros; eauto; split_all.
  left; exists (S x); eexists; simpl; rewrite quant_succ; eauto.
  right; exists (S x); simpl; rewrite quant_succ; do 3 f_equal; try lia.
  rewrite H1.   instantiate(1:= S k); do 2 f_equal; lia.
  instantiate(1:= rty). instantiate(1:= pred n); instantiate(1:= uty); auto.    no_quant; auto.
  (* 1 *)
  no_quant. left; exists 0; simpl; eauto.
Qed.


Lemma subtype_to_stemty: 
  forall ty1 ty2,
    subtype ty1 ty2 ->
    forall n2 uty2,
      ty2 = quant n2 (Stem uty2) ->
      (subtype ty1 (Quant (Var 0)) \/
       exists n1 uty1,
         ty1 = quant n1 (Stem uty1) /\ 
         subtype (quant n1 uty1) (quant n2 uty2)).
Proof.
  intros ty1 ty2 s; induction s; intros; subst; no_quant; no_quant.
  (* 9 *)
  right; repeat eexists; auto_t.
  (* 8 *)
  eelim IHs2; intros; eauto; split_all.
  left; eapply sub_trans; eauto.
  eelim IHs1; intros.  3: eauto.  left; auto. split_all. right; repeat eexists; eauto. eapply sub_trans; eauto. 
  (* 7 *)
  right; exists 0; repeat eexists; auto_t.
  (* 6 *) 
  eelim IHs; intros; eauto; split_all.
  left; eapply sub_trans.   eapply sub_quant; eauto. subst_tac.
  right; repeat eexists. instantiate(2:= S x); simpl; rewrite quant_succ; eauto. 
  simpl; rewrite quant_succ; auto_t.
  (* 5 *)
  right; exists 1; repeat eexists; auto_t.
  caseEq ty; intros; subst; unfold subst in *; simpl in *; no_quant.
  generalize H1; caseEq n; intro; subst; insert_Var_tac; intro; subst.   
  left; eapply sub_zero.
  discriminate.
  (* 4 *)
  inv_out H1; right; exists 1; repeat eexists; subst_tac.
  (* 3 *)
  eelim subst_rec_to_stem; intros. 
  3: rewrite quant_succ2 in *; eauto. 
  split_all.
  right; exists (S x); repeat eexists. simpl; rewrite quant_succ; eauto.
  unfold subst in *; rewrite subst_rec_preserves_quant in *; simpl in *.   
  no_quant2_tac. inv_out H0. 
  rewrite quant_succ.   subst_tac. rewrite subst_rec_preserves_quant. eapply sub_zero.
  split_all.
  left; rewrite plus_0_r. eapply sub_quant. 
  clear. induction x; intros.  auto_t.
  simpl. eapply sub_trans; eauto. eapply subtype_quant. subst_tac; var_tac.
  (* 2 *)
  caseEq ty; intros; subst; unfold lift in *; simpl in *; no_quant.
  inv_out H0.   right; exists 0; repeat eexists; simpl; auto_t.
  (* 1 *)
  assert(subst (lift 1 ty) Leaf = subst (quant (S n0) (Stem uty2)) Leaf).
  simpl; rewrite quant_succ; f_equal; eauto.
  generalize H. unfold subst, lift; rewrite subst_rec_lift_rec; try lia.
  rewrite lift_rec_null; intro; subst.
  right. exists (S n0); repeat eexists. 
  rewrite subst_rec_preserves_quant.   simpl; eauto.
  unfold lift in *. rewrite subst_rec_preserves_quant in *. 
  rewrite lift_rec_preserves_quant in *.
  simpl in *; inv_out H0. 
  rewrite quant_succ in H2. inv_out H2. no_quant2_tac. inv_out H2. 
  rewrite <- H4 in *.
  rewrite ! plus_0_r . 
  rewrite subst_rec_lift_rec; try lia.
  rewrite subst_rec_lift_rec; try lia.
  erewrite lift_rec_lift_rec; try lia. simpl. 
  eapply sub_trans. eapply sub_lift.
  unfold lift. rewrite lift_rec_preserves_quant.
  simpl. rewrite quant_succ. rewrite plus_0_r.  rewrite ! quant_succ; eapply sub_zero.
  Unshelve.
  all: apply Leaf.
Qed.

Lemma subtype_of_stemty:  forall uty vty, subtype (Stem uty) (Stem vty) -> subtype uty vty.
Proof.
  intros; eelim subtype_to_stemty; intros.  3: eauto. 3: instantiate(2:= 0); simpl; eauto.
  clear H. eelim subtype_from_stemty; intros; eauto; split_all. 3: auto_t. 1,2: inv_out H; inv_out H2.
  split_all; no_quant; auto. 
Qed.




Lemma subst_rec_to_fork:
  forall ty uty k n rty sty,
    subst_rec ty uty k = quant n (Fork rty sty) ->
    ((exists m rty0 sty0, ty = quant m (Fork rty0 sty0)) \/ exists m, ty = quant m (Var (m+k))).
Proof.
  induction ty; intros; subst; simpl in *; try (no_quant; fail).
  (* 3 *)
  generalize H; assert(n < k \/ n = k \/ n > k) by lia;
    disjunction_tac; insert_Var_tac; intro; no_quant; right; exists 0; simpl; auto. 
  (* 2 *)
  no_quant.  eelim IHty; intros; eauto; split_all.
  left; exists (S x); repeat eexists; simpl; rewrite quant_succ; eauto.
  right; exists (S x); simpl; rewrite quant_succ; do 3 f_equal; try lia.
  no_quant. left; exists 0; repeat eexists;  eauto. 
Qed.

  



Lemma subtype_to_forkty: 
  forall ty1 ty2,
    subtype ty1 ty2 ->
    forall n2 uty2 vty2,
      ty2 = quant n2 (Fork uty2 vty2) ->
      (subtype ty1 (Quant (Var 0)) \/
       exists n1 uty1 vty1,
         ty1 = quant n1 (Fork uty1 vty1) /\ 
         subtype (quant n1 uty1) (quant n2 uty2) /\ 
         subtype (quant n1 vty1) (quant n2 vty2)).
Proof.
  intros ty1 ty2 s; induction s; intros; subst; no_quant; no_quant.
  (* 9 *)
  right; repeat eexists; auto_t.
  (* 8 *)
  eelim IHs2; intros; eauto; split_all.
  left; eapply sub_trans; eauto.
  eelim IHs1; intros.  3: eauto.  left; auto. split_all. right; repeat eexists; eauto.
  1,2: eapply sub_trans; eauto. 
  (* 7 *)
  right; exists 0; repeat eexists; auto_t.
  (* 6 *) 
  eelim IHs; intros; eauto; split_all.
  left; eapply sub_trans.   eapply sub_quant; eauto. subst_tac.
  right; repeat eexists. instantiate(3:= S x); simpl; rewrite quant_succ; eauto. 
  1,2:  simpl; rewrite quant_succ; auto_t.
  (* 5 *)
  right; exists 1; repeat eexists; auto_t.
  caseEq ty; intros; subst; unfold subst in *; simpl in *; no_quant.
  generalize H1; caseEq n; intro; subst; insert_Var_tac; intro; subst.   
  left; eapply sub_zero.
  intro;  discriminate.
  (* 4 *)
  inv_out H1; right; exists 1; repeat eexists; subst_tac.
  (* 3 *)
  eelim subst_rec_to_fork; intros. 
  3: rewrite quant_succ2 in *; eauto. 
  split_all.
  right; exists (S x); repeat eexists. simpl; rewrite quant_succ; eauto.
  unfold subst in *; rewrite subst_rec_preserves_quant in *; simpl in *.   
  no_quant2_tac. inv_out H0. 
  rewrite quant_succ.   subst_tac. rewrite subst_rec_preserves_quant. eapply sub_zero.
  unfold subst in *; rewrite subst_rec_preserves_quant in *; simpl in *.   
  no_quant2_tac. inv_out H0. 
  rewrite quant_succ.   subst_tac. rewrite subst_rec_preserves_quant. eapply sub_zero.
  split_all.
  left; rewrite plus_0_r. eapply sub_quant. 
  clear. induction x; intros.  auto_t.
  simpl. eapply sub_trans; eauto. eapply subtype_quant. subst_tac; var_tac.
  (* 2 *)
  caseEq ty; intros; subst; unfold lift in *; simpl in *; no_quant.
  inv_out H0.   right; exists 0; repeat eexists; simpl; auto_t.
  (* 1 *)
  assert(subst (lift 1 ty) Leaf = subst (quant (S n0) (Fork uty2 vty2)) Leaf).
  simpl; rewrite quant_succ; f_equal; eauto.
  generalize H. unfold subst, lift; rewrite subst_rec_lift_rec; try lia.
  rewrite lift_rec_null; intro; subst.
  right. exists (S n0); repeat eexists. 
  rewrite subst_rec_preserves_quant.   simpl; eauto.
  (* 2 *)
  unfold lift in *. rewrite subst_rec_preserves_quant in *. 
  rewrite lift_rec_preserves_quant in *.
  simpl in *; inv_out H0. 
  rewrite quant_succ in H2. inv_out H2. no_quant2_tac. inv_out H2. 
  rewrite <- H4 in *.
  rewrite ! plus_0_r . 
  rewrite subst_rec_lift_rec; try lia.
  rewrite subst_rec_lift_rec; try lia.
  erewrite lift_rec_lift_rec; try lia. simpl. 
  eapply sub_trans. eapply sub_lift.
  unfold lift. rewrite lift_rec_preserves_quant.
  simpl. rewrite quant_succ. rewrite plus_0_r.  rewrite ! quant_succ; eapply sub_zero.
  (* 1 *)
  unfold lift in *. rewrite subst_rec_preserves_quant in *. 
  rewrite lift_rec_preserves_quant in *.
  simpl in *; inv_out H0. 
  rewrite quant_succ in H2. inv_out H2. no_quant2_tac. inv_out H2. 
  rewrite <- H5 in *.
  rewrite ! plus_0_r . 
  rewrite subst_rec_lift_rec; try lia.
  rewrite subst_rec_lift_rec; try lia.
  erewrite lift_rec_lift_rec; try lia. simpl. 
  eapply sub_trans. eapply sub_lift.
  unfold lift. rewrite lift_rec_preserves_quant.
  simpl. rewrite quant_succ. rewrite plus_0_r.  rewrite ! quant_succ; eapply sub_zero.
  Unshelve.
  all: apply Leaf.
Qed.



Lemma subtype_of_forkty:
  forall uty vty uty2 vty2, subtype (Fork uty vty) (Fork uty2 vty2) ->
                            subtype uty uty2 /\ subtype vty vty2. 
Proof.
  intros; eelim subtype_to_forkty; intros.  3: eauto. 3: instantiate(3:= 0); simpl; eauto.
  clear H. eelim subtype_from_forkty; intros; eauto; split_all. 5: auto_t. 1-4: inv_out H; inv_out H2.
  split_all; no_quant; auto. 
Qed.


(*** Introducing and instantiating a sequence of quantifiers *)



Inductive chip : Set :=
| Lift : nat -> chip
| Inst: dtype -> nat -> chip
.

Hint Constructors chip : TreeHintDb.


Fixpoint trim sigma ty :=
  match sigma with
  | nil => ty
  | Lift k :: sigma1 => trim sigma1 (lift_rec ty k 1)
  | Inst u k :: sigma1 => trim sigma1 (subst_rec ty u k)
  end.


Definition chip_lift p sc :=
  match sc with
  | Lift k => Lift (p+ k)
  | Inst u k => Inst u (p+ k)
  end.

Lemma trim_lift_miss:
  forall sigma k n, k > n -> trim (map (chip_lift k) sigma) (Var n) = Var n.
Proof. induction sigma; intros; simpl; auto; caseEq a; intros; subst; simpl; eauto.
       assert(k + n0 <= n \/ k + n0 > n) by lia; disjunction_tac; relocate_tac; eauto.
       insert_Var_tac; eauto.
Qed.


Lemma chip_lift_zero:
  forall sigma, map (chip_lift 0) sigma = sigma.
Proof. induction sigma; intros; simpl; auto; caseEq a; intros; subst; simpl; rewrite IHsigma; eauto. Qed. 

Lemma chip_lift_plus:
  forall sigma p q, map (chip_lift p) (map (chip_lift q) sigma) = map (chip_lift (p+q)) sigma.
Proof.
  induction sigma; intros; simpl; auto; rewrite IHsigma;
         caseEq a; intros; subst; simpl; f_equal; f_equal; lia.
Qed. 


Lemma chip_lift_trim:
  forall sigma k ty,  lift k (trim sigma ty) = trim (map (chip_lift k) sigma) (lift k ty).
Proof.
  induction sigma; intros; unfold lift in *; simpl; auto.                                                      
  caseEq a; intros; subst; simpl; rewrite IHsigma.  
  rewrite lift_lift_rec; try lia; auto.
  rewrite <- subst_rec_lift_rec1; auto; lia. 
Qed.


Lemma trim_Quant :
  forall sigma ty,
    trim sigma (Quant ty) = Quant (trim (map (chip_lift 1) sigma) ty). 
Proof.
  induction sigma; intros; simpl; auto; caseEq a; intros; unfold lift; simpl; rewrite IHsigma; auto.
Qed.


Lemma trim_quant :
  forall p sigma ty,
    trim sigma (quant p ty) = quant p (trim (map (chip_lift p) sigma) ty). 
Proof.
  induction p; intros; simpl; auto.  rewrite chip_lift_zero; auto.
  rewrite IHp; rewrite ? trim_Quant;   auto. rewrite chip_lift_plus; auto. 
Qed.


Lemma trim_funty :
  forall sigma uty vty,
    trim sigma (Funty uty vty) = Funty (trim sigma uty) (trim sigma vty).
Proof.
  cut (forall k sigma, length sigma < k ->   forall uty vty,
    trim sigma (Funty uty vty) = Funty (trim sigma uty) (trim sigma vty)).
   intros. eapply H. instantiate(1:= S (length sigma)); lia. 
   induction k; intros; simpl; auto.  lia.
   caseEq sigma; intros; subst; simpl; auto. caseEq c; intros; subst; unfold lift; simpl in *; 
   eapply IHk; lia. 
Qed.

Lemma trim_leaf :
  forall sigma,
    trim sigma Leaf = Leaf. 
Proof.
  cut (forall k sigma, length sigma < k ->  
    trim sigma Leaf = Leaf).
   intros. eapply H. instantiate(1:= S (length sigma)); lia. 
   induction k; intros; simpl; auto.  lia.
   caseEq sigma; intros; subst; simpl; auto. caseEq c; intros; subst; unfold lift; simpl in *; 
   eapply IHk; lia. 
Qed.

Lemma trim_stem :
  forall sigma uty,
    trim sigma (Stem uty) = Stem (trim sigma uty).
Proof.
  cut (forall k sigma, length sigma < k ->   forall uty,
    trim sigma (Stem uty) = Stem (trim sigma uty)).
   intros. eapply H. instantiate(1:= S (length sigma)); lia. 
   induction k; intros; simpl; auto.  lia.
   caseEq sigma; intros; subst; simpl; auto. caseEq c; intros; subst; unfold lift; simpl in *; 
   eapply IHk; lia. 
Qed.

Lemma trim_fork :
  forall sigma uty vty,
    trim sigma (Fork uty vty) = Fork (trim sigma uty) (trim sigma vty).
Proof.
  cut (forall k sigma, length sigma < k ->   forall uty vty,
    trim sigma (Fork uty vty) = Fork (trim sigma uty) (trim sigma vty)).
   intros. eapply H. instantiate(1:= S (length sigma)); lia. 
   induction k; intros; simpl; auto.  lia.
   caseEq sigma; intros; subst; simpl; auto. caseEq c; intros; subst; unfold lift; simpl in *; 
   eapply IHk; lia. 
Qed.


Lemma trim_asf :
  forall sigma uty,
    trim sigma (Asf uty) = Asf (trim sigma uty).
Proof.
  cut (forall k sigma, length sigma < k ->   forall uty,
    trim sigma (Asf uty) = Asf (trim sigma uty)).
   intros. eapply H. instantiate(1:= S (length sigma)); lia. 
   induction k; intros; simpl; auto.  lia.
   caseEq sigma; intros; subst; simpl; auto. caseEq c; intros; subst; unfold lift; simpl in *; 
   eapply IHk; lia. 
Qed.


Lemma trim_app:
  forall sigma1 sigma2 ty,
    trim (app sigma1 sigma2) ty = trim sigma2 (trim sigma1 ty). 
Proof. induction sigma1; intros; simpl; auto; caseEq a; intros; auto. Qed. 


  
Lemma trim_quantf : forall p sigma ty, trim sigma (quantf p ty) = quantf p (trim sigma ty). 
Proof. induction p; intros; simpl; auto; rewrite IHp; rewrite trim_asf; auto. Qed.




Ltac trim_tac :=
  rewrite ? trim_quant in *;
  rewrite ? trim_leaf in *;
  rewrite ? trim_stem in *;
  rewrite ? trim_fork in *;
  rewrite ? trim_funty in *;
  rewrite ? trim_Quant in *; try discriminate.


Lemma trim_preserves_bfff_aug:
  forall sigma ty, trim sigma (bfff_aug ty) = bfff_aug (trim sigma ty).
Proof.
  intros; unfold bfff_aug,eval_ty,quant; repeat trim_tac; rewrite ! trim_asf; rewrite trim_lift_miss; auto; lia.
Qed.



Lemma trim_preserves_iter_bfff_aug:
  forall n sigma ty, trim sigma (iter n bfff_aug ty) = iter n bfff_aug (trim sigma ty).
Proof. induction n; intros; simpl; auto; rewrite trim_preserves_bfff_aug; f_equal; auto. Qed. 


Lemma trim_preserves_bffs_aug:
  forall sigma ty, trim sigma (bffs_aug ty) = bffs_aug (trim sigma ty).
Proof.
  intros; unfold bffs_aug,eval_ty,quant; repeat trim_tac; repeat f_equal.
  cbv; repeat trim_tac; auto; rewrite chip_lift_plus. rewrite ! trim_lift_miss; auto; lia.
  eapply trim_preserves_bfff_aug. 
Qed.



Lemma trim_preserves_iter_bffs_aug:
  forall n sigma ty, trim sigma (iter n bffs_aug ty) = iter n bffs_aug (trim sigma ty).
Proof. induction n; intros; simpl; auto; rewrite trim_preserves_bffs_aug; f_equal; auto. Qed. 

                                                            
Ltac no_quant ::=
  split_all;
  match goal with
  | H : _ = quant ?k _ |- _ => caseEq k; intros; subst; simpl in *; rewrite ? quant_succ in *; inv_out H
  | H : quant ?k _ = _ |- _ => caseEq k; intros; subst; simpl in *; rewrite ? quant_succ in *; inv_out H
  | _ => idtac
           end; 
  rewrite ? trim_quant in *;
  rewrite ? trim_funty in *;
  rewrite ? trim_leaf in *;
  rewrite ? trim_stem in *;
  rewrite ? trim_fork in *. 

 

Inductive  chip_count : list chip -> nat -> nat -> Prop :=
| chip_count_nil : forall n, chip_count nil n n
| chip_count_lift : forall k sigma m n, k <= m -> chip_count sigma (S m) n -> chip_count (Lift k :: sigma) m n
| chip_count_inst : forall u k sigma m n, k <= m -> chip_count sigma m n -> chip_count (Inst u k ::sigma) (S m) n
.

Hint Constructors chip_count : TreeHintDb. 


Lemma chip_count_succ: forall sigma m n, chip_count sigma m n -> chip_count sigma (S m) (S n).
Proof.  induction sigma; intros; simpl; inv_out H; auto with TreeHintDb. Qed. 

Lemma chip_count_plus: forall p sigma m n, chip_count sigma m n -> chip_count sigma (p+ m) (p+ n).
Proof.  induction p; intros; simpl; auto; eapply chip_count_succ; eauto. Qed. 



Lemma chip_count_map: forall sigma m n p, chip_count sigma m n -> chip_count (map (chip_lift p) sigma) (p+ m) (p+ n).
Proof.
  induction sigma; intros; simpl; inv_out H; simpl;  auto with TreeHintDb.
    eapply chip_count_lift; [  lia | replace (S (p+m)) with (p + S m) by lia;  eapply IHsigma; auto]. 
    replace (p + S m0) with (S (p+m0)) by lia; eapply chip_count_inst; [ lia | eapply IHsigma; auto]. 
Qed. 


Lemma chip_count_down: forall n p, exists sigma, chip_count sigma (n+p) p.
Proof. induction n; intros; simpl; auto_t; eelim (IHn p); intros; 
       exists (Inst Leaf 0 :: x); eapply chip_count_inst; eauto; lia. 
Qed.

Lemma chip_count_up: forall n p, exists sigma, chip_count sigma p (p+n).
Proof.
  induction n; intros; simpl; auto_t.
  replace (p+0) with p by lia; auto_t.
  eelim (IHn (S p)); intros. 
  exists (Lift 0 :: x); eapply chip_count_lift; eauto. lia.
  replace (p + S n) with (S p + n) by lia; auto. 
Qed.

Lemma chip_count_links: forall n p, exists sigma, chip_count sigma n p.
Proof.
  intros; assert(n <= p \/ n > p) by lia; disjunction_tac. 
  replace p with (n + (p - n)) by lia. eapply chip_count_up. 
  replace n with (n - p + p) by lia. eapply chip_count_down. 
Qed.


Lemma chip_count_decr: forall k sigma m n, chip_count sigma (k+m) n -> exists sigma2, chip_count sigma2 m n.
Proof.
  induction k; intros; simpl in *; eauto; eapply IHk; instantiate(1:= Lift 0 :: sigma);
         eapply chip_count_lift; auto; lia.
Qed. 

Lemma chip_count_app:
  forall sigma1 n1 n2,
    chip_count sigma1 n1 n2 ->
    forall sigma2 n3, chip_count sigma2 n2 n3 -> chip_count (app sigma1 sigma2) n1 n3.
Proof.
  induction sigma1; intros; simpl; eauto; inv_out H; auto.
  eapply chip_count_lift; auto. eapply IHsigma1; eauto.
  eapply chip_count_inst; auto. eapply IHsigma1; eauto.
Qed. 
  
Lemma chip_count_app2
  : forall sigma1 sigma2 m n p q r,
    chip_count sigma1 m (n+p) -> chip_count sigma2 p (q + r) ->
    chip_count (sigma1 ++ (map (chip_lift n) sigma2)) m (n+q+r).
Proof.
  intros; eapply chip_count_app; eauto;
    replace (n + q + r) with (n + (q + r)) by lia;
    eapply chip_count_map; eauto.
Qed.


Lemma lift_preserves_trim:
  forall sigma p ty, lift p (trim sigma ty) = trim (map (chip_lift p) sigma) (lift p ty).
Proof.
  cut (forall k sigma, length sigma < k -> forall p
   ty, lift p (trim sigma ty) = trim (map (chip_lift
                                                                 p) sigma) (lift p ty)).
  intros; eapply H; eauto.  induction k; intros; simpl; auto_t. lia.
  caseEq sigma; intros; subst;  simpl in *; auto.
  caseEq c; intros; subst; simpl; rewrite IHk; try lia.
  unfold lift; rewrite lift_lift_rec; try lia; auto.
  unfold lift; rewrite subst_rec_lift_rec1; try lia; auto.
Qed.


Lemma lift_rec_preserves_trim
     : forall sigma  (p : nat) (ty : dtype),
    lift_rec (trim sigma ty) 0 p = trim (map (chip_lift p) sigma) (lift_rec ty 0 p).
Proof.
  intros;
    replace (lift_rec (trim sigma ty) 0 p) with (lift p (trim sigma ty)) by auto;
    replace (lift_rec ty 0 p) with (lift p ty) by auto. eapply lift_preserves_trim.
Qed.
            

Lemma trim_preserves_subst_rec:
  forall ty uty k sigma, trim (map (chip_lift k) sigma) (subst_rec ty uty k) = 
                      subst_rec (trim (map (chip_lift (S k)) sigma) ty) (trim sigma uty) k.
Proof.   
  induction ty; intros; simpl; eauto. 
  (* 7 *)
  assert(n < k \/ n = k \/ n>k) by lia; disjunction_tac; insert_Var_tac.
  rewrite ! trim_lift_miss; try lia; simpl;  var_tac; auto. 
  replace (lift_rec uty 0 k) with (lift k uty)
    by auto. rewrite <- lift_preserves_trim.
  rewrite ! trim_lift_miss; try lia. simpl; var_tac; auto. 
  replace (Var (pred n)) with (lift k (Var (pred n - k))) by (unfold lift; simpl; relocate_tac; f_equal; lia).
  replace (Var n) with (lift (S k) (Var (n - S k))) by (unfold lift; simpl; relocate_tac; f_equal; lia).
  rewrite <- ! lift_preserves_trim.
  unfold lift; rewrite subst_rec_lift_rec; try lia; auto.
  f_equal; f_equal; f_equal; lia. 
  (* 6 *)
  rewrite ! trim_Quant; simpl. rewrite chip_lift_plus. simpl. rewrite IHty.
  rewrite chip_lift_plus. auto.
  (* 5 *)
  rewrite ! trim_funty; simpl; f_equal; auto. 
  (* 4 *)
  rewrite ! trim_leaf; simpl; f_equal; auto. 
  rewrite ! trim_stem; simpl; f_equal; auto. 
  rewrite ! trim_fork; simpl; f_equal; auto. 
  rewrite ! trim_asf; simpl; f_equal; auto. 
  Qed. 



Lemma trim_preserves_isFunty: forall sigma ty, isFunty ty -> isFunty (trim sigma ty). 
Proof.
  induction sigma; intros; simpl; auto. caseEq a; intros; subst; eapply IHsigma. 
  eapply lift_rec_preserves_funty; auto.
  eapply subst_rec_preserves_funty; auto.
Qed.

Lemma trim_preserves_isLeafty: forall sigma ty, isLeafty ty -> isLeafty (trim sigma ty). 
Proof.
  induction sigma; intros; simpl; auto. caseEq a; intros; subst; eapply IHsigma. 
  eapply lift_rec_preserves_leafty; auto.
  eapply subst_rec_preserves_leafty; auto.
Qed.


Lemma trim_preserves_isStemty: forall ty, isStemty ty -> forall sigma, isStemty (trim sigma ty).
Proof. intros ty isF; induction isF; intros; trim_tac; auto_t;  rewrite trim_asf; auto_t.  Qed.

Lemma subtype_to_asf: forall n ty, subtype ty (quantf n ty).
Proof.  induction n; intros; simpl; auto_t.  Qed.

Lemma subtype_from_asf: forall n uty vty, subtype (quantf n (Funty uty vty)) (Funty uty vty).
Proof.
  induction n; intros; simpl; auto_t; eapply sub_trans; [ eapply subtype_quantf; eapply sub_from_asf |
                                                          eapply IHn].        
Qed.



Lemma trim_preserves_subtype:
  forall sigma ty1 ty2, subtype ty1 ty2 -> subtype (trim sigma ty1) (trim sigma ty2).
Proof.
  induction sigma; intros; subst; simpl; eauto 2 with TreeHintDb. 
  caseEq a; intros; subst; eapply IHsigma.
  unfold lift; eapply lift_rec_preserves_subtype; eauto.
  unfold subst; eapply subst_rec_preserves_subtype; eauto. 
Qed.

Lemma subtype_by_trim:
  forall sigma m n ty,
    chip_count sigma m n -> subtype (quant m ty) (quant n (trim sigma ty)). 
Proof.
  induction sigma; intros; subst; simpl; inv_out H; try  eapply sub_zero.
  (* 2 *)
  assert(subtype (quant (S m) (lift_rec ty k 1)) (quant n (trim sigma (lift_rec ty k 1)))).
  eapply IHsigma; eauto.   eapply sub_trans; eauto.
  replace (quant m) with (quant (m-k + k)) by (f_equal; lia).   rewrite quant_plus.
  eapply sub_trans. eapply subtype_quant. eapply sub_lift.
  unfold lift; rewrite lift_rec_preserves_quant.
  rewrite quant_succ; rewrite quant_succ2; rewrite <- quant_plus.
  replace (S (m-k) + k) with (S m) by lia. replace (k+0) with k by lia. eapply sub_zero.
  (* 1 *)
  replace (quant (S m0)) with (quant (m0-k + 1 + k)) by (f_equal; lia).   rewrite ! quant_plus.
  assert(subtype (quant m0 (subst_rec ty u k)) (quant n (trim sigma (subst_rec ty u k)))).
  eapply IHsigma; eauto.   eapply sub_trans; eauto.
  eapply sub_trans. eapply subtype_quant. simpl. eapply sub_inst.
  unfold subst; rewrite subst_rec_preserves_quant.
  rewrite <- quant_plus.
  replace (m0-k + k) with m0 by lia. replace (k+0) with k by lia. eapply sub_zero.
Qed.



Ltac trim2_tac :=   eapply sub_trans; [ eapply subtype_by_trim |]; eauto.



Lemma trim_program_type:
  forall p, program p -> forall sigma, trim sigma (program_type p) = program_type p.
Proof.  intros p pr; induction pr; intros; simpl; trim_tac; f_equal; eauto. Qed. 


Lemma trim_lift2:
  forall sigma n1 n2 ty,
    chip_count sigma n1 n2 ->
    subtype (trim sigma (lift n1 (quant n2 ty))) ty .
 Proof.
   induction sigma; intros; eauto; inv_out H; simpl; unfold lift; try eapply lift_rec_null. 
   (* 3 *)
   eapply subtype_lift3.
   (* 2 *)
   rewrite ! lift_rec_lift_rec; try lia; simpl; eapply IHsigma; auto.
   (* 1 *)
   rewrite ! subst_rec_lift_rec; try lia;  eapply IHsigma; auto.
 Qed.


Lemma trim_quanta :
  forall bs sigma ty,
    trim sigma (quanta bs ty) = quanta bs (trim (map (chip_lift (quant_count bs)) sigma) ty). 
Proof.
  induction bs; intros; simpl; auto. rewrite chip_lift_zero; auto.
  caseEq a; intros; subst; simpl; rewrite IHbs; rewrite ? trim_Quant; auto.
  rewrite chip_lift_plus; auto. 
  rewrite trim_asf; auto. 
Qed.

    
Lemma chip_lift_variant:
  forall ty b n sigma k,  n < k -> variant b n (trim (map (chip_lift k) sigma) ty) = variant b n ty.
Proof.
  induction ty; intros; simpl.
  (* 7 *)
  assert(n < k \/ n>= k) by lia; disjunction_tac.
  rewrite ! trim_lift_miss; try lia; simpl; auto.
  replace (Var n) with (lift k (Var (n-k))) by (unfold lift; simpl; relocate_tac; f_equal; lia).
  rewrite <- ! lift_preserves_trim; simpl.
  unfold lift; rewrite lift_rec_preserves_variant3; try lia.
  assert(n0=? n = false) by (eapply Nat.eqb_neq; lia). rewrite H0; auto. 
  (* 6 *)
  rewrite ! trim_Quant; simpl. rewrite chip_lift_plus. simpl. rewrite IHty; try lia; auto. 
  (* 5 *)
  rewrite ! trim_funty; simpl; f_equal; auto.
  rewrite ! trim_leaf; simpl; f_equal; auto. 
  rewrite ! trim_stem; simpl; auto. 
  rewrite ! trim_fork; simpl. rewrite ! IHty1; try lia; rewrite ! IHty2; try lia; auto. 
  rewrite ! trim_asf; simpl; auto. 
  Qed. 
  
 

(*** classification of subtyping to show reduction preserves typing *) 


Proposition subtype_from_stemty4:
  forall n uty ty2,
    subtype (quant n (Stem uty)) ty2 ->
    isFunty ty2 \/ 
    exists n2 uty2,
      subtype (quant n uty) (quant n2 uty2) /\
      ty2 = quant n2 (Stem uty2).
Proof.
  cut (forall ty1 ty2,
    subtype ty1 ty2 ->
    forall n uty,
    ty1 = quant n (Stem uty) -> 
    isFunty ty2 \/ 
    exists n2 uty2,
      subtype (quant n uty) (quant n2 uty2) /\
      ty2 = quant n2 (Stem uty2)).
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate;
    auto_t; no_quant; no_quant.
  (* 6 *)
  eelim IHs1; intros; eauto; no_quant; disjunction_tac; no_quanta. 
  left; eapply subtype_from_funty; eauto.
  eelim IHs2; intros.  3: eauto. auto. split_all. right; repeat eexists; auto_t.
  (* 5 *)
  right; exists 0; repeat eexists; auto. 
  (* 4 *)
  eelim IHs; intros; eauto.   left; auto_t. split_all.
  right; exists (S x); repeat eexists; simpl; rewrite quant_succ; eauto; auto_t.
  (* 3 *)
  right; exists 0; repeat eexists; eauto; eapply sub_zero.
  (* 2 *)
  right; repeat eexists. 2: unfold subst; rewrite subst_rec_preserves_quant; simpl; eauto.
  subst_tac;  rewrite subst_rec_preserves_quant; simpl; eauto; eapply sub_zero.
  (* 1 *)
  right; repeat eexists.
  2: unfold lift; rewrite lift_rec_preserves_quant; simpl; eauto; rewrite quant_succ2; eauto.
  eapply sub_trans. eapply sub_lift.
  unfold lift; rewrite lift_rec_preserves_quant; simpl; eauto; rewrite quant_succ2; eapply sub_zero.
Qed.




Proposition subtype_from_stemty3:
  forall bs uty ty2,
    subtype (quanta bs (Stem uty)) ty2 ->
   (exists bs2 p sigma uty2,
        ty2 = quanta bs2 (Stem uty2) /\ subtype (quant p (trim sigma uty)) uty2 /\
        chip_count sigma (quant_count bs) (p + quant_count bs2))
    \/
    subtype (quant (quant_count bs) (Quant (Funty (Var 0) (Fork (lift 1 uty) (Var 0))))) ty2.
Proof.
  cut (forall ty1 ty2,
    subtype ty1 ty2 ->
    forall bs uty,
      ty1 = quanta bs (Stem uty) -> 
    (exists bs2 p sigma uty2,
        ty2 = quanta bs2 (Stem uty2) /\ subtype (quant p (trim sigma uty)) uty2 /\
        chip_count sigma (quant_count bs) (p + quant_count bs2))
    \/
    subtype (quant (quant_count bs) (Quant (Funty (Var 0) (Fork (lift 1 uty) (Var 0))))) ty2).
  intros; eapply H; eauto.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate;
    auto_t.
  (* 15 *)
  left; exists bs; exists 0; repeat eexists; simpl; eauto. 
  2: eapply chip_count_nil.
  eapply sub_zero.   
  (* 14 *)
  eelim IHs1; intros; eauto; no_quant; disjunction_tac; no_quanta. 
  eelim IHs2; intros.  3: eauto.
  split_all; disjunction_tac; no_quant.
  left; repeat eexists.
  2: eapply chip_count_app2; eauto.
  rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
  eapply sub_trans; eauto.
  eapply subtype_quant. eapply trim_preserves_subtype; eauto.   
  right.
  eapply sub_trans; eauto. 
  trim2_tac. 
  rewrite quant_plus2. eapply subtype_quant.
  rewrite trim_Quant. 
  rewrite trim_funty. rewrite trim_fork. rewrite ! trim_lift_miss; try lia.
  rewrite <- chip_lift_trim. 
  eapply sub_trans. eapply sub_lift. eapply sub_quant.
  rewrite quant_succ3.   unfold lift; rewrite lift_rec_preserves_quant. simpl; var_tac.  
  rewrite lift_lift_rec; try lia. rewrite plus_0_r. 
  eapply sub_trans. eapply subtype_quant. subst_tac.   dist_tac; var_tac. 
  eapply subtype_lift.
  eapply sub_trans. eapply subtype_quant_fork. eapply sub_fork. 
  2: eapply subtype_lift2.
  replace x0 with (x0 + 0) at 2 by lia. rewrite <- lift_rec_preserves_quant.
  eapply lift_rec_preserves_subtype; eauto.
  right; eapply sub_trans; eauto.
  (* 13 *)
  inv_out H; left.  exists nil; exists 0; repeat eexists; simpl. 2: eapply chip_count_nil. eauto.  
  (* 12 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H.
  eelim IHs; intros; eauto; no_quanta; disjunction_tac.
  left; exists (app x0 (false :: nil)); repeat eexists. rewrite quanta_app; simpl; eauto .
  eauto.
  rewrite ! quant_count_app; simpl; auto_t. rewrite ! plus_0_r; auto. 
  right; rewrite quant_count_app; simpl; rewrite plus_0_r; eapply sub_trans; eauto; eapply sub_to_asf.
  (* 11 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H.
  eelim IHs; intros; eauto; no_quanta; disjunction_tac.
  left;   exists (app x0 (true :: nil)); repeat eexists. rewrite quanta_app; simpl; eauto . eauto. 
  rewrite ! quant_count_app; simpl; auto_t.
  replace (quant_count x + 1) with (S (quant_count x)) by lia.
  replace  (x1 + (quant_count x0 + 1)) with (S (x1 + quant_count x0)) by lia.
  eapply chip_count_succ; eauto.
  right. rewrite quant_count_app; simpl. 
    replace (quant_count x + 1) with (S (quant_count x)) by lia; simpl;
      rewrite quant_succ; eapply sub_quant; eauto.
  (* 10 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H.
  no_quanta. inv_out H1. 
  left; exists nil; exists 1; repeat eexists. 2: eapply chip_count_nil. simpl; eapply sub_zero. 
  (* 9 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H. no_quanta.
  (* 10 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H. 
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H1. 
  left; exists (app x0 (true :: false :: nil)); repeat eexists. 
  rewrite quanta_app in *; simpl in *. auto.
  2: rewrite ! quant_count_app; simpl.
  2: rewrite plus_0_r; instantiate(1:= 0); eapply chip_count_nil.
  eapply sub_zero. 
  (* 9 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H. 
  eelim (quanta_cases x); intros; disjunction_tac; subst. simpl; discriminate. 
  rewrite H0 in H1; rewrite quanta_app in *; simpl in *. inv_out H1. 
  rewrite H0 in H1; rewrite quanta_app in *; simpl in *. inv_out H1. 
  (* 8 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  rewrite quanta_app in *; simpl in *; inv_out H. no_quanta.
  (* 7 *)
  left; repeat eexists.
  unfold subst; rewrite subst_rec_preserves_quanta; simpl; eauto. 
  2: rewrite quant_count_app; simpl; replace (quant_count x + 1) with (S (quant_count x)) by lia. 
  2: instantiate(1:=0); eapply chip_count_inst. 3: eapply chip_count_nil.
  simpl; eapply sub_zero. lia. 
  (* 6 *)
  left; repeat eexists.
  unfold lift; rewrite lift_rec_preserves_quanta; simpl.
  instantiate(2:= app bs (true :: nil)); rewrite quanta_app; simpl; eauto.
  2: rewrite quant_count_app; simpl; instantiate(1:= 0); simpl;
    replace (quant_count bs + 1) with (S (quant_count bs)) by lia; eapply chip_count_lift.
  3: eapply chip_count_nil.
  simpl; eapply sub_zero. lia. 
  (* 5 *)
  inv_out H; right; simpl; subst_tac. 
  (* 4 *)
  replace omega2_ty with (Fork (Stem omega21_ty) omega22_ty) in H by (cbv; auto);  no_quanta.
  (* 3 *)
  left; repeat eexists; simpl; auto. 
  instantiate(2:= app bs (false :: nil)); rewrite quanta_app; simpl; eauto.
  2: rewrite quant_count_app; simpl; rewrite plus_0_r.
  2: instantiate(1:= 0); eapply chip_count_nil.
  eapply sub_zero.
  (* 2 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; split_all. 
  rewrite quanta_app in *. simpl in *. inv_out H. no_quanta.
  (* 1 *)
Qed.



Proposition subtype_from_forkty4:
  forall n uty vty ty2,
    subtype (quant n (Fork uty vty)) ty2 ->
    isFunty ty2 \/ 
    exists n2 uty2 vty2,
      subtype (quant n uty) (quant n2 uty2) /\
      subtype (quant n vty) (quant n2 vty2) /\
      ty2 = quant n2 (Fork uty2 vty2).
Proof.
  cut (forall ty1 ty2,
    subtype ty1 ty2 ->
    forall n uty vty,
    ty1 = quant n (Fork uty vty) -> 
    isFunty ty2 \/ 
    exists n2 uty2 vty2,
      subtype (quant n uty) (quant n2 uty2) /\
      subtype (quant n vty) (quant n2 vty2) /\
      ty2 = quant n2 (Fork uty2 vty2)).
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate;
    auto_t; no_quant; no_quant.
  (* 7 *)
  right; repeat eexists; eapply sub_zero.
  (* 6 *)
  eelim IHs1; intros; eauto; no_quant; disjunction_tac; no_quanta. 
  left; eapply subtype_from_funty; eauto.
  eelim IHs2; intros.  3: eauto. auto. split_all. right; repeat eexists; auto_t.
  (* 5 *)
  right; exists 0; repeat eexists; auto. 
  (* 4 *)
  eelim IHs; intros; eauto.   left; auto_t. split_all.
  right; exists (S x); repeat eexists; simpl; rewrite quant_succ; eauto; auto_t.
  (* 3 *)
  right; exists 0; repeat eexists; eauto; eapply sub_zero.
  (* 2 *)
  right; repeat eexists. 3: unfold subst; rewrite subst_rec_preserves_quant; simpl; eauto.
  1,2: subst_tac;  rewrite subst_rec_preserves_quant; simpl; eauto; eapply sub_zero.
  (* 1 *)
  right; repeat eexists.
  3: unfold lift; rewrite lift_rec_preserves_quant; simpl; eauto; rewrite quant_succ2; eauto.
  1,2: eapply sub_trans; [
    eapply sub_lift |
    unfold lift; rewrite lift_rec_preserves_quant; simpl; eauto; rewrite quant_succ2; eapply sub_zero].
Qed.



Theorem subtype_from_quanta_funty:
  forall ty1 ty2,
    subtype ty1 ty2 -> 
    forall bs u v,
      ty1 = quanta bs (Funty u v) ->
      exists p bs2 u2 v2 sigma, 
          ty2 = quanta bs2 (Funty u2 v2) /\
          chip_count sigma (quant_count bs) (p + (quant_count bs2)) /\
          subtype (quant p (trim sigma v)) v2 /\
          subtype u2 (quant p (trim sigma u)).
 Proof.
  intros ty ty2 s; induction s; simpl in *;  repeat split; intros; subst; no_quanta. 
  (* 15 *)
  exists 0; repeat eexists; eauto. eapply chip_count_nil. 1,2: eapply sub_zero. 
  (* 14 *)
  eelim IHs1; intros; eauto; clear IHs1; split_all.
  eelim IHs2; intros. 2: eauto.   clear IHs2; split_all.  
  repeat eexists. eapply chip_count_app2; eauto.
  eapply sub_trans; eauto. 
  rewrite trim_app. rewrite quant_plus2. eapply subtype_quant. 
  rewrite <- trim_quant. eapply trim_preserves_subtype; eauto.
  eapply sub_trans; eauto. 
  rewrite trim_app. rewrite quant_plus2. eapply subtype_quant. 
  rewrite <- trim_quant. eapply trim_preserves_subtype; eauto.
  (* 13 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; split_all. 
  eelim IHs; intros; eauto; split_all.
  repeat eexists.   instantiate(3:= app x1 (false :: nil)).  
  rewrite quanta_app.   simpl. eauto.
  rewrite ! quant_count_app.   simpl. rewrite ! plus_0_r; eauto. auto. auto.
  (* 12 *)
  inv_out H. exists 0; exists nil; repeat eexists. simpl; eapply chip_count_nil. 1,2: eauto. 
  (* 11 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; split_all. 
  eelim IHs; intros; eauto; split_all.
  repeat eexists.   instantiate(3:= app x1 (true :: nil)).  
  rewrite quanta_app.   simpl. eauto.
  rewrite ! quant_count_app.   simpl.
  instantiate(1:= x0). replace (quant_count x + 1) with (S (quant_count x)) by lia.
  replace (x0 + (quant_count x1 + 1)) with (S (x0 + quant_count x1)) by lia.
  eapply chip_count_succ; eauto. 1,2: auto. 
  (* 10 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; split_all; no_quanta.
  (* 9 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; split_all;  no_quanta.
  (* 8 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; split_all. 
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; split_all. 
  repeat eexists.
  instantiate(3:= (app x0 (true :: false :: nil))).
  rewrite quanta_app. simpl. eauto.
  rewrite ! quant_count_app. simpl. rewrite plus_0_r; instantiate(1:= 0); eapply chip_count_nil.
  1,2: eapply sub_zero.
  (* 7 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; split_all. 
  eelim (quanta_cases x); intros; disjunction_tac; subst.
  2,3: rewrite  H1 in *; rewrite ? quanta_app in *; simpl; try discriminate.
  inv_out H2.
  exists 1; exists nil; repeat eexists. simpl; eapply chip_count_nil. 1,2: eapply sub_zero. 
  (* 6 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; split_all.
  repeat eexists.
  unfold subst; rewrite subst_rec_preserves_quanta; simpl; eauto.
  rewrite quant_count_app; simpl.
  instantiate(1:= 0); replace (quant_count x + 1) with (S (quant_count x)) by lia; simpl.
  eapply chip_count_inst. 2: eapply chip_count_nil. 
  2,3: simpl; eapply sub_zero.   lia.
  (* 5 *)
  repeat eexists.
  unfold lift; rewrite lift_rec_preserves_quanta; simpl; eauto.
  instantiate(3:= app bs (true :: nil)).   rewrite quanta_app; simpl; eauto.
  rewrite quant_count_app; simpl.
  instantiate(1:= 0); replace (quant_count bs + 1) with (S (quant_count bs)) by lia; simpl.
  eapply chip_count_lift. 2: eapply chip_count_nil. 
  2,3: simpl; eapply sub_zero.   lia.
  (* 4 *)
  replace omega2_ty with (Fork (Stem omega21_ty) omega22_ty) in H by (cbv; auto).  no_quanta.
  (* 3 *)
  exists 0; exists (app bs (false :: nil)); repeat eexists; simpl; auto. 
  rewrite quanta_app in *; simpl in *; eauto.
  rewrite quant_count_app; simpl; rewrite plus_0_r. eapply chip_count_nil. 
  1,2: eapply sub_zero.  
  (* 2 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; split_all.  no_quanta. inv_out H. 
  exists 0; exists nil; repeat eexists; simpl. eapply chip_count_nil. 1,2: eapply sub_zero.
 Qed. 




Theorem subtype_of_funty:
  forall n u v u2 v2,
    subtype (quant n (Funty u v)) (Funty u2 v2) ->
    exists sigma n2, 
      chip_count sigma n n2 /\  
      subtype (quant n2 (trim sigma v)) v2 /\
      subtype u2 (quant n2 (trim sigma u)).   
Proof.
  intros; eelim subtype_from_quanta_funty; intros; eauto.
  2: instantiate(3:= quant_to_quanta n). 
  2: rewrite <- quanta_to_quant; eauto. 
  split_all. no_quanta. inv_out H1. 
  rewrite quant_count_quant_to_quanta in *. rewrite plus_0_r in *.
  repeat eexists; eauto.
Qed.


Proposition subtype_from_leafty2:
  forall bs ty2,
    subtype (quanta bs Leaf) ty2 ->
    (exists bs2, ty2 = quanta bs2 Leaf) \/ 
       subtype (Quant (Funty (Var 0) (Stem (Var 0)))) ty2.
Proof.
  cut(forall ty1 ty2, subtype ty1 ty2 ->
                      forall bs, ty1 = quanta bs Leaf ->
                                 (  (exists bs2, ty2 = quanta bs2 Leaf) \/ 
                                    subtype (Quant (Funty (Var 0) (Stem (Var 0)))) ty2)).
intros; eauto. 
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate;
    auto_t.
  (* 14 *)
  all: cycle 1.
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  eelim IHs; intros; eauto; no_quanta; disjunction_tac.
  left; exists (app x0 (false :: nil)); rewrite quanta_app; simpl; eauto .
  right; eapply sub_trans; eauto; eapply sub_to_asf.   
  (* 13 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  eelim IHs; intros; eauto; no_quanta; disjunction_tac.
  left;  exists (app x0 (true :: nil)); rewrite quanta_app; simpl; eauto .
  right; eapply sub_trans; [ eapply sub_lift | auto_t].
  (* 12 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.  no_quanta. 
  (* 11 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all. no_quanta.
  (* 10 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  left;  exists (app x0 (true :: false :: nil)); rewrite ! quanta_app in *; simpl in *; eauto. 
  (* 9 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all. no_quanta. 
  (* 8 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all; no_quanta.
  left; unfold subst; rewrite subst_rec_preserves_quanta; simpl; eauto. 
  (* 7 *)
  left; eexists; unfold lift; rewrite lift_rec_preserves_quanta; simpl; eauto. 
  instantiate(1:= app bs (true :: nil)); rewrite quanta_app; simpl; eauto.
  (* 6 *)
  right; subst_tac. 
  (* 5 *)
  unfold omega2_ty in *; no_quanta.
  (* 4 *)
  left;  exists (app bs (false :: nil)); repeat eexists; simpl; auto. 
  rewrite quanta_app in *; simpl in *; eauto.
  (* 3 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; split_all;  no_quanta.
  (* 1 *)
  eelim IHs1; intros; eauto; split_all.
  eelim IHs1; intros; eauto; split_all.
  right; eapply sub_trans; eauto.
Qed.  


Proposition subtype_from_stemty_to_fun:
  forall uty zty ty, subtype (Stem uty) (Funty zty ty) -> subtype (Fork uty zty) ty.
Proof.
  intros; eelim subtype_from_stemty3; intros. 3: instantiate(3:= nil); simpl; eauto.
  split_all; disjunction_tac.   no_quanta.
  simpl in *.   eelim subtype_from_quanta_funty; intros.
  2: eapply H0. 2: instantiate(3:= true :: nil); simpl; eauto.
  split_all.  no_quanta. inv_out H2. 
  eapply sub_trans. 2: eapply H3.
  rewrite trim_fork.   eapply sub_trans. 2: eapply fork_quant_commute. eapply sub_fork. 2: eauto. 
  eapply sub_trans. eapply sub_lift.  replace Quant with (quant 1) by auto.
  trim2_tac. rewrite plus_0_r; eapply sub_zero.
Qed.


Theorem subtype_from_fork_of_funty:
  forall bs uty vty ty2,
    subtype (quanta bs (Fork uty vty)) ty2 -> isFunty uty -> 
    exists p bs2 uty2 vty2 sigma,
       ty2 = quanta bs2 (Fork uty2 vty2) /\
       chip_count sigma (quant_count bs)  (p + (quant_count bs2)) /\
       subtype (quant p (trim sigma uty)) uty2 /\
       subtype (quant p (trim sigma vty)) vty2.
Proof.
  cut(forall ty1 ty2,
         subtype ty1 ty2 ->
         forall bs uty vty,
           ty1 = quanta bs (Fork uty vty) -> isFunty uty -> 
  exists p bs2 uty2 vty2 sigma,
    ty2 = quanta bs2 (Fork uty2 vty2) /\
    chip_count sigma (quant_count bs)  (p + (quant_count bs2)) /\
    subtype (quant p (trim sigma uty)) uty2 /\
    subtype (quant p (trim sigma vty)) vty2).
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate; auto_t.
  (* 22 *)
  all: try (inv_out H; simpl; inv_out H0; fail).
  all: try (eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all;  no_quanta; fail). 
  (* 13 *)
  exists 0; repeat eexists; simpl; (eapply chip_count_nil || eapply sub_zero). 
  (* 12 *)
  all: cycle 4.
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all. no_quanta. inv_out H3. 
  exists 1; exists nil; repeat eexists; simpl in *; eauto. eapply chip_count_nil.
  1-2: simpl; eapply sub_zero.
  (* 11 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  exists 0; exists (app x0 (true :: false :: nil)); repeat eexists.
  rewrite quanta_app; simpl; auto_t.  rewrite ! quant_count_app; simpl; rewrite ! plus_0_r.
  eapply chip_count_nil.
  1-2:  simpl; eapply sub_zero.
  (* 10 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  exists 0;  exists x; repeat eexists.
  unfold subst; rewrite subst_rec_preserves_quanta; simpl; eauto.
  rewrite ! quant_count_app; simpl; replace (quant_count x + 1) with (S (quant_count x)) by lia;
    eapply chip_count_inst.
  2: eapply chip_count_nil.
  2,3:  simpl; eapply sub_zero.
  lia.
  (* 9 *)
  exists 0; exists (app bs (true :: nil));  repeat eexists.
  rewrite quanta_app; simpl.
  unfold lift; rewrite lift_rec_preserves_quanta; simpl; eauto.
  rewrite quant_count_app; simpl; eapply chip_count_lift.
  2: replace (quant_count bs + 1) with (S (quant_count bs)) by lia; eapply chip_count_nil.
  2,3: simpl; eapply sub_zero. lia. 
  (* 8 *)
  replace omega2_ty with (Fork (Stem omega21_ty) omega22_ty) in H by (cbv; auto);  no_quanta.
  inv_out H; inv_out H0.
  (* 7 *)
  inv_out H0; inv_out H1.
  (* 6 *)
  exists 0; exists (app bs (false :: nil)); repeat eexists.
  rewrite quanta_app; simpl; auto.  rewrite quant_count_app; simpl. rewrite plus_0_r; eapply chip_count_nil.
  1,2:  eapply sub_zero. 
  (* 5 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all; no_quanta. 
  (* 4 *)
  all: cycle -1.
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  eelim IHs; intros; eauto; clear IHs; split_all.
  exists x0; exists (app x1 (true :: nil)); repeat eexists. rewrite quanta_app; simpl; eauto.
  rewrite 2 quant_count_app; simpl. 
  replace (quant_count x + 1) with (S (quant_count x)) by lia.
  replace (x0 + (quant_count x1 + 1)) with (S (x0 + quant_count x1)) by lia.
  eapply chip_count_succ; eauto.
  1,2: eauto.
  (* 3 *)
  all: cycle -1.
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  eelim IHs; intros; eauto; clear IHs; split_all.
  exists x0; exists (app x1 (false :: nil)); repeat eexists. rewrite quanta_app; simpl; eauto.
  rewrite 2 quant_count_app; simpl. rewrite ! plus_0_r; eauto.   
  1,2: eauto.
  (* 2 *)
  all: cycle -1.
  inv_out H. 
  exists 0; exists nil; repeat eexists. eapply chip_count_nil. 1,2: eauto.
  (* 1 *)
  eelim IHs1; intros; eauto; clear IHs1; split_all; disjunction_tac; split_all.
  eelim IHs2; intros.  2:eauto. 
  2: eapply subtype_from_funty; eauto; eapply isFunty_quant;
    eapply trim_preserves_isFunty; eauto.
  split_all.
  repeat eexists.
  eapply chip_count_app2; eauto.
  1,2: rewrite trim_app; rewrite quant_plus2; rewrite <- trim_quant; eapply sub_trans; eauto;
    eapply subtype_quant; eapply trim_preserves_subtype; eauto.
Qed.


Theorem subtype_from_fork_of_leaf:
  forall bs uty vty ty2,
    subtype (quanta bs (Fork uty vty)) ty2 -> isLeafty uty -> 
    (exists p bs2 uty2 vty2 sigma,
       ty2 = quanta bs2 (Fork uty2 vty2) /\
       chip_count sigma (quant_count bs)  (p + (quant_count bs2)) /\
       subtype (quant p (trim sigma uty)) uty2 /\
       subtype (quant p (trim sigma vty)) vty2)
    \/
subtype (Quant (Funty (Var 0) (lift 1 (quant (quant_count bs) vty)))) ty2.
Proof.
  cut(forall ty1 ty2,
         subtype ty1 ty2 ->
         forall bs uty vty,
           ty1 = quanta bs (Fork uty vty) -> isLeafty uty -> 
    (exists p bs2 uty2 vty2 sigma,
       ty2 = quanta bs2 (Fork uty2 vty2) /\
       chip_count sigma (quant_count bs)  (p + (quant_count bs2)) /\
       subtype (quant p (trim sigma uty)) uty2 /\
       subtype (quant p (trim sigma vty)) vty2)
    \/
    subtype (Quant (Funty (Var 0) (lift 1 (quant (quant_count bs) vty)))) ty2).
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate; auto_t.
  (* 23 *)
  all: try (inv_out H; simpl; inv_out H0; fail).
  all: try (eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all;  no_quanta; fail). 
  (* 14 *)
  left; exists 0; repeat eexists; simpl; (eapply chip_count_nil || eapply sub_zero). 
  (* 13 *)
  all: cycle 4.
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all. no_quanta. inv_out H3. 
  left; exists 1; exists nil; repeat eexists; simpl in *; eauto. eapply chip_count_nil.
  1-2: simpl; eapply sub_zero.
  (* 12 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  left;  exists 0; exists (app x0 (true :: false :: nil)); repeat eexists.
  rewrite quanta_app; simpl; auto_t.  rewrite ! quant_count_app; simpl; rewrite ! plus_0_r.
  eapply chip_count_nil.
  1-2:  simpl; eapply sub_zero.
  (* 11 *)
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  left; exists 0;  exists x; repeat eexists.
  unfold subst; rewrite subst_rec_preserves_quanta; simpl; eauto.
  rewrite ! quant_count_app; simpl; replace (quant_count x + 1) with (S (quant_count x)) by lia;
    eapply chip_count_inst.
  2: eapply chip_count_nil.
  2,3:  simpl; eapply sub_zero.
  lia.
  (* 10 *)
  left; exists 0; exists (app bs (true :: nil));  repeat eexists.
  rewrite quanta_app; simpl.
  unfold lift; rewrite lift_rec_preserves_quanta; simpl; eauto.
  rewrite quant_count_app; simpl; eapply chip_count_lift.
  2: replace (quant_count bs + 1) with (S (quant_count bs)) by lia; eapply chip_count_nil.
  2,3: simpl; eapply sub_zero. lia. 
  (* 9 *)
  inv_out H. right; subst_tac.
  (* 8 *)
  replace omega2_ty with (Fork (Stem omega21_ty) omega22_ty) in H by (cbv; auto);  no_quanta.
  inv_out H; inv_out H0.
  (* 7 *)
  inv_out H0; inv_out H1.
  (* 6 *)
  left; exists 0; exists (app bs (false :: nil)); repeat eexists.
  rewrite quanta_app; simpl; auto.  rewrite quant_count_app; simpl. rewrite plus_0_r; eapply chip_count_nil.
  1,2:  eapply sub_zero. 
  (* 5 *)
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all; no_quanta. 
  (* 4 *)
  all: cycle -1.
  eelim quanta_is_quant; intros; eauto; subst; simpl in *; auto; split_all.
  eelim IHs; intros; eauto; clear IHs; split_all.
  left; exists x0; exists (app x1 (true :: nil)); repeat eexists. rewrite quanta_app; simpl; eauto.
  rewrite 2 quant_count_app; simpl. 
  replace (quant_count x + 1) with (S (quant_count x)) by lia.
  replace (x0 + (quant_count x1 + 1)) with (S (x0 + quant_count x1)) by lia.
  eapply chip_count_succ; eauto.
  1,2: eauto.
  right. rewrite quant_count_app; simpl. 
  eapply sub_trans. eapply sub_lift.   eapply sub_quant. eapply sub_trans; eauto.
  unfold lift; simpl; var_tac. eapply sub_quant. sub_fun_tac. 
  rewrite lift_lift_rec; try lia.
  eapply lift_rec_preserves_subtype.
  rewrite quant_plus2. eapply subtype_lift3.
  (* 3 *)
  all: cycle -1.
  eelim quanta_is_asf; intros; eauto; subst; simpl in *; auto; split_all.
  eelim IHs; intros; eauto; clear IHs; split_all.
  left; exists x0; exists (app x1 (false :: nil)); repeat eexists. rewrite quanta_app; simpl; eauto.
  rewrite 2 quant_count_app; simpl. rewrite ! plus_0_r; eauto.   
  1,2: eauto.
  right.  rewrite quant_count_app; simpl. rewrite plus_0_r. 
  eapply sub_trans. eauto. eapply sub_to_asf.
  (* 2 *)
  all: cycle -1.
  inv_out H. 
  left; exists 0; exists nil; repeat eexists. eapply chip_count_nil. 1,2: eauto.
  (* 1 *)
  eelim IHs1; intros; eauto; clear IHs1; split_all; disjunction_tac; split_all.
  (* 2 *)
  2: right; eapply sub_trans; eauto. 
  (* 1 *)
  eelim subtype_from_leafty; intros.
  3: eapply H2.
  3: eapply isLeafty_quant; eapply trim_preserves_isLeafty; eauto.
  (* 2 *)
  eelim IHs2; intros.  3:eauto. 3: eauto. 
  (* 3 *)
  split_all.
  left; repeat eexists.   eapply chip_count_app2; eauto.
  1,2: rewrite trim_app; rewrite quant_plus2; rewrite <- trim_quant; eapply sub_trans; eauto;
    eapply subtype_quant; eapply trim_preserves_subtype; eauto.
  (* 2 *)
  right. eapply sub_trans; eauto. 
  eapply sub_quant; sub_fun_tac. eapply lift_rec_preserves_subtype.
  trim2_tac. rewrite quant_plus2. eapply subtype_quant; eauto.
  (* 1 *)
  clear IHs2; eelim subtype_from_fork_of_funty; intros. 
  2: eapply s2.   2: eauto. split_all.
  left;  repeat eexists. eapply chip_count_app2; eauto.
  1,2: rewrite trim_app; rewrite quant_plus2; rewrite <- trim_quant; eapply sub_trans; eauto;
    eapply subtype_quant; eapply trim_preserves_subtype; eauto.
Qed.


Theorem subtype_from_fork_of_leaf_to_fun:
  forall vty zty ty, subtype (Fork Leaf vty) (Funty zty ty) -> subtype vty ty. 
Proof.
  intros; eelim subtype_from_fork_of_leaf; intros. 
  3: instantiate(4:= nil); simpl; eauto. 
  3: auto_t. 
  split_all; no_quant. 
  no_quanta.  simpl in *. 
  eelim (subtype_of_funty 1); intros; eauto; split_all.
  eapply sub_trans; eauto. eapply sub_trans. eapply (subtype_lift 1). trim2_tac. 
  eapply sub_zero.
Qed.



Proposition subtype_omega21_ty:
  forall uty vty,
    subtype omega21_ty (Funty omega2_ty (Funty (Funty (Funty uty vty) uty) (Funty (Funty uty vty) vty))).
Proof.
  intros; eapply sub_trans. cbv; eapply sub_zero. repeat sub_fork2_tac. 
  eapply sub_trans. eapply sub_stem_fun. sub_fun_tac.   
  repeat sub_fork2_tac.
  eapply subtype_Kty. 
Qed.



Proposition subtype_omega22_ty
  : forall k uty vty,
    subtype
      omega22_ty
      (Funty
         omega2_ty
         (Funty (Funty (quant k (Funty uty vty)) (quant k (Funty uty vty))) (quant k (Funty uty vty)))). 
Proof.
  intros; eapply sub_trans. cbv; eapply sub_zero. repeat sub_fork2_tac. 
  2,3: eapply subtype_Kty.
  eapply sub_trans. eapply subtype_leaf_fork. do 2 sub_fun_tac. 
  repeat sub_fork2_tac. 
  2: eapply subtype_Kty.
  eapply sub_trans. eapply subtype_leaf_fork. do 2 sub_fun_tac. 
  eapply sub_trans. eapply subtype_lift. eapply subtype_quant. unfold lift; refold lift_rec.
  do 2 sub_fork2_tac. 
  3,4: eapply subtype_Kty.
  1,2: do 2 sub_fork2_tac.
  replace (lift_rec omega2_ty 0 k) with omega2_ty by (cbv; auto).
  rewrite lift_rec_preserves_quant; refold lift_rec.
  eapply sub_trans. eapply sub_recursion. repeat sub_fun_tac.
  rewrite <- lift_rec_funty. rewrite plus_0_r. eapply subtype_lift4.
  Unshelve. apply Leaf.
Qed.


  
Theorem subtype_from_fork_of_stem:
  forall ty1 ty2,
    subtype ty1 ty2 ->
    forall bs1 n1 uty1 vty1,
      ty1 = quanta bs1 (Fork (quant n1 (Stem uty1)) vty1) ->
      not_funty ty2 \/
      (exists sigma p1 k n2 bs2 uty2 vty2,
       chip_count sigma (quant_count bs1) (p1 + (quant_count bs2)) /\
       subtype (quant p1 (trim sigma (quant n1 uty1))) (iter k bffs_aug (quant n2 uty2)) /\
       subtype (quant p1 (trim sigma vty1)) (quantf k vty2) /\
       (ty2 = quanta bs2 (Fork (quant n2 (Stem uty2)) vty2) (* fold quantf k into bs2 *) 
        \/
        exists u2 v2 w2,
          n2 = 0 /\ 
          uty2 = Funty u2 (Funty v2 w2) /\
          vty2 = Funty u2 v2 /\ 
          ty2 = quanta bs2 (Funty u2 w2)
       )). 
Proof.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate; auto_t;
    try (inv_out H; no_quant).
 (* 17 *)
 right; exists nil; exists 0; exists 0; repeat eexists. eapply chip_count_nil. 1,2: eapply sub_zero.
 left; auto.
 (* 16 *)
 all: cycle 1.
 eelim subtype_from_stemty4; intros. 3: eauto. 
 left; eapply fork_not_funty; eauto.
 split_all.
 right;  repeat eexists.  instantiate(1:= nil); instantiate(1:= 0); simpl; eapply chip_count_nil.
 instantiate(3:= 0); simpl; eauto. eauto. left; auto.
 (* 15 *)
 eelim quanta_is_asf; intros; eauto; subst; simpl in *; no_quant. 
 eelim IHs; intros; eauto. left; auto_t. split_all; disjunction_tac. 
 right; repeat eexists. 
 rewrite quant_count_app; simpl.  instantiate(1:= app x4 (false :: nil)).
 rewrite quant_count_app; simpl; rewrite ! plus_0_r; eauto. eauto. eauto.
 left; rewrite quanta_app; simpl; eauto.
 split_all.
 right; repeat eexists. 
 4: right; repeat eexists; instantiate(3:= app x4 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. rewrite ! plus_0_r; eauto. eauto. eauto.
 (* 14 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quant. 
 eelim IHs; intros; eauto. left; auto_t. split_all; disjunction_tac. 
 right; repeat eexists. 
 rewrite quant_count_app; simpl.  instantiate(1:= app x4 (true :: nil)).
 rewrite quant_count_app; simpl.
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1). replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1,2: eauto.
 left; rewrite quanta_app; simpl; eauto.
 split_all.
 right; repeat eexists. 
 4: right; repeat eexists; instantiate(3:= app x4 (true :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl.
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1). replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1,2: eauto.
 (* 13 *)
 all: try (eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quant; no_quanta; fail). 
 (* 11 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quant; no_quanta. inv_out H2. 
 right; repeat eexists.
 4: left. 4: instantiate(4:= nil); simpl; rewrite quant_succ2; eauto.
 simpl; rewrite plus_0_r. eapply chip_count_nil.
 instantiate(1:= 0); simpl.  rewrite quant_succ; eapply sub_zero. eapply sub_zero.
 (* 10 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quant; no_quanta.
 eelim quanta_is_asf; intros; eauto; subst; simpl in *; no_quant; no_quanta.
 right; repeat eexists.
 4: left. 4: instantiate(4:= app x0 (true :: false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl; rewrite plus_0_r.  instantiate(1:= 0); eapply chip_count_nil.
 instantiate(1:= 0); eapply sub_zero. eapply sub_zero. 
 (* 9 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quant; no_quanta. 
 right; repeat eexists.
 4: left. 4: unfold subst; rewrite subst_rec_preserves_quanta; simpl;
                   rewrite subst_rec_preserves_quant; simpl; eauto.
 instantiate(1:= 0); rewrite quant_count_app; simpl.
 replace (quant_count x + 1) with (S (quant_count x)) by lia.  eapply chip_count_inst.
 2: eapply chip_count_nil.
 2: instantiate(1:= 0); simpl; rewrite subst_rec_preserves_quant; eapply sub_zero. lia.
 simpl; eapply sub_zero.
 (* 8 *)
 right; repeat eexists. 
 4: left. 4: unfold lift; rewrite lift_rec_preserves_quanta; simpl;
                   rewrite lift_rec_preserves_quant; simpl; eauto.
 instantiate(1:= app bs1 (true :: nil)); rewrite quant_count_app; simpl.
 4: rewrite quanta_app; simpl; eauto.
 instantiate(1:= 0); simpl; replace (quant_count bs1 + 1) with (S (quant_count bs1)) by lia. 
 eapply chip_count_lift. 2: eapply chip_count_nil.
 2: instantiate(1:= 0); simpl; rewrite lift_rec_preserves_quant; eapply sub_zero. lia.
 simpl; eapply sub_zero.
 (* 7 *)
 right; repeat eexists. 
 4: right; repeat eexists; instantiate(3:= nil); eauto. 
 instantiate(1:= 0); eapply chip_count_nil.
 instantiate(4:= 0);  simpl; eapply sub_zero. eapply sub_zero. eauto. 
 (* 6 *)
 replace omega2_ty with (Fork (Stem omega21_ty) omega22_ty) in H1; no_quanta. inv_out H1.  no_quant.
 right; repeat eexists.
 4: right; repeat eexists; instantiate(3:= nil); simpl; eauto. 
 instantiate(1:= 0); simpl; eapply chip_count_nil.
 instantiate(2:= 0); simpl; eapply subtype_omega21_ty. eapply subtype_omega22_ty.
 (* 5 *)
 inv_out H0; no_quant.
 (* 4 *)
 right; repeat eexists.
 4: left. 4: instantiate(4:= app bs1 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite quant_count_app; simpl. rewrite plus_0_r; instantiate(1:= 0); eapply chip_count_nil.
 instantiate(1:= 0); simpl; eapply sub_zero.
 eapply sub_zero.
 (* 3 *)
 eelim quanta_is_asf; intros; eauto; subst; simpl in *; no_quant; no_quanta. 
 (* 2 *)
 right; repeat eexists.
 4: left. 4: instantiate(4:= false :: nil); simpl; instantiate(3:= 0); simpl; eauto.
 instantiate(1:= 0); eapply chip_count_nil.
 instantiate(1:= 1); simpl. eapply sub_zero. eapply sub_zero.
 (* 1 *)
 eelim IHs1; intros; eauto; split_all; disjunction_tac; split_all.
 (* 3 *)
 left; eapply subtype_not_funty; eauto.
 (* 2 *)
 all: cycle 1.
 clear IHs1 IHs2.
 eelim subtype_from_quanta_funty; intros. 2: eapply s2. 2: eauto. split_all. 
 right; repeat eexists.  4: right; repeat eexists.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bffs_aug.
 eapply sub_trans. eapply subtype_quant_iter_bffs_aug. eapply subtype_preserves_iter_bffs_aug.
 simpl. rewrite ! trim_funty. dist_tac. eauto. dist_tac. eapply sub_zero. eauto. 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 eapply sub_trans. 2: eapply subtype_to_asf.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eapply subtype_from_asf.
 rewrite ! trim_funty. dist_tac. eauto.  eapply sub_zero.
 (* 1 *)
 eelim IHs2; intros.  3: eauto. auto. clear IHs1 IHs2. split_all; disjunction_tac; split_all; auto.
 (* 2 *)
 right; repeat eexists.  
 4: left; eauto.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bffs_aug.
 eapply sub_trans. eapply subtype_quant_iter_bffs_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bffs_aug; eauto.
 instantiate(1:= x1 + x8).
 replace (iter (x1 + x8) bffs_aug (quant x9 x11)) with (iter x1 bffs_aug (iter x8 bffs_aug (quant x9 x11))).
 eapply sub_zero. generalize x9 x11 x8. clear. induction x1; intros; simpl; auto.
 rewrite IHx1. auto.
 (* 2 *) 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite quantf_plus.  eapply sub_trans. 2: eapply subtype_quantf; eauto.
 rewrite trim_quantf. eapply subtype_quant_quantf.
 (* 1 *)
 right; repeat eexists.
 4: right; repeat eexists.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bffs_aug.
 eapply sub_trans. eapply subtype_quant_iter_bffs_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bffs_aug; eauto.
 instantiate(2:= x1 + x8). instantiate(1:= x14). simpl.  
 replace  (iter x1 bffs_aug (iter x8 bffs_aug (Funty x13 (Funty x14 x15))))
   with (iter (x1 + x8) bffs_aug (Funty x13 (Funty x14 x15))).
 eapply sub_zero. generalize x8 x13 x14 x15. clear. induction x1; intros; simpl; auto.
 rewrite IHx1. auto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite quantf_plus.  eapply sub_trans. 2: eapply subtype_quantf; eauto.
 rewrite trim_quantf. eapply subtype_quant_quantf.
Qed.

  
Theorem subtype_from_fork_of_stem_to_funty:
  forall uty vty zty ty,  subtype (Fork (Stem uty) vty) (Funty zty ty) -> 
      exists v2, subtype uty (Funty zty (Funty v2 ty)) /\ subtype vty (Funty zty v2).
Proof.
  intros; eelim subtype_from_fork_of_stem; intros. 3: eapply H. 
  3: instantiate(3:= 0); instantiate(3:= nil); simpl; eauto.
  inv_out H0.  
  split_all; disjunction_tac; split_all.
  inv_out H3.
  no_quanta.
  no_quanta.   inv_out H7.
  exists x7; split. 
  1,2: eapply sub_trans; [ rewrite quant0 at 1; trim2_tac; rewrite plus_0_r; eauto |]. 
  2: eapply subtype_from_asf.
  clear. induction x1; intros; simpl; auto_t.
  eapply sub_trans. eapply subtype_preserves_bffs_aug; eauto.  eapply bffs_aug_of_binary_fun.
Qed.


Theorem subtype_from_fork_of_fork:
  forall ty1 ty2,
    subtype ty1 ty2 ->
    forall bs1 n1 wty1 uty1 vty1,
      ty1 = quanta bs1 (Fork (quant n1 (Fork wty1 uty1)) vty1) ->
      not_funty ty2 \/
      (exists sigma p1 k n2 bs2 wty2 uty2 vty2,
        chip_count sigma (quant_count bs1) (p1 + (quant_count bs2)) /\
        subtype (quant p1 (trim sigma (quant n1 wty1))) (quant n2 wty2) /\
        subtype (quant p1 (trim sigma (quant n1 uty1))) (quantf k (quant n2 uty2)) /\
        subtype (quant p1 (trim sigma vty1)) (iter k bfff_aug vty2) /\
        (ty2 = quanta bs2 (Fork (quant n2 (Fork wty2 uty2)) vty2)  (* fold quantf k into bs2 *) 
         \/
         (exists zty, n2 = 0 /\ ty2 = quanta bs2 (Funty zty wty2) /\ subtype zty Leaf)
         \/
         (exists u2 u3 zty, n2 = 0 /\ ty2 = quanta bs2 (Funty zty u3) /\ uty2 = Funty u2 u3 /\ subtype zty (Stem u2))
         \/ 
         (exists v2 v3 v4 zty, n2 = 0 /\ ty2 = quanta bs2 (Funty zty v4) /\ vty2 = Funty v2 (Funty v3 v4) /\subtype zty (Fork v2 v3))
         \/
         (exists zty cty,
             n2 = 0 /\ 
             covariant cty /\
             wty2 = subst cty Leaf /\
             uty2 = quant 1 (Funty (Var 0) (subst (lift_rec cty 1 1) (Stem (Var 0)))) /\
             vty2 = quant
                      2
                      (Funty
                         (Var 1)
                         (Funty (Var 0) (subst (lift_rec cty 1 2) (Fork (Var 1) (Var 0))))) /\
             subtype (quanta bs2 (Funty zty (subst cty zty))) ty2))).
Proof.
  intros ty1 ty2 s; induction s; intros; subst; simpl in *; no_quanta; try discriminate; auto_t;
    try (inv_out H; no_quant).
 (* 19 *)
 right; exists nil; exists 0; repeat eexists. eapply chip_count_nil.
 4: left; eauto. 2: instantiate(1:= 0). 1-3: simpl;  eapply sub_zero. 
 (* 18 *)
 all: cycle 4.
 all: try (eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quanta; fail). 
 (* 16 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quanta. inv_out H2. 
 right; repeat eexists. 5: left; instantiate(5:= nil); simpl; rewrite quant_succ2; eauto.
 instantiate(1:= 1); simpl; eapply chip_count_nil.
 2:  instantiate(1:= 0). 1-3: simpl; rewrite ? quant_succ; eapply sub_zero.
 (* 15 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quanta. 
 eelim quanta_is_asf; intros; eauto; subst; simpl in *; no_quanta. 
 right; repeat eexists.
 5: left; instantiate(5:= app x0 (true :: false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl; rewrite plus_0_r; instantiate(1:= 0); eapply chip_count_nil.
 2: instantiate(1:= 0). 1-3: simpl; eapply sub_zero.
 (* 14 *)
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quanta. 
 right; repeat eexists.
 5: left; unfold subst; rewrite subst_rec_preserves_quanta; simpl;
   rewrite subst_rec_preserves_quant; simpl; eauto.
 rewrite quant_count_app; simpl. replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= 0); simpl; eapply chip_count_inst. 2: eapply chip_count_nil.
 3: instantiate(1:= 0).  2,3: simpl; rewrite subst_rec_quant; eapply sub_zero. lia.
 simpl; eapply sub_zero. 
 (* 13 *)
 right; repeat eexists.
 5: left; unfold lift; rewrite lift_rec_preserves_quanta; simpl;
   rewrite lift_rec_preserves_quant; simpl; eauto.
 5: instantiate(5:= app bs1 (true :: nil)); rewrite quanta_app; simpl; eauto.
 instantiate(1:= 0); rewrite quant_count_app; simpl.
 replace (quant_count bs1 + 1) with (S (quant_count bs1)) by lia. 
 eapply chip_count_lift.  2: eapply chip_count_nil.
 3: instantiate (1:= 0).  2,3: simpl; rewrite lift_rec_preserves_quant; eapply sub_zero. lia.
 simpl; eapply sub_zero. 
 (* 12 *)
 right; repeat eexists.
 5: right; left; repeat eexists.
 5: instantiate(3:= nil); simpl; eauto; auto_t.
 instantiate(1:= 0); eapply chip_count_nil.
 2: instantiate(2:= 0). 1-4: simpl; eapply sub_zero.
 (* 11 *)
 right; repeat eexists.
 5: do 2 right; left; repeat eexists.
 5: instantiate(3:= nil); simpl; eauto. 
 instantiate(1:= 0); eapply chip_count_nil.
 3: instantiate(2:= 0).
 1-4: simpl; eapply sub_zero.
 (* 10 *)
 right; repeat eexists.
 5: do 3 right; left; repeat eexists.
 5: instantiate(3:= nil); simpl; eauto; eapply sub_zero.
 instantiate(1:= 0); eapply chip_count_nil.
 2: instantiate(2:= 0). 1-4: simpl; eapply sub_zero.
 (* 9 *)
 replace omega2_ty with (Fork (Stem omega21_ty) omega22_ty) in H1; no_quanta. inv_out H1.  no_quant.
 (* 8 *)
 inv_out H0; no_quant.
 right; repeat eexists.
 5: do 4 right; repeat eexists; eauto.
 5: instantiate(3:= nil); simpl; eauto.
 instantiate(1:= 0); eapply chip_count_nil.
 2: instantiate(1:= 0); simpl.
 1-4: simpl; eapply sub_zero.
 (* 7 *)
 right; repeat eexists.
 5: left; instantiate(5:= app bs1 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite quant_count_app; simpl. rewrite plus_0_r; instantiate(1:= 0); eapply chip_count_nil.
 2: instantiate(1:= 0).  1-3: simpl; eapply sub_zero.
 (* 6 *)
 eelim quanta_is_asf; intros; eauto; subst; simpl in *; no_quant; no_quanta. 
 (* 5 *)
 right; repeat eexists.
 5: left. 5: instantiate(5:= false :: nil); simpl; instantiate(4:= 0); simpl; eauto.
 instantiate(1:= 0); eapply chip_count_nil.
 2: instantiate(1:= 1); simpl. 1-3: eapply sub_zero.
 (* 4 *)
 all: cycle -1. 
 eelim quanta_is_quant; intros; eauto; subst; simpl in *; no_quant; no_quanta. 
 eelim IHs; intros; eauto; clear IHs; split_all; disjunction_tac; split_all; disjunction_tac; split_all.
 (* 9 *)
 left; auto_t.
 (* 8 *)
 right; repeat eexists.
 5: left. 5: instantiate(5:= app x4 (true :: nil)); rewrite quanta_app; simpl; eauto. 
 rewrite ! quant_count_app; simpl. 
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1); replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1-3: eauto.
 (* 7 *)
 right; repeat eexists.
 5: right; left; repeat eexists.
 5: instantiate(3:= app x4 (true :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. 
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1); replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1-4: eauto.
 (* 6 *)
 right; repeat eexists.
 5: do 2 right; left; repeat eexists.
 5: instantiate(3:= app x4 (true :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. 
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1); replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1-4: eauto.
 (* 5 *)
 right; repeat eexists.
 5: do 3 right; left; repeat eexists.
 5: instantiate(3:= app x4 (true :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. 
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1); replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1-4: eauto.
 (* 4 *)
 right; repeat eexists.
 5: do 4 right; repeat eexists.
 5: eauto.
 5: instantiate(3:= app x4 (true :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. 
 replace (quant_count x + 1) with (S (quant_count x)) by lia.
 instantiate(1:= x1); replace (x1 + (quant_count x4 + 1)) with (S (x1 + quant_count x4)) by lia.
 eapply chip_count_succ; eauto.
 1-4: auto_t.
 (* 3 *)
 all: cycle -1. 
 eelim quanta_is_asf; intros; eauto; subst; simpl in *; no_quant; no_quanta. 
 eelim IHs; intros; eauto; clear IHs; split_all; disjunction_tac; split_all; disjunction_tac; split_all.
 (* 8 *)
 left; auto_t. 
 (* 7 *)
 right; repeat eexists.
 5: left. 5: instantiate(5:= app x4 (false :: nil)); rewrite quanta_app; simpl; eauto. 
 rewrite ! quant_count_app; simpl.
 rewrite ! plus_0_r; eauto. 
 1-3: eauto.
 (* 6 *)
 right; repeat eexists.
 5: right; left; repeat eexists.
 5: instantiate(3:= app x4 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. rewrite ! plus_0_r; eauto.  
 1-4: eauto.
 (* 5 *)
 right; repeat eexists.
 5: do 2 right; left; repeat eexists.
 5: instantiate(3:= app x4 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. rewrite ! plus_0_r; eauto. 
 1-4: eauto.
 (* 4 *)
 right; repeat eexists.
 5: do 3 right; left; repeat eexists.
 5: instantiate(3:= app x4 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. rewrite ! plus_0_r; eauto. 
 1-4: eauto.
 (* 3 *)
 right; repeat eexists.
 5: do 4 right; repeat eexists.
 5: eauto.
 5: instantiate(3:= app x4 (false :: nil)); rewrite quanta_app; simpl; eauto.
 rewrite ! quant_count_app; simpl. rewrite ! plus_0_r; eauto. 
 1-4: auto_t.
 (* 2 *)
 all: cycle -1.
 eelim subtype_from_forkty4; intros. 3: eauto. 
 left; eapply fork_not_funty; eauto.
 split_all.
 right;  repeat eexists.  instantiate(1:= nil); instantiate(1:= 0); simpl; eapply chip_count_nil.
 2: instantiate(3:= 0); simpl; eauto. eauto. eauto. left; auto.
 (* 1 *)
 eelim IHs1; intros; eauto; clear IHs1; split_all; disjunction_tac; split_all; disjunction_tac; split_all.
 (* 6 *)
 left; eapply subtype_not_funty; eauto.
 (* 5 *)
 all: cycle 1.
 clear IHs2.
 eelim subtype_from_quanta_funty; intros. 2: eapply s2. 2: eauto. split_all. 
 right; repeat eexists.  5: right; left; repeat eexists.
 5: eapply sub_trans; eauto;  eapply sub_trans. 5: eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 5: rewrite trim_leaf; replace Leaf with (lift x2 Leaf) at 1 by auto; eapply subtype_lift2.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 simpl.  eauto. 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto. simpl. 
 rewrite trim_quantf. eapply sub_trans. eapply subtype_quant_quantf.
 eapply subtype_quantf; eauto. eapply sub_zero. 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply subtype_preserves_iter_bfff_aug; eauto. eapply sub_zero. 
 (* 4 *)
 clear IHs2.
 eelim subtype_from_quanta_funty; intros. 2: eapply s2. 2: eauto. split_all. 
 right; repeat eexists.  5: do 2 right; left; repeat eexists.
 5: eapply sub_trans; eauto;  eapply sub_trans. 5: eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 5: rewrite trim_stem; eapply subtype_quant_stem. 
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 simpl.   eapply sub_zero.  
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto. simpl. 
 rewrite trim_quantf. eapply sub_trans. eapply subtype_quant_quantf.
 eapply subtype_quantf. rewrite trim_funty. dist_tac. eapply sub_zero. eauto. 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply subtype_preserves_iter_bfff_aug; eauto.  eapply sub_zero. 
 (* 3 *)
 clear IHs2.
 eelim subtype_from_quanta_funty; intros. 2: eapply s2. 2: eauto. split_all. 
 right; repeat eexists.  5: do 3 right; left; repeat eexists.
 5: eapply sub_trans; eauto;  eapply sub_trans. 5: eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 5: rewrite trim_fork; eapply subtype_quant_fork. 
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 simpl.  eapply sub_zero.  
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto. simpl. 
 rewrite trim_quantf. eapply sub_trans. eapply subtype_quant_quantf.  eapply sub_zero. 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply subtype_preserves_iter_bfff_aug; eauto.
 rewrite ! trim_funty. dist_tac. eapply sub_zero.  dist_tac. eapply sub_zero. eauto. 
 (* 2 *)
 clear IHs2.
 eelim subtype_from_quanta_funty; intros. 2: eapply sub_trans; [ eapply H9 | eapply s2]. 2: eauto. split_all. 
 right; repeat eexists.  5: do 4 right; repeat eexists.  5: eauto.
 5: rewrite quanta_to_quant; trim2_tac; rewrite quant_plus2.
 5: eapply sub_trans. 5: eapply subtype_quant_to_quanta. 5: eapply subtype_quanta.
 5: rewrite trim_funty; dist_tac; eauto.
 rewrite quant_count_quant_to_quanta. eauto.
 1-3: eauto.
 (* 1 *)
 eelim IHs2; intros.  3: eauto. auto. clear IHs2. split_all; disjunction_tac; split_all; auto.
 (* 3 *)
 right; repeat eexists.  
 5: left; eauto.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 eauto.  
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_quantf. 
 eapply sub_trans. eapply subtype_quant_quantf.  rewrite quantf_plus. eapply subtype_quantf. eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bfff_aug; eauto.
 replace (iter (x1 + x9) bfff_aug x14) with (iter x1 bfff_aug (iter x9 bfff_aug x14)). 
 eapply sub_zero. generalize x9 x14. clear. induction x1; intros; simpl; auto.
 rewrite IHx1; auto.
 (* 2 *) 
 disjunction_tac; split_all.
 (* 4 *) 
 right; repeat eexists.  
 5: right; left; eauto; repeat eexists; left; repeat eexists; eauto.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 simpl; eauto.  
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_quantf. 
 eapply sub_trans. eapply subtype_quant_quantf.  rewrite quantf_plus. eapply subtype_quantf. eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bfff_aug; eauto.
 replace  (iter x1 bfff_aug (iter x9 bfff_aug x14)) with (iter (x1 + x9) bfff_aug x14). 
 eapply sub_zero. generalize x9 x14. clear. induction x1; intros; simpl; auto. rewrite IHx1; auto.
 (* 3 *) 
 right; repeat eexists.  
 5: do 2 right; left; repeat eexists; eauto.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto. eauto. 
  rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_quantf. 
 eapply sub_trans. eapply subtype_quant_quantf.  rewrite quantf_plus. eapply subtype_quantf. eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bfff_aug; eauto.
 replace  (iter x1 bfff_aug (iter x9 bfff_aug x14)) with (iter (x1 + x9) bfff_aug x14). 
 eapply sub_zero. generalize x9 x14. clear. induction x1; intros; simpl; auto. rewrite IHx1; auto.
 (* 2 *) 
 right; repeat eexists.  
 5: do 3 right; left; eauto; repeat eexists.
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto. eauto.  
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_quantf. 
 eapply sub_trans. eapply subtype_quant_quantf.  rewrite quantf_plus. eapply subtype_quantf. eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bfff_aug; eauto.
 replace  (iter x1 bfff_aug (iter x9 bfff_aug (Funty x15 (Funty x16 x17)))) with
      (iter (x1 + x9) bfff_aug (Funty x15 (Funty x16 x17))). 
 eapply sub_zero. generalize x9 x15 x16 x17. clear. induction x1; intros; simpl; auto. rewrite IHx1; eauto.
 eauto.
 (* 1 *) 
 right; repeat eexists.  
 5: do 4 right; repeat eexists; eauto. 
 eapply chip_count_app2; eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto. eauto. 
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_quantf. 
 eapply sub_trans. eapply subtype_quant_quantf.  rewrite quantf_plus. eapply subtype_quantf. eauto.
 rewrite trim_app. rewrite quant_plus2. rewrite <- trim_quant.
 eapply sub_trans. eapply subtype_quant; eapply trim_preserves_subtype; eauto.
 rewrite trim_preserves_iter_bfff_aug.
 eapply sub_trans. eapply subtype_quant_iter_bfff_aug.
 eapply sub_trans. eapply subtype_preserves_iter_bfff_aug; eauto.
 replace     (iter x1 bfff_aug
       (iter x9 bfff_aug
          (Quant (Quant (Funty (Var 1) (Funty (Var 0) (subst (lift_rec x16 1 2) (Fork (Var 1) (Var 0)))))))))
    with (iter (x1 + x9) bfff_aug
       (Quant (Quant (Funty (Var 1) (Funty (Var 0) (subst (lift_rec x16 1 2) (Fork (Var 1) (Var 0)))))))). 
 eapply sub_zero. generalize x9 x16. clear. induction x1; intros; simpl; auto. rewrite IHx1; auto.
Qed.


Theorem subtype_from_fork_of_fork_of_leaf:
  forall wty uty vty ty, subtype (Fork (Fork wty uty) vty) (Funty Leaf ty) -> subtype wty ty.
Proof.
  intros; eelim subtype_from_fork_of_fork; intros.  3: eauto.
  3: instantiate(5:= nil); instantiate(4:= 0); simpl; eauto. 
  inv_out H0.
  split_all; disjunction_tac; split_all; no_quanta; rewrite ? plus_0_r in *.   
  (* 4 *)
  inv_out H4; rewrite quant0 at 1; trim2_tac; rewrite plus_0_r; auto. 
  (* 3 *)
  inv_out H5. cut False. tauto.    eapply subtype_leafty_not_stemty. eapply H8. 1,2: auto_t.
  (* 2 *)
  inv_out H5. cut False. tauto.    eapply subtype_leafty_not_forkty. eapply H8. 1,2: auto_t.
  (* 1 *)
  simpl in *. 
  eelim subtype_from_quanta_funty; intros. 2: eapply H10. 2: eauto. split_all. no_quanta. inv_out H6. 
  eapply sub_trans; eauto.
  rewrite quant0 at 1; trim2_tac. rewrite quant_plus2. 
  eapply sub_trans. eapply subtype_quant; eauto. trim2_tac. rewrite plus_0_r in *.
  eapply subtype_quant.
  unfold subst; replace x9 with (map (chip_lift 0) x9) by (rewrite chip_lift_zero; auto). (* good trick! *) 
  rewrite ! trim_preserves_subst_rec. 
  unfold covariant in *.
  eapply variant_subst_rec_preserves_subtype; eauto.
  rewrite chip_lift_variant; try lia; auto.
  rewrite trim_leaf.
  replace Leaf with (lift x2 Leaf) by auto.
  eapply sub_trans. 2: eapply subtype_lift3.
  eapply lift_rec_preserves_subtype; eauto.
Qed.



Theorem subtype_from_fork_of_fork_of_stem:
  forall wty uty vty zty ty,
    subtype (Fork (Fork wty uty) vty) (Funty (Stem zty) ty) -> subtype uty (Funty zty ty).
Proof.
  intros; eelim subtype_from_fork_of_fork; intros.  3: eauto.
  3: instantiate(5:= nil); instantiate(4:= 0); simpl; eauto. 
  inv_out H0.
  split_all; disjunction_tac; split_all; no_quanta.   
  (* 4 *)
  inv_out H4. cut False. tauto.    eapply subtype_stemty_not_leafty. eapply H7. 1,2: auto_t.
  all: cycle 1. 
  inv_out H5.  cut False. tauto.    eapply subtype_stemty_not_forkty. eapply H8. 1,2: auto_t.
  all: cycle -1.
  (* 2 *) 
  inv_out H5. 
  eelim (subtype_from_stemty4); intros.   3: instantiate(3:= 0); simpl; eauto.
  inv_out H4. split_all. no_quant. 
  rewrite plus_0_r in *.   rewrite quant0 at 1. trim2_tac. eapply sub_trans; eauto.
  eapply sub_trans. eapply subtype_from_asf. sub_fun_tac. auto.
  (* 1 *)
  simpl in *. 
  eelim subtype_from_quanta_funty; intros. 2: eapply H10. 2: eauto. split_all. no_quanta. inv_out H6. 
  rewrite plus_0_r in *; rewrite quant0 at 1; trim2_tac. rewrite quant_plus2. 
  eapply sub_trans. eapply subtype_quant; eauto.
  eapply sub_trans. eapply subtype_quant.
  eapply sub_trans. eapply subtype_quantf_Quant.
  eapply sub_trans. eapply sub_quant. eapply subtype_from_asf. eapply sub_zero.
  eapply sub_trans. 
  eapply subtype_quant. subst_tac.   rewrite subst_rec_subst_rec; try lia.
  rewrite subst_rec_lift_rec; try lia.
  rewrite lift_rec_null.
  dist_tac.
  eapply subtype_lift.
  simpl; var_tac.
  trim2_tac. eapply sub_trans; eauto.
  eapply subtype_quant.
  unfold subst; replace x9 with (map (chip_lift 0) x9) by (rewrite chip_lift_zero; auto). (* good trick! *) 
  rewrite ! trim_preserves_subst_rec. 
  unfold covariant in *.
  eapply variant_subst_rec_preserves_subtype; eauto.
  rewrite chip_lift_variant; try lia; auto.
  replace (Stem (lift_rec zty 0 (quant_count x3))) with (lift_rec (Stem zty) 0 (quant_count x3)) by auto.
  eapply sub_trans. eapply trim_preserves_subtype; eapply lift_rec_preserves_subtype; eauto.
  eapply trim_lift2; eauto.
Qed.



Theorem subtype_from_fork_of_fork_of_fork:
  forall wty uty vty zty1 zty2 ty,
    subtype (Fork (Fork wty uty) vty) (Funty (Fork zty1 zty2) ty) -> subtype vty (Funty zty1 (Funty zty2 ty)).
Proof.
  intros; eelim subtype_from_fork_of_fork; intros.  3: eauto.
  3: instantiate(5:= nil); instantiate(4:= 0); simpl; eauto. 
  inv_out H0.
  split_all; disjunction_tac; split_all; no_quanta.   
  (* 4 *)
  inv_out H4. cut False. tauto.    eapply subtype_forkty_not_leafty. eapply H7. 1,2: auto_t.
  inv_out H5. cut False. tauto.    eapply subtype_forkty_not_stemty. eapply H8. 1,2: auto_t.
  (* 2 *)
  inv_out H5.
  eelim (subtype_from_forkty4); intros.   3: instantiate(4:= 0); simpl; eauto.
  inv_out H4. split_all. no_quant. 
  rewrite plus_0_r in *.   rewrite quant0 at 1. trim2_tac. eapply sub_trans; eauto.
  eapply sub_trans. eapply  iter_bfff_aug_of_binary_fun.
  eapply sub_funty; eauto; sub_fun_tac; eauto.
  (* 1 *)
  simpl in *. 
  eelim subtype_from_quanta_funty; intros. 2: eapply H10. 2: eauto. split_all. no_quanta. inv_out H6. 
  rewrite plus_0_r in *; rewrite quant0 at 1; trim2_tac. rewrite quant_plus2. 
  eapply sub_trans. eapply subtype_quant; eauto.
  eapply sub_trans. eapply subtype_quant. eapply iter_bfff_aug_Quant.   rewrite quant_succ3. 
  eapply sub_trans. eapply subtype_quant. eapply iter_bfff_aug_Quant.   rewrite quant_succ3. 
  eapply sub_trans. eapply subtype_quant. eapply iter_bfff_aug_of_binary_fun. simpl.
  eapply sub_trans. eapply subtype_quant. eapply sub_trans; subst_tac.
  dist_tac. eapply subtype_lift.
  dist_tac. eapply subtype_lift.
  rewrite (subst_rec_subst_rec (lift_rec _ _ _)); try lia. 
  rewrite subst_rec_subst_rec; try lia. 
  rewrite subst_rec_lift_rec; try lia. 
  rewrite subst_rec_lift_rec; try lia. simpl; var_tac. 
  rewrite lift_rec_lift_rec; try lia.
  rewrite subst_rec_lift_rec; try lia.
  eapply sub_trans; eauto. 
  trim2_tac.
  eapply subtype_quant.
  unfold subst; replace x9 with (map (chip_lift 0) x9) by (rewrite chip_lift_zero; auto). (* good trick! *) 
  rewrite ! trim_preserves_subst_rec. 
  unfold covariant in *.
  eapply variant_subst_rec_preserves_subtype; eauto.
  rewrite chip_lift_variant; try lia; auto.
  rewrite <- lift_rec_fork.
  eapply sub_trans. eapply trim_preserves_subtype; eapply lift_rec_preserves_subtype; eauto.
  eapply trim_lift2; eauto.
Qed.

   
 
 
