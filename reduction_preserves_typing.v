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
(*                  Subject Reduction                                 *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import String Arith Lia Bool List Nat Datatypes.
Require Import terms types subtypes derive classify classify_derive. 

Set Default Proof Using "Type".



(* Each reduction rule of tree calculus must be shown to preserve typing *)


Proposition derive_fork_leaf :
  forall gamma N vty ty, derive gamma (K @ N) (Funty vty ty) -> derive gamma N ty.
Proof.
  unfold K; intros.  eelim derive_fork; intros; eauto; clear H; no_quant. 
  assert(subtype Leaf (quant x0 x1)) by (eapply derive_leaf_rev; eauto); clear H; split_all.
  assert(subtype (Fork Leaf (quant x3 x4)) (Funty vty ty)). 
  eapply sub_trans. 2: eauto. 
  rewrite <- trim_fork.   eapply sub_trans. 2: trim2_tac. 
  eapply sub_trans. 2: eapply fork_quant_commute. eapply sub_fork. eapply subtype_lift. eapply sub_zero. 
  eapply subtype_quant. eapply trim_preserves_subtype. eapply sub_fork. 2: eapply sub_zero.
  unfold lift; eapply sub_trans. eapply lift_rec_preserves_subtype.
  eapply sub_trans. eauto. trim2_tac. eapply sub_zero. eapply subtype_lift3. 
  (* 1 *)
  eapply derive_subtype; eauto.  clear H1 H3 H4.
  eapply subtype_from_fork_of_leaf_to_fun; eauto. 
Qed.


Proposition derive_fork_stem :
  forall gamma M N P vty ty,
    derive gamma (Node @ (Node @ M) @ N) (Funty vty ty) -> derive gamma P vty ->
    derive gamma (M @ P @ (N @ P)) ty. 
Proof.
  intros gamma M N P vty ty d1 d2.
  eelim derive_fork_rev; intros.  2: eapply d1. 2:eauto. clear d1; no_quant. 
  eelim derive_stem_rev; intros. 2: eapply H. 2:eauto. clear H; no_quant.
  eelim subtype_from_fork_of_stem_to_funty; intros.
  2: eapply sub_trans; eauto; eapply sub_fork; eauto; eapply sub_zero.
  split_all.
   repeat eapply derive_app; eauto; eapply derive_subtype; eauto; rewrite quant0 at 1; trim2_tac;
    rewrite quant_plus2;  (eapply sub_trans; [ eapply subtype_quant; eauto |]);
      trim2_tac; rewrite ! trim_funty; repeat (dist_tac; auto); eapply sub_zero.
Qed.


Proposition derive_fork_fork_leaf :
  forall gamma P Q M N ty,
    derive gamma (Node @ (Node @ P @ Q) @ M) (Funty Leaf ty) -> derive gamma N Leaf ->
    derive gamma P ty. 
Proof.
  intros gamma P Q M N vty d1 d2.  
  eelim derive_fork_rev; intros. 2: eapply d1. 2: eauto. clear d1; no_quant. 
  eelim derive_fork_rev; intros. 2: eapply H. 2: eauto. clear H; no_quant.
  eapply derive_subtype; eauto. 
  eapply subtype_from_fork_of_fork_of_leaf. eapply sub_trans; eauto; eapply sub_fork; eauto; eapply sub_zero.
Qed.
 

Proposition derive_fork_fork_stem :
  forall gamma P Q M N zty ty,
    derive gamma (Node @ (Node @ P @ Q) @ M) (Funty (Stem zty) ty) -> derive gamma N (Stem zty) ->
    derive gamma Q (Funty zty ty). 
Proof.
  intros gamma P Q M N zty ty d1 d2.  
  eelim derive_fork_rev; intros. 2: eapply d1. 2: eauto. clear d1; no_quant. 
  eelim derive_fork_rev; intros. 2: eapply H. 2: eauto. clear H; no_quant. 
  eapply derive_subtype; eauto.  clear d2 H0 H1 H.
  eapply subtype_from_fork_of_fork_of_stem.
  eapply sub_trans; eauto; eapply sub_fork; eauto; eapply sub_zero.
Qed.


Proposition  derive_fork_fork_fork :
  forall gamma P Q M N zty1 zty2 ty,
    derive gamma (Node @ (Node @ P @ Q) @ M) (Funty (Fork zty1 zty2) ty) ->
    derive gamma N (Fork zty1 zty2) ->
    derive gamma M (Funty zty1 (Funty zty2 ty)). 
Proof.
  intros gamma P Q M N zty1 zty2 ty d1 d2.  
  eelim derive_fork_rev; intros. 2: eapply d1. 2: eauto. clear d1; no_quant. 
  eelim derive_fork_rev; intros. 2: eapply H. 2: eauto. clear H; no_quant. 
  eapply derive_subtype; eauto. clear gamma P Q M N d2 H H0 H1.
  eapply subtype_from_fork_of_fork_of_fork.
  eapply sub_trans; eauto; eapply sub_fork; eauto; eapply sub_zero.
Qed.


Theorem reduction_preserves_typing:
  forall gamma M ty, derive gamma M ty -> forall N, t_red1 M N -> derive gamma N ty. 
Proof.
  intros gamma M ty d;  induction d; intros; try (inv_out H0; fail); inv_out H.  
  (* 8 *)
  inv_out H1.
  eapply derive_fork_leaf; eauto.
  eapply derive_fork_stem; eauto.
  (* 5 *)
  assert(subtype Leaf u) by (eapply derive_leaf_rev; eauto). 
  eapply derive_fork_fork_leaf.  eapply derive_subtype; auto_t. auto_t.
  (* 4 *)
  eelim derive_stem_rev; intros; eauto; split_all.
  eapply derive_app. 2: eauto.  
  eapply derive_fork_fork_stem. eapply derive_subtype; auto_t. eapply derive_app.
  eapply derive_node. auto_t. eauto.
  (* 3 *)
  eelim derive_fork_rev; intros; eauto; split_all.
  eapply derive_app. 2: eauto.  eapply derive_app. 2: eauto. 
  eapply derive_fork_fork_fork. eapply derive_subtype; auto_t. eapply derive_app.
  eapply derive_app.   eapply derive_node. eapply subtype_leaf_fork. eauto. eauto. 
  (* 2 *)
  eapply derive_app; [  eapply IHd1 | ]; eauto.  
  eapply derive_app; eauto;  eapply IHd2; auto.
Qed.


 
 
