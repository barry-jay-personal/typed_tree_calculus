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
(*                Classifying Derivation                              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)




Require Import String Arith Lia Bool List Nat.
Require Import terms types subtypes derive classify. 

Open Scope string_scope.
Open Scope nat_scope.

Set Default Proof Using "Type".




Proposition derive_ref_rev:
  forall gamma x ty,
    derive gamma (Ref x) ty ->
    exists ty0, get x gamma = Some ty0 /\ subtype ty0 ty. 
Proof.
  cut(forall gamma M ty,
         derive gamma M ty ->
         forall x, M = Ref x ->
                   exists ty0, get x gamma = Some ty0 /\ subtype ty0 ty). 
  intros; eapply H; eauto.  
  intros gamma M ty d; induction d; intros; subst; try discriminate.
  inv_out H1.   repeat eexists; auto_t.
Qed.  



Proposition derive_leaf_rev: forall gamma ty, derive gamma Node ty -> subtype Leaf ty. 
Proof.
  cut(forall gamma M ty, derive gamma M ty -> M = Node -> subtype Leaf ty). 
  intros; eapply H; eauto.  
  intros gamma M ty d; induction d; intros; subst; try discriminate; auto.
Qed. 



Proposition derive_stem_rev:
  forall gamma M ty,
    derive gamma M ty ->
    forall N, M = Node @ N -> exists ty1, derive gamma N ty1 /\ subtype (Stem ty1) ty.
Proof.
  intros gamma M ty d; induction d; intros; subst; eauto; try discriminate.
  clear IHd1 IHd2; inv_out H. 
  repeat eexists; eauto.
  assert(subtype Leaf (Funty u ty)) by (eapply derive_leaf_rev; eauto); no_quant.
  eelim (subtype_from_leafty2 nil); intros; eauto. split_all. no_quanta.
  eelim (subtype_from_quanta_funty); intros. 2: eapply H0. 2: instantiate(3:= true :: nil); auto.
  split_all. no_quanta. inv_out H2. 
  eapply sub_trans; eauto.
  eapply sub_trans. eapply sub_stem; eauto.
  rewrite trim_stem. eapply stem_quant_commute. 
Qed.



 
Proposition derive_fork_rev:
  forall gamma M ty,
    derive gamma M ty ->
    forall N P,
      M = Node @ N @ P ->
      ((exists ty1 ty2, derive gamma N ty1 /\ derive gamma P ty2 /\ subtype (Fork ty1 ty2) ty)).
Proof.
  intros gamma M ty d; induction d; intros; subst; eauto; try discriminate.
  clear IHd1 IHd2; inv_out H. 
  (* 1 *)   
  assert(exists ty1, derive gamma N0 ty1 /\ subtype (Stem ty1) (Funty u ty))
    by (eapply derive_stem_rev; eauto); no_quant. clear d1. 
  assert(subtype (Fork x u) ty) by (eapply subtype_from_stemty_to_fun; eauto).   
  repeat eexists; eauto; eapply sub_trans; eauto.
Qed.


Theorem derive_stem :
  forall gamma P ty,
    derive gamma (Node @ P) ty ->
    (exists k pty,  derive gamma P (quant k pty) /\ subtype (quant k (Stem pty)) ty).
Proof.
  cut(forall gamma M ty,
         derive gamma M ty ->
         forall P, M = Node @ P -> 
                   (exists k pty,  derive gamma P (quant k pty) /\ subtype (quant k (Stem pty)) ty)). 
  intros; eapply H; eauto.
  intros gamma M ty d; induction d; intros; subst; try discriminate.
  clear IHd1 IHd2; inv_out H.
  assert(subtype Leaf (Funty u ty)) by  (eapply derive_leaf_rev; eauto);
    clear d1; disjunction_tac; no_quant. 
  eelim (subtype_from_leafty2 nil); intros; eauto. split_all. no_quanta.
  eelim (subtype_from_quanta_funty); intros. 2: eapply H0. 2: instantiate(3:= true :: nil); auto.
  split_all. no_quanta. inv_out H2. 
  exists 0; repeat eexists; eauto. 
  eapply sub_trans; eauto. rewrite trim_stem.
  eapply sub_trans. eapply sub_stem. eauto. eapply stem_quant_commute. 
Qed.



Theorem derive_fork :
  forall gamma P Q ty,
    derive gamma (Node @ P @ Q) ty ->
    ((exists scs kp pty scsq kq qty kr,
        derive gamma P (quant kp pty) /\
        chip_count scs kp kq /\
        derive gamma Q (quant kq qty) /\
        chip_count scsq kq kr /\
        subtype (quant kr (Fork (trim scsq (trim scs pty))
                                  (trim scsq qty))) ty)
).
Proof.
  cut(forall gamma M ty,
         derive gamma M ty ->
         forall P Q,
           M = (Node @ P @ Q) -> 
    ((exists scs kp pty scsq kq qty kr,
        derive gamma P (quant kp pty) /\
        chip_count scs kp kq /\
        derive gamma Q (quant kq qty) /\
        chip_count scsq kq kr /\
        subtype (quant kr (Fork (trim scsq (trim scs pty))
                                  (trim scsq qty))) ty))
       )
     .
  intros; eapply H; eauto. 
  intros gamma M ty d; induction d; intros; subst; try discriminate.
  clear IHd1 IHd2. inv_out H. 
  eelim derive_stem; intros; eauto; clear d1; disjunction_tac; no_quant.
  assert(subtype (Fork (quant x x0) u) ty).
  eapply subtype_from_stemty_to_fun; eapply sub_trans; [ eapply stem_quant_commute | eauto]. 
  repeat eexists; eauto.
  2: eapply derive_subtype; eauto; eapply subtype_lift.
  1,2: eapply chip_count_nil.
  simpl. eapply sub_trans; eauto.
  eapply sub_trans. eapply subtype_quant_fork.
  eapply sub_fork. eapply sub_zero.   eapply subtype_lift2. 
Qed.


 


Theorem programs_have_principal_types:
  forall p, program p ->
            forall gamma ty, derive gamma p ty -> subtype (program_type p) ty.
Proof.
  cut (forall n p,
          term_size p < n -> program p -> 
             forall gamma ty, derive gamma p ty -> subtype (program_type p) ty).
  intros; eapply H; eauto.
  induction n; intros; try lia.
  inv_out H0; simpl.
  (* 3 *)
  eapply derive_leaf_rev; eauto. 
  (* 2 *) 
  eelim derive_stem_rev; intros.  2: eapply H1. 2: eauto. no_quant. clear H1. 
  eapply sub_trans. eapply sub_stem.  eapply IHn; simpl in *; eauto; try lia. auto.
  (* 1 *)
  eelim derive_fork_rev; intros.  2: eapply H1. 2: eauto. no_quant. 
  eapply sub_trans. 2: eauto.
  simpl in *; eapply sub_fork;  eapply IHn; eauto; lia. 
Qed.

 

  
Theorem normal_types: forall gamma p ty, normal_type gamma p = Some ty -> derive gamma p ty. 
Proof.
  induction p; intros; inv_out H; auto_t.
  caseEq p1; intros; subst; try discriminate.
  caseEq (normal_type gamma p2); intros; rewrite H in *.
  inv_out H1.
  eapply derive_app.   eapply derive_node. auto_t. eauto. discriminate.
  (* 1 *)
  caseEq t; intros; subst; try discriminate.
  caseEq (normal_type gamma t0); intros; rewrite H in *.
  caseEq (normal_type gamma p2); intros; rewrite H0 in *.
  inv_out H1.
  eapply derive_app. eapply derive_subtype.  eapply IHp1. simpl.  rewrite H. eauto. 
  auto_t.
  eauto.
  1,2: discriminate.
Qed.


Theorem principal_types:
  forall gamma p ty, normal_type gamma p = Some ty -> 
    forall ty2, derive gamma p ty2 -> subtype ty ty2.
Proof.
  induction p; intros.
  eelim derive_ref_rev; eauto; intros; split_all.
  simpl in *. rewrite H in *. inv_out H2. auto. 
  simpl in *.   inv_out H. eapply derive_leaf_rev; eauto.
  caseEq p1; intros; subst; simpl in *; try discriminate.
  caseEq (normal_type gamma p2); intros;   rewrite H1 in *; inv_out H. 
  eelim derive_stem_rev; intros.  2: eapply H0. 2: eauto. no_quant.
  eapply sub_trans; eauto. eapply sub_stem; auto.
  caseEq t; intros; subst; try discriminate.
  (* 1 *) 
  eelim derive_fork_rev; intros.  2: eapply H0. 2: eauto. no_quant. 
  caseEq (normal_type gamma t0); intros; rewrite H3 in *; inv_out H. 
  caseEq (normal_type gamma p2); intros; rewrite H in *; inv_out H6. 
  eelim derive_fork_rev; intros.  2: eapply H0. 2: eauto. no_quant.
  eapply sub_trans; eauto. eapply sub_fork; auto.
  assert(subtype (Stem d) (Stem x1)). eapply IHp1; eauto.
  eapply derive_app. eapply derive_node. eapply sub_leaf_fun.   auto.
  eapply subtype_of_stemty; eauto. 
Qed.
 

 
 
