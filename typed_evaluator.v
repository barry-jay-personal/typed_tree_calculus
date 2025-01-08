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
(*                   Typed Evaluator                                  *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import String Arith Lia Bool List Nat Datatypes.
Require Import terms types subtypes derive typed_lambda typed_triage typed_recursion.

Set Default Proof Using "Type".

Definition eager_s_ty := quant 2 (Funty (Var 0) (Funty (Funty (Var 0) (Var 1)) (Var 1))).

Proposition derive_eager_s: (* note the use of double-negative covariance ! *) 
  forall gamma, derive gamma eager_s eager_s_ty.
Proof.
  intros; eapply derive_generalisation_q;
  replace  (Funty (Funty (Var 0) (Var 1)) (Var 1))
    with (subst (Funty (Funty (Var 0) (Var 2)) (Var 2)) (Var 0)) by (cbv; auto);
    eapply derive_triage; try (cbv; eauto; fail);
    unfold subst; simpl; var_tac; simpl; repeat eapply derive_generalisation; 
    eapply derive_S2.
  - eapply derive_I.
  - eapply derive_K1; eapply derive_node; auto_t. 
  - eapply derive_K1; eapply derive_app; [
      |
        eapply derive_app; [ eapply derive_node; eapply sub_leaf_fun | eapply derive_I]];
      eapply derive_node; eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac; sub_fork2_tac].
  - eapply derive_S2; [ eapply derive_K1; eapply derive_K |];
      eapply derive_S2; [ eapply derive_K1; eapply derive_node; eapply sub_leaf_fun | eapply derive_I].
  - eapply derive_K1; eapply derive_app; [
    |
      eapply derive_app; [ eapply derive_node; eapply sub_leaf_fun | eapply derive_K1];
      eapply derive_app; [ eapply derive_node; eapply sub_leaf_fun |];
      eapply derive_app; [eapply derive_node; eapply sub_leaf_fun | eapply derive_I]];
      eapply derive_node;  eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac];
      sub_fork2_tac; eapply sub_trans; [eapply sub_stem_fun | sub_fun_tac; sub_fork2_tac].
  - eapply derive_S2.
    + eapply derive_K1; eapply derive_app; [
        |
          eapply derive_app; [eapply derive_node;  eapply sub_leaf_fun | eapply derive_K1; eapply derive_K]];
        eapply derive_node; eapply sub_trans; [ eapply subtype_leaf_fork |]; do 2 sub_fun_tac; sub_fork2_tac.
    + eapply derive_S2.
      * eapply derive_S2; [
          | 
            eapply derive_S2; [ eapply derive_K1; eapply derive_node; eapply sub_leaf_fun |]]; [
            eapply derive_K1;  eapply derive_node; eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac; sub_fork2_tac] |];
          eapply derive_S2; [ eapply derive_K1; eapply derive_K |]; 
          eapply derive_S2; [ eapply derive_K1; eapply derive_node; eapply subtype_leaf_fork | eapply derive_I].
      * eapply derive_K1; eapply derive_S2; eapply derive_K.
  Unshelve. apply Leaf.
Qed. 


Theorem derive_eager: (* note the use of double-negative covariance ! *) 
  forall gamma, derive gamma eager eager_ty.
Proof.
  intros; eapply derive_generalisation_q; do 2 eapply derive_star;
    eapply derive_app; [ eapply derive_app; [ | eapply derive_ref; simpl; eauto; eapply sub_zero] |
                         eapply derive_ref; simpl; eauto; eapply sub_zero]; 
    eapply derive_subtype; [ eapply derive_eager_s | do 2 subst_tac]. 
Qed.




Proposition subtype_bf: subtype (Fork (Fork Leaf Leaf)
                        (quant 2 (Funty (Var 1) (Funty (Var 0) (Asf (Fork (Var 1) (Var 0)))))))
                          eval_ty.
Proof.
  eapply sub_trans; [ eapply sub_lift | ];
    eapply sub_quant; unfold lift; simpl; var_tac; 
    replace (Asf (Var 0)) with (subst (Asf (Var 0)) (Var 0)) by (cbv; auto);
    eapply sub_trans; [ | eapply sub_tree; cbv; auto];
    unfold subst; simpl; var_tac; eapply sub_fork; [ | eapply sub_zero];
    eapply sub_fork; auto_t.
Qed.



 Theorem derive_bf : derive nil bf eval_ty.
 Proof.
   eapply derive_Z; eapply derive_star;
     eapply derive_subtype; [ | eapply subtype_bf];
     eapply derive_app; [ 
       repeat eapply derive_app; eapply derive_node;
       (eapply sub_zero || (eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac])); eapply sub_zero |];
     (* bff *)
     eapply derive_generalisation_q;
     replace (Funty (Var 0) (Asf (Fork (Var 1) (Var 0)))) with
     (subst (Funty (Var 1) (Asf (Fork (Var 0) (Var 1)))) (Var 1)) by (cbv; auto);
     eapply derive_subtype; [ | eapply sub_tree; cbv; eauto];
     unfold subst; simpl; var_tac; simpl;
     eapply derive_app. 
   + eapply derive_app; [
         eapply derive_node;
         (eapply sub_zero || (eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac]));
         eapply sub_zero |];
       eapply derive_app; [
         repeat  eapply derive_app; eapply derive_node; [
           eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac]; eapply sub_zero |
           eapply sub_trans; [ eapply subtype_leaf_fork | do 2 sub_fun_tac; eapply sub_to_asf] |
           eapply sub_zero] |].
     (* bffs *)
     eapply derive_generalisation;   do 2 eapply derive_star; eapply derive_subtype; [ | eapply sub_bffs];
       eapply derive_app; [ 
         eapply derive_app; [ eapply derive_node; eapply subtype_leaf_fork |];
         eapply derive_app; [ eapply derive_node; eapply sub_leaf_fun |];
         eapply derive_app; [ 
           eapply derive_app; [  eapply derive_node; eapply subtype_leaf_fork |];
           eapply derive_app; [ eapply derive_node; eapply sub_leaf_fun |];
           eapply derive_app; [ 
             eapply derive_app; [ eapply derive_node; eapply subtype_leaf_fork |];
             eapply derive_node; eapply sub_zero |
             eapply derive_eager] |
           eapply derive_app; [ 
             eapply derive_app; [ eapply derive_node; eapply subtype_leaf_fork |];
             eapply derive_app; [ eapply derive_node; eapply sub_leaf_fun |];
             eapply derive_app; [ 
               eapply derive_app; [ eapply derive_node; eapply subtype_leaf_fork |]; 
               eapply derive_node; eapply sub_zero |
               eapply derive_ref; simpl; eauto; eapply sub_zero] |
             eapply derive_app; eapply derive_ref; simpl; eauto; [ subst_tac | eapply sub_zero]]] |
         eapply derive_app; eapply derive_ref; simpl; eauto; [ subst_tac | eapply sub_zero]].
   +    (* bfff *)
     do 2 eapply derive_generalisation;   do 3 eapply derive_star;   eapply derive_subtype; [ 
       eapply derive_app; [ 
         eapply derive_app; [ eapply derive_node; eapply subtype_leaf_fork |];
         eapply derive_app; [ 
           eapply derive_app; [ eapply derive_node; eapply subtype_leaf_fork |];
           eapply derive_ref; simpl; eauto; eapply sub_zero |
           eapply derive_app; eapply derive_ref; simpl; eauto; [ cbv; subst_tac | eapply sub_zero]] |
         eapply derive_app; [ | eapply derive_ref; simpl; eauto; eapply sub_zero];
         eapply derive_star;   cbv; 
         repeat eapply derive_app; (eapply derive_ref || eapply derive_node); simpl; eauto; try eapply sub_zero;
         (eapply sub_zero || eapply sub_leaf_fun || eapply subtype_leaf_fork || subst_tac || idtac)] |
       replace (Quant (Funty (Var 0) (Asf (Var 0)))) with eval_ty by (cbv; auto); eapply sub_bfff].
 Qed.
 
