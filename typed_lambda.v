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
(*                 Lambda Abstraction                                 *) 
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List Nat Datatypes String.
Require Import terms types subtypes derive classify.


Set Default Proof Using "Type".

Open Scope string_scope.
 

Lemma derive_occurs_false:
  forall gamma M ty, derive gamma M ty ->
                     forall x uty gamma1, gamma = (x,uty):: gamma1 -> occurs x M = false ->
                                          derive gamma1 M ty.
Proof.
  intros gamma M ty d; induction d; intros; subst; simpl in *; auto_t.
  - rewrite H2 in *; eapply derive_ref; eauto.
  - rewrite orb_false_iff in *; split_all;  eapply derive_app; [  eapply IHd1 | eapply IHd2]; eauto.
Qed.

Lemma derive_occurs_false2:
  forall gamma M ty, derive gamma M ty ->
                     forall x uty, occurs x M = false ->
                                          gamma <> nil -> derive ((x,uty):: gamma) M ty.
Proof.
  intros gamma M ty d; induction d; intros; subst; simpl in *; auto_t.
  - replace (get x gamma) with (get x ((x0, uty) :: gamma)) by (simpl; rewrite H1; auto);
      eapply derive_ref; simpl; [rewrite H1; eauto | auto].
  - rewrite orb_false_iff in *; split_all; eapply derive_app; [  eapply IHd1 | eapply IHd2]; eauto.
Qed.


Proposition derive_ref_sub:
  forall gamma M ty,
    derive gamma M ty ->
    forall s uty gamma1, gamma = (s,uty):: gamma1 -> M = Ref s -> subtype uty ty. 
Proof.
  intros gamma M ty d; induction d; intros; subst; auto_t; try discriminate; 
  inv_out H2; simpl in *; rewrite String.eqb_refl in *; inv_out H; auto. 
Qed.


Theorem derive_star:
  forall M gamma x uty ty, derive ((x,uty) :: gamma) M ty -> derive gamma (star x M) (Funty uty ty).
Proof.
  cut(forall M gamma0 ty,
         derive gamma0 M ty ->
         forall x uty gamma, gamma0 = ((x,uty)::gamma) -> derive gamma (star x M) (Funty uty ty)); [
      intros; eapply H; eauto |];
    intros M gamma0 ty d; induction d; intros; subst; simpl in *.
  - caseEq (x0=?x)%string; intros; subst; rewrite H1 in *; [
        inv_out H; eapply derive_subtype; [  eapply derive_I |  sub_fun_tac; auto] |
        eapply derive_K1; auto_t].
  - eapply derive_K1; auto_t.
  - caseEq N; intros; subst.
    + caseEq (x=? s)%string; intros. 
      * assert(x = s) by (eapply String.eqb_eq; eauto); subst;
          assert(subtype uty u) by (eapply derive_ref_sub; eauto).
          caseEq (occurs s M); intros; simpl; [
            eapply derive_S2; eauto | ]. 
          eapply derive_subtype; [ eapply derive_I | auto_t].
          assert(derive gamma0 (\ s M) (Funty uty (Funty u ty))) by (eapply IHd1; eauto).  
          rewrite star_occurs_false in H2; auto. inv_out H2.
          eapply derive_subtype; eauto.
          inv_out H6; inv_out H5; inv_out H9.
          eelim subtype_from_leafty2; intros.
          3: instantiate(2:= nil); simpl; eapply sub_trans; [ eapply H2 | eapply sub_funty; eauto; eapply sub_zero].
          split_all; no_quanta.
          eelim subtype_from_quanta_funty; intros. 2: eapply H4. 
          2: instantiate(3:= true :: nil); simpl; eauto.
          split_all. no_quanta. inv_out H6. 
          trim_tac.
          eelim subtype_from_stemty3; intros.
          3: instantiate(3:= nil); simpl; eapply sub_trans; [ eapply sub_stem; eapply H10 | eapply sub_trans; [ eapply stem_quant_commute | eauto]]. 
          split_all; no_quanta.           
          unfold lift in *; simpl in *.           
          eelim subtype_from_quanta_funty; intros. 
          2: eapply H6.
          2: rewrite quanta_quant_to_quanta; eauto; instantiate(3:= 1); simpl; eauto. 
          split_all; no_quanta. inv_out H11. trim_tac. trim_tac.
          eapply sub_trans; eauto; eapply subtype_from_fork_of_leaf_to_fun.
          eapply sub_trans.
          eapply sub_fork. eapply subtype_lift. eapply sub_zero. eapply sub_trans. eapply fork_quant_commute. unfold lift; simpl.
          eapply sub_trans; eauto.
          do 2 sub_funty_tac; auto. 
      * caseEq (occurs x M); intros; simpl.  
        eapply derive_S2; [ eauto | eapply derive_K1;  eapply derive_occurs_false; eauto].
        eapply derive_K1; eapply derive_app; eauto; eapply derive_occurs_false; eauto.
    + caseEq (occurs x M); intros; simpl; [ 
          eapply derive_S2; eauto; eapply derive_K1; eapply derive_occurs_false; eauto |
          eapply derive_K1; eapply derive_app; eapply derive_occurs_false; eauto].   
    + caseEq (occurs x M|| occurs x (t @ t0)); intros; [ 
          eapply derive_S2; [  eapply IHd1; eauto | eapply IHd2; eauto] |
          eapply derive_K1; eapply derive_occurs_false; [ | | simpl; eauto]; [ eapply derive_app; eauto | eauto]].
Qed.

   
 
