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
Require Import terms types subtypes derive.


Set Default Proof Using "Type".

Open Scope string_scope.
 

Lemma derive_occurs_false:
  forall gamma M ty, derive gamma M ty ->
                     forall x uty gamma1, gamma = (x,uty):: gamma1 -> occurs x M = false ->
                                          derive gamma1 M ty.
Proof.
  intros gamma M ty d; induction d; intros; subst; simpl in *; auto_t.
  rewrite H2 in *; eapply derive_ref; eauto.
  rewrite orb_false_iff in *; split_all.
  eapply derive_app; [  eapply IHd1 | eapply IHd2]; eauto.
Qed.

Lemma derive_occurs_false2:
  forall gamma M ty, derive gamma M ty ->
                     forall x uty, occurs x M = false ->
                                          gamma <> nil -> derive ((x,uty):: gamma) M ty.
Proof.
  intros gamma M ty d; induction d; intros; subst; simpl in *; auto_t.
  replace (get x gamma) with (get x ((x0, uty) :: gamma)). eapply derive_ref. simpl. rewrite H1; eauto. 
  auto.
  simpl.   rewrite H1; auto.
  rewrite orb_false_iff in *; split_all.
  eapply derive_app; [  eapply IHd1 | eapply IHd2]; eauto.
Qed.


Proposition derive_ref_sub:
  forall gamma M ty,
    derive gamma M ty ->
    forall s uty gamma1, gamma = (s,uty):: gamma1 -> M = Ref s -> subtype uty ty. 
Proof.
  intros gamma M ty d; induction d; intros; subst; auto_t; try discriminate. 
  inv_out H2; simpl in *; rewrite String.eqb_refl in *. inv_out H. auto. 
Qed.


Theorem derive_star:
  forall M gamma x uty ty, derive ((x,uty) :: gamma) M ty -> derive gamma (star x M) (Funty uty ty).
Proof.
  cut(forall M gamma0 ty,
         derive gamma0 M ty ->
         forall x uty gamma, gamma0 = ((x,uty)::gamma) -> derive gamma (star x M) (Funty uty ty)).
  intros; eapply H; eauto.
  intros M gamma0 ty d; induction d; intros; subst; simpl in *.
  (* 4 *)
  caseEq (x0=?x)%string; intros; subst; rewrite H1 in *.   inv_out H. eapply derive_subtype. eapply derive_I. 
  sub_fun_tac; auto.
  all: try (eapply derive_app; [  eapply derive_K | auto_t]).
  (* 1 *)
  caseEq N; intros; subst.
  (* 3 *) 
  caseEq (x=? s)%string; intros. assert(x = s) by (eapply String.eqb_eq; eauto); subst. 
  assert(subtype uty u) by (eapply derive_ref_sub; eauto); split_all.
  (* 4 *)
  caseEq (occurs s M); intros; simpl.
  eapply derive_S2. eauto.
  rewrite String.eqb_refl. eapply derive_subtype. eapply derive_I. sub_funty_tac. auto.
  rewrite String.eqb_refl. eapply derive_S2. eauto. eapply derive_subtype. eapply derive_I.
  sub_funty_tac. auto.  
  (* 3 *)
  caseEq (occurs x M); intros; simpl; rewrite H.
  eapply derive_S2. eauto.
  eapply derive_K1. eapply derive_occurs_false; eauto.
  eapply derive_K1. eapply derive_app; eauto; eapply derive_occurs_false; eauto.
  (* 2 *)
  caseEq (occurs x M); intros; simpl.
  eapply derive_S2. eauto. eapply derive_K1. 
  eapply derive_occurs_false; eauto.
  eapply derive_K1. eapply derive_app; eapply derive_occurs_false; eauto.   
  (* 1 *)
  caseEq (occurs x M|| occurs x (t @ t0)); intros. 
  eapply derive_S2.  eapply IHd1; eauto. eapply IHd2; eauto.
  eapply derive_K1.  eapply derive_occurs_false. 3: simpl; eauto.
  eapply derive_app; eauto. eauto.
Qed.

   
 
