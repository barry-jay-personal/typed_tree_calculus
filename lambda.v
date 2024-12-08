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


Set Default Proof Using "Type".

Open Scope string_scope.
 


(* 4.3: Variable Binding *)


Fixpoint substitute M x N :=
  match M with
  | Ref y => if eqb x y then N else Ref y
  | △ => △
  | M1 @ M2 => (substitute M1 x N) @ (substitute M2 x N)
end. 

Lemma substitute_app:
  forall M1 M2 x N, substitute (M1@ M2) x N = (substitute M1 x N) @ (substitute M2 x N). 
Proof. auto. Qed.

Lemma substitute_node:
  forall x N, substitute △ x N = △. 
Proof. auto. Qed.


     
Lemma substitute_preserves_t_red:
    forall M x N N', t_red N N' -> t_red (substitute M x N) (substitute M x N').
Proof.
 induction M; intros; simpl; zerotac;
 [ match goal with |- t_red (if ?b then _ else _) _  =>  caseEq b; intros; zerotac; auto end |
 apply preserves_app_t_red; auto].
Qed.


(* Bracket Abstraction *)

  
Fixpoint bracket x M := 
match M with 
| Ref y =>  if eqb x y then I else (K@ (Ref y))
| △ => K@ △ 
| App M1 M2 => S1 (bracket x M1) @ (bracket x M2)
end
.

Theorem bracket_beta: forall M x N, t_red ((bracket x M) @ N) (substitute M x N).
Proof.
  induction M; intros; unfold S1; simpl;
  [ match goal with |- t_red ((if ?b then _ else _) @ _) _ => case b; tree_red end | 
  tree_red | 
  unfold S1; eapply succ_red;  auto_t; apply preserves_app_t_red; trtac; auto]; [
  eapply IHM1 |
  eapply IHM2]. 
Qed.


(* star abstraction *)


Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y 
  | △ => false
  | M1@ M2 => (occurs x M1) || (occurs x M2)
  end.


Lemma substitute_occurs_false: forall M x N, occurs x M = false -> substitute M x N = M. 
Proof.
  induction M; simpl; intros x N e; split_all;
    [ rewrite e; auto | rewrite orb_false_iff in *; rewrite IHM1; try tauto; rewrite IHM2; tauto]. 
Qed.


Fixpoint star x M := (* no eta-contractions because argument types must be invariant *) 
  match M with
  | Ref y =>  if eqb x y then I else (K@ (Ref y))
  | △ => K@ △
  | App M1 M2 => if occurs x (M1 @ M2)
                 then S1 (star x M1) @ (star x M2)
                 else K@ (M1 @ M2)
  end. 

Notation "\" := star : tree_scope.


 
Theorem star_beta: forall M x N, t_red ((\x M) @ N) (substitute M x N).
Proof.
  induction M as [s | | M1 ? M2]; intros x N; simpl;  auto.
  caseEq (x=?s); intros; tree_red . 
  tree_red. 
  unfold S1; caseEq (occurs x M1 || occurs x M2); intros; trtac.  apply preserves_app_t_red; auto.
  rewrite orb_false_iff in *; split_all;  rewrite ! substitute_occurs_false; auto; zerotac. 
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
  eapply derive_S1. eauto.
  rewrite String.eqb_refl. eapply derive_subtype. eapply derive_I. sub_funty_tac. auto.
  rewrite String.eqb_refl. eapply derive_S1. eauto. eapply derive_subtype. eapply derive_I.
  sub_funty_tac. auto.  
  (* 3 *)
  caseEq (occurs x M); intros; simpl; rewrite H.
  eapply derive_S1. eauto.
  eapply derive_K1. eapply derive_occurs_false; eauto.
  eapply derive_K1. eapply derive_app; eauto; eapply derive_occurs_false; eauto.
  (* 2 *)
  caseEq (occurs x M); intros; simpl.
  eapply derive_S1. eauto. eapply derive_K1. 
  eapply derive_occurs_false; eauto.
  eapply derive_K1. eapply derive_app; eapply derive_occurs_false; eauto.   
  (* 1 *)
  caseEq (occurs x M|| occurs x (t @ t0)); intros. 
  eapply derive_S1.  eapply IHd1; eauto. eapply IHd2; eauto.
  eapply derive_K1.  eapply derive_occurs_false. 3: simpl; eauto.
  eapply derive_app; eauto. eauto.
Qed.

   
 
