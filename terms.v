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
(*              Tree Calculus with five reduction rules               *)
(*                        or                                          *)
(*                  Triage Calculus                                   *) 
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List Nat Datatypes String.

Set Default Proof Using "Type".

(* Module TreeModule.*) 

Open Scope string_scope.
Declare Scope tree_scope.
Global Open Scope tree_scope.


(* Generalities *) 

Ltac refold r := unfold r; fold r.
Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f. 
Ltac auto_t := eauto with TreeHintDb. 
Ltac eapply2 H := eapply H; auto_t; try lia.
Ltac split_all := intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); subst; try contradiction
end; try congruence.

Ltac inv_out H := inversion H; clear H; subst.

Ltac disjunction_tac:=
  match goal with
  | H : _ \/ _ |- _ => inv_out H; disjunction_tac
  | _ => try lia
  end.


Inductive Tree:  Set :=
  | Ref : string -> Tree  (* variables are indexed by strings *) 
  | Node : Tree   
  | App : Tree -> Tree -> Tree   
.

Global Hint Constructors Tree : TreeHintDb.

Notation "△" := Node : tree_scope.
Notation "x @ y" := (App x y) (at level 65, left associativity) : tree_scope.


Definition K := △ @ △. 
Definition S1 x := △ @ (△@x).
Definition Sop := S1 (K @ Node) @ Node. 
Definition I := S1 K @ Node.
Definition KI := K@I.

Ltac unfold_op := unfold KI, I, K, S1.


(* Programs *)

Inductive program : Tree -> Prop :=
| pr_leaf : program △
| pr_stem : forall M, program M -> program (△ @ M)
| pr_fork : forall M N, program M -> program N -> program (△ @ M@ N)
.

Ltac program_tac := cbv; repeat (apply pr_stem || apply pr_fork || apply pr_leaf); auto.


(* Tree-reduction *)

(* 
This differs from the reduction of untyped tree calculus, using rules suggested by Johannes Bader.
We have worked together on optimising many constructions below. 

Node Node = K 
Node (Node x) = S x 
(Node (Node w x) y = triage {w,x,y} 
 *) 

Inductive t_red1 : Tree -> Tree -> Prop :=
| k_red : forall y z, t_red1 (△ @ △ @ y @ z) y 
| s_red: forall (x y z : Tree), t_red1 (△ @ (△ @ x) @ y @ z) (x @ z @ (y @ z))
| leaf_red: forall (w x y : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ Node) w
| stem_red: forall (w x y z : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ (Node @ z)) (x @ z)
| fork_red: forall (w x y z1 z2 : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ (Node @ z1 @ z2)) (y @ z1 @ z2)
| appl_red : forall M M' N, t_red1 M M' -> t_red1 (M@N) (M'@N)  
| appr_red : forall M N N', t_red1 N N' -> t_red1 (M@N) (M@N')  
.
Global Hint Constructors t_red1 : TreeHintDb. 

(* Multiple reduction steps *) 

Inductive multi_step : (Tree -> Tree -> Prop) -> Tree -> Tree -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: Tree-> Tree -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.
Global Hint Constructors multi_step: TreeHintDb.  



Definition t_red := multi_step t_red1.


Ltac tree_red := 
  intros; cbv; repeat (eapply succ_red ; [ auto 10 with *; fail|]); try eapply zero_red.

(* The reduction rules for K and S are built in: here is the rule for I *) 

Lemma i_red: forall x, t_red (I @ x) x. Proof. tree_red. Qed.




Definition transitive red := forall (M N P: Tree), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; split_all; eapply2 succ_red. Qed. 

Definition preserves_appl (red : Tree -> Tree -> Prop) := 
forall M N M', red M M' -> red (M@N) (M'@ N).

Definition preserves_appr (red : Tree -> Tree -> Prop) := 
forall M N N', red N N' -> red (M@N) (M@N').

Definition preserves_app (red : Tree -> Tree -> Prop) := 
forall M M', red M M' -> forall N N', red N N' -> red (M@N) (M'@N').

Lemma preserves_appl_multi_step : 
forall (red: Tree -> Tree -> Prop), preserves_appl red -> preserves_appl (multi_step red). 
Proof. red; intros red pa M N M' r ; induction r; auto_t; eapply2 succ_red. Qed.

Lemma preserves_appr_multi_step : 
forall (red: Tree -> Tree -> Prop), preserves_appr red -> preserves_appr (multi_step red). 
Proof. red; intros red pa M N M' r ; induction r; auto_t; eapply2 succ_red. Qed.

Lemma preserves_app_multi_step : 
  forall (red: Tree -> Tree -> Prop),
    preserves_appl red -> preserves_appr red -> 
    preserves_app (multi_step red). 
Proof.
  red; intros; apply transitive_red with (M'@N); 
    [ apply preserves_appl_multi_step |
      apply preserves_appr_multi_step]
    ; auto.
Qed.


Lemma preserves_appl_t_red : preserves_appl t_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_t_red : preserves_appr t_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_t_red : preserves_app t_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.



Ltac zerotac := try apply zero_red; auto.
Ltac succtac :=
  repeat (eapply transitive_red;
  [ eapply succ_red ; auto_t; 
    match goal with
    | |- multi_step t_red1 _ _ => idtac
    | _ => fail (*gone too far ! *)
    end
  | ])
.

Ltac trtac := unfold_op; unfold t_red; succtac; 
  match goal with
  | |- multi_step t_red1 △ _ => zerotac
  | |- multi_step t_red1 (△ @ _ @ _ @ _) _ =>
    eapply transitive_red;
    [ eapply preserves_app_t_red ;
      [ eapply preserves_app_t_red ;
        [ eapply preserves_app_t_red ; [| trtac ] (* reduce the argument of △ *) 
        | ]
      | ]
     |] ;
    zerotac; (* put the "redex" back together *) 
    match goal with
    | |- multi_step t_red1 (△ @ ?arg @ _ @ _) _ =>
      match arg with
      | △  => trtac (* made progress so recurse *) 
      | △ @ _  => trtac (* made progress so recurse *) 
      | △ @ _ @ _ => trtac (* made progress so recurse *) 
      | _ => idtac (* no progress so stop *)
      end
    | _ => idtac (* for safety ? *) 
    end 
  | |- multi_step t_red1 (_ @ _) _ => (* not a ternary tree *) 
    eapply transitive_red; [ eapply preserves_app_t_red ; trtac |] ; (* so reduce the function *)
    match goal with
    | |- multi_step t_red1 (△ @ ?arg @ _ @ _) _ =>
      match arg with
      | △  => trtac (* made progress so recurse *) 
      | △ @ _  => trtac (* made progress so recurse *) 
      | △ @ _ @ _ => trtac (* made progress so recurse *) 
      | _ => idtac (* no progress so stop *)
      end
    | _ => idtac
    end
  | _ => idtac (* the head is not △ *) 
  end;
  zerotac; succtac; zerotac. 
                                        
 



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





Ltac inv1 prop :=
match goal with
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| H: prop (_ @ _) |- _ => inversion H; clear H; inv1 prop
| H: prop △ |- _ => inversion H; clear H; inv1 prop
| _ => auto_t
 end.


(* 4.2: Combinations versus Terms *)

Inductive combination : Tree -> Prop :=
| is_Node : combination △
| is_App : forall M N, combination M -> combination N -> combination (M@ N)
.
Global Hint Constructors combination: TreeHintDb.

Ltac combination_tac := repeat (apply is_App || apply is_Node); auto. 


(* Normal Forms *)

Inductive active: Tree -> Prop :=
| active_ref: forall x, active (Ref x)
| active_app: forall M N, active M -> active (M@N)
.

Inductive normal : Tree -> Prop :=
| nf_ref: forall x, normal (Ref x)
| nf_active: forall M N, active M -> normal M -> normal N -> normal (M@N)
| nf_leaf : normal △
| nf_stem : forall M, normal M -> normal (△ @ M)
| nf_fork : forall M N, normal M -> normal N -> normal (△ @ M@ N)
.


Ltac normal_tac := cbv; repeat (apply nf_stem || apply nf_fork || apply nf_leaf || apply nf_ref); auto.


(* star abstraction *)


Ltac aptac := eapply transitive_red; [ eapply preserves_app_t_red |].

Ltac htac r :=
  ((eapply transitive_red; [ eapply r |]) ||
     (aptac; [ htac r; trtac | trtac | trtac ]) ||
     (aptac; [ trtac | htac r; trtac | trtac ]))
   ; trtac.


Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y 
  | △ => false
  | M1@ M2 => (occurs x M1) || (occurs x M2)
  end.

Lemma occurs_combination: forall M x,  combination M -> occurs x M = false.
Proof.
  induction M; simpl; split_all; inv1 combination; subst; auto; rewrite IHM1; auto; rewrite IHM2; auto.
Qed. 

Lemma occurs_ref: forall x y, occurs x (Ref y) = (String.eqb x y).
Proof. auto. Qed. 

Lemma occurs_node: forall x, occurs x △ = false. 
Proof. auto. Qed. 

Lemma occurs_app: forall x M N, occurs x (M@ N) = occurs x M || occurs x N.
Proof. auto. Qed. 

Lemma substitute_occurs_false: forall M x N, occurs x M = false -> substitute M x N = M. 
Proof.
  induction M; simpl; intros x N e; split_all;
    [ rewrite e; auto | rewrite orb_false_iff in *; rewrite IHM1; try tauto; rewrite IHM2; tauto]. 
Qed.


Fixpoint star x M := (* no eta-contractions because argument types must be invariant *) 
  match M with
  | Ref y =>  if eqb x y then I else (K@ Ref y)
  | △ => K@ △
  | App M1 M2 =>
      match M2 with
      | Ref y => if eqb x y
                 then if occurs x M1
                      then  S1 (star x M1) @ I
                      else M1
                 else if occurs x M1
                      then  S1 (star x M1) @ (K @ Ref y)
                      else K @ (M1 @ M2)
      | _ => if occurs x (M1 @ M2)
                 then S1 (star x M1) @ (star x M2)
                 else K@ (M1 @ M2)
      end
  end.


Notation "\" := star : tree_scope.



Theorem star_beta: forall M x N, t_red ((\x M) @ N) (substitute M x N).
Proof.
  induction M as [s | | M1 ? M2]; intros x N; simpl;  auto; [
      caseEq (x=?s); intros; tree_red |
      tree_red | assert(t_red (\ x M2 @ N) (substitute M2 x N)) by auto; clear IHM2];
    unfold S1; caseEq (occurs x M1 || occurs x M2); intros; trtac; caseEq M2; intros; subst; simpl in *.
    - rewrite orb_true_iff in *; disjunction_tac; rewrite H1 in *; simpl.
      + caseEq (x=?s); intros; trtac; htac IHM1. 
      + caseEq (occurs x M1); intros; simpl; trtac; [
          htac IHM1 |
          rewrite ! substitute_occurs_false; auto; zerotac]. 
    - rewrite orb_false_r in *; trtac; htac IHM1.
    - trtac; htac IHM1; eapply preserves_appr_t_red; caseEq t0; intros; subst; simpl in *.
      + caseEq (x=? s); intro aux; rewrite aux in *; simpl in *; auto.
      + rewrite orb_false_r in *; caseEq (occurs x t); intros aux; rewrite aux in *; simpl in *; auto.
      + caseEq (occurs x t || (occurs x t1 || occurs x t2)); intro aux; rewrite aux in *; simpl in *; htac H.
    - caseEq (x=?s); intro aux; rewrite aux in *; simpl.
      + caseEq (occurs x M1); intros aux2; rewrite aux2 in *; simpl in *; trtac; [
            htac IHM1 |
            rewrite substitute_occurs_false; auto; zerotac].
      + rewrite orb_false_r in *; rewrite H0; trtac; rewrite substitute_occurs_false; auto; zerotac. 
    - trtac; rewrite orb_false_r in *; rewrite substitute_occurs_false; auto; zerotac. 
    - trtac; rewrite ! orb_false_iff in *; split_all; rewrite ! substitute_occurs_false; auto; zerotac. 
Qed. 


Lemma star_combination: forall M x, combination M -> \x M = K@ M. 
Proof.
  induction M as [ | | M1 M2 M3]; intros x c; simpl;
    try (split_all; inv1 combination; subst; auto; fail);
    inversion c as [ | ? ? c1 c3]; inversion c3; subst; split_all; rewrite ! occurs_combination; split_all.  
Qed.


Lemma star_leaf: forall x, \x △ = K@ △.
Proof. auto. Qed.


Lemma star_id: forall x, \x (Ref x) = I.
Proof. intro; unfold star, occurs; rewrite eqb_refl; auto. Qed.

Lemma star_occurs_false: forall M x, occurs x M = false -> \x M = K@ M. 
Proof.
  induction M; simpl; intros x occ; rewrite ? occ; auto; rewrite orb_false_iff in *; split_all;
    caseEq M2; intros; subst; simpl in *; auto; rewrite H0; simpl; rewrite H; auto.
Qed.


Lemma star_occurs_true:
  forall M1 M2 x, occurs x (M1@ M2) = true -> M2 <> Ref x -> \x (M1@ M2) = S1 (\x M1) @ (star x M2).
Proof.
  intros M1 M2 x occ; unfold star at 1; fold star; rewrite occ; auto; simpl in *; disjunction_tac; 
    caseEq M2; intros; subst; simpl in *; auto;  caseEq (x=? s); intros aux; rewrite aux in *.
  - assert(x = s) by (eapply eqb_eq; eauto); subst; congruence.
  - rewrite orb_false_r in *; rewrite occ; auto.
Qed.

Lemma star_eta: forall M x, occurs x M = false -> \x (M @ Ref x) = M.
Proof. intros M x H; simpl; rewrite eqb_refl; rewrite H; auto.  Qed. 


Lemma occurs_substitute_true:
  forall M x y N, x<> y -> occurs x M = true -> occurs x (substitute M y N) = true.
Proof.     
  induction M; intros x y N d occ; simpl in *; auto; 
    [
      match goal with H : (String.eqb x  ?s) = true |- _ =>
                  assert(x=s) by (apply eqb_eq; auto);
                    assert(d2: eqb y s = false) by (apply eqb_neq;  split_all);
                    rewrite d2; simpl; auto end
  |
  rewrite orb_true_iff in occ; inversion occ; 
  [ rewrite IHM1; auto | rewrite IHM2; auto; apply orb_true_r]
    ].
Qed.


Lemma star_occurs_false_app
     : forall (M N : Tree) (x : string), occurs x (M@ N) = false -> \ x (M@N) = K @ (M@N). 
Proof. intros; eapply star_occurs_false; cbv; auto. Qed. 

Ltac occurstac :=
  unfold_op; unfold occurs; fold occurs; rewrite ? orb_true_r; cbv; auto 1000 with *; fail. 



Ltac startac_true x := rewrite (star_occurs_true _ _ x); [| occurstac | discriminate ]. 
Ltac startac_false x :=  rewrite (star_occurs_false _ x); [ | occurstac].
Ltac startac x := unfold S1; repeat (startac_false x || startac_true x || (rewrite star_eta; [ | occurstac]) || rewrite star_id ).

Ltac starstac1 xs :=
  match xs with
  | nil => trtac
  | ?x :: ?xs1 => startac x; starstac1 xs1
  end.
Ltac starstac xs := repeat (starstac1 xs).

   
Ltac startac2 :=
rewrite star_id
  || (rewrite star_occurs_true; [ | rewrite ? String.eqb_refl; cbv; auto; fail ])
  || (rewrite star_occurs_false;  [ | cbv; auto; fail ])
  || (rewrite star_occurs_false_app;  [ | cbv; auto; fail ])
  ; trtac. 



(*** General Recursion *)

(* Johannes Bader and I have optimised this by:
replacing omega2 omega2 by self_apply omega2;
replacing wait2 by wait;
optimising wait;
introducing wait1;
introducing self_apply_k

Such optimisation will require adjustment to the subtyping rule sub_recursion. 
 *)




(** waiting *)

Definition wait M N := S1 (S1 (K @ (S1 M)) @ K) @  (K @ N).

Theorem wait_red: forall M N x, t_red (wait M N @ x) (M @ N @ x). Proof. tree_red.  Qed. 

Definition wait1 M := S1 (S1 (K @ (S1 M)) @ K) .


(*** Self-application and fixfunctions *)



Definition self_apply_k := Eval cbv in \"x" (Ref "x" @ (K @ (Ref "x"))).


Definition Z f := wait self_apply_k (S1 (K @ f) @ (wait1 self_apply_k)).

Theorem Z_red: forall f x, t_red (Z f @ x) (f @ (Z f) @ x).
Proof.
  intros; unfold Z at 1; unfold self_apply_k at 1; htac wait_red;
    eapply preserves_appl_t_red; eapply preserves_appr_t_red;
    unfold wait at 1; refold star; simpl; trtac.
Qed. 


Theorem Z_program: forall f, program f -> program (Z f). 
Proof. intros; program_tac. Qed.


Definition swap f := S1 (K @ (S1 f)) @ K.

Theorem swap_red: forall f x y, t_red (swap f @ x @ y) (f @ y @ x). Proof. tree_red. Qed. 


Definition Yop2 f := Z (swap f).

Theorem Y2_red: forall f, (program f -> program (Yop2 f)) /\ (forall x, t_red (Yop2 f @ x) (f @ x @ (Yop2 f))).
Proof. intros; split; intro; [ program_tac | htac Z_red; htac swap_red]. Qed. 

 Fixpoint term_size t :=
  match t with
  | App t1 t2 => term_size t1 + term_size t2
  | _ => 1
  end.

 Lemma term_size_Z: term_size (Z Node) = 45.
 Proof. cbv; auto. Qed. 

 Lemma term_size_Y2: term_size (Yop2 Node) = 53.
 Proof. cbv; auto. Qed. 

 

Definition omega := \"w" (\"f" (Ref "f" @ (Ref "w" @ Ref "w" @ Ref "f"))).

Definition Yop := omega @ omega.

Theorem Yop_red: forall f, t_red (Yop @ f) (f @ (Yop @ f)).
Proof. intros; unfold Yop; unfold omega at 1; unfold star; simpl; unfold S1, I; trtac. Qed. 

(* 
Definition wait2 M N x :=  S1 (S1 (S1 (K @ M) @ (K @ N)) @ (K @ x)) @ I.


Theorem wait2_red: forall M N x y, t_red (wait2 M N x @ y) (M @ N @ x @ y).
Proof. tree_red. Qed. 

       
   
Definition omega2 := \"w" (\"f" (Ref "f" @ (wait2 (Ref "w") (Ref "w") (Ref "f")))).

Lemma omega2_red: forall w f, t_red (omega2@ w @ f) (f @ (wait2 w w f)).
Proof. intros; unfold omega2; unfold wait2 at 1; startac "f"; startac "w"; trtac. Qed. 

Definition omega21 := K @ (△ @ (△ @ I)). 
Definition omega22 :=  \ "w" (\ "f" (wait2 (Ref "w") (Ref "w") (Ref "f"))).

Lemma omega2_parts: omega2 = S1 omega21 @ omega22. 
Proof. cbv; auto. Qed. 


Definition Z f := wait2 omega2 omega2 f. 

Theorem Z_red: forall f x, t_red (Z f @ x) (f @ (Z f) @ x).
Proof. intros; unfold Z at 1; htac wait2_red; htac omega2_red. Qed.



Theorem Z_program: forall f, program f -> program (Z f). 
Proof. intros; program_tac. Qed.


   
Definition omega2__alt := \"w" (\"f" (Ref "f" @ (wait2 self_apply (Ref "w") (Ref "f")))).



Definition Z__alt f := wait2 self_apply omega2__alt f. 

Theorem Z__alt_red: forall f x, t_red (Z__alt f @ x) (f @ (Z__alt f) @ x).
Proof.
  intros; unfold Z__alt. unfold wait2 at 1. trtac. unfold self_apply at 1. trtac.
  unfold omega2__alt at 1.
  startac "f"; startac "w". trtac. do 2 (eapply preserves_app_t_red; trtac).
  tree_red. 
Qed.



Definition Yop2 f := Z (swap f).

*) 

(* generic equality *)


Definition triage f0 f1 f2 := Node @ (Node @ f0 @ f1) @ f2.


Definition equal :=
  Yop2
    (triage
       (\"e" (triage K (K @ KI) (K @ (K @ KI))))
       (\"x" (\"e" (triage KI (Ref "e" @ Ref "x") (K @ (K @ KI)))))
       (\"x1"
         (\"x2"
           (\"e"
             (triage KI (K @ KI)
                     (\"y1" (\"y2" (Ref "e" @ Ref "x1" @ Ref "y1" @ (Ref "e" @ Ref "x2" @ Ref "y2") @ KI)))
    ))))).

Lemma equal_leaf: t_red (equal @ Node @ Node) K.
Proof. htac Y2_red;  tree_red. Qed.

Lemma equal_stem: forall x y, t_red (equal @ (Node @ x) @ (Node @ y)) (equal @ x @ y).
Proof. intros; htac Y2_red; unfold triage; trtac. startac "e"; startac "x"; trtac. Qed.

Lemma equal_fork:
  forall x1 x2 y1 y2, t_red (equal @ (Node @ x1 @ x2) @ (Node @ y1 @ y2))
                            (equal @ x1 @ y1 @ (equal @ x2 @ y2) @ KI).
Proof. intros; htac Y2_red; unfold triage; trtac; startac "y2"; startac "y1"; startac "e"; startac "x2"; startac "x1"; trtac. Qed.

Theorem equal_programs: forall M, program M -> t_red (equal @ M @ M) K.
Proof.
  intros M pr; induction pr; intros. 
  - htac equal_leaf.
  - htac equal_stem. 
  - htac equal_fork; htac IHpr1. 
Qed.


Lemma equal_leaf_stem: forall y,  t_red (equal @ Node @ (Node @ y)) KI.
Proof. intros; htac Y2_red; unfold triage; trtac; startac "e"; trtac. Qed.

Lemma equal_leaf_fork: forall y1 y2,  t_red (equal @ Node @ (Node @ y1 @ y2)) KI.
Proof. intros; htac Y2_red; unfold triage; startac "e"; trtac. Qed.

Lemma equal_stem_leaf: forall x,  t_red (equal @ (Node @ x) @ Node) KI.
Proof. intros; htac Y2_red; unfold triage; startac "e"; startac "x"; trtac. Qed.

Lemma equal_stem_fork: forall x y1 y2,  t_red (equal @ (Node @ x) @ (Node @ y1 @ y2)) KI.
Proof. intros; htac Y2_red; unfold triage; startac "e"; startac "x"; trtac. Qed.

Lemma equal_fork_leaf: forall x1 x2,  t_red (equal @ (Node @ x1 @ x2) @ Node) KI.
Proof. intros; htac Y2_red; unfold triage; startac "e"; startac "x2"; startac "x1"; trtac. Qed.

Lemma equal_fork_stem: forall x1 x2 y,  t_red (equal @ (Node @ x1 @ x2) @ (Node @ y)) KI.
Proof. intros; htac Y2_red; unfold triage; startac "e"; startac "x2"; startac "x1"; trtac. Qed.



Theorem unequal_programs: forall M, program M -> forall N, program N -> M <> N -> t_red (equal@ M @ N) KI.
Proof.
  intros M prM; induction prM; intros; inv_out H; try congruence.
  eapply equal_leaf_stem. 
  eapply equal_leaf_fork.
  eapply equal_stem_leaf.   
  eapply transitive_red. eapply equal_stem. eapply IHprM; eauto.  intro; subst; congruence. 
  eapply equal_stem_fork.
  eapply equal_fork_leaf.
  eapply equal_fork_stem.
  eapply transitive_red. eapply equal_fork.
  assert(M = M0 \/ M <> M0) by (repeat decide equality). disjunction_tac. 
  aptac. aptac. eapply equal_programs; eauto. eapply IHprM2; eauto. intro; subst; congruence. 
  trtac. trtac. trtac.
  aptac. aptac. eapply IHprM1; eauto. trtac. trtac. trtac. trtac. 
  Qed. 



Definition tt := K.
Definition ff := KI.


Lemma tt_red: forall x y, t_red (tt @ x @ y) x. Proof. tree_red. Qed. 
Lemma ff_red: forall x y, t_red (ff @ x @ y) y. Proof. tree_red. Qed. 


Theorem equality_of_programs:
  forall M, program M -> t_red (equal @ M @ M) tt /\ forall N, program N -> M <> N -> t_red (equal@ M @ N) ff.
Proof.  intros; split; [ eapply equal_programs | eapply unequal_programs]; auto.  Qed. 

(*** Pairing and projections *)



Definition pairL x y := S1 (S1 I @ (K @ x)) @ (K @ y).
Definition fstL := S1 I @ (K@K). 
Definition sndL := S1 I @ (K@KI). 

Theorem fstL_red: forall x y, t_red (fstL @ (pairL x y)) x. Proof. tree_red. Qed. 
Theorem sndL_red: forall x y, t_red (sndL @ (pairL x y)) y. Proof. tree_red. Qed. 


(*** Function composition *)

(* given f_i : Nat ^m -> Nat and g : Nat^n -> N, define g (f_i) : Nat^m -> Nat by 
g(f_i) (x_j) = g (f_i(x_j)) 
 *)

Lemma fold_left_app_preserves_red:
  forall xs f1 f2, t_red f1 f2 -> t_red (fold_left App xs f1) (fold_left App xs f2).
Proof.  induction xs; intros; simpl; eauto; eapply IHxs; eapply preserves_appl_t_red; auto. Qed. 


Fixpoint Kn n := (* Kn n g xs = g if length xs = n *) 
  match n with
  | 0 => I
  | S n1 => \"x" (K@ (Kn n1 @ Ref "x"))
  end. 

Fixpoint compose1 n := (* compose1 g f xs = g xs (f xs)  if length xs = n *) 
  match n with
  | 0 => I
  | S n1 => \"g" (\"f" (\"x" (compose1 n1 @ (Ref "g" @ Ref "x") @ (Ref "f" @ Ref "x"))))
  end.

Fixpoint compose0 m n := (* compose0 m n g fs xs = g xs (map fs xs) if length fs = m and length xs = n *) 
  match m with
  | 0 => I 
  | S m1 => \"g" (\"f" (compose0 m1 n @ (compose1 n @ Ref "g" @ Ref "f")))
  end.

Definition compose m n := S1 (K @ compose0 m n) @ (Kn n) . (* \"x" (compose0 m n @ (Kn n @ Ref "x")).  *) 

Lemma Kn_closed: forall n x, occurs x (Kn n) = false.
Proof.  induction n; intros; simpl; auto; rewrite  IHn; simpl; auto. Qed. 

  
Lemma Kn_red: forall xs g, t_red (fold_left App xs (Kn (List.length xs) @ g)) g. 
Proof.
  induction xs; intros; simpl; auto.
  - repeat trtac; rewrite Kn_closed.
  - simpl;   eapply transitive_red; [ eapply fold_left_app_preserves_red; trtac |];
      rewrite star_occurs_false; simpl; rewrite ! Kn_closed; auto; simpl;
      eapply transitive_red; [ eapply fold_left_app_preserves_red; trtac | eapply IHxs]. 
Qed.


Lemma compose1_closed: forall n x, occurs x (compose1 n) = false. 
Proof.
  induction n; intros; simpl; auto; rewrite ! orb_true_r;
    rewrite (star_occurs_false _ "x"); eauto;
      unfold S1, star; fold star; repeat (simpl; rewrite ! IHn); auto.
Qed.
       

Proposition compose1_red:
  forall xs g f,
    t_red (fold_left App xs (compose1 (List.length xs) @ g @ f)) ((fold_left App xs g) @ (fold_left App xs f)).
Proof.
  induction xs; intros; simpl; auto; [ trtac |];
    rewrite compose1_closed; refold orb; eapply transitive_red.
  -  eapply fold_left_app_preserves_red;
       rewrite (star_occurs_false _ "x"); eauto; [ | eapply compose1_closed];
       unfold S1; startac "f"; rewrite star_eta; [ | simpl; rewrite compose1_closed; auto]; trtac.
  - startac "g"; trtac;  rewrite star_eta; [ | simpl; rewrite compose1_closed; auto];
       eapply transitive_red; [ eapply fold_left_app_preserves_red; trtac | eapply IHxs].
Qed. 


 Lemma compose0_closed: forall m n x, occurs x (compose0 m n) = false. 
Proof.
  induction m; intros; simpl; auto; rewrite ! orb_true_r;
    rewrite ! compose1_closed; simpl;
    rewrite star_occurs_false; eauto; simpl;
    rewrite IHm; simpl;
    rewrite star_occurs_false; simpl;
    rewrite compose1_closed; auto; simpl;
    rewrite IHm; simpl; 
    rewrite compose1_closed; auto. 
Qed.

Proposition compose0_red:
  forall fs xs g,
    t_red (fold_left App xs (fold_left App fs (compose0 (List.length fs) (List.length xs) @ g)))
           (fold_left App (map (fun f => (fold_left App xs f)) fs) (fold_left App xs g)).
Proof.
  induction fs; intros; simpl; auto.
  - repeat trtac;  eapply fold_left_app_preserves_red; repeat trtac. 
  - rewrite ! compose0_closed; rewrite ! compose1_closed; unfold orb;
      eapply transitive_red; [
        |
          eapply transitive_red; [ eapply IHfs | eapply fold_left_app_preserves_red;  eapply compose1_red]];
      eapply fold_left_app_preserves_red;
      eapply fold_left_app_preserves_red;
      rewrite (star_occurs_false _ "f"); [ | eapply compose0_closed];
      unfold S1; rewrite star_occurs_true; [ | simpl; rewrite ! orb_true_r; auto | discriminate];
      rewrite star_occurs_false; [ | simpl; eapply compose0_closed];
      rewrite star_eta; [ | eapply compose1_closed];
      trtac.
 Qed.

Theorem compose_red:
  forall fs xs g,
    t_red (fold_left App xs (fold_left App fs (compose (List.length fs) (List.length xs) @ g))) 
      (fold_left App (map (fun f => (fold_left App xs f)) fs) g).
Proof.
  intros; unfold compose; eapply transitive_red; [
      do 2 eapply fold_left_app_preserves_red; trtac |
      eapply transitive_red; [
        eapply compose0_red |   
        eapply fold_left_app_preserves_red; eapply Kn_red]]. 
Qed.


(*** Zero, successor and numerals as iterators *) 

Definition zero := KI.


Definition succ1 := S1 (S1 (K @ Node) @ (S1 (K @ Node) @ K)).


Theorem succ1_red: forall n f x, t_red (succ1 @ n @ f @ x) (f @ (n @ f @ x)).
Proof.  tree_red. Qed. 
  
Definition num k := iter k (fun x => succ1 @ x) zero.

 
Lemma num_iterates: forall m f x, t_red (num m @ f @ x) (iter m (App f) x).
Proof.
  induction m; intros; unfold num; fold num; simpl; eauto; repeat trtac; [ tree_red | 
  unfold succ1 at 1; trtac; eapply preserves_appr_t_red; eapply IHm].
Qed.


Lemma num_succ_red: forall k, t_red (num (S k)) (succ1 @ (num k)).
Proof. tree_red. Qed.  

  
(*** The zero test and conditionals *)


Definition isZero := \"n" (Ref "n" @ (K @ ff) @ tt). 

Theorem isZero_zero: t_red (isZero @ zero) tt.
Proof.  tree_red. Qed.

Theorem isZero_succ: forall n, t_red (isZero @ (succ1 @ n)) ff.
Proof.  tree_red. Qed.

Definition cond := I. 

Theorem cond_false : forall x y, t_red (cond @ ff @ x @ y) y.
Proof. tree_red. Qed. 

Theorem cond_true : forall x y, t_red (cond @ tt @ x @ y) x.
Proof. tree_red. Qed. 


(*** The predecessor function  - underpinning primitive recursion *) 
  
Definition PZero := pairL zero zero.  (*   \ (Var 0 @ (num 0) @ (num 0)). *)  
Definition PSucc := \"p" (pairL (sndL @ Ref "p") (succ1 @ (sndL @ Ref "p"))). 
Definition predN := \"n" (fstL @ (Ref "n" @ PSucc @ PZero)).

Lemma PSucc_red: forall m n,  t_red (PSucc @ (pairL m n)) (pairL n (succ1 @ n)).
Proof. tree_red. Qed.


Lemma pred_aux:  forall k, t_red (iter k (App PSucc) PZero) (pairL (num (Nat.pred k)) (num k)).
Proof. induction k; intros; repeat eexists; simpl; [ eapply zero_red | htac IHk; htac PSucc_red]. Qed.

 
Theorem pred_red: forall k,  t_red (predN @ (num k)) (num (pred k)). 
Proof.
  intros; unfold predN.  startac "n". trtac. unfold fstL; trtac;
    htac num_iterates; htac pred_aux; tree_red.  
Qed.



(*** Primitive Recursion *)



Definition primrec0_abs :=
  \"n"
          (\"x"
            (isZero @ (Ref "n")
                    @ Ref "g"
                    @ (Ref "h" @ (predN @ Ref "n") @ (Ref "x" @ (predN @ Ref "n")))                  
          )).

Lemma primrec0_val:
  primrec0_abs = S1 (S1 (K @ △) @ (S1 (K @ △) @ (S1 (K @ K) @ (S1 isZero @ (K @ Ref "g"))))) @
  (S1 (S1 (K @ △) @ (S1 (K @ △) @ (S1 (K @ K) @ (S1 (K @ Ref "h") @ predN)))) @
   (S1 (K @ (△ @ (△ @ I))) @ (S1 (K @ K) @ predN))). 
Proof.  cbv; auto.  Qed.


Definition primrec0 g h :=
    Yop2 ( S1 (S1 (K @ △) @ (S1 (K @ △) @ (S1 (K @ K) @ (S1 isZero @ (K @ g))))) @
  (S1 (S1 (K @ △) @ (S1 (K @ △) @ (S1 (K @ K) @ (S1 (K @ h) @ predN)))) @
   (S1 (K @ (△ @ (△ @ I))) @ (S1 (K @ K) @ predN)))). 


Lemma primrec0_red_zero :
  forall g h, t_red (primrec0 g h @ zero) g.
Proof.  intros; unfold primrec0;  startac "y"; startac "x"; htac Y2_red; htac isZero_zero. Qed. 


Lemma primrec0_red_succ :
  forall k g h, t_red (primrec0 g h @ (num (S k))) (h @ (num k) @ (primrec0 g h @ (num k))).
Proof. intros; unfold primrec0; startac "y"; startac "x"; htac Y2_red;  htac isZero_succ; htac ff_red; repeat htac pred_red. Qed.
  

Definition primrec g h xs := primrec0 (fold_left App xs g) (fold_left App xs h).


Theorem primrec_red_zero:
  forall xs g h, t_red (primrec g h xs @ zero) (fold_left App xs g). 
Proof.  intros; eapply primrec0_red_zero. Qed. 


Theorem primrec_red_succ:
  forall xs g h k,
    t_red (primrec g h xs @ (num (S k))) (fold_left App xs h @ (num k) @ (primrec g h xs @ (num k))). 
Proof.  intros; simpl; auto; eapply primrec0_red_succ. Qed. 


Definition prim_plus0 n := primrec I (K @ (K @ (\"z" (succ1 @ (Ref "z"))))) (n::nil). 

Definition prim_plus := \"n" (prim_plus0 (Ref "n")). 

Theorem prim_plus_zero: forall n, t_red (prim_plus @ n @ zero) n. 
Proof.
  intros; htac star_beta;
  replace (substitute (prim_plus0 (Ref "n")) "n" n) with (prim_plus0 n) by (cbv; auto);
  htac primrec_red_zero; tree_red.
Qed.

Theorem prim_plus0_succ1: forall m n, t_red (prim_plus0 m @ (num (S n))) (succ1 @ (prim_plus0 m @ (num n))). 
Proof.  intros; htac primrec_red_succ; simpl; trtac. Qed. 
  


  
(*** Minimisation *)


Definition minrec_abs := \"r1" (\"r0" (Ref "f" @ Ref "r1" @ Ref "r1" @ (Ref "r0" @ (succ1 @ (Ref "r1"))))).

Lemma min_rec_abs_val :
  minrec_abs =   △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ △))) @
      (△ @ (△ @ Ref "f") @ (△ @ (△ @ (△ @ △)) @ △)))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @
   (△ @ (△ @ (△ @ △ @ (△ @ △))) @
    (△ @ (△ @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ △))))))).
Proof.  cbv; auto. Qed. 


  

Definition minrec0 f := Yop2   (  △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ △))) @
      (△ @ (△ @ f) @ (△ @ (△ @ (△ @ △)) @ △)))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @
   (△ @ (△ @ (△ @ △ @ (△ @ △))) @
    (△ @ (△ @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ △)))))))). 

  
Lemma minrec0_found: forall f n, t_red (f @ n) tt -> t_red (minrec0 f @ n) n. 
Proof.  intros f n H; htac Y2_red; htac H. Qed.


Lemma minrec0_next: forall f n, t_red (f @ n) ff -> t_red (minrec0 f @ n) (minrec0 f @ (succ1 @ n)).
Proof.  intros f n H; htac Y2_red; htac H; htac ff_red; eapply preserves_appr_t_red; tree_red. Qed.

Definition minrec f xs := minrec0 (fold_left App xs f).


Theorem minrec_found:
  forall f xs n, t_red (fold_left App xs f @ n) tt -> t_red (minrec f xs @ n) n. 
Proof. intros; eapply minrec0_found; eauto. Qed.

Theorem minrec_next:
  forall f xs n, t_red (fold_left App xs f @ n) ff -> t_red (minrec f xs @ n) (minrec f xs @ (succ1 @ n)).
Proof. intros; eapply minrec0_next; eauto. Qed.



(* This shows Turing completeness *)

(* 

(*** Zero, successor and numerals as iterators *) 

Definition zero := KI.


Definition succ1 := S1 (S1 (K @ Node) @ (S1 (K @ Node) @ K)).


Theorem succ1_red: forall n f x, t_red (succ1 @ n @ f @ x) (f @ (n @ f @ x)).
Proof.  tree_red. Qed. 
  
Definition num k := iter k (fun x => succ1 @ x) zero.

 
Lemma num_iterates: forall m f x, t_red (num m @ f @ x) (iter m (App f) x).
Proof.
  induction m; intros; unfold num; fold num; simpl; eauto; repeat trtac; [ tree_red | 
  unfold succ1 at 1; trtac; eapply preserves_appr_t_red; eapply IHm].
Qed.


Lemma num_succ_red: forall k, t_red (num (S k)) (succ1 @ (num k)).
Proof. tree_red. Qed.  

  
(*** The zero test and conditionals *)


Definition isZero := \"n" (Ref "n" @ (K @ ff) @ tt). 

Theorem isZero_zero: t_red (isZero @ zero) tt.
Proof.  tree_red. Qed.

Theorem isZero_succ: forall n, t_red (isZero @ (succ1 @ n)) ff.
Proof.  tree_red. Qed.

Definition cond := I. 

Theorem cond_false : forall x y, t_red (cond @ ff @ x @ y) y.
Proof. tree_red. Qed. 

Theorem cond_true : forall x y, t_red (cond @ tt @ x @ y) x.
Proof. tree_red. Qed. 


(*** The predecessor function  - underpinning primitive recursion *) 
  
Definition PZero := pairL zero zero.  (*   \ (Var 0 @ (num 0) @ (num 0)). *)  
Definition PSucc := \"p" (pairL (sndL @ Ref "p") (succ1 @ (sndL @ Ref "p"))). 
Definition predN := \"n" (fstL @ (Ref "n" @ PSucc @ PZero)).

Lemma PSucc_red: forall m n,  t_red (PSucc @ (pairL m n)) (pairL n (succ1 @ n)).
Proof. tree_red. Qed.


Lemma pred_aux:  forall k, t_red (iter k (App PSucc) PZero) (pairL (num (Nat.pred k)) (num k)).
Proof. induction k; intros; repeat eexists; simpl; [ eapply zero_red | htac IHk; htac PSucc_red]. Qed.

 
Theorem pred_red: forall k,  t_red (predN @ (num k)) (num (pred k)). 
Proof.
  intros; unfold predN;  startac "n"; 
  trtac. unfold fstL.  trtac. Search num. htac num_iterates; htac pred_aux; tree_red.  
Qed.



(*** Primitive Recursion *)



Definition primrec0_abs :=
  \"n"
          (\"x"
            (isZero @ (Ref "n")
                    @ Ref "g"
                    @ (Ref "h" @ (predN @ Ref "n") @ (Ref "x" @ (predN @ Ref "n")))                  
          )).

Lemma primrec0_val:
  primrec0_abs =
  S1 (S1 (K @ △) @ (S1 (K @ △) @ (S1 (K @ K) @ (S1 (S1 (K @ isZero) @ I) @ (K @ Ref "g"))))) @
  (S1 (S1 (K @ △) @ (S1 (K @ △) @ (S1 (K @ K) @ (S1 (K @ Ref "h") @ (S1 (K @ predN) @ I))))) @
   (S1 (K @ (△ @ (△ @ I))) @ (S1 (K @ K) @ (S1 (K @ predN) @ I)))) .
Proof.  unfold primrec0_abs; startac "x"; startac "n"; auto.  Qed.


Definition primrec0 g h :=
    Yop2 (S1 (S1 (K @ Node) @ (S1 (K @ Node) @ (S1 (K @ K) @ (S1 (S1 (K @ isZero) @ I) @ (K @ g))))) @
  (S1 (S1 (K @ △) @ (S1 (K @ Node) @ (S1 (K @ K) @ (S1 (K @ h) @ (S1 (K @ predN) @ I))))) @
   (S1 (K @ (Node @ (△ @ I))) @ (S1 (K @ K) @ (S1 (K @ predN) @ I))))) .


Lemma primrec0_red_zero :
  forall g h, t_red (primrec0 g h @ zero) g.
Proof.  intros; unfold primrec0;  startac "y"; startac "x"; htac Y2_red; htac isZero_zero. Qed. 


Lemma primrec0_red_succ :
  forall k g h, t_red (primrec0 g h @ (num (S k))) (h @ (num k) @ (primrec0 g h @ (num k))).
Proof. intros; unfold primrec0; startac "y"; startac "x"; htac Y2_red;  htac isZero_succ; htac ff_red; repeat htac pred_red. Qed.
  

Definition primrec g h xs := primrec0 (fold_left App xs g) (fold_left App xs h).


Theorem primrec_red_zero:
  forall xs g h, t_red (primrec g h xs @ zero) (fold_left App xs g). 
Proof.  intros; eapply primrec0_red_zero. Qed. 


Theorem primrec_red_succ:
  forall xs g h k,
    t_red (primrec g h xs @ (num (S k))) (fold_left App xs h @ (num k) @ (primrec g h xs @ (num k))). 
Proof.  intros; simpl; auto; eapply primrec0_red_succ. Qed. 


Definition prim_plus0 n := primrec I (K @ (K @ (\"z" (succ1 @ (Ref "z"))))) (n::nil). 

Definition prim_plus := \"n" (prim_plus0 (Ref "n")). 

Theorem prim_plus_zero: forall n, t_red (prim_plus @ n @ zero) n. 
Proof.
  intros; htac star_beta;
  replace (substitute (prim_plus0 (Ref "n")) "n" n) with (prim_plus0 n) by (cbv; auto);
  htac primrec_red_zero; tree_red.
Qed.

Theorem prim_plus0_succ1: forall m n, t_red (prim_plus0 m @ (num (S n))) (succ1 @ (prim_plus0 m @ (num n))). 
Proof.  intros; htac primrec_red_succ; simpl; trtac. Qed. 
  


  
(*** Minimisation *)


Definition minrec_abs := \"r1" (\"r0" (Ref "f" @ Ref "r1" @ Ref "r1" @ (Ref "r0" @ (succ1 @ (Ref "r1"))))).

Lemma min_rec_abs_val :
  minrec_abs =  △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ △))) @
      (△ @ (△ @ (△ @ (△ @ (△ @ △ @ Ref "f")) @ (△ @ (△ @ (△ @ △)) @ (△ @ △)))) @
       (△ @ (△ @ (△ @ △)) @ (△ @ △))))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △)))))) @ \ "r1" (K @ (succ1 @ (Ref "r1")))).

Proof.  unfold minrec_abs; repeat startac2. Qed. 


  

Definition minrec0 f := Yop2   (  △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ △))) @
      (△ @ (△ @ (△ @ (△ @ (△ @ △ @ f)) @ (△ @ (△ @ (△ @ △)) @ (△ @ △)))) @
       (△ @ (△ @ (△ @ △)) @ (△ @ △))))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △)))))) @ \ "r1" (K @ (succ1 @ (Ref "r1"))))). 

  
Lemma minrec0_found: forall f n, t_red (f @ n) tt -> t_red (minrec0 f @ n) n. 
Proof.  intros f n H; htac Y2_red; htac H. Qed.


Lemma minrec0_next: forall f n, t_red (f @ n) ff -> t_red (minrec0 f @ n) (minrec0 f @ (succ1 @ n)).
Proof.  intros f n H; htac Y2_red; htac H; htac ff_red; eapply preserves_appr_t_red; tree_red. Qed.

Definition minrec f xs := minrec0 (fold_left App xs f).


Theorem minrec_found:
  forall f xs n, t_red (fold_left App xs f @ n) tt -> t_red (minrec f xs @ n) n. 
Proof. intros; eapply minrec0_found; eauto. Qed.

Theorem minrec_next:
  forall f xs n, t_red (fold_left App xs f @ n) ff -> t_red (minrec f xs @ n) (minrec f xs @ (succ1 @ n)).
Proof. intros; eapply minrec0_next; eauto. Qed.



(* This shows Turing completeness *)

(* an alternative account 

(*** Zero, successor and numerals as iterators *) 

Definition zero := Node.
Definition succ1 := Node. 
Definition num k := iter k (App Node) Node.

 

Lemma num_succ_red: forall k, t_red (num (S k)) (succ1 @ (num k)).
Proof. tree_red. Qed.  

  
(*** The zero test and conditionals *)


Definition isZero := triage K (K @ KI) (K @ (K @ K)). (* forks are zero *) 

Theorem isZero_zero: t_red (isZero @ zero) tt.
Proof.  tree_red. Qed.

Theorem isZero_succ: forall n, t_red (isZero @ (succ1 @ n)) ff.
Proof.  tree_red. Qed.

Definition cond := I. 

Theorem cond_false : forall x y, t_red (cond @ ff @ x @ y) y.
Proof. tree_red. Qed. 

Theorem cond_true : forall x y, t_red (cond @ tt @ x @ y) x.
Proof. tree_red. Qed. 
  
Definition predN := triage Node I (K @ (K @ Node)) (* forks are zero *).
 
Theorem pred_red: forall k,  t_red (predN @ (num k)) (num (pred k)). 
Proof.  intros; caseEq k; intros; simpl; tree_red. Qed.


(*** Primitive Recursion *)



Definition primrec0_abs :=
  \"n"
          (\"x"
            (isZero @ (Ref "n")
                    @ Ref "g"
                    @ (Ref "h" @ (predN @ Ref "n") @ (Ref "x" @ (predN @ Ref "n")))                  
          )).

Lemma primrec0_val:
  primrec0_abs = △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ △))) @
      (△ @ (△ @ (△ @ (△ @ (△ @ △) @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ (△ @ △)) @ △)))) @ (△ @ △ @ (△ @ △ @ (△ @ △))))) @
       (△ @ △ @ Ref "g")))))) @
  (△ @
   (△ @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ △)) @
      (△ @ (△ @ (△ @ △ @ (△ @ △))) @
       (△ @ (△ @ (△ @ △ @ Ref "h")) @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △ @ (△ @ △ @ △)))))))) @
   (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @
      (△ @ (△ @ (△ @ △ @ (△ @ △))) @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △ @ (△ @ △ @ △)))))) .
Proof.  tree_red; f_equal. Qed. 


Definition primrec0 g h :=
    Yop2 ( △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ △))) @
      (△ @ (△ @ (△ @ (△ @ (△ @ △) @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ (△ @ △)) @ △)))) @ (△ @ △ @ (△ @ △ @ (△ @ △))))) @
       (△ @ △ @ g)))))) @
  (△ @
   (△ @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ △)) @
      (△ @ (△ @ (△ @ △ @ (△ @ △))) @
       (△ @ (△ @ (△ @ △ @ h)) @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △ @ (△ @ △ @ △)))))))) @
   (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @
      (△ @ (△ @ (△ @ △ @ (△ @ △))) @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △ @ (△ @ △ @ △)))))) ).



Lemma primrec0_red_zero :
  forall g h, t_red (primrec0 g h @ zero) g.
Proof.  intros; unfold primrec0; htac Y2_red; htac isZero_zero. Qed. 


Lemma primrec0_red_succ :
  forall k g h, t_red (primrec0 g h @ (num (S k))) (h @ (num k) @ (primrec0 g h @ (num k))).
Proof. intros; unfold primrec0; htac Y2_red;  htac isZero_succ; htac ff_red; repeat htac pred_red. Qed.
  

Definition primrec g h xs := primrec0 (fold_left App xs g) (fold_left App xs h).


Theorem primrec_red_zero:
  forall xs g h, t_red (primrec g h xs @ zero) (fold_left App xs g). 
Proof.  intros; eapply primrec0_red_zero. Qed. 


Theorem primrec_red_succ:
  forall xs g h k,
    t_red (primrec g h xs @ (num (S k))) (fold_left App xs h @ (num k) @ (primrec g h xs @ (num k))). 
Proof.  intros; simpl; auto; eapply primrec0_red_succ. Qed. 

Definition comp g f := S1 (K @ g) @ f. 

Definition prim_plus_abs := Eval cbv in triage KI (\"x" (\"p" (comp Node (Ref "p" @ Ref "x")))) (K @ (K @ KI)). 

Definition prim_plus := Yop2 prim_plus_abs.

Theorem prim_plus_zero: forall n, t_red (prim_plus @ zero @ n) n. 
Proof.  intros; unfold prim_plus; htac Y2_red; unfold prim_plus_abs at 1; trtac. Qed. 

Theorem prim_plus_succ1: forall m n, t_red (prim_plus @ (succ1 @ m) @ n) (succ1 @ (prim_plus @ m @ n)).
Proof.  intros; unfold prim_plus; htac Y2_red; unfold prim_plus_abs at 1; trtac. Qed. 

  
(*** Minimisation *)


Definition minrec_abs := \"r1" (\"r0" (Ref "f" @ Ref "r1" @ Ref "r1" @ (Ref "r0" @ (succ1 @ (Ref "r1"))))).

Lemma min_rec_abs_val :
  minrec_abs =  △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ (△ @ △ @ (△ @ △))) @ (△ @ (△ @ Ref "f") @ (△ @ (△ @ (△ @ △)) @ △)))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @ (△ @ (△ @ (△ @ △ @ (△ @ △))) @ △)).
Proof.  tree_red; f_equal. Qed. 

Definition minrec0 f := Yop2   (   △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ (△ @ △ @ (△ @ △))) @ (△ @ (△ @ f) @ (△ @ (△ @ (△ @ △)) @ △)))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @ (△ @ (△ @ (△ @ △ @ (△ @ △))) @ △))).   

Lemma minrec0_found: forall f n, t_red (f @ n) tt -> t_red (minrec0 f @ n) n. 
Proof.  intros f n H; htac Y2_red; htac H. Qed.


Lemma minrec0_next: forall f n, t_red (f @ n) ff -> t_red (minrec0 f @ n) (minrec0 f @ (succ1 @ n)).
Proof.  intros f n H; htac Y2_red; htac H; htac ff_red; eapply preserves_appr_t_red; tree_red. Qed.

Definition minrec f xs := minrec0 (fold_left App xs f).


Theorem minrec_found:
  forall f xs n, t_red (fold_left App xs f @ n) tt -> t_red (minrec f xs @ n) n. 
Proof. intros; eapply minrec0_found; eauto. Qed.

Theorem minrec_next:
  forall f xs n, t_red (fold_left App xs f @ n) ff -> t_red (minrec f xs @ n) (minrec f xs @ (succ1 @ n)).
Proof. intros; eapply minrec0_next; eauto. Qed.



(* This shows Turing completeness *)

 *)
 *)



(* Triage *)


Definition prim_succ_plus := \"x" (\"y" (succ1 @ (prim_plus @ (Ref "x") @ Ref "y"))).


Definition size_loop :=
  \"s"
      (triage
         (succ1 @ zero)
         (\"x" (succ1 @ (Ref "s" @  Ref "x")))
         (\"x" (\"y" (prim_succ_plus @ (Ref "s" @  Ref "x") @ (Ref "s" @  Ref "y"))))).

Definition size := Z size_loop.




(*** Tagging *)

Definition tag t i := wait (K @ t) i.

Lemma tag_is_functional: forall t i x, t_red (tag t i @ x) (t@ x).
Proof. intros; tree_red. Qed.

Definition untag :=  triage Node Node (K @ (triage Node Node KI)).

Lemma untag_untags: forall t i, t_red (untag @ (tag t i)) i.
Proof. tree_red. Qed. 



(*** Evaluators *)

(* eager evaluation *)

Inductive factorable: Tree -> Prop :=
| factorable_leaf : factorable △
| factorable_stem: forall M, factorable (△ @ M)
| factorable_fork: forall M N, factorable (△ @ M @ N)
.

Global Hint Constructors factorable :TreeHintDb. 



Lemma factorable_or_not: forall M,  factorable M \/ ~ (factorable M).
Proof.
  induction M; intros; auto_t.
  - right; intro; inv1 factorable. 
  - case M1; intros; auto_t.
    + right; intro; inv1 factorable.
    + case t; intros; auto_t;  right; intro; inv1 factorable.
Qed.


Lemma programs_are_factorable: forall p, program p -> factorable p.
Proof. intros p pr; inversion pr; auto_t. Qed. 


Definition eager_s :=
  triage
    (\"f" (Ref "f" @ Node))
    (\"x" (\"f" (Ref "f" @ (Node @ Ref "x"))))
    (\"w" (\"x" (\"f" (Ref "f" @ (Node @ Ref "w" @ Ref "x"))))).


Lemma eager_s_of_factorable : forall M N, factorable N -> t_red (eager_s @ N @ M)  (M @ N).
Proof.  intros M N fac1; inversion fac1; subst; tree_red. Qed.


Definition eager := \"f" (\"x" (eager_s @ Ref "x" @ Ref "f")).

Theorem eager_of_factorable : forall M N, factorable N -> t_red (eager @ M @ N)  (M @ N).
Proof.  intros M N fac1; inversion fac1; subst; tree_red. Qed.



(* Branch-first evaluation *)

Inductive branch_first_eval: Tree -> Tree -> Tree -> Prop :=
| e_leaf : forall x, branch_first_eval △ x (△ @ x)
| e_stem : forall x y, branch_first_eval (△ @ x) y (△ @ x @ y)
| e_fork_leaf: forall y z, branch_first_eval (△ @ △ @ y) z y
| e_fork_stem: forall x y z xz yz v,
    branch_first_eval x z xz -> branch_first_eval y z yz -> branch_first_eval xz yz v -> 
    branch_first_eval (△ @ (△ @ x) @ y) z v
| e_fork_fork_leaf: forall w x y, branch_first_eval (△ @ (△ @ w @ x) @ y) Node w
| e_fork_fork_stem: forall w x y z xz,
    branch_first_eval x z xz -> 
    branch_first_eval (△ @ (△ @ w @ x) @ y) (Node @ z) xz
| e_fork_fork_fork: forall w x y z u yz v,
    branch_first_eval y z yz -> branch_first_eval yz u v -> 
    branch_first_eval (△ @ (△ @ w @ x) @ y) (Node @ z @ u) v
.
              
Global Hint Constructors branch_first_eval: TreeHintDb.


Theorem branch_first_reduces: forall M N P, branch_first_eval M N P -> t_red (M @ N) P. 
Proof. intros M N P e; induction e; intros; trtac; aptac; eauto; trtac. Qed. 
       

Theorem branch_first_program :
  forall M N P, branch_first_eval M N P -> program M -> program N -> program P.
Proof.
  intros M N P ev; induction ev; intros; inv_out H;program_tac; auto_t; inv_out H3; auto_t; inv_out H0; auto_t. 
Qed.

Lemma branch_first_eval_program_red: forall M N, program (M@N) -> branch_first_eval M N (M@N).
Proof. intros M N p; inversion p; auto_t. Qed.



(* 377 

Definition bffs := (* the function is a fork of a stem *) 
  \ "x" (\"e" (\ "y" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 
Definition bfff := (* the function is a fork of a fork, so triage on the argument *) 
  \"w"
   (\"x"
      (\"e" (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
   )))).
Definition bff :=  \"e" (\"x" (triage (K@K) bffs bfff @ Ref "x" @ Ref "e")).
Definition bf := Z (\ "e" (triage Node Node (bff @ Ref "e"))). 


Eval cbv in (term_size bffs). (* 139 *) 
Eval cbv in (term_size bfff). (* 172, up from 155  *) 



Theorem bf_leaf_red: forall p,  t_red (bf @ △ @ p) (△@ p).  
Proof.
  intros; aptac; [ apply Z_red | trtac | unfold triage at 1; startac "e"; startac "x"; trtac].  
Qed.

Theorem bf_stem_red: forall x y, t_red (bf @ (△ @ x) @ y) (△ @ x @ y).  
Proof.
  intros; aptac; [ apply Z_red | trtac | unfold triage at 1; startac "e"; startac "x"; trtac]; tree_red.
Qed.

Theorem bf_fork_red:
  forall x y, t_red (bf @ (△ @ x @ y)) ( bff @ bf @ x @ y).
Proof. intros; htac Z_red; unfold triage; startac "e"; trtac. Qed. 


Theorem bf_fork_leaf_red:  forall y z, t_red(bf @ (△@△@y) @ z) y.
Proof. intros; htac bf_fork_red; tree_red. Qed. 


Theorem bf_fork_stem_red:
  forall x y z, t_red (bf @ (△@(△@x) @y) @ z) (eager_s @ (bf @ y @ z) @ (bf @ (bf @ x @ z)) ). 
Proof. intros; htac bf_fork_red.   unfold bff, bffs, triage; 
    startac "z"; startac "y"; startac "e"; startac "x"; startac "e"; startac "x"; trtac. 
Qed. 

Theorem bf_fork_fork_red: forall w x y,
    t_red (bf @ (△@(△@w @x) @y)) (triage w (bf @ x) (S1 (K @ bf) @ (bf @ y))).
Proof.
  intros; htac bf_fork_red; unfold bff, bfff, triage, K; refold substitute; trtac;
    startac "y"; startac "e"; startac "x"; startac "w"; startac "e"; startac "x"; unfold S1, K; trtac;
    startac "w"; startac "e"; trtac; unfold star; simpl; trtac. 
Qed.


Theorem bf_fork_fork_leaf_red: forall w x y,  t_red (bf @ (△@(△@w @x) @y) @ Node) w. 
Proof.
  intros; htac bf_fork_fork_red; unfold bfff, triage; simpl; startac "y"; startac "x"; startac "w"; startac "e"; trtac.
Qed. 

Theorem bf_fork_fork_stem_red: forall w x y z,  t_red (bf @ (△@(△@w @x) @y) @ (Node @ z)) (bf @ x @ z). 
Proof.
  intros; htac bf_fork_fork_red; unfold bfff, triage; simpl; startac "y"; startac "x"; startac "w"; startac "e"; trtac.
Qed. 

Theorem bf_fork_fork_fork_red:
  forall w x y z u,  t_red (bf @ (△@(△@w @x) @y) @ (Node @ z @ u)) (bf @ (bf @ y @ z) @ u).
Proof.  intros; htac bf_fork_fork_red; unfold bfff, triage; simpl;
          startac "u"; startac "z"; startac "y"; startac "x"; startac "w"; startac "e"; trtac.
Qed.


Theorem branch_first_eval_to_bf:
  forall M N P, program M -> program N -> branch_first_eval M N P -> t_red(bf@M@N) P. 
Proof.
  intros M N P prM prN ev; induction ev; intros; subst.
  - apply bf_leaf_red.  
  - apply bf_stem_red.
  - apply bf_fork_leaf_red.
  - inv_out prM; inv_out H1; htac bf_fork_stem_red;
      htac IHev2; htac eager_s_of_factorable; [
          eapply programs_are_factorable | aptac; [ aptac; [ | htac IHev1 |] |  | ]; zerotac; eapply IHev3; eauto];
        eapply branch_first_program; eauto.
  - eapply bf_fork_fork_leaf_red.
  - inv_out prM; inv_out prN; inv_out H1;
      htac bf_fork_fork_stem_red; eapply IHev; eauto.
  - inv_out prM; inv_out prN; inv_out H1;
      htac bf_fork_fork_fork_red; aptac; [ aptac; [ zerotac | eapply IHev1 | zerotac] | zerotac |zerotac]; eauto;
      htac IHev2; eauto; eapply branch_first_program; eauto.
Qed.

(* the converse theorem is in rewriting_theorems.v *) 
   



Theorem term_size_equal: term_size equal = 406. Proof. cbv; auto. Qed. 

Theorem term_size_bf: term_size bf = 376. Proof. cbv; auto. Qed. 

*) 
 
(* 
Definition C x := S1 (K @ (S1 x)) @ K. 

Definition bffs := (* the function is a fork of a stem *) 
  \ "x" (\"e" (\ "y" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 

Eval cbv in (term_size bffs). (* 139 *) 

Definition bfff := (* the function is a fork of a fork, so triage on the argument *)

\"w" ( match  ((\"e" (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
         )))) with
              | M @ N => C (\"x" M) @ N
              | _ => Node
  end).

Eval cbv in (term_size bfff). (* 192 *) 


Print bfff. 

  \"w"
   (\"x"
      (\"e" (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
   )))).

Eval cbv in (term_size bfff).

Eval cbv in ((\"e" (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
   )))). 

Definition bff :=  triage K bffs bfff.
Definition bf := Z (\ "e" (triage Node Node bff)). 

 *)

Definition bffs := (* the function is a fork of a stem *) 
  \ "x" (\ "y" (\"z" (eager @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z"))  @ (Ref "e" @ Ref "y" @ Ref "z")))). 
Definition bfff := (* the function is a fork of a fork, so triage on the argument *) 
  \"w"
   (\"x"
      (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
   ))).
Definition bff :=  triage K bffs bfff.
Definition bf := Z (\ "e" (triage Node Node bff)). 

(* 
Eval cbv in (term_size (\"e" bffs)). (* 155 *) 
Eval cbv in (term_size (\"e" bfff)). (* 155 *) 
 *)

Set Printing Depth 200.

Lemma bf_val : bf =  △ @
  (△ @
   (△ @
    (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △)))))) @
    (△ @ △))) @
  (△ @ △ @
   (△ @
    (△ @
     (△ @ △ @
      (△ @ (△ @ (△ @ △ @ (△ @ (△ @ △ @ △)))) @
       (△ @
        (△ @
         (△ @ (△ @ (△ @ △ @ △)) @
          (△ @ (△ @ (△ @ △ @ (△ @ (△ @ △)))) @
           (△ @
            (△ @
             (△ @ (△ @ (△ @ △ @ △)) @
              (△ @ (△ @ (△ @ △ @ △)) @
               (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
                (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
                 (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △)))))) @
                  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
                   (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
                    (△ @
                     (△ @
                      (△ @ △ @
                       (△ @
                        (△ @
                         (△ @ △ @
                          (△ @
                           (△ @
                            (△ @ △ @
                             (△ @
                              (△ @
                               (△ @ △ @
                                (△ @
                                 (△ @
                                  (△ @
                                   (△ @
                                    (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △)) @
                                     (△ @ △ @ △)) @
                                    (△ @
                                     (△ @
                                      (△ @ △ @
                                       (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @
                                     (△ @ (△ @ (△ @ △ @ (△ @ △))) @ △))) @
                                   (△ @
                                    (△ @
                                     (△ @ △ @
                                      (△ @
                                       (△ @
                                        (△ @ △ @
                                         (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △)))))))) @
                                    (△ @
                                     (△ @
                                      (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △)))))) @
                                     △))))))) @ (△ @ △)))))))))) @
                     (△ @
                      (△ @
                       (△ @ (△ @ (△ @ △ @ △)) @
                        (△ @ (△ @ (△ @ △ @ △)) @
                         (△ @ (△ @ (△ @ △ @ (△ @ △))) @
                          (△ @ (△ @ (△ @ △ @ △)) @
                           (△ @ (△ @ (△ @ △ @ △)) @ (△ @ △))))))) @
                      (△ @ (△ @ (△ @ △)) @ △))))))))))) @ 
            (△ @ △))))) @
        (△ @
         (△ @
          (△ @ (△ @ (△ @ △ @ △)) @
           (△ @ (△ @ (△ @ △ @ △)) @
            (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
             (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
              (△ @
               (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △)))))))) @
               (△ @
                (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △)))))))) @
                (△ @
                 (△ @
                  (△ @ △ @
                   (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △))))))))) @
                 (△ @
                  (△ @
                   (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △)))))))) @
                  (△ @
                   (△ @
                    (△ @ △ @
                     (△ @
                      (△ @
                       (△ @ (△ @ (△ @ △ @ △)) @
                        (△ @ (△ @ (△ @ △ @ △)) @
                         (△ @ (△ @ (△ @ △ @ (△ @ △))) @ △))))))) @ 
                   (△ @ △))))))))))) @
         (△ @ (△ @ (△ @ △ @ (△ @ △))) @
          (△ @ (△ @ (△ @ △ @ (△ @ △))) @
           (△ @
            (△ @
             (△ @ (△ @ (△ @ △ @ △)) @
              (△ @ (△ @ (△ @ △ @ △)) @
               (△ @ (△ @ (△ @ △ @ (△ @ △))) @
                (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ △))))))) @
            (△ @ (△ @ (△ @ △)) @ △))))))))) @
    (△ @
     (△ @
      (△ @
       (△ @
        (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △)))))) @
       (△ @ △)))))).
Proof. cbv; auto. Qed. 

Theorem bf_leaf_red: forall p,  t_red (bf @ △ @ p) (△@ p).  
Proof.
  intros; aptac; [ apply Z_red | trtac | unfold triage at 1; startac "e"; startac "x"; trtac].  
Qed.

Theorem bf_stem_red: forall x y, t_red (bf @ (△ @ x) @ y) (△ @ x @ y).  
Proof.
  intros; aptac; [ apply Z_red | trtac | unfold triage at 1; startac "e"; startac "x"; trtac]; tree_red.
Qed.

Theorem bf_fork_red:
  forall x y, t_red (bf @ (△ @ x @ y)) (substitute bff "e" bf @ x @ y).
Proof.
  intros; htac Z_red; unfold bff, triage; startac "e"; trtac; refold substitute; trtac;
    htac star_beta; eapply preserves_appl_t_red;  eapply preserves_appl_t_red; eapply preserves_appr_t_red; eapply star_beta.
Qed. 


Theorem bf_fork_leaf_red:  forall y z, t_red(bf @ (△@△@y) @ z) y.
Proof. intros; htac bf_fork_red; tree_red. Qed. 


Theorem bf_fork_stem_red:
  forall x y z, t_red (bf @ (△@(△@x) @y) @ z) (eager @ (bf @ (bf @ x @ z)) @ (bf @ y @ z)  ). 
Proof. intros; htac bf_fork_red.   unfold bff, bffs, triage; 
    startac "z"; startac "y"; startac "e"; startac "x"; unfold S1, K; refold substitute; trtac. 
Qed. 

Theorem bf_fork_fork_red: forall w x y,
    t_red (bf @ (△@(△@w @x) @y)) (triage w (bf @ x) (S1 (K @ bf) @ (bf @ y))).
Proof.
  intros; htac bf_fork_red; unfold bff, bfff, triage, K; refold substitute; trtac.
    startac "y"; startac "x"; startac "w"; unfold S1, K; unfold substitute; rewrite ! String.eqb_refl;  trtac.  
Qed.


Theorem bf_fork_fork_leaf_red: forall w x y,  t_red (bf @ (△@(△@w @x) @y) @ Node) w. 
Proof.
  intros; htac bf_fork_fork_red; unfold bfff, triage; simpl; startac "y"; startac "x"; startac "w"; startac "e"; trtac.
Qed. 

Theorem bf_fork_fork_stem_red: forall w x y z,  t_red (bf @ (△@(△@w @x) @y) @ (Node @ z)) (bf @ x @ z). 
Proof.
  intros; htac bf_fork_fork_red; unfold bfff, triage; simpl; startac "y"; startac "x"; startac "w"; startac "e"; trtac.
Qed. 

Theorem bf_fork_fork_fork_red:
  forall w x y z u,  t_red (bf @ (△@(△@w @x) @y) @ (Node @ z @ u)) (bf @ (bf @ y @ z) @ u).
Proof.  intros; htac bf_fork_fork_red; unfold bfff, triage; simpl;
          startac "u"; startac "z"; startac "y"; startac "x"; startac "w"; startac "e"; trtac.
Qed.


Theorem branch_first_eval_to_bf:
  forall M N P, program M -> program N -> branch_first_eval M N P -> t_red(bf@M@N) P. 
Proof.
  intros M N P prM prN ev; induction ev; intros; subst.
  - apply bf_leaf_red.  
  - apply bf_stem_red.
  - apply bf_fork_leaf_red.
  - inv_out prM; inv_out H1; htac bf_fork_stem_red;
      htac IHev2; htac eager_of_factorable; [
          eapply programs_are_factorable | aptac; [ aptac; [ | htac IHev1 |] |  | ]; zerotac; eapply IHev3; eauto];
        eapply branch_first_program; eauto.
  - eapply bf_fork_fork_leaf_red.
  - inv_out prM; inv_out prN; inv_out H1;
      htac bf_fork_fork_stem_red; eapply IHev; eauto.
  - inv_out prM; inv_out prN; inv_out H1;
      htac bf_fork_fork_fork_red; aptac; [ aptac; [ zerotac | eapply IHev1 | zerotac] | zerotac |zerotac]; eauto;
      htac IHev2; eauto; eapply branch_first_program; eauto.
Qed.

(* the converse theorem is in rewriting_theorems.v *) 
   



Theorem term_size_equal: term_size equal = 406. Proof. cbv; auto. Qed. 

Theorem term_size_bf: term_size bf = (* 376 *) 392. Proof. cbv; auto. Qed. 
(*

Set Printing Depth 200. 

Lemma bffs_val : bffs =  △ @
  (△ @
   (△ @ △ @
    (△ @
     (△ @
      (△ @ (△ @ (△ @ △ @ △)) @
       (△ @ (△ @ (△ @ △ @ △)) @
        (△ @
         (△ @
          (△ @ △ @
           (△ @
            (△ @
             (△ @ △ @
              (△ @
               (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △)) @ (△ @ △ @ △)) @
                (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △))))) @
                 (△ @ (△ @ (△ @ △ @ (△ @ △))) @ △))) @
               (△ @
                (△ @
                 (△ @ △ @
                  (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ △)))))))) @
                (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △)))))) @ △)))))))) @
         Ref "e"))))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ △))) @
   (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ Ref "e"))))) @ Ref "e")) .
Proof. cbv; auto. Qed. 

Lemma bfff_val : bfff =  △ @
  (△ @
   (△ @ (△ @ (△ @ △ @ △)) @
    (△ @ (△ @ (△ @ △ @ △)) @
     (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
      (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
       (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △)))))) @
        (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △))))) @
         (△ @
          (△ @
           (△ @ (△ @ (△ @ △ @ △)) @
            (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ (△ @ △ @ (△ @ △))) @ △)))) @
          (△ @ △ @ Ref "e"))))))))) @
  (△ @ △ @
   (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ Ref "e"))))) @ Ref "e"))).
Proof. cbv; auto. Qed.


Eval cbv in (term_size eager_s). (* 56 *) 


Definition bffs2 := (* the function is a fork of a stem *) 
  \"e" (\ "x" (\ "y" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 

Eval cbv in (term_size bffs2).  (* 155 *) 

Definition bffs3 := (* the function is a fork of a stem *) 
  \"e" (\ "y" (\ "x" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 

Eval cbv in (term_size bffs3).  (* 163 *) 

Definition bffs4 := (* the function is a fork of a stem *) 
  \"x" (\ "e" (\ "y" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 

Eval cbv in (term_size bffs4).  (* 139 *) 

Definition bffs5 := (* the function is a fork of a stem *) 
  \"x" (\ "y" (\ "e" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 

Eval cbv in (term_size bffs5).  (* 152 *) 

Definition bffs6 := (* the function is a fork of a stem *) 
  \"y" (\ "e" (\ "x" (\"z" (eager_s @ (Ref "e" @ Ref "y" @ Ref "z") @ (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))))). 

Eval cbv in (term_size bffs6).  (* 176 *) 

Definition bfff2 := (* the function is a fork of a fork, so triage on the argument *) 
  \"e" (
      \"w"
   (\"x"
      (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
   )))).

Eval cbv in (term_size bfff2). (* 155 *)

Definition bfff3 := (* the function is a fork of a fork, so triage on the argument *) 
  \"w" (
      \"x"
   (\"e"
      (\"y"
       (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
   )))).

Eval cbv in (term_size bfff3). (* 172 *)






Fixpoint program_to_ternary p :=
  match p with
  | Ref _ => "fail"
  | Node => "0"
  | Node @ p1 => "1" ++ (program_to_ternary p1)
  | Node @ p1 @ p2 => "2" ++  (program_to_ternary p1) ++  (program_to_ternary p2)
  | _ @ _ => "fail"
  end.

Lemma ptt_equal: program_to_ternary equal =
                    "2121201121211001010202120212011222022102020211002020202110021212002120021201120021201120120211002120112110010202020202021100212011201120122021100202021100212120021200212011200212011200212011201120021201120112002120112011201120021201120112011200212120021200212010212002120021201120021201120021201120112002120112011200212011201120102120112110010202120112010212011211001020202020202021100101121201121211001010" .
Proof.  cbv; auto. Qed.

Lemma ptt_bf: program_to_ternary bf =
       "2121201121211001010202120212012002121200212011021212002120021201021200212002120112002120112001120112022212110020021201121100212010021201120112110021201120100212011201021212002120021201021200212001021100212120021200212011200212011200212011201120021201120112002120112011201021201120112002120112120021200212010010212010212010212120021200212010212002120010211001121201121211001010".
Proof.  cbv; auto. Qed. 

(* bf using Yop2 is longer !



Definition bffs := (* the function is a fork of a stem *) 
  \ "x" (\ "y" (\"e" (S1 (S1 (K @ eager) @ (S1 (K @ Ref "e") @ (Ref "e" @ Ref "x"))) @ (Ref "e" @ Ref "y")))).
Definition bfff := (* the function is a fork of a fork, so triage on the argument *) 
  \"w"
   (\"x"
     (\"y"
       (\"e" (triage
               (Ref "w")
               (Ref "e" @ Ref "x")
               (S1 (K @ Ref "e") @ (Ref "e" @ Ref "y"))
               )))). 
Definition bff :=  triage (S1 (K @ K) @ K) bffs bfff.
Definition bf := Yop2 (triage (K @ Node) (S1 (K @ K) @ Node) bff). 

Theorem bf_leaf_red: forall p,  t_red (bf @ △ @ p) (△@ p).  
Proof. intros; htac Y2_red; tree_red. Qed.

Theorem bf_stem_red: forall x y, t_red (bf @ (△ @ x) @ y) (△ @ x @ y).  
Proof. intros; htac Y2_red; tree_red. Qed.

Theorem bf_fork_red:
  forall x y, t_red (bf @ (△ @ x @ y)) (bff @ x @ y @ bf).
Proof. intros; htac Y2_red; tree_red. Qed.

Theorem bf_fork_leaf_red:  forall y z, t_red(bf @ (△@△@y) @ z) y.
Proof. intros; htac Y2_red; tree_red. Qed.

Theorem bf_fork_stem_red:
  forall x y z, t_red (bf @ (△@(△@x) @y) @ z) (eager @ (bf @ (bf @ x @ z)) @ (bf @ y @ z)). 
Proof. intros; htac bf_fork_red; unfold bff, bffs, triage; trtac; startac "e"; startac "y"; startac "x"; trtac. Qed. 

Theorem bf_fork_fork_red: forall w x y,
    t_red (bf @ (△@(△@w @x) @y)) (triage w (bf @ x) (S1 (K @ bf) @ (bf @ y))).
Proof. intros; htac bf_fork_red; unfold bff, bfff, triage; trtac; startac "e"; startac "y"; startac "x"; startac "w"; trtac. Qed. 


Theorem bf_fork_fork_leaf_red: forall w x y,  t_red (bf @ (△@(△@w @x) @y) @ Node) w. 
Proof.  intros; htac bf_fork_fork_red; tree_red. Qed. 

Theorem bf_fork_fork_stem_red: forall w x y z,  t_red (bf @ (△@(△@w @x) @y) @ (Node @ z)) (bf @ x @ z). 
Proof.  intros; htac bf_fork_fork_red; unfold triage; trtac. Qed. 

Theorem bf_fork_fork_fork_red:
  forall w x y z u,  t_red (bf @ (△@(△@w @x) @y) @ (Node @ z @ u)) (bf @ (bf @ y @ z) @ u).
Proof.  intros; htac bf_fork_fork_red; unfold triage; trtac. Qed. 
Qed.


Theorem branch_first_eval_to_bf:
  forall M N P, program M -> program N -> branch_first_eval M N P -> t_red(bf@M@N) P. 
Proof.
  intros M N P prM prN ev; induction ev; intros; subst.
  - apply bf_leaf_red.  
  - apply bf_stem_red.
  - apply bf_fork_leaf_red.
  - inv_out prM; inv_out H1; htac bf_fork_stem_red;
      htac IHev1; auto; htac IHev2; eauto; 
      htac eager_of_factorable; [
        eapply programs_are_factorable |  eapply IHev3; eauto];
      eapply branch_first_program; eauto.
  - eapply bf_fork_fork_leaf_red.
  - inv_out prM; inv_out prN; inv_out H1;
      htac bf_fork_fork_stem_red; eapply IHev; eauto.
  - inv_out prM; inv_out prN; inv_out H1;
      htac bf_fork_fork_fork_red; htac IHev1; eauto;
      htac IHev2; eauto; eapply branch_first_program; eauto.
Qed.

(* the converse theorem is in rewriting_theorems.v *) 
   

*) 

*) 
(*
Definition star1 x M := (* uses Sop instead of S1, for one level *) 
  match M with
  | Ref y =>  if eqb x y then I else (K @ Ref y)
  | △ => K@ △
  | App M1 M2 =>
      match M2 with
      | Ref y => if eqb x y
                 then if occurs x M1
                      then  Sop @ (star x M1) @ I
                      else M1
                 else if occurs x M1
                      then  Sop @ (star x M1) @ (K @ Ref y)
                      else K @ (M1 @ M2)
      | _ => if occurs x (M1 @ M2)
                 then Sop @ (star x M1) @ (star x M2)
                 else K@ (M1 @ M2)
      end
  end.
Notation "\\" := star1 : tree_scope.
Notation "\" := star : tree_scope.
Definition self_apply_k := \ "x" (Ref "x" @ (K @ Ref "x")).
Definition wait1 M := S1 (S1 (K @ (Node @ (Node @ M))) @ K).
Definition Z' f := wait self_apply_k (S1 (K @ f) @ (wait1 self_apply_k)).
Definition C1 a := \ "b" (S1 a @ (K @ Ref "b")).
Definition eager_s' :=
  triage
    (\"f" (Ref "f" @ Node))
    (\"x" (\"f" (Ref "f" @ (Node @ Ref "x"))))
    (\"w" (\"x" (C1 I @ (Node @ Ref "w" @ Ref "x")))).
Definition bffs' :=
  (\ "x" (\ "e" (\ "y" (\\ "z"
      ((eager_s' @ (Ref "e" @ Ref "y" @ Ref "z")) @
       (Ref "e" @ (Ref "e" @ Ref "x" @ Ref "z")))
  )))).
Eval cbv in (term_size bffs'). (* 131 *)
Definition triageOp := \ "a" (\ "b" (\ "c" (triage (Ref "a") (Ref "b") (Ref "c")))).
Definition bfff' :=
  \"w"
   (\"x"
     (\\"e"
      (\\ "y"
        ((triageOp 
              @ (Ref "w") 
              @ (Ref "e" @ Ref "x"))
              @ (\ "z" (Ref "e" @ (Ref "e" @ Ref "y" @ Ref "z")))
        )))). 
Eval cbv in (term_size bfff'). (* 156 *)
Definition bff' := \"e" (\"x" (triage (K @ K) bffs' bfff' @ Ref "x" @ Ref "e")).
Eval cbv in (term_size bff'). (* 301 *)
Definition bf' := Z' (\ "e" (triage Node Node (bff' @ Ref "e"))).
Eval cbv in (term_size bf'). (* 353 *)
Eval cbv in bf'.

 *)

Close Scope tree_scope.

(* End TreeModule. *) 
