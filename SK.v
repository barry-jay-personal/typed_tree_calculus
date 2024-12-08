(**********************************************************************)
(* Copyright 2020 Barry Jay                                           *)
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
(*                 Typed Combinatory Logic                            *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List Nat Datatypes String.

Set Default Proof Using "Type".

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


Ltac invsub := 
match goal with 
| H : _ = _ |- _ => injection H; clear H; invsub 
| _ => intros; subst
end. 


(* 8.2: SK-Calculus *) 


Inductive SK:  Set :=
  | Ref : string -> SK  (* variables are indexed by strings *) 
  | Sop : SK   
  | Kop : SK 
  | App : SK -> SK -> SK   
.

Hint Constructors SK : TreeHintDb.

Open Scope string_scope. 
Declare Scope sk_scope.
Open Scope sk_scope. 

Notation "x @ y" := (App x y) (at level 65, left associativity) : sk_scope.



Definition Iop := Sop @ Kop @ Kop. 


Inductive combination : SK -> Prop :=
| is_S : combination Sop
| is_K : combination Kop 
| is_App : forall M N, combination M -> combination N -> combination (M@ N)
.
Hint Constructors combination : TreeHintDb. 

(* SK-reduction *) 
Inductive sk_red1 : SK -> SK -> Prop :=
| s__red: forall (M N P : SK), sk_red1 (Sop @M@ N@ P) (M@P@(N@P))
| k_red : forall M N, sk_red1 (Kop @ M@ N) M 
| appl_red : forall M M' N, sk_red1 M M' -> sk_red1 (M@ N) (M' @ N)  
| appr_red : forall M N N', sk_red1 N N' -> sk_red1 (M@ N) (M@ N')  
.
Hint Constructors sk_red1 : TreeHintDb. 

(* Multiple reduction steps *) 

Inductive multi_step : (SK -> SK -> Prop) -> SK -> SK -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: SK-> SK -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.
Hint Constructors multi_step : TreeHintDb.


Definition transitive red := forall (M N P: SK), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; intros; simpl;  auto. apply succ_red with N; auto. Qed. 

Definition preserves_appl (red : SK -> SK -> Prop) := 
forall M N M', red M M' -> red (M@ N) (M' @ N).

Definition preserves_appr (red : SK -> SK -> Prop) := 
forall M N N', red N N' -> red (M@ N) (M@ N').

Definition preserves_app (red : SK -> SK -> Prop) := 
forall M M', red M M' -> forall N N', red N N' -> red (M@ N) (M' @ N').

Lemma preserves_appl_multi_step : 
forall (red: SK -> SK -> Prop), preserves_appl red -> preserves_appl (multi_step red). 
Proof. red; intros red hy M N M' r; induction r; auto with TreeHintDb; eapply succ_red; eauto. Qed.

Lemma preserves_appr_multi_step : 
forall (red: SK -> SK -> Prop), preserves_appr red -> preserves_appr (multi_step red). 
Proof. red; intros red hy M N M' r; induction r; auto with TreeHintDb; eapply succ_red; eauto. Qed.


Lemma preserves_app_multi_step : 
forall (red: SK -> SK -> Prop), 
preserves_appl red -> preserves_appr red -> 
preserves_app (multi_step red). 
Proof.
red; intros red pl pr M M' rM N N' rN;  
  apply transitive_red with (M' @ N); [ apply preserves_appl_multi_step | apply preserves_appr_multi_step] ;
    auto.
Qed.



(* sk_red *) 

Definition sk_red := multi_step sk_red1.

Lemma sk_red_refl: forall M, sk_red M M. Proof. intros; apply zero_red. Qed.
Hint Resolve sk_red_refl : TreeHintDb. 

Lemma preserves_appl_sk_red : preserves_appl sk_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_sk_red : preserves_appr sk_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_sk_red : preserves_app sk_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.



Ltac eval_tac1 := 
match goal with 
| |-  sk_red ?M _ => red; eval_tac1
(* 4 apps *) 
| |- multi_step sk_red1 (_ @ _ @ _ @ _ @ _) _ => 
  eapply transitive_red;  [eapply preserves_app_sk_red; [eval_tac1|auto_t] |auto_t]
(* 3 apps *) 
| |- multi_step sk_red1 (Sop @ _ @ _ @ _) _  => eapply succ_red; auto_t 
| |- multi_step sk_red1 (Kop @ _ @ _ @ _) _ =>
    eapply transitive_red;  [eapply preserves_app_sk_red; [eval_tac1|auto_t] |]; auto_t
| |- multi_step sk_red1 (_ @ _ @ _ @  _) (_ @ _)  =>  eapply preserves_app_sk_red; eval_tac1
(* 2 apps *) 
| |- multi_step sk_red1 (Sop @ _ @ _) (Sop  @ _ @ _) _ =>
  apply preserves_app_sk_red; [ apply preserves_app_sk_red |]; eval_tac1
| |- multi_step sk_red1 (Kop @ _ @ _ )  _  => eapply succ_red; auto_t 
| |- multi_step sk_red1 (_ @ _ @ _) (_ @ _)  => eapply preserves_app_sk_red; eval_tac1
| |- multi_step sk_red1 (_ @ _) (_ @ _) => apply preserves_app_sk_red; eval_tac1
| _ => auto_t
end.

Ltac eval_tac := intros; cbv; repeat eval_tac1. 


Ltac zerotac := try apply zero_red.
Ltac succtac :=
  repeat (eapply transitive_red;
  [ eapply succ_red; auto_t ;
    match goal with | |- multi_step sk_red1 _ _ => idtac | _ => fail end
  | ])
.
Ltac aptac := eapply transitive_red; [ eapply preserves_app_sk_red |].
                                             
Ltac ap2tac:=
  unfold sk_red; 
  eassumption || 
              match goal with
              | |- multi_step _ (_ @ _) _ => try aptac; [ap2tac | ap2tac | ]
              | _ => idtac
              end. 

Ltac trtac := unfold Iop; succtac;  zerotac. 

Lemma i_red: forall M, sk_red (Iop @ M) M.
Proof. eval_tac. Qed. 

Lemma i_alt_red: forall y M, sk_red (Sop @Kop@ y@ M) M. 
Proof. eval_tac. Qed. 




Ltac inv1 prop := 
match goal with 
| H: prop (_ @ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Sop |- _ => inversion H; clear H; inv1 prop
| H: prop Kop |- _ => inversion H; clear H; inv1 prop
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| _ =>  subst; intros; auto_t
 end.



Ltac inv red := 
match goal with 
| H: multi_step red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red Sop _ |- _ => inversion H; clear H; inv red
| H: multi_step red Kop _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: red Sop _ |- _ => inversion H; clear H; inv red
| H: red Kop _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ Sop |- _ => inversion H; clear H; inv red
| H: multi_step red _ Kop |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: red _ Sop |- _ => inversion H; clear H; inv red
| H: red _ Kop |- _ => inversion H; clear H; inv red
| _ => subst; intros; auto_t
 end.




Definition implies_red (red1 red2: SK-> SK-> Prop) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; intros; auto with TreeHintDb. 
apply transitive_red with N; auto. 
Qed. 


Lemma to_sk_red_multi_step: forall red, implies_red red sk_red -> implies_red (multi_step red) sk_red. 
Proof. 
red.  intros red B M N R; induction R; intros.
red; intros; auto with TreeHintDb. 
assert(sk_red M N) by (apply B; auto). 
apply transitive_red with N; auto. 
apply IHR; auto with TreeHintDb. 
Qed.


Inductive s_red1 : SK -> SK -> Prop :=
  | ref_s_red : forall i, s_red1 (Ref i) (Ref i)
  | sop_s_red :  s_red1 Sop Sop
  | kop_s_red :  s_red1 Kop Kop
  | app_s_red :
      forall M M' ,
      s_red1 M M' ->
      forall N N' : SK, s_red1 N N' -> s_red1 (M@ N) (M' @ N')  
  | s_s_red: forall (M M' N N' P P' : SK),
             s_red1 M M' -> s_red1 N N' -> s_red1 P P' ->                  
             s_red1  (Sop @M @ N @ P) (M' @ P' @ (N' @ P'))
  | k_s_red : forall M  M' N,  s_red1 M M' -> s_red1 (Kop @ M @ N) M' 
.

Hint Constructors s_red1 : TreeHintDb.

Lemma s_red_refl: forall M, s_red1 M M.
Proof. induction M; intros; auto with TreeHintDb. Qed. 

Hint Resolve s_red_refl : TreeHintDb. 
     
Definition s_red := multi_step s_red1.

Lemma preserves_appl_s_red : preserves_appl s_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_s_red : preserves_appr s_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_s_red : preserves_app s_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.


Lemma sk_red1_to_s_red1 : implies_red sk_red1 s_red1.
Proof. red; intros M N B; induction B; intros; auto with TreeHintDb. Qed. 


Lemma sk_red_to_s_red: implies_red sk_red s_red.
Proof.
  apply implies_red_multi_step.
  red; intros.  eapply succ_red. eapply sk_red1_to_s_red1; auto_t. apply zero_red.
Qed. 


Lemma s_red1_to_sk_red: implies_red s_red1 sk_red .
Proof.
  red; intros M N OR; induction OR; auto_t.
  2,3: eapply succ_red; auto_t.
  all: ap2tac; zerotac. 
Qed.

Hint Resolve s_red1_to_sk_red: TreeHintDb.

Lemma s_red_to_sk_red: implies_red s_red sk_red. 
Proof. apply to_sk_red_multi_step; auto with TreeHintDb. Qed.


Ltac exist x := exists x; split_all; auto_t.



(* Diamond Lemmas *) 


Definition diamond (red1 red2 : SK -> SK -> Prop) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof.
  unfold diamond; intros red1 red2 d1 M N r1 P r2; elim (d1 M P r2 N r1); intros x (?&?);
    exists x; tauto.
Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof.
  intros red1 red2 d; eapply diamond_flip; intros M N r; induction r;
    [intro P; exist P |
     intros P0 r0;
     elim (d M P0 r0 N); auto_t; intros x (?&?);  
     elim(IHr d x); auto; intros x0 (?&?); exist x0;  eapply2 succ_red
    ]. 
Qed. 


Definition diamond_star (red1 red2: SK -> SK -> Prop) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
  intros red1 red2 d M N r; induction r; intros P0 r0;
  [ exist P0 | 
  elim(d M _ r0 N); auto; intros x (r1&r2);   
  elim(IHr d x); auto; intros x0 (?&?); 
  exist x0; eapply2 transitive_red
    ]. 
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
  intros red1 red2 d M N r; induction r as [| ? ? ? ? r1 r2]; 
    [  intro P; exist P |
       intros P0 r0; 
       elim(diamond_strip red red2 d M N r1 P0); auto;
       intros N3 (r3&?); 
       elim(IHr2 d N3 r3); intros P1 (?&?);  
       exist P1;  eapply2 succ_red
  ].  
Qed. 

Hint Resolve diamond_tiling: TreeHIntDb. 



Lemma diamond_s_red1 : diamond s_red1 s_red1. 
Proof.  
red. intros M N r; induction r; intros P0 rP; auto_t.
(* 3 *)
inversion rP; clear rP; subst; inv s_red1; inv s_red1; auto_t. 
(* 5 *)
elim(IHr1 M'0); auto; intros x (?&?);
  elim(IHr2 N'0); auto; intros x0 (?&?); exists (x@ x0); split; auto_t.
(* 4 *)
elim(IHr1 (Sop @ M'0 @ N'0)); auto_t; intros x (?&?); inv s_red1; invsub. 
elim(IHr2 P'); auto_t; intros x (?&?).
exist (N'4 @ x @ (N'3 @ x)).
(* 3 *)
elim(IHr1 (Kop@ P0)); auto_t; intros x (?&?); inv s_red1; invsub; auto_t. 
(* 2 *)
inversion rP; clear rP; subst; inv s_red1; invsub. 
elim(IHr1 N'2); elim(IHr2 N'1); elim(IHr3 N'0); auto_t; intros x (?&?) x0 (?&?) x1 (?&?).
exist (x1 @ x @ (x0 @ x)).
elim(IHr1 M'0); elim(IHr2 N'0); elim(IHr3 P'0);  auto_t; intros x (?&?) x0 (?&?) x1 (?&?).
exist (x1 @ x @ (x0 @ x)).
(* 1 *) 
inversion rP; clear rP; subst; inv s_red1; invsub; auto_t.
elim(IHr N'0); auto; intros x (?&?); exist x. 
Qed.



Hint Resolve diamond_s_red1: TreeHintDb.

Lemma diamond_s_red1_s_red : diamond s_red1 s_red.
Proof. eapply diamond_strip; auto_t. Qed. 

Lemma diamond_s_red : diamond s_red s_red.
Proof.  apply diamond_tiling; auto_t. Qed. 
Hint Resolve diamond_s_red: TreeHIntDb.


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_s_red: confluence SK s_red. 
Proof. red; intros; eapply diamond_s_red; auto_t. Qed. 


 

Theorem confluence_sk_red: confluence SK sk_red. 
Proof. 
  red; intros.
  match goal with H: sk_red ?x ?y , H1 : sk_red ?x ?z |- _ => 
                  assert(py: s_red x y) by  (apply sk_red_to_s_red; auto_t);
                    assert(pz: s_red x z) by (apply sk_red_to_s_red; auto_t);
                    elim(diamond_s_red x y py z); auto_t end.
  intros x0 (?&?); exists x0; split; auto_t; apply s_red_to_sk_red; auto_t. 
Qed. 
Hint Resolve confluence_sk_red: TreeHintDb.

(* programs *)

Inductive program : SK -> Prop :=
| pr_S0 : program Sop
| pr_S1 : forall M, program M -> program (Sop @ M)
| pr_S2 : forall M1 M2, program M1 -> program M2 -> program (Sop @ M1 @ M2)
| pr_K0 : program Kop
| pr_K1 : forall M, program M -> program (Kop @ M) .

Hint Constructors program: TreeHintDb.


Ltac program_tac :=
  cbv; repeat (apply pr_S0 || apply pr_S1 || apply pr_S2 || apply pr_K0 || apply pr_K1); auto_t. 


(* normal forms *) 

Inductive active : SK -> Prop := 
| active_ref : forall i, active (Ref i)
| active_app : forall M N, active M -> active (M@ N)
.


Inductive normal : SK -> Prop := 
| nf_ref : forall i, normal (Ref i)
| nf_S : normal Sop
| nf_K : normal Kop                
| nf_app : forall M N, active M -> normal M -> normal N -> normal (M@ N)
| nf_S1 : forall M, normal M -> normal (Sop @ M)
| nf_K1 : forall M, normal M -> normal (Kop @ M)
| nf_S2 : forall M N, normal M -> normal N -> normal (Sop @ M @ N)
.


Hint Constructors active normal : TreeHintDb.


Lemma active_sk_red1 :
  forall M, active M -> forall N, sk_red1 M N  -> active N.
Proof.  intros M a; induction a; intros; inv sk_red1; inv1 active. Qed.   

  
                    Lemma active_sk_red2:
  forall M N P, active M -> sk_red1 (M@ N) P ->
                (exists M1, P = M1 @ N /\ sk_red1 M M1)
                \/ (exists N1, P = M@ N1 /\ sk_red1 N N1).
Proof. induction M; intros; inv sk_red1; auto_t; inv1 active. Qed. 
                      

Lemma active_sk_red:
  forall M N P, active M -> sk_red (M@ N) P ->
                (exists M1 N1, P = M1 @ N1 /\ sk_red M M1 /\ sk_red N N1).
Proof.
  cut(forall red M P, multi_step red M P -> red = sk_red1 -> 
forall M1 M2, M = M1 @ M2 -> active M1 -> 
                (exists P1 P2, P = P1 @ P2 /\ sk_red M1 P1 /\ sk_red M2 P2));
    [ intro c;  intros; eapply2 c
    |
    intros red M P r; induction r; intros; subst; auto_t; inv sk_red1 ;
    [ inv1 active
    | inv1 active 
    | eelim IHr; [ | auto | auto_t| eapply active_sk_red1; auto_t];
      intros x ex; elim ex; intros P2 (?&?&?); subst;
      repeat eexists; auto_t; eapply succ_red; auto_t
    |  eelim IHr;  [ | auto | auto_t |]; auto;  intros x ex; elim ex; intros x0 (?&?&?); subst;
       exists x; exist x0 ; eapply2 succ_red
    ]]. 
Qed.



Lemma normal_is_irreducible: forall M, normal M -> forall N, sk_red1 M N -> False.
Proof.
  intros M n; induction n; intros; inv sk_red1;
    ((apply IHn1; fail) || (apply IHn2; fail) || (apply IHn; fail) || inv1 active).  
Qed.


Lemma active_is_stable:
  forall M N P, active M -> s_red1 (M@ N) P ->
                (exists M1 N1, P = M1 @ N1 /\ s_red1 M M1 /\ s_red1 N N1).
Proof.
  induction M; intros N P a r; inv s_red1; auto_t; inversion a; subst; eauto 10 with *; inv1 active.
Qed.   


Lemma normal_is_stable: forall M, normal M -> forall N, s_red1 M N -> N = M.
Proof. intros M n; induction n; intros; inv s_red1; repeat f_equal; auto; inv1 active. Qed.


Lemma normal_is_stable2: forall M N, s_red M N -> normal M -> N = M.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> normal M -> N = M); 
  [ intro c; intros; eapply2 c  
  | intros red M N r; induction r; intros; subst; auto_t; 
    assert(N = M) by (eapply normal_is_stable; eauto); subst; auto
  ].
  Qed.


Lemma triangle_s_red : forall M N P, s_red M N -> s_red M P -> normal P -> s_red N P.
Proof.
  intros; assert(d: exists Q, s_red N Q /\ s_red P Q) by (eapply diamond_s_red; auto_t);
  elim d; intros x (?&?); 
  assert(x = P) by (eapply normal_is_stable2; eauto);  subst; auto. 
Qed.


Lemma programs_are_normal: forall M, program M -> normal M.
Proof.  intros M pr; induction pr; intros; auto_t. Qed. 


Definition normalisable M := exists N,  sk_red M N /\ program N.


Ltac normal_tac :=
  cbv;
  repeat (apply nf_S2 || apply nf_K1 || apply nf_S1 || apply nf_app ||
          apply nf_K || apply nf_S || apply nf_ref);
  apply programs_are_normal; 
  auto_t. 

Ltac stable_tac :=
  match goal with
  | H : s_red ?Q ?R |- _ =>
    assert(R=Q) by (apply normal_is_stable2; auto_t; cbv; normal_tac); clear H 
  | H : s_red1 ?Q ?R |- _ =>
    assert(R=Q) by (apply normal_is_stable; auto_t; cbv; normal_tac); clear H
  | H : sk_red ?Q ?R |- _ => assert(s_red Q R) by (apply sk_red_to_s_red; auto_t); clear H; stable_tac 
  | _ => auto_t
  end; subst; try discriminate.

(* 8.3 Combinators in SK-Calculus *) 


Fixpoint bracket x M := 
match M with 
| Ref y =>  if eqb x y then Iop else (Kop @ (Ref y))
| Sop => Kop @ Sop
| Kop => Kop @ Kop 
| M1 @ M2 => Sop @ (bracket x M1) @ (bracket x M2) 
end
.


(* star abstraction *)


Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y
  | Sop => false
  | Kop => false 
  | M1 @ M2 => (occurs x M1) || (occurs x M2)
  end.


Fixpoint star x M :=
  match M with
  | Ref y => if eqb x y then Iop else Kop @ (Ref y)
  | Sop  => Kop @ Sop
  | Kop => Kop @ Kop 
  | M1 @ (Ref y) =>
    if eqb x y
    then if negb (occurs x M1)
         then M1
         else Sop @ (star x M1) @ Iop
    else if negb (occurs x M1)
         then Kop @ (M1 @ (Ref y))
         else Sop @ (star x M1) @ (Kop @ (Ref y))
  | M1 @ M2 => if occurs x (M1 @ M2)
                 then Sop @ (star x M1) @ (star x M2) 
                 else Kop @ (M1 @ M2)
  end.



Lemma star_id: forall x, star x (Ref x) = Iop.
Proof. intro; unfold star, occurs; rewrite eqb_refl; auto. Qed.


Lemma eta_red: forall M x, occurs x M = false -> star x (M@ (Ref x)) = M.
Proof.  intros M x occ; unfold star at 1; fold star; rewrite eqb_refl; rewrite occ; auto. Qed.


Lemma star_occurs_false: forall M x, occurs x M = false -> star x M = Kop @ M. 
Proof.
  induction M; simpl in *; auto_t; intros x occ;  rewrite occ; auto.
  rewrite orb_false_iff in occ;  elim occ.   intros occ1 occ2; rewrite ! occ1.  
  caseEq M2; simpl; intros; subst; simpl in *; intros; auto_t.
  rewrite occ2; auto.   
Qed.


Lemma star_occurs_true:
  forall M1 M2 x, occurs x (M1 @ M2) = true -> M2 <> Ref x ->
                  star x (M1 @ M2) = Sop @ (star x M1) @ (star x M2).
Proof.
  intros M1 M2 x occ ne; unfold star at 1; fold star. 
  caseEq M2; 
    [ intros s e; subst;  assert(neq: x=? s = false) by (apply eqb_neq; congruence); 
      simpl in *; rewrite neq in *; rewrite orb_false_r in *; rewrite occ; auto
    | | |]; intros; subst; rewrite ? occ; auto. 
                 
Qed.

Ltac star_tac x :=
  repeat ( (rewrite (star_occurs_true _ _ x); [| unfold occurs; fold occurs; rewrite ? orb_true_r; simpl; auto; fail| cbv; discriminate]) || 
          (rewrite eta_red; [| cbv; auto; fail]) ||
          rewrite star_id || 
          (rewrite (star_occurs_false _ x); [| unfold occurs; fold occurs; auto; cbv; auto; fail])
         ).


Notation "\" := star : sk_scope.


(* reprise of Extensional_Programs *) 

(* Fixpoints *) 

Definition omega := Sop @ (Kop @ (Sop @ Iop)) @ (Sop @ Iop @ Iop).
(*
  \(\(App (Ref 0) (App (App (Ref 1) (Ref 1)) (Ref 0)))).
*) 
Definition Yop := App omega omega. 

Lemma y_red: forall f, sk_red (Yop @ f) (f @ (Yop @ f)).
Proof.
  (* delicate proof since rhs is not normal *)
  intros; unfold Yop at 1; unfold omega at 1.
  aptac. eapply2 succ_red. zerotac.
  aptac;
    [ aptac;
      [ eapply2 succ_red
      | instantiate(1:= Yop); eapply2 succ_red; aptac; eval_tac
      | zerotac]
    | zerotac
    |  eapply2 succ_red; aptac; [  eval_tac | zerotac | aptac; [ succtac | |]; zerotac]
    ]. 
Qed. 
  

(* Waiting *) 

Definition wait M N := Sop @ (Sop @ (Kop @ M) @ (Kop @ N)) @ Iop.
Definition Wop := \"x" (\"y" (wait (Ref "x") (Ref "y"))). 

Lemma wait_red: forall M N P, sk_red (wait M N @ P) (M@ N @ P).
Proof.  intros; cbv; repeat (eapply2 succ_red). Qed. 

 
Lemma w_red1 : forall M N, sk_red (Wop @ M @ N) (wait M N).
Proof.  eval_tac.  Qed.    

Lemma w_red : forall M N P, sk_red (Wop @ M@ N @ P) (M@ N @ P).
Proof.  eval_tac.  Qed.

Definition wait2 M N x :=  Sop @ (Sop @ (Sop @ (Kop @ M) @ (Kop @ N)) @ (Kop @ x)) @ Iop.

Lemma wait2_red: forall M N x y, sk_red (wait2 M N x @ y) (M @ N @ x @ y).
Proof. eval_tac. Qed. 


Ltac occurstac := refold occurs; rewrite ? orb_true_r; cbv; auto 1000 with *; fail. 
 
Ltac startac_true x := rewrite (star_occurs_true _ _ x); [| occurstac ]. 
Ltac startac_false x :=  rewrite (star_occurs_false _ x); [ | occurstac].
Ltac startac x := repeat (startac_false x || startac_true x || rewrite star_id).

 
(* Fixpoint Functions *)


  
Definition omega2 := \"w" (\"f" (Ref "f" @ (wait2 (Ref "w") (Ref "w") (Ref "f")))).

Definition Z := wait2 omega2 omega2.

Theorem Z_red: forall f x, sk_red (Z f @ x) (f @ (Z f) @ x).
Proof.  intros; cbv; trtac; repeat (eapply preserves_app_sk_red; trtac). Qed.


(*** Booleans *) 

Definition KI := Kop @ Iop. 
Definition tt := Kop.
Definition ff := KI.


(*** Pairing and projections *)



Definition pairL x y := Sop @ (Sop @ Iop @ (Kop@ x)) @ (Kop@ y).
Definition fstL := Sop @ Iop @ (Kop @ Kop). 
Definition sndL := Sop @ Iop @ (Kop @ KI). 

Theorem fstL_red: forall x y, sk_red (fstL @ (pairL x y)) x. Proof. eval_tac.  Qed. 
Theorem sndL_red: forall x y, sk_red (sndL @ (pairL x y)) y. Proof. eval_tac. Qed. 


(*** Function composition *)

(* given f_i : Nat ^m -> Nat and g : Nat^n -> N, define g (f_i) : Nat^m -> Nat by 
g(f_i) (x_j) = g (f_i(x_j)) 
 *)

Lemma fold_left_app_preserves_red:
  forall xs f1 f2, sk_red f1 f2 -> sk_red (fold_left App xs f1) (fold_left App xs f2).
Proof.  induction xs; intros; simpl; eauto; eapply IHxs; eapply preserves_appl_sk_red; auto. Qed. 


Fixpoint Kn n := (* Kn n g xs = g if length xs = n *) 
  match n with
  | 0 => Iop
  | S n1 => \"x" (Kop @ (Kn n1 @ Ref "x"))
  end. 

Fixpoint compose1 n := (* compose1 g f xs = g xs (f xs)  if length xs = n *) 
  match n with
  | 0 => Iop
  | S n1 => \"g" (\"f" (\"x" (compose1 n1 @ (Ref "g" @ Ref "x") @ (Ref "f" @ Ref "x"))))
  end.

Fixpoint compose0 m n := (* compose0 m n g fs xs = g xs (map fs xs) if length fs = m and length xs = n *) 
  match m with
  | 0 => Iop 
  | S m1 => \"g" (\"f" (compose0 m1 n @ (compose1 n @ Ref "g" @ Ref "f")))
  end.

Definition compose m n := Sop @ (Kop@ compose0 m n) @ (Kn n) . (* \"x" (compose0 m n @ (Kn n @ Ref "x")).  *) 

Lemma Kn_closed: forall n x, occurs x (Kn n) = false.
Proof.  induction n; intros; simpl; auto; rewrite  IHn; simpl; auto. Qed. 

  
Lemma Kn_red: forall xs g, sk_red (fold_left App xs (Kn (List.length xs) @ g)) g. 
Proof.
  induction xs; intros; simpl; auto. repeat trtac. rewrite Kn_closed; simpl.  
  eapply transitive_red. eapply fold_left_app_preserves_red. 
  aptac. trtac. trtac.  trtac. eapply IHxs. 
Qed.


Lemma compose1_closed: forall n x, occurs x (compose1 n) = false. 
Proof.
  induction n; intros; simpl; auto; rewrite ! orb_true_r;
    rewrite (star_occurs_false _ "x"); eauto;
      refold star; repeat (simpl; rewrite ! IHn); auto.
Qed.
       

Proposition compose1_red:
  forall xs g f,
    sk_red (fold_left App xs (compose1 (List.length xs) @ g @ f)) ((fold_left App xs g) @ (fold_left App xs f)).
Proof.
  induction xs; intros; simpl; auto. trtac.
  rewrite compose1_closed.  refold orb. 
  eapply transitive_red. eapply fold_left_app_preserves_red. 
  rewrite (star_occurs_false _ "x"); eauto. 2: eapply compose1_closed.
  rewrite eta_red. 2: simpl; rewrite compose1_closed; auto.
  rewrite star_occurs_true. 2: simpl; rewrite ! orb_true_r; auto. 2: discriminate. 
  rewrite (star_occurs_false). 2: auto.
  rewrite eta_red. 2: simpl; rewrite compose1_closed; auto.
  trtac. eapply IHxs. 
Qed. 


 Lemma compose0_closed: forall m n x, occurs x (compose0 m n) = false. 
Proof.
  induction m; intros; simpl; auto; rewrite ! orb_true_r. 
  rewrite ! compose1_closed; simpl. rewrite ! compose1_closed; simpl.
  rewrite star_occurs_false. 2: eauto.
  simpl. rewrite IHm. simpl. rewrite ! IHm.
  simpl; rewrite compose1_closed; auto. 
Qed.

Proposition compose0_red:
  forall fs xs g,
    sk_red (fold_left App xs (fold_left App fs (compose0 (List.length fs) (List.length xs) @ g)))
           (fold_left App (map (fun f => (fold_left App xs f)) fs) (fold_left App xs g)).
Proof.
  induction fs; intros; simpl; auto.
  (* 2 *)
  repeat trtac;  eapply fold_left_app_preserves_red; repeat trtac. 
  (* 1 *)
  rewrite ! compose0_closed. rewrite ! compose1_closed. unfold orb.  
  eapply transitive_red. eapply fold_left_app_preserves_red. eapply fold_left_app_preserves_red.
  rewrite (star_occurs_false _ "f"). 2: eapply compose0_closed.
  unfold negb.
  rewrite star_occurs_true. 2: simpl; rewrite ! orb_true_r; auto.  2: discriminate. 
  trtac.  
  eapply transitive_red. eapply fold_left_app_preserves_red.  eapply fold_left_app_preserves_red. 
  rewrite star_occurs_false.   2: simpl;   rewrite ! compose0_closed; auto. trtac.
  eapply transitive_red. eapply IHfs.
  rewrite eta_red. 2: eapply compose1_closed. eapply fold_left_app_preserves_red.
  eapply compose1_red. 
Qed.

Theorem compose_red:
  forall fs xs g,
    sk_red (fold_left App xs (fold_left App fs (compose (List.length fs) (List.length xs) @ g))) 
          (fold_left App (map (fun f => (fold_left App xs f)) fs) g).
Proof.
  intros; unfold compose; eapply transitive_red. eapply fold_left_app_preserves_red.
   eapply fold_left_app_preserves_red.
   eapply transitive_red. trtac. trtac. 
   eapply transitive_red. eapply compose0_red.    
   eapply fold_left_app_preserves_red. eapply Kn_red. 
Qed.




(*** Zero, successor and numerals as iterators *) 

Definition zero := KI.

Definition succ1 := Eval cbv in \"n" (\"f" (\"x" (Ref "f" @ (Ref "n" @ Ref "f" @ Ref "x")))). 


Theorem succ1_red: forall n f x, sk_red (succ1 @ n @ f @ x) (f @ (n @ f @ x)).
Proof.  eval_tac. Qed. 
  
Definition num k := iter k (fun x => succ1 @ x) zero.

 
Lemma num_iterates: forall m f x, sk_red (num m @ f @ x) (iter m (App f) x).
Proof.
  induction m; intros; unfold num; fold num; simpl; eauto; repeat trtac.    eval_tac.
  unfold succ1 at 1; trtac.  eapply preserves_appr_sk_red; eapply IHm.
Qed.


Lemma num_succ_red: forall k, sk_red (num (S k)) (succ1 @ (num k)).
Proof. eval_tac. Qed.  

  
(*** The zero test and conditionals *)


Definition isZero := \"n" (Ref "n" @ (Kop@ ff) @ tt). 

Theorem isZero_zero: sk_red (isZero @ zero) tt.
Proof.  eval_tac. Qed.

Theorem isZero_succ: forall n, sk_red (isZero @ (succ1 @ n)) ff.
Proof.  eval_tac. Qed.


Definition cond := Iop. 

Theorem cond_false : forall x y, sk_red (cond @ ff @ x @ y) y.
Proof. eval_tac. Qed. 

Theorem cond_true : forall x y, sk_red (cond @ tt @ x @ y) x.
Proof. eval_tac. Qed. 

                              
(*** The predecessor function  - underpinning primitive recursion *) 
  
Definition PZero := pairL zero zero.  (*   \ (Var 0 @ (num 0) @ (num 0)). *)  
Definition PSucc := \"p" (pairL (sndL @ Ref "p") (succ1 @ (sndL @ Ref "p"))). 
Definition predN := \"n" (fstL @ (Ref "n" @ PSucc @ PZero)).

Lemma PSucc_red: forall m n,  sk_red (PSucc @ (pairL m n)) (pairL n (succ1 @ n)).
Proof. eval_tac. Qed.


Lemma pred_aux:  forall k, sk_red (iter k (App PSucc) PZero) (pairL (num (Nat.pred k)) (num k)).
Proof.
  induction k; intros; repeat eexists; simpl; [
    eapply zero_red |
    aptac; [ trtac | eapply IHk | eapply PSucc_red]].
Qed.

 
Theorem pred_red: forall k,  sk_red (predN @ (num k)) (num (pred k)). 
Proof.
  intros; unfold predN.
  rewrite star_occurs_true. 2: simpl; auto. 2: discriminate. trtac.
  startac "n". trtac. unfold fstL. trtac.
  rewrite star_occurs_true. 2: simpl; auto. 2: discriminate. trtac.
  rewrite star_occurs_true. 2: simpl; auto. 2: discriminate. trtac.
  rewrite star_id.   trtac.
  rewrite ! star_occurs_false. 2,3: cbv; auto.
  aptac. aptac.  aptac. trtac. trtac. trtac. trtac. trtac. trtac.
  aptac. eapply num_iterates. trtac. aptac. eapply pred_aux. trtac. 
  unfold pairL. trtac.   
Qed.



(*** Primitive Recursion *)



Definition primrec0_abs :=
  \"x"
          (\"n"
            (isZero @ (Ref "n")
                    @ Ref "g"
                    @ (Ref "h" @ (predN @ Ref "n") @ (Ref "x" @ (predN @ Ref "n")))                  
          )).


Lemma primrec0_val:
  primrec0_abs =    Sop @ (Kop @ (Sop @ (Sop @ isZero @ (Kop @ Ref "g")))) @
  (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ Ref "h") @ predN))) @ (Sop @ (Sop @ (Kop @ Sop) @ Kop) @ (Kop @ predN))).
Proof.
  unfold primrec0_abs.
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_false. 2: cbv; auto. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite eta_red.   2: cbv; auto.
  rewrite star_occurs_false. 2: cbv; auto. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_false. 2: cbv; auto. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite eta_red.   2: cbv; auto.
  rewrite star_occurs_false. 2: cbv; auto. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_false. 2: cbv; auto. 
  rewrite (star_occurs_false _ "n"). 2: cbv; auto. 
  rewrite eta_red.   2: cbv; auto.
  rewrite eta_red.   2: cbv; auto.
  rewrite star_occurs_false. 2: cbv; auto. 
  auto.
Qed.


Definition primrec0 g h :=
  Z  (Sop @ (Kop @ (Sop @ (Sop @ isZero @ (Kop @ g)))) @
          (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ h) @ predN))) @ (Sop @ (Sop @ (Kop @ Sop) @ Kop) @ (Kop @ predN)))).


Lemma primrec0_red_zero :
  forall g h, sk_red (primrec0 g h @ zero) g.
Proof.
  intros; unfold primrec0. eapply transitive_red. eapply Z_red. trtac. aptac. aptac. cbv; trtac.
  trtac. trtac. trtac. trtac. 
Qed. 


Lemma primrec0_red_succ :
  forall k g h, sk_red (primrec0 g h @ (num (S k))) (h @ (num k) @ (primrec0 g h @ (num k))).
Proof.
  intros; unfold primrec0.  eapply transitive_red. eapply Z_red. trtac. aptac. aptac. cbv; trtac.
  trtac. trtac. trtac. trtac. 
  eapply preserves_app_sk_red. eapply preserves_app_sk_red. trtac. 
  eapply pred_red. 
  eapply preserves_app_sk_red. trtac. 
  eapply pred_red. 
Qed.
  

Definition primrec g h xs := primrec0 (fold_left App xs g) (fold_left App xs h).


Theorem primrec_red_zero:
  forall xs g h, sk_red (primrec g h xs @ zero) (fold_left App xs g). 
Proof.  intros; eapply primrec0_red_zero. Qed. 


Theorem primrec_red_succ:
  forall xs g h k,
    sk_red (primrec g h xs @ (num (S k))) (fold_left App xs h @ (num k) @ (primrec g h xs @ (num k))). 
Proof.  intros; simpl; auto; eapply primrec0_red_succ. Qed. 


  
(*** Minimisation *)


Definition minrec_abs := \"r0" (\"r1" (Ref "f" @ Ref "r1" @ Ref "r1" @ (Ref "r0" @ (succ1 @ (Ref "r1"))))).

Lemma min_rec_abs_val :
  minrec_abs = Sop @ (Kop @ (Sop @ (Sop @ Ref "f" @ Iop))) @
  (Sop @ (Sop @ (Kop @ Sop) @ Kop) @ (Kop @ (Sop @ (Sop @ (Kop @ Sop) @ Kop)))).

Proof.
  unfold minrec_abs.
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_true. 2: cbv; auto. 2: discriminate. 
  rewrite star_occurs_false. 2: cbv; auto.
  unfold star at 1; rewrite String.eqb_refl; simpl.
  auto. 
 Qed. 


  

Definition minrec0 f := Z   ( Sop @ (Kop @ (Sop @ (Sop @ f @ Iop))) @
  (Sop @ (Sop @ (Kop @ Sop) @ Kop) @ (Kop @ (Sop @ (Sop @ (Kop @ Sop) @ Kop))))). 

  
Lemma minrec0_found: forall f n, sk_red (f @ n) tt -> sk_red (minrec0 f @ n) n. 
Proof.
  intros; eapply transitive_red; [ eapply Z_red | trtac].
  aptac. aptac. eauto. trtac. trtac. trtac. trtac. 
Qed.


Lemma minrec0_next: forall f n, sk_red (f @ n) ff -> sk_red (minrec0 f @ n) (minrec0 f @ (succ1 @ n)).
Proof.
  intros; eapply transitive_red; [ eapply Z_red |  trtac ].
  aptac. aptac. eauto. trtac. trtac. trtac. unfold ff, KI.  trtac. 
Qed.



Definition minrec f xs := minrec0 (fold_left App xs f).


Theorem minrec_found:
  forall f xs n, sk_red (fold_left App xs f @ n) tt -> sk_red (minrec f xs @ n) n. 
Proof. intros; eapply minrec0_found; eauto. Qed.

Theorem minrec_next:
  forall f xs n, sk_red (fold_left App xs f @ n) ff -> sk_red (minrec f xs @ n) (minrec f xs @ (succ1 @ n)).
Proof. intros; eapply minrec0_next; eauto. Qed.




(*** Simple Subtypes *)

Inductive sktype : Set :=
| Bool
| Nat
| Omega2 
| Funty : sktype -> sktype -> sktype
  .



(* Type derivation *)

Fixpoint get x (gamma: list (string * sktype)) :=
  match gamma with
  | (s,ty)::gamma1 => if (s =? x)%string then Some ty else get x gamma1
  | _ => None
  end.

Definition fix_ty ty := Funty (Funty ty ty) ty. 


Inductive subtype : sktype -> sktype -> Prop :=
  (* a pre-order *) 
| sub_zero : forall ty, subtype ty ty
| sub_trans : forall ty1 ty2 ty3, subtype ty1 ty2 -> subtype ty2 ty3 -> subtype ty1 ty3
| sub_funty : forall uty1 uty2 vty1 vty2, subtype uty2 uty1 -> subtype vty1 vty2 ->
                                          subtype (Funty uty1 vty1) (Funty uty2 vty2)
| sub_bool: forall uty, subtype Bool (Funty uty (Funty uty uty))
| sub_nat: forall uty, subtype Nat (Funty (Funty uty uty) (Funty uty uty))
| sub_omega2: forall uty vty, subtype Omega2 (Funty Omega2 (fix_ty (Funty uty vty)))
.

Ltac sub_fun_tac := (eapply sub_funty; [ eapply sub_zero | ]) || (eapply sub_funty; [ | eapply sub_zero ]) .


Inductive derive: list (string * sktype) -> SK -> sktype -> Prop :=
| derive_ref : forall gamma x uty ty, get x gamma = Some uty -> subtype uty ty -> derive gamma (Ref x) ty
| derive_S : forall gamma uty vty wty ty,
    subtype (Funty (Funty uty (Funty vty wty)) (Funty (Funty uty vty) (Funty uty wty))) ty ->
    derive gamma Sop ty
| derive_K : forall gamma uty vty ty, subtype (Funty uty (Funty vty uty)) ty -> 
    derive gamma Kop ty
| derive_true: forall gamma ty, subtype Bool ty -> derive gamma Kop ty
| derive_false: forall gamma ty, subtype Bool ty -> derive gamma KI ty
| derive_zero: forall gamma ty, subtype Nat ty -> derive gamma KI ty
| derive_succ: forall gamma ty, subtype (Funty Nat Nat) ty -> derive gamma succ1 ty
| derive_omega2 : forall gamma ty, subtype Omega2 ty -> derive gamma omega2 ty
| derive_app: forall gamma M N ty u, derive gamma M (Funty u ty) -> derive gamma N u -> derive gamma (M@N) ty
.

Hint Constructors subtype derive: TreeHintDb.



Lemma derive_subtype:
  forall gamma M ty1, derive gamma M ty1 -> forall ty2, subtype ty1 ty2 -> derive gamma M ty2.
Proof.  intros gamma M ty1 d; induction d; intros; auto_t. Qed. 


Lemma derive_K1: forall gamma M uty vty, derive gamma M uty -> derive gamma (Kop @M) (Funty vty uty). 
Proof.  intros; eapply derive_app; [ eapply derive_K | eauto]; auto_t. Qed. 


Theorem derive_S1 :  forall gamma f uty vty wty,
    derive gamma f (Funty uty (Funty vty wty)) -> 
    derive gamma (Sop @ f) (Funty (Funty uty vty) (Funty uty wty)). 
Proof. auto_t. Qed.

Theorem derive_S2 :  forall gamma f g uty vty wty,
    derive gamma f (Funty uty (Funty vty wty)) -> derive gamma g (Funty uty vty) -> 
    derive gamma (Sop @ f @ g) (Funty uty wty). 
Proof. auto_t. Qed. 


Theorem derive_I: forall gamma uty, derive gamma Iop (Funty uty uty). 
Proof.  intros; eapply derive_S2; eapply derive_K; auto_t.  Unshelve. apply Bool. Qed. 



Theorem derive_wait:
  forall gamma M N uty vty wty,
    derive gamma M (Funty uty (Funty vty wty)) -> derive gamma N uty -> 
    derive gamma (wait M N) (Funty vty wty). 
Proof. intros; eapply derive_S2; [ | eapply derive_I]; eapply derive_S2; eapply derive_K1; eauto. Qed.


Theorem derive_wait2:
  forall gamma M N P u1 u2 u3 ty,
    derive gamma M (Funty u1 (Funty u2 (Funty u3 ty))) ->
    derive gamma N u1 -> derive gamma P u2 -> derive gamma (wait2 M N P) (Funty u3 ty).
Proof.
  intros; eapply derive_S2. 2: eapply derive_I. 
  repeat eapply derive_S2; eapply derive_K1; eauto.
Qed.


Theorem derive_Z:
  forall gamma f uty vty, derive gamma f (Funty (Funty uty vty) (Funty uty vty)) ->
                  derive gamma (Z f) (Funty uty vty).
Proof.
  intros; eapply derive_S2. 2: eapply derive_I. eapply derive_S2. 2: eapply derive_K1; eauto. 
  eapply derive_S2; eapply derive_K1; eauto. 1,2: eapply derive_omega2. eapply sub_omega2.  eapply sub_zero. 
Qed.


Lemma derive_isZero : forall gamma, derive gamma isZero (Funty Nat Bool).
Proof.
  intros; cbv; eapply derive_S2. eapply derive_S2.
  eapply derive_subtype. eapply derive_I. eapply sub_funty. eapply sub_zero. eapply sub_nat.
  1,2: repeat eapply derive_K1; auto_t.
Qed.

Lemma derive_cond: forall gamma uty, derive gamma cond (Funty Bool (Funty uty (Funty uty uty))).
Proof. intros; eapply derive_subtype; [ eapply derive_I | eapply sub_funty; [ eapply sub_zero | auto_t]]. Qed. 

Lemma derive_pred: forall gamma, derive gamma predN (Funty Nat Nat).
Proof.
  intros; unfold predN.
  rewrite star_occurs_true.  2: cbv; auto. 2: discriminate.
  eapply derive_S2. rewrite star_occurs_false. 2: cbv; auto.
  eapply derive_K1. eapply derive_S2. eapply derive_I.  eapply derive_K1.
  eapply derive_K; eapply sub_zero. 
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_id. eapply derive_subtype. eapply derive_I. auto_t. 
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. 
  unfold PSucc, pairL. rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. eapply derive_S. eapply sub_zero. 
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. eapply derive_S1. eapply derive_I.
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. eapply derive_K. eapply sub_zero. 
  rewrite eta_red. 2: cbv; auto. cbv. eapply derive_S2. eapply derive_I. do 2 eapply derive_K1. eapply derive_I.
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. eapply derive_K. eapply sub_zero. 
  rewrite star_occurs_true.   2: cbv; auto. 2: discriminate.  eapply derive_S2.
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. eapply derive_succ. eapply sub_zero. 
  rewrite eta_red.  2: cbv; auto. 
  unfold sndL.   eapply derive_S2. eapply derive_I. eapply derive_K1.
  eapply derive_app; [ eapply derive_K | eapply derive_I]. eapply sub_zero. 
  rewrite star_occurs_false. 2: cbv; auto. eapply derive_K1. cbv.
  eapply derive_S2.  eapply derive_S2.  eapply derive_I.  eapply derive_K1.   eapply derive_zero.
  eapply sub_zero.  eapply derive_K1. eapply derive_zero. eapply sub_zero. 
Qed.



Lemma derive_compose1:
  forall gamma xtys yty ty,
    derive gamma (compose1 (Datatypes.length xtys))
           (Funty
              (fold_right Funty (Funty yty ty) xtys)
              (Funty (fold_right Funty yty xtys)
                     (fold_right Funty ty xtys)))
.
Proof.
  induction xtys; intros; simpl; auto.
  (* 2 *)
  apply derive_I.
  (* 1 *)
  rewrite ! orb_true_r.
  rewrite eta_red.  2: simpl; rewrite star_occurs_false; simpl; rewrite compose1_closed; auto. 
  rewrite star_occurs_true. 2: simpl; rewrite orb_true_r; auto. 2: discriminate.
  rewrite star_occurs_false. 2: cbv; auto.
  rewrite (star_occurs_false _ "x"). 2: eapply compose1_closed.
  rewrite eta_red.  2: simpl; rewrite compose1_closed; auto. 
  eapply derive_S2. eapply derive_K1. eapply derive_S. eapply sub_zero. 
  eapply derive_S1. eapply derive_K1. 
  eapply IHxtys.
Qed.

  

Lemma derive_compose0:
  forall gamma ftys xtys ty,
    derive gamma (compose0 (Datatypes.length ftys) (Datatypes.length xtys))
           (Funty
              (fold_right Funty ty (app xtys ftys))
              (fold_right (fun fty rty => Funty (fold_right Funty fty xtys) rty)
                          (fold_right Funty ty xtys)
                          ftys))              
.
Proof.
  induction ftys; intros; simpl; auto.
  (* 2 *)
  rewrite app_nil_r; eapply derive_I.
  (* 1 *)
  rewrite ! orb_true_r.  rewrite ! compose1_closed. unfold orb, negb.  
  rewrite fold_right_app.
  rewrite star_occurs_true. 2: simpl; rewrite ! orb_true_r; auto. 2: discriminate.
  eapply derive_S2.
  2: rewrite eta_red.   3: eapply compose1_closed.
  2: eapply derive_compose1. 
  rewrite star_occurs_false.   2: simpl; rewrite star_occurs_false; simpl; eapply compose0_closed.
  eapply derive_K1. eapply derive_S1. rewrite star_occurs_false.  2: eapply compose0_closed.
  eapply derive_K1. eapply derive_subtype. eapply IHftys.
  rewrite fold_right_app. eapply sub_zero.
Qed.


Lemma derive_Kn:
  forall xs gamma ty, derive gamma (Kn (Datatypes.length xs)) (Funty ty (fold_right Funty ty xs)).
Proof.
  induction xs; intros; simpl. 
  (* 2 *)
  eapply derive_I.
  (* 1 *)
  rewrite Kn_closed; simpl. eapply derive_S2. 2: eapply IHxs. eapply derive_K1. eapply derive_K.
  eapply sub_zero.
Qed.


Lemma derive_compose:
  forall gamma ftys xtys ty,
    derive gamma (compose (Datatypes.length ftys) (Datatypes.length xtys))
           (Funty
              (fold_right Funty ty ftys)
              (fold_right (fun fty rty => Funty (fold_right Funty fty xtys) rty)
                           (fold_right Funty ty xtys)
                          ftys))              
.
Proof.
  intros. eapply derive_S2. 2: eapply derive_Kn.
  eapply derive_K1. eapply derive_subtype. eapply derive_compose0.  rewrite fold_right_app.  eapply sub_zero.
Qed.


Lemma derive_primrec0:
  forall gamma g h ty, derive gamma g ty ->
                          derive gamma h (Funty Nat (Funty ty ty)) ->
                          derive gamma (primrec0 g h) (Funty Nat ty).
Proof.
  intros; eapply derive_Z. eapply derive_S2. eapply derive_K1. eapply derive_S1.
  eapply derive_S2. eapply derive_subtype. eapply derive_isZero. eapply sub_funty. eapply sub_zero. auto_t.
  eapply derive_K1; auto.
  eapply derive_S2. eapply derive_K1. eapply derive_S1.
  eapply derive_S2. eapply derive_K1; eauto.
  eapply derive_pred.
  eapply derive_S2. eapply derive_S2. eapply derive_K1. eapply derive_S.  eapply sub_zero. 
  eapply derive_K.  eapply sub_zero. eapply derive_K1; eauto.  eapply derive_pred.
Qed. 


Lemma derive_primrec:
  forall xs xtys gamma g h ty, derive gamma g (fold_right Funty ty xtys) ->
                               derive gamma h (fold_right Funty (Funty Nat (Funty ty ty)) xtys) ->
                                Forall2 (fun x xty => derive gamma x xty) xs xtys -> 
                                derive gamma (primrec g h xs) (Funty Nat ty).
Proof.
  intros; unfold primrec; simpl; eapply derive_primrec0.
  (* 2 *) 
  generalize xs xtys g H H1; clear. induction xs; intros; simpl in *; inv_out H1; simpl in *; auto. 
  eapply IHxs. eapply derive_app; eauto. auto.
  (* 1 *)
  generalize xs xtys g h H H0 H1; clear. induction xs; intros; simpl in *; inv_out H1; simpl in *; auto. 
  eapply IHxs; eauto; eapply derive_app; eauto.
Qed.

(* 
Lemma derive_succ1: forall gamma, derive gamma succ1 (Funty Nat Nat).
Proof. intros; eapply derive_subtype. eapply derive_S1. eapply derive_S2. eapply derive_K1. 
       eapply derive_S. eapply derive_K. eapply sub_funty. eapply sub_nat. 
*) 


Lemma derive_minrec0:
  forall gamma f, derive gamma f (Funty Nat Bool) -> derive gamma (minrec0 f) (Funty Nat Nat). 
Proof.
  intros; eapply derive_Z. replace (Sop @ (Sop @ (Kop @ Sop) @ Kop)) with succ1 at 2 by auto.
  eapply derive_S2. eapply derive_K1. eapply derive_S1.  eapply derive_S2.
  eapply derive_subtype; auto_t. eapply derive_I.  
  eapply derive_S2.
  2: eapply derive_K1; eapply derive_succ; eapply sub_zero. 
  eapply derive_S2. eapply derive_K1. 2: eapply derive_K. eapply derive_S.  eapply sub_zero.  eapply sub_zero.  
Qed.


Lemma derive_minrec:
  forall xs xtys gamma f, derive gamma f (fold_right Funty (Funty Nat Bool) xtys) ->
                          Forall2 (fun x xty => derive gamma x xty) xs xtys -> 
                          derive gamma (minrec f xs) (Funty Nat Nat). 
Proof.
  intros; unfold minrec. eapply derive_minrec0.
  generalize xs xtys f H H0; clear. induction xs; intros; simpl in *; inv_out H0; simpl in *; auto. 
  eapply IHxs. eapply derive_app; eauto. auto.
Qed.


Ltac inv_succ1_tac := repeat (match goal with H: sk_red1 _ _ |- _ => inv_out H end).

Lemma subtype_from_funty:
  forall uty vty ty, subtype (Funty uty vty) ty ->
                     exists uty2 vty2, ty = Funty uty2 vty2 /\ subtype uty2 uty /\ subtype vty vty2.
Proof.
  cut(forall ty1 ty2,
         subtype ty1 ty2 ->
         forall uty vty, ty1 = Funty uty vty ->
                         exists uty2 vty2, ty2 = Funty uty2 vty2 /\ subtype uty2 uty /\ subtype vty vty2).
  intros; eauto. 
  intros ty1 ty2 s; induction s; intros; subst; auto_t; try discriminate.
  (* 2 *)
  eelim IHs1; intros; eauto; split_all. eelim IHs2; intros. 2:eauto. split_all. repeat eexists; eauto; auto_t. 
  inv_out H; repeat eexists; eauto.
Qed.

Lemma subtype_of_funty:
  forall uty1 vty1 uty2 vty2,
    subtype (Funty uty1 vty1) (Funty uty2 vty2) -> subtype uty2 uty1 /\ subtype vty1 vty2.
Proof. intros; eelim subtype_from_funty; intros; eauto; split_all. Qed.

Lemma subtype_from_bool :
  forall ty, subtype Bool ty -> ty = Bool \/ exists uty, subtype (Funty uty (Funty uty uty)) ty. 
Proof.
  cut(forall ty1 ty2, subtype ty1 ty2 -> ty1 = Bool ->
                      ty2 = Bool \/ exists uty, subtype (Funty uty (Funty uty uty)) ty2). 
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; auto_t; try discriminate.   
  eelim IHs1; intros; eauto; split_all; right; exists x; auto_t.
Qed.


Lemma subtype_from_nat :
  forall ty, subtype Nat ty -> ty = Nat \/ exists uty, subtype (Funty (Funty uty uty) (Funty uty uty)) ty. 
Proof.
  cut(forall ty1 ty2, subtype ty1 ty2 -> ty1 = Nat ->
                      ty2 = Nat \/ exists uty, subtype (Funty (Funty uty uty) (Funty uty uty)) ty2). 
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; auto_t; try discriminate.   
  eelim IHs1; intros; eauto; split_all; right; exists x; auto_t.
Qed.


Lemma subtype_from_omega2 :
  forall ty, subtype Omega2 ty ->
             ty = Omega2 \/ exists uty vty, subtype (Funty Omega2 (fix_ty (Funty uty vty))) ty.
Proof.
  cut(forall ty1 ty2, subtype ty1 ty2 -> ty1 = Omega2 ->
                      ty2 = Omega2 \/ exists uty vty, subtype (Funty Omega2 (fix_ty (Funty uty vty))) ty2).      
  intros; eauto.
  intros ty1 ty2 s; induction s; intros; subst; auto_t; try discriminate.   
  eelim IHs1; intros; eauto; split_all; right; exists x; auto_t.
Qed.



  
Theorem SK_reduction_preserves_typing:
  forall gamma M ty, derive gamma M ty -> forall N, sk_red1 M N -> derive gamma N ty. 
Proof.
  intros gamma M ty d;  induction d; intros.
  1-8: inv_succ1_tac.
  inv_out H.
  (* 4 *)
  inv_out d1.
  (* 5 *)
  eelim subtype_from_omega2; intros; eauto; split_all.
  eelim subtype_of_funty; intros; eauto; split_all.
  eapply derive_subtype; eauto.
  eapply derive_app. eapply derive_app. 
  eapply derive_K1.
  eapply derive_S1.
  eapply derive_I.
  eauto.
  eapply derive_app. 2: eauto. eapply derive_S2. eapply derive_S2.  eapply derive_K1. eapply derive_S.
  eapply sub_zero.
  eapply derive_S2. eapply derive_K1.  eapply derive_S1. eapply derive_K1. eapply derive_S.
  eapply sub_zero.
  eapply derive_S2. eapply derive_S2.  eapply derive_K1. eapply derive_S.  eapply sub_zero.
  eapply derive_S2. eapply derive_K1. eapply derive_K.  eapply sub_zero.
  eapply derive_S2. eapply derive_K1. eapply derive_S.  eapply sub_zero.
  eapply derive_S2. eapply derive_S2.  eapply derive_K1. eapply derive_S.  eapply sub_zero.
  eapply derive_K.  do 2 sub_fun_tac. eapply sub_trans; eauto. eapply sub_omega2. 
  eapply derive_K.  do 2 sub_fun_tac. auto.
  eapply derive_K1. eapply derive_K. eapply sub_zero. 
  eapply derive_K1. eapply derive_K1. eapply derive_I.
  (* 4 *)
  inv_out H2. eelim subtype_of_funty; intros; eauto; split_all.
  eelim subtype_from_nat; intros; eauto; split_all.   
  eelim subtype_of_funty; intros; eauto; split_all.   
  eapply derive_app. eapply derive_app. 
  eapply derive_S2. eapply derive_K1.  eapply derive_S.  do 2 sub_fun_tac. eauto.
  eapply derive_K. do 2 sub_fun_tac. eauto. eauto.
  eapply derive_app; eauto. eapply derive_subtype; eauto. eapply sub_trans; eauto.
  eapply sub_trans. eapply sub_nat. sub_fun_tac. auto.
  inv_out H3.
  eelim subtype_of_funty; intros; eauto.
  eelim subtype_of_funty; intros; eauto.
  eelim subtype_of_funty; intros; eauto.
  eapply derive_subtype; eauto.
  repeat eapply derive_app; eauto; eapply derive_subtype; eauto; eapply sub_trans; eauto.
  eapply sub_funty; eauto. eapply sub_zero. sub_fun_tac. auto. 
  (* 3 *)
  inv_out d1.
  (* 5 *)
  eelim subtype_from_bool; intros; eauto; split_all.
  eelim subtype_of_funty; intros; eauto; split_all.
  eapply derive_subtype; eauto. eapply derive_I. 
  (* 4 *)
  eelim subtype_from_nat; intros; eauto; split_all.
  eelim subtype_of_funty; intros; eauto; split_all.
  eapply derive_subtype; eauto. eapply derive_I. 
  (* 3 *)
  inv_out H2. eelim subtype_of_funty; intros; eauto; split_all.
  eelim subtype_of_funty; intros; eauto; split_all.   
  eapply derive_subtype; eauto; auto_t.
  eelim subtype_from_bool; intros; eauto; split_all.
  eelim subtype_of_funty; intros; eauto; split_all.
  eelim subtype_of_funty; intros; eauto; split_all.
  eapply derive_subtype; eauto. auto_t.
  (* 2 *)
  eapply derive_app. eapply IHd1; eauto. auto.
  (* 1 *)
  eapply derive_app. eauto. eapply IHd2; eauto.
Qed.

(* 
Fixpoint is_subtype n ty1 ty2 :=
  match n with
  | 0 => false
  | S n1 => 
    match ty1 with
    | Bool =>
      match ty2 with
      | Bool => true
      | Funty uty2 (Funty vty2 wty2) => is_subtype n1 uty2 wty2 && is_subtype n1 vty2 wty2
      | _ => false
      end
    | Nat =>
      match ty2 with
      | Nat => true
      | Funty uty2 (Funty vty2 wty2) => is_subtype n1 uty2 (Funty wty2 wty2) && is_subtype n1 vty2 wty2
      | _ => false
      end
     | Omega2 =>
      match ty2 with
      | Omega2 => true
      | Funty uty2 (Funty vty2 (Funty wty2 xty2) =>
        is_subtype n1 uty2 Omega2 &&
        is_subtype n1 vty2 (Funty (Funty wty2 wty3) (Funty wty2 wty3)) &&
        is_subtype n1 (Funty uty3 vty3) wty2 
      | _ => false
      end
     | Funty uty1 vty1 =>
       match ty2 with
       | Funty uty2 vty2 => is_subtype n1 uty2 uty1 && is_subtype n1 vty1 vty2
       | _ => false
       end
    end
  end.

Lemma is_subtype_is_subtype: forall n ty1 ty2, is_subtype n ty1 ty2 = true -> subtype ty1 ty2. 
Proof.
  induction n; intros; inv_out H. 
    caseEq ty1; caseEq ty2; intros; subst; try discriminate; auto_t;  
      caseEq s0; intros; subst; try discriminate. 
    (* 7 *)
    rewrite andb_true_iff in *; split_all.
    eapply sub_trans. eapply sub_bool.
    eapply sub_funty. 2: eapply sub_funty. 3: eapply sub_zero. 1,2:  eapply IHn; eauto.
    (* 6 *) 
    rewrite andb_true_iff in *; split_all.
    eapply sub_trans. eapply sub_nat.
    eapply sub_funty. 2: eapply sub_funty. 3: eapply sub_zero. 1,2:  eapply IHn; eauto.
    (* 5 *) 
   rewrite andb_true_iff in *; split_all.
    eapply sub_trans. eapply sub_omega2.
    eapply sub_funty. 2: eapply sub_funty. 3: eapply sub_zero. 1,2:  eapply IHn; eauto.
    (* 5 *) 
    (* 3 *)
    sub_fun_tac. eapp
Theorem subtype_decidable: forall ty1 ty2, subtype ty1 ty2 \/ ~ subtype ty1 ty2.
Proof.
  induction ty1; intros; subst. 

*) 
