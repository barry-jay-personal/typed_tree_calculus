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
(*                 Rewriting Theorems                                 *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Lia Bool List String.
Require Import terms. 


Set Default Proof Using "Type".

Open Scope string_scope.


(* new theorems that require rewriting *)


(* Confluence *)

(* Simultaneous Reduction *) 


Inductive s_red1 : Tree -> Tree -> Prop :=
| ref_sred : forall i, s_red1 (Ref i) (Ref i)
| node_sred : s_red1 △ △
| k_sred : forall M M' N, s_red1 M M' -> s_red1 (△@△@M@N) M' 
| s_sred: forall (M M' N N' P P': Tree), s_red1 M M' -> s_red1 N N' -> s_red1 P P' ->
                                         s_red1 (△@(△@P)@M@N) (P'@N'@(M'@N'))
| tl_sred : forall (P P' Q M: Tree), s_red1 P P' -> 
                                            s_red1 (△@(△@P@Q)@M@Node) P'
| ts_sred : forall (P Q Q' M N N': Tree), s_red1 Q Q' -> s_red1 N N' ->
                                            s_red1 (△@(△@P@Q)@M@(Node @ N)) (Q' @ N')
| tf_sred : forall (P Q M M' N1 N1' N2 N2': Tree), s_red1 M M' -> s_red1 N1 N1' -> s_red1 N2 N2' -> 
                                            s_red1 (△@(△@P@Q)@M@(Node @ N1 @ N2)) (M' @ N1' @ N2')
| app_sred : forall M M' N N', s_red1 M M' -> s_red1 N N' -> s_red1 (M@N) (M'@N')  
.
Hint Constructors s_red1 : TreeHintDb. 

Lemma s_red_refl: forall M, s_red1 M M.
Proof. induction M; intros; auto with TreeHintDb. Qed. 

Hint Resolve s_red_refl: TreeHintDb. 
     
Definition s_red := multi_step s_red1.

Lemma preserves_appl_s_red : preserves_appl s_red.
Proof. apply preserves_appl_multi_step. red; auto with *. Qed.

Lemma preserves_appr_s_red : preserves_appr s_red.
Proof. apply preserves_appr_multi_step. red; auto with *. Qed.

Lemma preserves_app_s_red : preserves_app s_red.
Proof. apply preserves_app_multi_step;  red; auto with *. Qed.


Definition implies_red (red1 red2: Tree-> Tree-> Prop) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof.
  red. intros red1 red2 IR M N R; induction R; split_all. apply zero_red. apply transitive_red with N; auto.
Qed. 

Definition diamond (red1 red2 : Tree -> Tree -> Prop) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof.  unfold diamond; intros red1 red2 d M N r1 P r2; elim (d M P r2 N r1); intros x ?. exists x; split_all.
Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof.
  intros red1 red2 d;  apply diamond_flip; 
    intros M N r; induction r; intros P0 r0; auto_t; 
      elim (d M P0 r0 N); auto; intros x (?&?); elim(IHr d x); split_all.
  exists x0; split; auto_t.
Qed. 


Definition diamond_star (red1 red2: Tree -> Tree -> Prop) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
  intros red1 red2 d M N r; induction r; intros P0 r0; auto_t;
    elim(d M P0 r0 N); auto; intros x (?&?);  
      elim(IHr d x); auto; intros x0 (?&?).  exists x0; split; auto_t. eapply2 transitive_red.
Qed. 


Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
  intros red1 red2 d M N r; induction r as [ | red1 P P1 Q H]; intros P0 ?; auto_t;
    elim(diamond_strip red1 red2 d P P1 H P0); auto; intros x (?&?);
      elim(IHr d x); auto; intros x0 (?&?); exists x0; split; auto_t.
Qed. 

Hint Resolve diamond_tiling: TreeHintDb. 




Ltac inv red := 
match goal with 
| H: multi_step red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red △ _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: red △ _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ △ |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: red _ △ |- _ => inversion H; clear H; inv red
| _ => subst; auto_t
 end.




Theorem diamond_s_red1_s_red1 : diamond s_red1 s_red1. 
Proof.  
  red; intros M N OR; induction OR; intros R s0.
  (* 8 *) 
  inv s_red1.
  inv s_red1.
  (* 6 *)
  inv s_red1. eelim IHOR; intros. 2: eapply H8. split_all.   exists x; auto_t.
  (* 5 *)
  inv s_red1;
  eelim IHOR1; intros; eauto;
  eelim IHOR2; intros; eauto;
  eelim IHOR3; intros; eauto;
    split_all;   repeat eexists.
  1-3:   repeat eapply app_sred; eauto.
  auto_t. 
  (* 4 *)
  inversion s0; subst; clear s0.
  eelim IHOR; intros; eauto.
  inv_out H3.  clear OR; inv s_red1.  eelim IHOR; intros.  2: eauto. split_all. exists x; split; eauto; auto_t. 
  (* 3 *)
  clear OR1 OR2. inv s_red1.
  eelim IHOR1; intros; eauto; split_all. 
  eelim IHOR2; intros; eauto; split_all. exists (x @ x0); split; auto_t.
  eelim IHOR1; intros; eauto; split_all. 
  eelim IHOR2; intros; eauto; split_all. exists (x @ x0); split; auto_t.
  (* 2 *) 
  clear OR1 OR2 OR3. inv s_red1.
  eelim IHOR1; intros; eauto; split_all. 
  eelim IHOR2; intros; eauto; split_all.
  eelim IHOR3; intros; eauto; split_all.
  exists (x @ x0 @ x1); split; auto_t.
  eelim IHOR1; intros; eauto; split_all. 
  eelim IHOR2; intros; eauto; split_all.
  eelim IHOR3; intros; eauto; split_all.
  exists (x @ x0 @ x1); split; auto_t.
  (* 1 *)
 inv_out s0. 
  (* 6 *)
  inv s_red1. 
  eelim IHOR1; intros.  2: eapply app_sred. 2: auto_t. 2: eapply H2. split_all.
  inv s_red1.   inv_out H14. exists N'1; eexists; eauto; auto_t.
  (* 5 *)
  inv s_red1. 
  eelim IHOR1; intros.   2: eapply app_sred. 3: eapply H1.
  2: eapply app_sred. 2: auto_t.
  2: eapply app_sred. 2: auto_t.
  2: eapply H4. 
  split_all.
  inv s_red1.   inv_out H21.
  eelim IHOR2; intros.   2: eapply H2. split_all.
  exists (N'5 @ x @ (N'2 @ x)); split; auto_t.
  (* 4 *)
  inv s_red1.
  eelim IHOR1; intros. 2: eapply app_sred; eauto; eapply app_sred; eauto. 2: auto_t.
  2: eapply app_sred; eauto; eapply app_sred. 2: auto_t. 2: eapply H2. split_all. inv s_red1. inv_out H24. 
  exists N'5; split; auto_t.
  (* 3 *)
  eelim IHOR2; intros. 2: eapply app_sred; auto_t. split_all. inv s_red1. 
  eelim IHOR1; intros. 2: repeat eapply app_sred; try eapply node_sred.  3: eapply H1. 2,3: eauto. split_all.
  inv s_red1. inv_out H27. 
  exists (N'7 @ N'1); split; auto_t.
  (* 2 *)
  eelim IHOR2; intros. 2: repeat eapply app_sred; try eapply node_sred;  eauto. split_all. inv s_red1. 
  eelim IHOR1; intros. 2: repeat eapply app_sred; try eapply node_sred.  4: eapply H1. 2,3: eauto. split_all.
  inv s_red1. inv_out H29. 
  exists (N' @ N'1 @ N'0); split; auto_t.
  (* 1 *)
  eelim IHOR2; intros. 2: eapply H3. split_all. 
  eelim IHOR1; intros. 2: eapply H1. split_all.
  exists (x0 @ x); split; auto_t. 
Qed.

  
Hint Resolve diamond_s_red1_s_red1: TreeHintDb.

Lemma diamond_s_red1_s_red : diamond s_red1 s_red.
Proof. apply diamond_strip; auto_t. Qed. 

Lemma diamond_s_red : diamond s_red s_red.
Proof.  apply diamond_tiling; auto_t. Qed. 
Hint Resolve diamond_s_red: TreeHintDb.



Lemma t_red1_to_s_red1 : implies_red t_red1 s_red1. 
Proof.  intros M N R; induction R; split_all; auto_t. Qed. 


Lemma t_red_to_s_red: implies_red t_red s_red. 
Proof. 
apply implies_red_multi_step; red; intros; eapply succ_red; [eapply2 t_red1_to_s_red1 | zerotac].  
Qed. 

Lemma to_t_red_multi_step: forall red, implies_red red t_red -> implies_red (multi_step red) t_red. 
Proof. 
intros red B M N R; induction R; intros; [ zerotac |];
assert(t_red M N) by (apply B; auto); apply transitive_red with N; [ | apply IHR] ; auto. 
Qed. 


Lemma s_red1_to_t_red: implies_red s_red1 t_red .
Proof. 
  intros M N OR; induction OR; intros; zerotac;
    try (apply preserves_app_t_red; auto; fail).  
    eapply succ_red. auto_t. eauto. 
    eapply transitive_red. repeat eapply preserves_app_t_red. 1,2: eapply zero_red. 1-3: eauto. auto_t.
    eapply transitive_red. repeat eapply preserves_app_t_red. 1,2,4,5,6: eapply zero_red. eauto. auto_t.
    eapply transitive_red. repeat eapply preserves_app_t_red. 1,2,3,5,6: eapply zero_red. 1,2: eauto. auto_t.
    eapply transitive_red. repeat eapply preserves_app_t_red. 1,2,3,4,6: eapply zero_red. 1-3: eauto. auto_t.
Qed.


Hint Resolve s_red1_to_t_red: TreeHintDb.

Lemma s_red_to_t_red: implies_red s_red t_red. 
Proof. eapply2 to_t_red_multi_step. Qed.


Lemma diamond_t_red: diamond t_red t_red. 
Proof. 
red; intros. 
assert(rMN: s_red M N) by (apply t_red_to_s_red; auto_t).  
assert(s_red M P) by (apply t_red_to_s_red; auto_t).  
elim(diamond_s_red M N rMN P); auto.  intros x (?&?); exists x; split; eapply s_red_to_t_red; auto.
Qed. 
Hint Resolve diamond_t_red: TreeHintDb.



(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_tree_calculus: confluence Tree t_red. 
Proof. apply diamond_t_red.  Qed.




Lemma programs_are_stable: forall M, program M -> forall N, s_red1 M N -> N = M.
Proof. intros M n; induction n; intros; inv s_red1; repeat f_equal; auto. Qed.


Lemma programs_are_stable2: forall M N, s_red M N -> program M -> N = M.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> program M -> N = M).
  intro c; intros; eapply c; eauto.  
  intros red M N r; induction r; intros; subst; zerotac. 
  assert(N = M) by (eapply programs_are_stable; eauto); subst; auto. 
  Qed.
  
Lemma t_red_preserves_stems:
  forall M N, t_red M N -> forall M0, M = △ @ M0 -> exists N0, N = △ @ N0 /\ t_red M0 N0.
Proof.
  cut (forall red M N, multi_step red M N -> red = t_red1 ->
                       forall M0, M = △ @ M0 -> exists N0, N = △ @ N0 /\ t_red M0 N0).
  intro H; intros; eapply H; eauto. 
  intros red M N r; induction r; intros e M0 eM; subst. 
  exists M0; split; zerotac. 
  inv t_red1. assert(H: exists N0, P = △ @ N0 /\ t_red N' N0) by (eapply IHr; eauto).
  elim H; clear H; intros ? (?&?); subst; eexists; split; [eauto | eapply2 succ_red].
Qed.

Lemma t_red_preserves_forks:
  forall M N, t_red M N -> forall M0 M1, M = △ @ M0 @ M1 ->
                                         exists N0 N1, N = △ @ N0 @ N1 /\ t_red M0 N0 /\ t_red M1 N1.
Proof.
  cut (forall red M N, multi_step red M N -> red = t_red1 ->
                       forall M0 M1, M = △ @ M0 @ M1 ->
                                     exists N0 N1, N = △ @ N0 @ N1 /\ t_red M0 N0 /\ t_red M1 N1).
  intro H; intros; eapply H; eauto. 
  intros red M N r; induction r; intros e M0 M1 eM; subst. 
  exists M0, M1; split_all; zerotac.
  { assert (e: t_red1 = t_red1) by reflexivity;  inv t_red1. 
  match goal with | r1: t_red1 M0 ?M2 |- _ =>  elim (IHr e M2 M1); auto end;
    intros Q ex; elim ex; intros Q1 ([=] & r1 & r2); subst; 
      exists Q, Q1; repeat split; zerotac;   succtac; zerotac.
  match goal with | r1: t_red1 M1 ?M2 |- _ =>  elim (IHr e M0 M2); auto end; 
    intros Q ex; elim ex; intros Q1 ([=] & r1 & r2); subst; 
      exists Q, Q1; repeat split; zerotac;   succtac; zerotac.
  }
Qed.


Lemma t_red_preserves_factorable: forall M N, t_red M N -> factorable M -> factorable N.
Proof.
  intros M N r fac; inversion fac; subst.
  {
  assert(N = △)  by (apply programs_are_stable2; [  apply t_red_to_s_red | apply pr_leaf]; auto);
    subst; auto. 
  }{
  assert(ex: exists Q, N = △ @ Q /\ t_red M0 Q) by (eapply t_red_preserves_stems; eauto);
    elim ex; intros Q (?&?); subst; auto_t. 
  }{
  assert(ex: exists Q1 Q2, N = △ @ Q1 @ Q2 /\ t_red M0 Q1 /\ t_red N0 Q2)
    by (eapply t_red_preserves_forks; eauto); 
    elim ex; split_all; subst; split_all. auto_t. 
  }
Qed.  


(* Counting reduction steps *) 


Inductive multi_ranked : (Tree -> Tree -> Prop) -> (nat -> Tree -> Tree -> Prop) :=
| zero_ranked : forall red M, multi_ranked red 0 M M
| succ_ranked : forall (red: Tree -> Tree -> Prop) M N n P,
    red M N -> multi_ranked red n N P -> multi_ranked red (S n) M P
. 

Hint Constructors multi_ranked : TreeHintDb.

Lemma multi_ranked_trans:
  forall red n M N, multi_ranked red n M N -> forall p P, multi_ranked red p N P -> multi_ranked red (n+p) M P. 
Proof.  induction n; intros M N rN p P rP; intros; inversion rN; subst; eauto; eapply2 succ_ranked. Qed. 


  
Lemma multi_ranked_iff_multi_red :
  forall (red : Tree -> Tree -> Prop) M N, multi_step red M N <-> exists n, multi_ranked red n M N.
Proof.
  intros red M N; split; intro r. 
  induction r. exists 0; auto_t.
  elim IHr; intro k; exists (S k); eapply2 succ_ranked. 
  elim r; intros k r1.    generalize M N r1; clear.
  induction k ; intros; inversion r1; subst;  zerotac;   eapply2 succ_red.
Qed.


Lemma diamond_multi_ranked:
  forall red1 red2, diamond red1 red2 -> forall n, diamond (multi_ranked red1 n) red2.
Proof.
  intros red1 red2 d; induction n as [| n']; red; intros M N r P rP; inversion r; subst.
  exists P; auto_t.
  match goal with | Hr : red1 M ?N0 |- _ => elim (d M N0 Hr P rP); auto; intros x (Hx & ?); intros end.  
  match goal with
  | Hr : multi_ranked red1 n' ?N0 N, Hx : red2 ?N0 _ |- _ =>
    elim(IHn' _ _ Hr  _ Hx); auto; intro x1; intros (?&?)
  end. 
  exists x1; split; auto_t; eapply2 succ_ranked. 
Qed.

Lemma diamond_multi_ranked2:
  forall red1 red2, diamond red1 red2 -> forall m n, diamond (multi_ranked red1 m) (multi_ranked red2 n).
Proof. intros; repeat (apply diamond_multi_ranked; apply diamond_flip); auto_t. Qed.


  



(* Halting Problem *)

Definition valuable M := exists P, t_red M P /\ program P.

Definition omega := △ @ (△ @ I) @ I.

Ltac stable_tac := inv1 program; match goal with | H : s_red1 ?Q ?R |- _ =>   assert(R=Q) by 
                                (apply programs_are_stable; cbv; program_tac); clear H end.

Lemma omega_omega_doesn't_halt:
  forall n h M, h < n -> multi_ranked s_red1 h (omega@ omega) M -> factorable M -> False.
Proof.
  induction n as [| n0]; intros h M hn r fac.  lia.
  inversion r; clear r; subst.
  unfold omega at 1 in fac; inv1 factorable. 
  match goal with | H : s_red1 (omega@omega) _ |- _ =>   unfold omega at 1 in H; inv s_red1 end.
  repeat stable_tac; subst. auto. 
  assert(r1: exists Q, s_red M Q /\ multi_ranked s_red1 n (omega@omega) Q). 
  eapply2 diamond_multi_ranked. eapply2 diamond_strip. 
  apply t_red_to_s_red;  trtac. elim r1;  intros Q (r2 & r3).   
  eapply2 (IHn0 n Q); eapply t_red_preserves_factorable; [  eapply2 s_red_to_t_red | auto].  
  {
  repeat stable_tac; subst.
  assert(r1: exists Q, s_red M Q /\ multi_ranked s_red1 n (omega@omega) Q). 
  eapply2 diamond_multi_ranked. eapply2 diamond_strip. eauto. 
  eapply t_red_to_s_red; trtac.
 elim r1;  intros Q (r2 & r3).   
 eapply2 (IHn0 n Q); eapply t_red_preserves_factorable; [eapply2 s_red_to_t_red | auto].
 }
Qed.



Lemma omega_omega_has_no_value: ~(valuable (omega @ omega)).
Proof.
  unfold valuable; intro v; elim v; clear v; intro P; intros (?&?).
  assert(ex:exists n, multi_ranked s_red1 n (omega @ omega) P). 
  apply multi_ranked_iff_multi_red; auto.   apply t_red_to_s_red; auto.
  elim ex; intros n r.   eapply omega_omega_doesn't_halt; eauto. apply programs_are_factorable; auto.
Qed.


Definition halting h :=
  forall M, (t_red (h @ M) K /\ valuable M) \/ (t_red (h @ M) KI /\ ~ (valuable M)).  

Definition self_negation :=  \"h" (\"f" ((Ref "h")@ ((Ref "f") @ (Ref "f")) @ (omega@omega) @ K)).  


Theorem halting_problem_insoluble : forall h, ~(halting h).
Proof.
  unfold halting; intro h; intro halt.
  assert(h1: t_red (h @ K) K /\ valuable K \/ t_red (h @ K) KI /\ ~ valuable K) by   apply halt. 
  inversion h1 as [ (r&v) | (r &nv) ]; clear h1.
  2: apply nv; unfold valuable; exists K; split; [zerotac | program_tac].

  assert(h2: t_red (h @ (omega @ omega)) K
             /\ valuable (omega @ omega) \/ t_red (h @ (omega @ omega)) KI
                                            /\ ~ valuable (omega @ omega)) by   apply halt. 
  inversion h2 as [ (r2&v2) | (r2 &nv2) ]; clear h2; intros. 
  apply  omega_omega_has_no_value; auto.

  assert (h3: (t_red (h @ (self_negation @ h @ (self_negation @ h))) K /\ valuable (self_negation @ h @ (self_negation @ h))) \/ (t_red (h @ (self_negation @ h @ (self_negation @ h))) KI /\ ~ (valuable (self_negation @ h @ (self_negation @ h))))) by 
  apply halt. 
  inversion h3 as [ (r3&v3) | (r3 &nv3) ]; clear h3; intros. 
  assert(h4: t_red ((self_negation @ h @ (self_negation @ h))) (omega@omega)).
  unfold self_negation at 1. starstac ("f" :: "h" :: nil). 
  assert(t_red (h @  (self_negation @ h @ (self_negation @ h))) KI). 
  aptac. zerotac. eauto. eauto. 
  assert(h5: exists Q, t_red K Q /\ t_red KI Q) by eapply2 diamond_t_red.
  elim h5; clear h5; intros Q (?&?). 
  assert(Q = K).  apply programs_are_stable2.  apply t_red_to_s_red; auto. program_tac. 
  assert(Q = KI).  apply programs_are_stable2.  apply t_red_to_s_red; auto. program_tac. 
  subst; discriminate. 
 
  assert( t_red ((self_negation @ h @ (self_negation @ h))) K).
  unfold self_negation at 1. starstac ("f" :: "h" :: nil). 
  assert(t_red (h @  (self_negation @ h @ (self_negation @ h))) K). 
  aptac. zerotac.   eauto. eauto. 
  assert(h5: exists Q, t_red K Q /\ t_red KI Q) by eapply2 diamond_t_red.
  elim h5; intros Q (?&?). 
  assert(Q = K) .  apply programs_are_stable2.  eapply2 t_red_to_s_red. program_tac. 
  assert(Q = KI) .  apply programs_are_stable2.  eapply2 t_red_to_s_red. program_tac. 
  subst; discriminate. 
Qed.



(* Standard Reduction *)



Definition is_redex M  :=
  match M with
  | △ @ △ @ M @ N  => 1
  | △ @ (△ @ P) @ M @ N  => 1
  | △ @ (△ @ P @ Q) @ M @ Node  => 1
  | △ @ (△ @ P @ Q) @ M @ (Node @ N)  => 1 
  | △ @ (△ @ P @ Q) @ M @ (Node @ N1 @ N2) => 1
  | _ => 0
  end.

Fixpoint redexes M  :=
  (* counts the number of redexes currently available *) 
  match M with
  | Ref _ => 0
  | △ => 0
  | M @ N => is_redex (M@N) + redexes M + redexes N
  end.

  
Definition irreducible M := forall N, t_red1 M N -> False.

Lemma programs_are_irreducible: forall M, program M -> irreducible M.
Proof. intros M prM; induction prM; intro; intro; auto; inv t_red1.  Qed. 

Lemma irreducible_no_redexes: forall N, irreducible N -> redexes N = 0.
Proof.
  induction N; intro irr; subst; simpl; auto_t.
  caseEq N1; intros; subst; simpl; auto_t; try (apply IHN2; intro; intro; eapply2 irr). 
  caseEq t; intros; subst; simpl in *; rewrite IHN1; rewrite ? IHN2; auto;
    try (intro; intro; eapply irr; auto_t).
  caseEq t1; intros; subst; simpl in *; auto.
  caseEq t2; intros; subst; simpl in *; auto.
  cut False; [ tauto | eapply irr; auto_t]. 
  caseEq t; intros; subst; simpl in *; auto.
  cut False; [ tauto | eapply irr; auto_t]. 
  caseEq t2; intros; subst; simpl in *; auto.
  caseEq N2; intros; subst; simpl in *; auto.
  cut False; [ tauto | eapply irr; auto_t]. 
  caseEq t; intros; subst; simpl in *; auto.
  cut False; [ tauto | eapply irr; auto_t]. 
  caseEq t4; intros; subst; simpl in *; auto.
  cut False; [ tauto | eapply irr; auto_t]. 
Qed.


Lemma program_no_redexes: forall N, program N -> redexes N = 0.
Proof. intros; apply irreducible_no_redexes; apply programs_are_irreducible; auto. Qed. 


Lemma quaternary_redexes:
  forall M, combination M -> forall N P Q R, M = N @ P @ Q @ R -> redexes  M >0.
Proof.
  cut (forall p M, term_size M < p -> combination M ->
                   forall N P Q R, M = N@P@Q@R -> redexes  M >0).
  intro H; intros; eapply H; eauto. 
  induction p; intros M s c N P Q R e; subst. lia. 
  assert(cN:combination N) by (inv1 combination).
  inversion cN as [ | P1 Q1 d1 d2]; subst.
 (* 2 *)
  assert(cP: combination P) by (inv1 combination).
  inversion cP as [| M0 N0 c1 c2]; subst; auto. simpl; lia.
  inversion c1 as [ | M1 N1 c3 c4]; subst; auto. simpl; lia. 
  inversion c3 as [ | M2 N2]; subst; auto.
  assert(cR: combination R) by (inv1 combination).
  inversion cR as [| R0 R1 c5 c6]; subst; auto. simpl; lia.
  inversion c5 as [ | R2 R3 c7 c8]; subst; auto. simpl; lia. 
  inversion c7 as [ | R4 R5]; subst; auto. simpl; lia. 
  assert(redexes (R4 @ R5 @ R3 @ R1) >0). eapply IHp. simpl in *; lia.  auto. eauto. 
  simpl in *; lia.
  assert(redexes (M2 @ N2 @ N1 @ N0) >0) by ( eapply IHp; eauto; simpl in *; lia).
  simpl in *; lia.
  (* 1 *)
  assert(redexes (P1 @ Q1 @ P @ Q @ R) >= redexes (P1 @ Q1 @ P @ Q) + redexes R)
    by (simpl; lia). 
  assert(term_size R >0).
  clear. induction R; intros; auto_t; simpl; lia.
    assert(redexes (P1 @ Q1 @ P @ Q) > 0) .  eapply IHp; auto_t.  simpl in *; lia. 
  combination_tac; inv1 combination.  
  lia.
Qed. 



Lemma no_redexes_program: forall N, redexes N = 0 -> combination N -> program N. 
Proof.
  induction N; intros; subst; auto; subst.
  (* 3 *)
  inv1 combination. 
  apply pr_leaf.
  (* 1 *)
  assert(cN1: combination N1) by inv1 combination.
  inversion cN1 as [| M0 N0 c1 c2]; subst. apply pr_stem. apply IHN2. simpl in *; lia.   inv1 combination.
  (* 1 *)
  inversion c1 as [| M1 N1 c3 c4]; subst. apply pr_fork. 
  assert(program (△ @ N0)). apply IHN1. simpl in *; lia. eauto.  inv1 program.
  apply IHN2. simpl in *; lia. inv1 combination. 
  assert(redexes (M1 @ N1 @ N0 @ N2) >0) . eapply quaternary_redexes; eauto. lia. 
Qed.



(* ready combinations *)

(* The proof of standardisation is adapted from the work of Ryo Kashima on lambda-calculus. *)

Inductive ready : Tree -> Prop :=
| kernelready: forall M N, ready (△ @ △ @ M @ N)
| stem_ready : forall M N P, ready (△ @ (△ @ M) @ N @ P)
| fork_leaf_ready : forall M N P, ready (△ @ (△ @ M @ N) @ P @ Node)
| fork_stem_ready : forall M N P Q, ready (△ @ (△ @ M @ N) @ P @ (Node @ Q))
| fork_fork_ready : forall M N P Q R, ready (△ @ (△ @ M @ N) @ P @ (Node @ Q @ R))
.

Hint Constructors ready :TreeHintDb.


Lemma ready_or_not: forall M, ready M \/ ~(ready M).
Proof.
  induction M; intros; subst; auto; try (right; intro H; inversion H; fail); subst. 
  inversion IHM1. right; intro. inv1 ready; subst; inv1 ready. 
  (* 1 *)
  case M1; intros; try (right; intro; inv1 ready; fail). 
  case t; intros; try (right; intro; inv1 ready; fail). 
  case t1; intros; try (right; intro; inv1 ready; fail). 
  case t2; intros; try (right; intro; inv1 ready; fail). left; auto_t. 
  case t3; intros; try (right; intro; inv1 ready; fail). left; auto_t. 
  case t5; intros; try (right; intro; inv1 ready; fail).
  eelim (factorable_or_not M2); intros.
  left; inv_out H0; auto_t.
  right; intro aux; inv_out aux;  eapply H0; auto_t. 
Qed.

Lemma t_red_preserves_leaf: forall M N red, multi_step red M N -> red = t_red1 -> M = Node -> N = Node.
Proof. intros M N red r; induction r; intros; subst; auto_t. inv_out H; auto. Qed.

Lemma t_red_preserves_stem:
  forall M N red, multi_step red M N -> red = t_red1 ->
                  forall M1, M = Node @ M1 -> exists N1,  N = Node @ N1 /\ t_red M1 N1.
Proof.
  intros M N red r; induction r; intros; subst; auto_t. inv_out H.  inv_out H3; auto.
  eelim IHr; intros.  2,3: eauto. split_all; exists x; split; auto_t; eapply succ_red; eauto.
Qed.


Lemma t_red_preserves_fork:
  forall M N red, multi_step red M N -> red = t_red1 ->
                  forall M1 M2, M = Node @ M1 @ M2 ->
                                exists N1 N2,  N = Node @ N1 @ N2 /\ t_red M1 N1 /\ t_red M2 N2.
Proof.
  intros M N red r; induction r; intros; subst; auto_t.
  repeat eexists; auto_t.
  inv_out H.  inv_out H3.  inv_out H2.
  eelim IHr; intros.  2,3: eauto.  split_all.  repeat eexists. eapply succ_red; eauto.   eauto.
  eelim IHr; intros.  2,3: eauto.  split_all.  repeat eexists. eauto. eapply succ_red; eauto.   
Qed.



Lemma t_red_preserves_ready:
  forall M N, ready (M @ N) -> forall M' N', t_red M M' -> t_red N N' -> ready (M' @ N'). 
Proof.
  intros; inv_out H.
  (* 5 *) 
  eelim t_red_preserves_fork; intros.  2: eapply H0. 2,3: eauto. split_all. inv_out H2. auto_t.
  inv_out H.
  (* 4 *)
  eelim t_red_preserves_fork; intros.  2: eapply H0. 2,3: eauto. split_all.
  eelim t_red_preserves_stem; intros.  2: eapply H2. 2,3: eauto. split_all.
  auto_t.
  (* 3 *)
  eelim t_red_preserves_fork; intros.  2: eapply H0. 2,3: eauto. split_all.
  eelim t_red_preserves_fork; intros.  2: eapply H2. 2,3: eauto. split_all.
  assert(N' = Node). eapply t_red_preserves_leaf; eauto. subst. auto_t.
  (* 2 *)
  eelim t_red_preserves_fork; intros.  2: eapply H0. 2,3: eauto. split_all.
  eelim t_red_preserves_fork; intros.  2: eapply H2. 2,3: eauto. split_all.
  eelim t_red_preserves_stem; intros.  2: eapply H1. 2,3: eauto. split_all.
  auto_t.
  (* 1 *)
  eelim t_red_preserves_fork; intros.  2: eapply H0. 2,3: eauto. split_all.
  eelim t_red_preserves_fork; intros.  2: eapply H2. 2,3: eauto. split_all.
  eelim t_red_preserves_fork; intros.  2: eapply H1. 2,3: eauto. split_all.
  auto_t.
Qed.

Lemma redexes_ready: forall M N, ready (M @ N) -> redexes (M @ N) = S (redexes M  + redexes N).
Proof.  intros M N r; inv_out r; simpl; lia. Qed. 
  
Lemma redexes_unready: forall M N, ~ ready (M @ N) -> redexes (M @ N) = redexes M  + redexes N.
Proof.
  intros M N r; simpl.
  caseEq M; intros; subst; try lia.
  caseEq t; intros; subst; try lia.
  caseEq t1; intros; subst; try lia.
  caseEq t2; intros; subst; simpl; try lia.
  cut False; [ tauto | eapply r; auto_t].
  caseEq t; intros; subst; try lia.
  cut False; [ tauto | eapply r; auto_t].
  caseEq t2; intros; subst; try lia.
  caseEq N; intros; subst; try lia.
  cut False; [ tauto | eapply r; auto_t].
  caseEq t; intros; subst; simpl; try lia.
  cut False; [ tauto | eapply r; auto_t].
  caseEq t4; intros; subst; try lia.
  cut False; [ tauto | eapply r; auto_t].
Qed.
  


(* t_nred1 tags reductions with the number of overlooked reductions on the left *) 
  
Inductive t_nred1 : nat -> Tree -> Tree -> Prop :=
| kernel_nred : forall M N, t_nred1 0 (△ @ △ @ M @ N) M
| stem_nred : forall M N P,  t_nred1 0 (△ @ (△ @ P) @ M @ N) (P@N @ (M @ N))
| fork_leaf_nred : forall M P Q,  t_nred1 0 (△ @ (△ @ P @ Q)@ M@ Node) P
| fork_stem_nred : forall M N P Q,  t_nred1 0 (△ @ (△ @ P @ Q)@ M@ (Node @ N)) (Q@N)
| fork_fork_nred : forall M N1 N2 P Q,  t_nred1 0 (△ @ (△ @ P @ Q)@ M@ (Node @ N1 @ N2)) (M @ N1 @ N2)
| appl_unready : forall n M M1 N, t_nred1 n M M1 -> ~(ready (M@N)) -> t_nred1 n (M@N) (M1 @ N)
| appl_ready : forall n M M1 N, t_nred1 n M M1 -> ready (M@ N) ->
                                           t_nred1 (S n)  (M@N) (M1 @ N)
| appr_unready : forall n M N N1, t_nred1 n N N1 -> ~(ready (M@N)) -> t_nred1 (n + redexes M) (M@N) (M@N1)
| appr_ready : forall n M N N1, t_nred1 n N N1 -> ready (M@N) -> t_nred1 (S (n+redexes M)) (M@N) (M@N1)
| appr_outer : forall M1 M2 N P P' n,
    t_nred1 n P P' ->
    t_nred1 n (Node @ (Node @ M1 @ M2) @ N @ P) (Node @ (Node @ M1 @ M2) @ N @ P') 
.

Lemma t_nred1_to_t_red1: forall n M N, t_nred1 n M N -> t_red1 M N.
Proof.  intros n M N r; induction r; split_all; auto_t. Qed. 
  

(* l_red is leftmost reduction (since nothing has been overlooked) *) 

Inductive seq_red : nat -> Tree -> Tree -> Prop :=
| zero_seq_red : forall m M, m<= redexes M -> seq_red m M M
| succ_seq_red: forall n n1 M N P,  n <= n1 -> t_nred1 n M N -> seq_red n1 N P -> seq_red n1 M P
.

Definition l_red := seq_red 0.

Hint Constructors ready t_nred1 seq_red :TreeHintDb.

Lemma seq_red_to_t_red : forall n M N, seq_red n M N -> t_red M N.
Proof.
  intros n M N r; induction r; intros; zerotac. 
  eapply succ_red; eauto. eapply t_nred1_to_t_red1; eauto.
Qed. 

Theorem l_red_to_t_red: forall M N, l_red M N -> t_red M N.
Proof. apply seq_red_to_t_red. Qed. 
  
Lemma l_red_transitive: forall M N, l_red M N -> forall P, l_red N P -> l_red M P.
Proof.
  cut (forall n M N, seq_red n M N -> n = 0 -> forall P, l_red N P -> l_red M P).
  intro H; intros; auto. eapply H; eauto. 
  intros n M N r; induction r; intros; subst; auto.  
  eapply2 succ_seq_red; eapply2 IHr.
Qed.

  

(* basic properties *)


Lemma redexes_ready_factorable:
  forall M N, ready (M@N) -> redexes (M @ N) = S (redexes M + redexes N).  
Proof.  intros; inv_out H; simpl; lia. Qed. 


Lemma seq_red_redexes: forall n M N, seq_red n M N -> n <= redexes N.
Proof.  intros n M N r; induction r; auto. Qed.

Lemma seq_red_preserves_factorable: forall n M N, seq_red n M N -> factorable M -> factorable N.
Proof.
  intros n M N r; induction r as [r1 | ? ? ? ? ? ? tr]; intro rdy; auto. apply IHr.  clear - rdy tr.
  inversion rdy; subst; inv (t_nred1 n); inv1 ready; inv (t_nred1 n1); inv1 ready. 
Qed.

  
Lemma seq_red_app:
  forall M M1, seq_red (redexes M1) M M1 ->
               forall N N1, seq_red (redexes N1) N N1 ->
                            seq_red (redexes (M1 @ N1)) (M@N) (M1 @ N1).
Proof.
  intros M M1 s; induction s as [| n1 n2 M N P lt r1 s0];  intros N0 N1 s1; subst; auto.
  (* 2 *)
  induction s1 as [| n0 n1 N P Q]; subst; auto_t.
  assert (n1 <= redexes Q) by (eapply seq_red_redexes; eauto). 
  eelim (ready_or_not (M@N)); intros.
  eapply succ_seq_red. 3: eauto. 2: eapply appr_ready; eauto.
  rewrite redexes_ready. 2: eapply t_red_preserves_ready; eauto. 2: zerotac. 2: eapply seq_red_to_t_red; auto_t.
  lia.
  eapply succ_seq_red. 3: eauto. 2: eapply appr_unready; eauto.
  assert(redexes M + redexes Q <= redexes (M@Q)).  2: lia.
  eelim (ready_or_not (M@Q)); intros.
  rewrite redexes_ready; auto; lia.
  rewrite redexes_unready; auto; lia.
  (* 1 *)
  eelim (ready_or_not (M@N0)); intros.
  eapply succ_seq_red. 3: eauto. 2: eapply appl_ready; eauto.
  rewrite redexes_ready.
  assert(n2 <= redexes P). eapply seq_red_redexes. eapply succ_seq_red. 3: eauto. 2: eauto. auto . lia.
  eapply t_red_preserves_ready; eauto. 1,2: eapply seq_red_to_t_red; auto_t.
  eapply succ_seq_red. 3: eauto. 2: eapply appl_unready; eauto.
  assert(redexes P + redexes N1 <= redexes (P@N1)).  
  eelim (ready_or_not (P@N1)); intros.
  rewrite redexes_ready; auto; lia.
  rewrite redexes_unready; auto; lia.
  (* 1 *)
  assert(n2 <= redexes P). eapply seq_red_redexes. eauto. lia.
Qed.


(* hap performs head reduction *)

Inductive hap1 : Tree -> Tree -> Prop :=
| hap_kernel : forall M N, hap1 (△ @ △ @ M @ N) M
| hap_stem : forall P M N, hap1 (△ @ (△ @ M) @ N @ P) (M@P @ (N@P))
| hap_fork_leaf : forall P Q M, hap1 (△ @ (△ @ P @ Q) @ M @ Node) P
| hap_fork_stem : forall P Q M N, hap1 (△ @ (△ @ P @ Q) @ M @ (Node@ N)) (Q@N)
| hap_fork_fork : forall P Q M N1 N2, hap1 (△ @ (△ @ P @ Q) @ M @ (Node @ N1 @ N2)) (M @ N1 @ N2)
| hap_app : forall M N P,  hap1 M N -> hap1 (M@ P) (N@ P)
| hap_inner1: forall M M' N P, hap1 M M' -> hap1 (△ @ M @ N@ P) (△ @ M' @ N@ P)
| hap_inner2: forall M1 M2 N P P', hap1 P P' ->
                                   hap1 (△ @ (Node @ M1 @ M2) @ N@ P) (△ @ (Node @ M1 @ M2) @ N@ P')
.

Definition hap := multi_step hap1.



Lemma hap1_functional: forall M N, hap1 M N -> forall P, hap1 M P -> N=P.
Proof.
  intros M N r; induction r; intros P0 rP; inv hap1; subst; inv hap1;
    repeat f_equal; apply IHr; auto.
Qed.


(* st_red allows nested head reductions, but always moving to the right *) 

Inductive st_red : Tree -> Tree -> Prop :=
| st_ref : forall M i, hap M (Ref i) -> st_red M (Ref i)
| st_node : forall M, hap M △ -> st_red M △
| st_app : forall M N N1 P P1, hap M (N@ P) -> st_red N N1 -> st_red P P1 -> st_red M (N1 @P1)
.


Hint Constructors  hap1 st_red :TreeHintDb.

Lemma hap_preserves_appr: forall M N P, hap M N -> hap (M@ P) (N@ P).
Proof.
  cut(forall red M N P, multi_step red M N -> red = hap1 -> hap (M@ P) (N@ P));
  [split_all |
  intros red M N P r; induction r; split_all; subst;
    [ zerotac | eapply succ_red; [ eapply2 hap_app | eapply2 IHr]]]; auto_t.   
Qed.


Lemma hap_inner1_multi:
  forall M M' N P, hap M M' -> hap (△ @ M @ N @ P) (△ @ M' @ N @ P).
Proof.
  cut (forall red M M',
          multi_step red M M' -> red = hap1 -> 
          forall N P, hap (△ @ M @ N @ P) (△ @ M' @ N @ P));
  [ split_all |
  intros red M M' r; induction r; intros; subst;
  [ zerotac  |  eapply succ_red; [ eapply2 hap_inner1 | eapply2 IHr]]]; auto_t.
Qed.

Lemma hap_inner2_multi:
  forall M1 M2 N P P', hap P P' -> hap (△ @ (Node @ M1 @ M2) @ N @ P) (△ @ (Node @ M1 @ M2) @ N @ P').
Proof.
  cut (forall red P P',
          multi_step red P P' -> red = hap1 -> 
          forall M1 M2 N, hap (△ @ (Node @ M1 @ M2) @ N @ P) (△ @ (Node @ M1 @ M2) @ N @ P'));
  [ split_all |
  intros red M M' r; induction r; intros; subst;
  [ zerotac  |  eapply succ_red; [ eapply2 hap_inner2 | eapply2 IHr]]]; auto_t.
Qed.


Lemma st_red_refl: forall M, st_red M M.
Proof. induction M; split_all; [ apply st_ref | apply st_node | eapply2 st_app]; zerotac. Qed.

Lemma hap_then_st_red: forall N M, hap M N -> forall P, st_red N P -> st_red M P.
Proof.
  intros M N H P st; inversion st; subst; [eapply2 st_ref | eapply2 st_node |  eapply2 st_app];
     (eapply transitive_red; [ eexact H |]; auto_t). 
Qed.


Lemma st_kernel_red :
  forall M N P,  st_red M (△ @ △ @ N @ P) -> st_red M N.
Proof.
  intros M N P st; inv st_red. 
  eapply hap_then_st_red. 2: eassumption. 
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. apply hap_inner1_multi; eauto. auto_t. 
Qed.

Lemma st_stem_red :
  forall M N P Q,  st_red M (△ @ (△ @ N) @ P @ Q) -> st_red M (N@Q @(P@Q)).
Proof.
  intros M N P Q H.  inv st_red.   eapply hap_then_st_red.
  (* 2 *)
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_inner1_multi. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. eapply hap_preserves_appr. eassumption.
  eapply succ_red;  auto_t.
  (* 1 *)
  eapply st_app. zerotac. eapply st_app. zerotac. auto. auto. eapply st_app. zerotac. auto. auto.
Qed.

Lemma st_fork_leaf_red :
  forall M N R P,  st_red M (App (App (△ @ (△ @ N @ R)) P) Node) -> st_red M N.
Proof.
  intros M N R P H; inv st_red.   eapply hap_then_st_red.
  (* 2 *)
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_inner1_multi. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. eapply hap_preserves_appr. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. do 2 eapply hap_preserves_appr. eassumption.
  eapply transitive_red. eapply hap_inner2_multi. eassumption.
  eapply succ_red. auto_t. zerotac. auto. 
Qed.

Lemma st_fork_stem_red :
  forall M N R P Q,  st_red M (App (App (△ @ (△ @ N @ R)) P) (Node @ Q)) -> st_red M (R @ Q).
Proof.
  intros M N R P Q H; inv st_red.   eapply hap_then_st_red.
  (* 2 *)
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_inner1_multi. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. eapply hap_preserves_appr. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eassumption.
  eapply transitive_red. eapply hap_inner2_multi. eapply transitive_red. eauto.
  eapply hap_preserves_appr. eauto. 
  eapply succ_red. auto_t. zerotac. 
  (* 1 *)
  eapply st_app. zerotac. eauto. eauto. 
Qed.

Lemma st_fork_fork_red :
  forall M N R P Q1 Q2,  st_red M (App (App (△ @ (△ @ N @ R)) P) (Node @ Q1 @ Q2)) -> st_red M (P @ Q1 @ Q2).
Proof.
  intros M N R P Q1 Q2 H; inv st_red.   eapply hap_then_st_red.
  (* 2 *)
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_inner1_multi. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. eapply hap_preserves_appr. eassumption.
  eapply transitive_red. eapply hap_inner1_multi. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eassumption.
  eapply transitive_red. eapply hap_inner2_multi. eapply transitive_red. eauto.
  eapply transitive_red. eapply hap_preserves_appr. eauto.
  eapply hap_preserves_appr. eapply hap_preserves_appr.  eassumption.
  eapply2 succ_red.
  (* 1 *)
  eapply st_app. zerotac. eapply st_app. zerotac. all: auto. 
Qed.


(* comparing and combining the relations *) 

Lemma hap1_implies_t_nred1: forall M N, hap1 M N -> t_nred1 0 M N.
Proof.
  intros M N h; induction h; simpl; split_all; try (auto_t; fail).
  apply appl_unready; auto. intro r; inversion r; subst; inversion h; subst; inv hap1.
  apply appl_unready; auto. apply appl_unready; auto.
  replace 0 with (0+ (redexes △)) by auto.
  apply appr_unready; auto.
  1-3: intro r; inversion r; subst; inv hap1.   
Qed.

Lemma hap_implies_l_red: forall M N, hap M N -> l_red M N.
Proof.
  cut(forall red M N, multi_step red M N  -> red = hap1 -> l_red M N).
  intro H; intros; eapply H; eauto.
  intros red M N r; induction r; simpl; subst; intros; auto; subst.
  (* 2 *)
  apply zero_seq_red; lia.
  (* 1 *) 
  eapply succ_seq_red; [| eapply hap1_implies_t_nred1; eauto | eauto]; [lia | eapply2 IHr]. 
Qed.


Lemma hap_then_seq_red: forall M N,  hap M N -> forall n P, seq_red n N P -> seq_red n M P.
Proof.
  cut(forall red M N, multi_step red M N -> red = hap1 ->
                      forall n P, seq_red n N P -> seq_red n M P).

  intro H; intros; eapply H; eauto.
  intros red M N r; induction r; intros; subst; auto. 
  eapply succ_seq_red; [| | eapply2 IHr]; [| eapply2 hap1_implies_t_nred1]; lia. 
  Qed.

Lemma st_red_implies_seq_red: forall M N, st_red M N -> seq_red (redexes N) M N.
Proof.
intros M N st; induction st; intros; auto;
  try (apply hap_implies_l_red; auto; fail);
  eapply2 hap_then_seq_red; eapply2 seq_red_app.   
Qed.

Ltac inv_st_red :=
  match goal with
  | H : st_red _ Node |- _ => inversion H; clear H; subst; inv_st_red
  | H : st_red _ (Node @ _) |- _ => inversion H; clear H; subst; inv_st_red
  | H : st_red _ (Node @ _ @ _) |- _ => inversion H; clear H; subst; inv_st_red
  | H : st_red _ (_@_ @ _ @ _) |- _ => inversion H; clear H; subst; inv_st_red
  | _ => split_all
  end.

Lemma st_red_then_t_nred1: forall n N P, t_nred1 n N P -> forall M, st_red M N -> st_red M P. 
Proof.
  intros n N P r; induction r; intros ? s;
    try (inv_st_red; try inversion s; subst; eapply2 st_app; auto_t; fail); 
    [eapply st_kernel_red |
     eapply st_stem_red |
     eapply st_fork_leaf_red |
     eapply st_fork_stem_red |
     eapply st_fork_fork_red |
     inv_out s]; auto_t.
Qed.






(* proofs below work from the other end of the reduction sequence *)

Inductive t_red_rev : Tree -> Tree -> Prop :=
| zero_t_red : forall M, t_red_rev M M
| succ_t_red : forall M N n P, t_red_rev M N -> t_nred1 n N P -> t_red_rev M P.

Hint Constructors t_red_rev :TreeHintDb.


Lemma transitive_t_red_rev :
  forall N P,  t_red_rev N P -> forall M, t_red_rev M N -> t_red_rev M P. 
Proof.
intros N P r; induction r; intros; auto. 
eapply succ_t_red. eapply IHr; auto. eauto.
Qed.

Lemma t_red1_implies_t_nred1:
  forall M N, t_red1 M N -> exists n, t_nred1 n M N.
Proof.
  induction M; intros N r; auto; inversion r; subst; auto_t. 
   (* 2 *)
  assert(ex: exists n, t_nred1 n M1 M') by (eapply IHM1; eauto). 
  inversion ex; subst. 
  assert(rM: ready (M1@ M2) \/ ~(ready (M1@ M2))) by apply ready_or_not.
  inversion rM; auto_t.  
  (* 1 *)
  assert(ex: exists n, t_nred1 n M2 N') by (eapply IHM2; eauto). 
  inversion ex; subst.
  match goal with | H : t_red1 (?M1 @ ?N1) _ |- _ =>
                    assert(rM1: ready (M1@ N1) \/ ~(ready (M1@ N1))) by apply ready_or_not;
                      inversion rM1; auto_t
  end.
Qed.

Lemma t_red_implies_t_red_rev:
  forall M N, t_red M N -> t_red_rev M N.
Proof.
  cut (forall red M N, multi_step red M N -> red = t_red1 -> t_red_rev M N).
  intro H; intros; eapply H; auto_t.        
  intros red M N r; induction r; intros; subst; auto_t. eapply transitive_t_red_rev. 
  eapply IHr. auto. 
  assert(ex: exists n, t_nred1 n M N) by (eapply t_red1_implies_t_nred1; eauto). 
  inversion ex; auto_t.
Qed.

Lemma t_red_rev_st_red : forall M N, t_red_rev M N -> st_red M N.
Proof.
  intros M N r; induction r; intros; subst; auto. 
  (* 2 *)
  apply st_red_refl. 
  (* 1 *) 
  eapply st_red_then_t_nred1; eauto. 
Qed.

Lemma t_red_st_red : forall M N, t_red M N -> st_red M N.
Proof.  intros; apply t_red_rev_st_red;  apply t_red_implies_t_red_rev; auto. Qed.

(* the standardization theorem *)

(* This whole approach to standardisation is taken from a paper that should be referenced in the book *)  

Theorem standardization : forall M N, t_red M N -> seq_red (redexes N) M N.
Proof.  intros; apply st_red_implies_seq_red; apply t_red_st_red; auto. Qed. 


Corollary leftmost_reduction:
  forall M N, t_red M N -> program N -> l_red M N. 
Proof.
  intros M N r pr.
  assert(seq_red (redexes N) M N) by (eapply standardization; eauto).
  assert(r0: redexes N = 0) by (eapply program_no_redexes; eauto).
  rewrite r0 in *; auto. 
Qed. 

Theorem head_reduction_to_factorable_form:
  forall M N, t_red M N -> factorable N -> exists Q, hap M Q /\ factorable Q /\ t_red Q N. 
Proof.
  intros M N r fac.
  assert(st: st_red M N) by (eapply t_red_rev_st_red; eapply t_red_implies_t_red_rev; eauto). 
  inversion st; subst; inv1 factorable; subst.
  (* 2 *)
  match goal with | st: st_red _ Node |- _ =>  inversion st; subst end.
  exists (△ @P); repeat split_all.
  eapply transitive_red. eassumption. apply hap_preserves_appr; auto. auto_t. 
  apply preserves_app_t_red. zerotac.
  eapply seq_red_to_t_red. apply st_red_implies_seq_red; auto_t.
  (* 1 *) 
  match goal with | st: st_red _ (Node @ _) |- _ =>  inversion st; subst end.
  match goal with | st: st_red _ Node |- _ =>  inversion st; subst end.
  match goal with | hap1: hap M (?N0 @ ?P), hap2: hap ?N0 (N@ ?P0) |- _ => exists (△ @P0@P) end.
  repeat split_all.
  eapply transitive_red. eassumption. apply hap_preserves_appr.
  eapply transitive_red. eassumption.  apply hap_preserves_appr; auto. auto_t. 
  repeat apply preserves_app_t_red; eapply seq_red_to_t_red;
    apply st_red_implies_seq_red; auto_t. apply st_node; zerotac. 
Qed.



(* Lemmas for self-evaluators *) 


Ltac irrtac :=
  match goal with
  | pr: program ?M , r: t_red1 ?M _ |- _ =>
    assert False by (eapply (programs_are_irreducible M); eauto); lia
  | _ => idtac
  end. 

Ltac s_red_program_tac :=
  match goal with
    | H : program ?P, H1: s_red1 ?P ?Q |- _ => assert(Q=P) by (eapply programs_are_stable; eauto); clear H1; s_red_program_tac
    | H : program ?P, H1: s_red ?P ?Q |- _ => assert(Q=P) by apply programs_are_stable2; clear H1; s_red_program_tac
    | _ => idtac
  end. 
 
         
Ltac invsub := 
match goal with 
| H : _ = _ |- _ => inversion H; subst; clear H; invsub 
| _ => split_all 
end. 

Lemma program_application_t_red1 :
  forall M N, t_red1 M N ->
              forall M1 M2, M = M1 @ M2 -> program M1 -> program M2 -> hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 e pr1 pr2; invsub; auto_t; inv t_red1; irrtac.    
Qed.

Lemma program_application2_t_red1 :
  forall M N, t_red1 M N ->
              forall M1 M2 M3, M = M1 @ M2 @ M3 -> program M1 -> program M2 -> program M3 -> hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 e pr1 pr2 pr3; invsub; inv t_red1; auto_t; irrtac. 
Qed.

Lemma program_application3_t_red1 :
  forall M N, t_red1 M N ->
              forall M1 M2 M3 M4, M = M1 @ M2 @ M3 @ M4 ->
                                  program M1 -> program M2 -> program M3 -> program M4 -> hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 M4 e pr1 pr2 pr3; invsub; inv t_red1; auto_t;
    irrtac.
Qed.

Lemma program_application_s_red1 :
  forall M N, s_red1 M N ->
              forall M1 M2, M = M1 @ M2 -> program M1 -> program M2 -> M = N \/ hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 e pr1 pr2; invsub; inv1 program; subst; 
    s_red_program_tac; subst; auto_t. 
Qed.

Lemma program_application2_s_red1 :
  forall M N, s_red1 M N ->
              forall M1 M2 M3, M = M1 @ M2 @ M3 -> program M1 -> program M2 -> program M3 -> M= N \/ hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 e pr1 pr2 pr3; invsub; inv1 program; subst; s_red_program_tac; subst;  auto_t; repeat stable_tac; subst; auto_t.
  eelim program_application_s_red1; intros. 3: eapply r1. 3,4,5: eauto. subst. auto. 
  right; auto_t.
Qed.

Lemma program_application3_s_red1 :
  forall M N, s_red1 M N ->
              forall M1 M2 M3 M4, M = M1 @ M2 @ M3 @ M4 ->
                                  program M1 -> program M2 -> program M3 -> program M4 -> M= N \/ hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 e pr1 pr2 pr3; invsub; inv1 program; subst; s_red_program_tac; subst;  auto_t; repeat stable_tac; subst; auto_t.
  eelim program_application2_s_red1; intros. 3: eapply r1. 3-6: eauto. subst. auto. 
  right; auto_t.
 Qed.


Lemma program_application_multi :
  forall n M N, multi_ranked s_red1 (S n) M N ->
                forall M1 M2, M = M1 @ M2 -> program M1 -> program M2 ->
                              M= N \/ exists Q, hap1 M Q /\ multi_ranked s_red1 n Q N.
Proof.
  induction n; intros M N r M1 M2 e prM1 prM2; subst.
    inversion r as [ | ? ? P0 ? ? s0 s1]; clear r; inversion s1; subst; 
      elim(program_application_s_red1 _ _ s0 M1 M2); auto; intro h;  inversion h; subst; auto_t.
    inversion r as [ | ? ? P ? ? s0 s1]; clear r; subst. 
 elim(program_application_s_red1 _ _ s0 M1 M2); intros; subst; auto.
  elim(IHn _ _ s1 M1 M2);  auto_t;  intros ex.  elim ex; intros Q (?&?).
  right; exists Q; repeat eexists. auto. eapply2 succ_ranked.
  right; exists P; repeat eexists; auto.
 Qed.

Lemma program_application2_multi :
  forall n M N, multi_ranked s_red1 (S n) M N ->
                forall M1 M2 M3, M = M1 @ M2 @ M3 -> program M1 -> program M2 ->program M3 ->
                                 M= N \/ exists Q, hap1 M Q /\ multi_ranked s_red1 n Q N.
Proof.
  induction n; intros M N r M1 M2 M3 e prM1 prM2 prM3; subst.
    inversion r as [ | ? ? P0 ? ? s0 s1]; clear r; inversion s1; subst; 
      elim(program_application2_s_red1 _ _ s0 M1 M2 M3); auto; intro h;  inversion h; subst; auto_t.
    inversion r as [ | ? ? P ? ? s0 s1]; clear r; inversion s1; subst. 
    elim(program_application2_s_red1 _ _ s0 M1 M2 M3); intros; subst; auto.
  elim(IHn _ _ s1 M1 M2 M3);  auto_t.  intro ex; elim ex; intros Q (?&?).
  right; exists Q; repeat eexists; eauto; eapply2 succ_ranked.
  right; exists P; repeat eexists; eauto.
 Qed.

Lemma program_application3_multi :
  forall n M N, multi_ranked s_red1 (S n) M N ->
                forall M1 M2 M3 M4, M = M1 @ M2 @ M3 @ M4 ->
                                    program M1 -> program M2 ->program M3 -> program M4 -> 
                                 M= N \/ exists Q, hap1 M Q /\ multi_ranked s_red1 n Q N.
Proof.
  induction n; intros M N r M1 M2 M3 M4 e prM1 prM2 prM3 prM4; subst.
    inversion r as [ | ? ? P0 ? ? s0 s1]; clear r; inversion s1; subst; 
      elim(program_application3_s_red1 _ _ s0 M1 M2 M3 M4); auto; intro h;  inversion h; subst; auto_t.
    inversion r as [ | ? ? P ? ? s0 s1]; clear r; inversion s1; subst. 
    elim(program_application3_s_red1 _ _ s0 M1 M2 M3 M4); intros; subst; auto.
  elim(IHn _ _ s1 M1 M2 M3 M4);  auto_t.  intro ex; elim ex; intros Q (?&?).
  right; exists Q; repeat eexists; eauto; eapply2 succ_ranked.
  right; exists P; repeat eexists; eauto. 
 Qed.


(* Identifying the needed argument *)

Lemma factorable_decidable:  forall M, factorable M \/ ~ factorable M.
Proof.
  intro; caseEq M; intros; subst; auto_t; [  right; intro; inv1 factorable |]. 
  caseEq t; intros; subst; auto_t;[  right; intro; inv1 factorable |]. 
  caseEq t1; intros; subst; auto_t; right; intro; inv1 factorable.
Qed.


Lemma substitution_preserves_s_red1:
  forall M N, s_red1 M N -> forall x U, s_red1 (substitute M x U) (substitute N x U).
Proof.  intros M N r; induction r; intros x U; intros; simpl; auto_t. Qed. 

Lemma substitution_preserves_s_red:
  forall M N, s_red M N -> forall x U, s_red (substitute M x U) (substitute N x U).
Proof.
  cut(forall n M N, multi_ranked s_red1 n M N ->
                    forall x U, multi_ranked s_red1 n (substitute M x U) (substitute N x U)).
  intro H; intros.
  assert(ex: exists n, multi_ranked s_red1 n M N) by (eapply multi_ranked_iff_multi_red; eauto).  
   elim ex; intros; eauto.  eapply multi_ranked_iff_multi_red; eauto; eapply H; eauto. 
   induction n; intros M N r; inversion r; clear r; subst; split_all. auto_t.  
   eapply succ_ranked; eauto. apply substitution_preserves_s_red1. auto.
Qed.

Definition reflexive (red: Tree -> Tree -> Prop) := forall M, red M M.

Lemma multi_ranked_of_reflexive:
  forall red, reflexive red ->
              forall n m, m <= n -> forall M N, multi_ranked red m M N -> multi_ranked red n M N.
Proof.
  intros red refl; induction n; intros m rel M N r; subst; inversion r; clear r; subst; auto_t.
  lia.   eapply succ_ranked; auto_t. apply IHn with 0. lia. auto_t.
   eapply succ_ranked; eauto. apply IHn with n0; auto.  lia. 
Qed. 


(* active finds the first argument of the leftmost, innermost redex, or the left branch of a triage *) 

Inductive next : Tree -> Tree -> Prop :=
| next_arg : forall M N P , next (△ @ M @ N @ P) M
| next_triage : forall M1 M2 N P , next (△ @ (Node @ M1 @ M2) @ N @ P) P
| next_app: forall R P M, next R M -> next (R@P) M
.

Inductive active : Tree -> Tree -> Prop :=
| active_one : forall M N , next M N -> active M N 
| active_succ: forall R P M,  next R P -> active P M -> active R M
.

Hint Constructors next active: TreeHintDb.

Lemma active_app: forall M N, active M N -> forall P, active (M@P) N.
Proof.
  intros M N a; induction a; intros; [ eapply active_one | eapply active_succ]; auto_t.
Qed. 
  

Lemma next_not_factorable: forall R M, next R M -> ~ factorable R.
Proof.
  intros R M nx; induction nx; intros; subst; intro; inv1 factorable; subst;
    eapply IHnx; auto_t.
Qed.

Lemma active_not_factorable: forall R M, active R M -> ~ factorable R.
Proof.
  intros R M nx; induction nx; intros; subst; intro; inv1 factorable; subst;
    eapply next_not_factorable; auto_t. 
Qed.

Ltac nnf_tac :=
  match goal with
  | H: active ?R _ |- _ => try (absurd (factorable R); auto_t;
                              apply next_not_factorable ||  clear H; nnf_tac || fail)
  | _ => idtac                                                                                                          end.

Lemma next_app3: forall R M, active R M ->
                             forall N P Q, R = △ @ N @ P @ Q -> N=M \/ active N M \/ Q = M \/ active Q M.
Proof. intros R M nx; induction nx; intros R1 P1 Q1 e; invsub; inv next. Qed.


Lemma next_combination: forall R M, next R M -> combination R -> combination M. 
Proof.  intros R M nx; induction nx; intro c; inv1 combination.  Qed. 

Lemma active_combination: forall R M, active R M -> combination R -> combination M. 
Proof.
  intros R M nx; induction nx; intro c; inv1 combination. eapply next_combination; auto_t.
  apply IHnx.  eapply next_combination; eauto. 
Qed.


Lemma substitution_preserves_next:
  forall R M, next R M -> forall s U, next (substitute R s U) (substitute M s U). 
Proof. intros R M nx; induction nx; intros; simpl; auto_t. Qed. 


Lemma substitution_preserves_active:
  forall R M, active R M -> forall s U, active (substitute R s U) (substitute M s U). 
Proof.
  intros R M nx; induction nx; intros; simpl; eauto; [ eapply active_one | eapply active_succ]; eauto;
    eapply substitution_preserves_next; auto.
Qed. 


Fixpoint head_term M :=
  match M with
  | M1 @ M2 => head_term M1
  | M1 => M1
  end.

Lemma  s_red_preserves_head_ref: forall M N s, s_red M N -> head_term M = Ref s -> head_term N = Ref s.
Proof.
  cut(forall n s M N, multi_ranked s_red1 n M N -> head_term M = Ref s -> head_term N = Ref s).
  intro H; intros; eauto.
  assert(ex: exists n, multi_ranked s_red1 n M N) by (eapply multi_ranked_iff_multi_red; eauto).
  elim ex; intros; eapply H; eauto.
  induction n; intros s M N r h; inversion r; subst; eauto.
  eapply IHn; eauto. 
  match goal with
  | s1: s_red1 M ?N0 |- _ => clear - h s1; induction s1; intros; simpl in *; auto;  discriminate end.
Qed.

Lemma next_head: forall R M, next R M -> head_term R = △.
Proof.  intros R M nx; induction nx; intros; auto. Qed.   

Lemma active_head: forall R M, active R M -> head_term R = △.
Proof.  intros R M nx; induction nx; intros; eapply next_head; eauto. Qed.   


Lemma next_s_red1:
  forall R M,  next R M -> forall R1, s_red1 R R1 -> factorable M \/ exists M1, s_red1 M M1 /\ next R1 M1. 
Proof.
  intros R M nx; induction nx; intros R1 r; inversion r; clear r; subst; try (left; auto_t; fail).
  (* 8 *) 
  1-2: inv s_red1.
  1-5: inv next. 
  elim(IHnx M'); eauto; intro ex; elim ex; intros Q (?&?); right; exists Q; split; auto_t. 
Qed.

Lemma active_s_red1:
  forall R M,  active R M -> forall R1, s_red1 R R1 ->
                                        factorable M \/ exists M1, s_red1 M M1 /\ active R1 M1. 
Proof.
  intros R M nx; induction nx as [ N N0 nx0 | ]; intros R1 r.
   (* 2 *)
  eelim(next_s_red1); [ | | eassumption | eassumption]; auto_t; 
  intro ex; elim ex; intros Q (?&?);
    right; exists Q; split; auto; eapply active_one; auto_t.
  (* 1 *)
  inversion r; subst; inv next.
  (* 11 *)
  inv s_red1; inv active;  inv next. 
  all: try (inv active; inv next; fail).
  (* 3 *)
  1,2: clear r; inv s_red1; eelim IHnx; [ | |  eauto]; split_all; auto_t. 
  (* 1 *)
  eelim(next_s_red1 M0 P);  [ | | assumption | eassumption]; auto_t. 
  intro; absurd(factorable P); auto; eapply2 active_not_factorable.
  intro ex; elim ex; intros M1 (?&?); elim(IHnx M1); auto;
  intro ex1; elim ex1; intros M2 (?&?);
    right; exists M2; split; auto; eapply active_app; eapply active_succ; eauto.
Qed. 
  

Lemma active_s_red_factorable:
  forall n R M Q, multi_ranked s_red1 n R Q -> active R M -> factorable Q ->
                    exists M1 , multi_ranked s_red1 n M M1 /\ factorable M1 . 
Proof.
  induction n; intros R M Q r nx fac; inversion r; clear r; subst.
  absurd (factorable Q); auto; eapply active_not_factorable; eauto. 
  assert(or1: factorable M \/ exists M1, s_red1 M M1 /\ active N M1) by (eapply active_s_red1; eauto). 
  inversion or1 as [facM | ex]; clear or1; intros.
  exists M; split; eauto; eapply succ_ranked; auto_t.
  eapply (multi_ranked_of_reflexive s_red1 s_red_refl n 0); auto_t; lia.
  elim ex; intros M0 (s&a).
  assert(ex2 : exists (M1 : Tree) , multi_ranked s_red1 n M0 M1 /\ factorable M1) by (eapply IHn; eauto).
  elim(ex2); intros M2 (s2 & facM1). 
  exists M2; split; eauto; eapply succ_ranked; eauto. 
Qed.


Definition needs R M := exists N, s_red R N /\ active N M. 

Lemma needy_not_factorable: forall R M, needs R M ->  ~ factorable R.
Proof.
  intros R M nd; intro fac; unfold needs in *; intros; elim nd; intros N (s&a);
    eapply active_not_factorable; eauto; eapply t_red_preserves_factorable; eauto;
      apply s_red_to_t_red; auto.
Qed.


Lemma needy_app: forall R M, needs R M -> forall N, needs (R@ N) M.
Proof.
  intros R M nd; induction nd as [x (s&a)]; intro N; eauto.
  exists (x@N); split; [ apply preserves_app_s_red; zerotac| apply active_app; auto]. 
Qed.   


Lemma needy_s_red_factorable:
  forall n R M Q, multi_ranked s_red1 n R Q -> factorable Q -> needs R M ->
                  exists  M1,  multi_ranked s_red1 n M M1 /\ factorable M1. 
Proof.
  intros n R M Q r fac nd; unfold needs in nd. elim nd; intros N (s&a). 
  assert(ex: exists Q1, s_red Q Q1  /\ multi_ranked s_red1 n N Q1)  by  
  (eapply diamond_multi_ranked ; eauto; eapply diamond_s_red1_s_red; eauto); intros.
  elim ex; intros Q1 (s1&s2).
  assert(ex2: exists M1, multi_ranked s_red1 n M M1 /\ factorable M1 ) 
    by (eapply active_s_red_factorable;  eauto; eapply t_red_preserves_factorable;
        [eapply s_red_to_t_red |]; eauto).
elim ex2; intros M1 (s3 & facM).    exists M1; eauto.
Qed.


Lemma triage_needy: forall f0 f1 f2 M , needs (triage f0 f1 f2 @ M) M. 
Proof. intros;  unfold triage;  repeat eexists; [ eapply t_red_to_s_red; trtac | auto_t]. Qed. 

Lemma eager_needy:  forall M N, needs (eager @ M @N) N. 
Proof. intros; cbv; repeat eexists; [ eapply t_red_to_s_red; trtac |  auto_t]. Qed. 

Lemma bf_needy:  forall M N, needs (bf @ M @ N) M. 
Proof. intros N; repeat eexists; [  cbv;  eapply t_red_to_s_red; trtac |  auto_t]. Qed. 



Theorem bf_to_branch_first_eval: 
  forall M N P, t_red (bf @ M @ N) P -> program M -> program N -> factorable P ->
                            exists Q, branch_first_eval M N Q /\ t_red P Q .
Proof.
  (* need to control the rank   *) 
  cut(forall n h M N P, multi_ranked s_red1 h (bf @ M @ N) P ->
                            program M -> program N -> factorable P -> h<n -> 
                            exists Q, branch_first_eval M N Q /\ s_red P Q) ;
  [intros ? M N P r prM prN fac;
  assert(mr1: exists n, multi_ranked s_red1 n  (bf @ M @ N) P) by 
  (apply multi_ranked_iff_multi_red; eapply2 t_red_to_s_red);
  elim mr1; intros n mr2;  assert(n < S n) by lia;  elim(H (S n) n _ _ _ mr2); auto;
  intros val (b&s); exists val; split; eauto; eapply s_red_to_t_red; eauto
  |].
 
  induction n; intros h M N P r prM prN fac hn; [lia |]. 
  inversion prM as [| | M0 M1 prM0 prM1]; clear prM.
  { (* M is a leaf *)
  assert(bf1: t_red (bf @ M @ N) (M @ N)) by (subst; apply bf_leaf_red).  
  assert(dp1: exists Q, s_red P Q /\ s_red (M @ N) Q) by
  (eapply diamond_s_red; [eapply2 multi_ranked_iff_multi_red | eapply2 t_red_to_s_red]);
  elim dp1; clear dp1; intros P1 (?&?);
    assert(P1 = M @ N) by (subst; apply programs_are_stable2; eauto; eapply pr_stem; eauto);
    subst;  exists (△ @ N); split; auto_t.
  }{ (* M is a stem *) 
  assert(bf1: t_red (bf @ M @ N) (M @ N)) by (subst; eapply bf_stem_red);   
  assert(dp1: exists Q, s_red P Q /\ s_red (△ @ M0 @ N) Q) by
  (subst; eapply diamond_s_red; [eapply2 multi_ranked_iff_multi_red | eapply2 t_red_to_s_red]);
  elim dp1; clear dp1; intros P1 (?&?);
  assert(P1 = △ @ M0 @ N) by  (apply programs_are_stable2; auto; apply pr_fork; auto); subst;
    exists (△ @ M0 @ N); split; auto_t.
  }{ (* M is a fork, so examine its left branch. First, prepare induction. *) 
   caseEq h;
     [ intros [=] | intros h' [=]]; inversion r; subst; clear r; inv1 factorable; [lia | invsub].
   inversion prM0  as [| M2 prM2 | M2 M3 prM2 prM3]; clear prM0; subst; auto_t. 
  { (* fork of leaf *) 
  exists M1; split; auto_t.  
  assert(dp1: exists Q, s_red P Q /\ s_red M1 Q) by  
      (eapply diamond_s_red;
       [eapply multi_ranked_iff_multi_red | eapply t_red_to_s_red; apply bf_fork_leaf_red]; auto_t); 
    elim dp1; clear dp1; intros P1 (?&?);  
  assert(P1 = M1) by (apply programs_are_stable2; auto); subst; auto. 
  }
  { (*  fork of stem  *)
  (* the upper square in Figure 7.5 *) 
  assert(bf1: t_red (bf @ (△ @ (△@ M2) @ M1) @ N) (eager @ (bf @ (bf @ M2 @ N)) @ (bf @ M1 @ N)))
    by apply bf_fork_stem_red.
 assert(mr1: exists n, multi_ranked t_red1 n (bf @ (△ @ (△@ M2) @ M1) @ N) (eager @ (bf @ (bf @ M2 @ N)) @ (bf @ M1 @ N))) 
    by (eapply multi_ranked_iff_multi_red; eauto).
  elim mr1; clear mr1; intros k mr2. 
  caseEq k; intros; subst; [ inversion mr2 | inversion mr2 as [ | ? ? Q0 ? ? ?]]; clear mr2; subst.  
  assert(hap1 (bf @ (△ @ (△ @ M2) @ M1) @ N) Q0). eapply2 program_application2_t_red1. 
  1,2: program_tac.
  elim(program_application2_s_red1 _ _ H0 bf (△ @ (△ @ M2) @ M1) N);  intros; clear H0; eauto; subst; 
    [eapply2 IHn; program_tac |  | program_tac | program_tac].
  assert(Q0 = N0) by eapply2 hap1_functional; subst. 
  assert(dp1: exists Q, s_red P Q /\ multi_ranked s_red1 h'  (eager @ (bf @ (bf @ M2 @ N)) @ (bf @ M1 @ N)) Q). 
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. apply t_red_to_s_red.
  apply multi_ranked_iff_multi_red; eauto.
  elim dp1; clear dp1; intros P1 (?&?). 
  assert(factorable P1) by (eapply t_red_preserves_factorable; eauto; eapply2 s_red_to_t_red). 
(* the middle square in Figure 7.5 *) 
  assert(nd1: exists M3, multi_ranked s_red1 h' (bf @ M1 @ N) M3 /\ factorable M3) by
  (eapply needy_s_red_factorable;  eauto; apply eager_needy).
  elim nd1; clear nd1; intros P_MN (?&?).
  assert(eval1: exists Q : Tree, branch_first_eval M1 N Q /\ s_red P_MN Q) by (eapply2 IHn; lia). 
  elim eval1; clear eval1; intros Q2 (?&?).
  assert(t_red (bf@M1 @ N) Q2) by eapply2 branch_first_eval_to_bf.
  assert(program Q2) by eapply2 branch_first_program. 
  assert(dp2: exists Q, s_red P1 Q /\ multi_ranked s_red1 h'  (bf @ (bf @ M2 @ N) @ Q2) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  apply t_red_to_s_red. aptac. trtac. eauto. apply eager_of_factorable; eapply2 programs_are_factorable.  
  elim dp2; clear dp2; intros P2 (?&?). 
  assert(factorable P2) by (eapply t_red_preserves_factorable; [ apply s_red_to_t_red | ]; eauto). 
  (* the lower square in Figure 7.5  *)
  assert(nd2: exists  Q, multi_ranked s_red1 h' (bf @ M2 @ N) Q /\ factorable Q) . 
  eapply needy_s_red_factorable; eauto; apply bf_needy.
  elim nd2; clear nd2; intros Q (?&?). 
  assert(eval2: exists Q3 : Tree, branch_first_eval M2 N Q3 /\ s_red Q Q3) by (eapply2 IHn; lia). 
  elim eval2; clear eval2; intros Q3 (?&?).
  assert(t_red (bf @ M2 @ N) Q3) by (eapply branch_first_eval_to_bf; eauto).
  assert(program Q3) by (eapply branch_first_program; eauto).
  assert(dp3: exists Q, s_red P2 Q /\ multi_ranked s_red1 h'  (bf @ Q3 @ Q2) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  eapply t_red_to_s_red. aptac. aptac. zerotac. eauto. zerotac. zerotac. zerotac. 
  elim dp3; clear dp3; intros P3 (?&?).
  (* Finally ... *)
  assert(eval3: exists Q : Tree, branch_first_eval Q3 Q2 Q /\ s_red P3 Q)  by
  (eapply2 IHn; eapply t_red_preserves_factorable; [ eapply2 s_red_to_t_red | auto]). 
  elim eval3; clear eval3; intros val (?&?).
  exists val; split; eauto; [ eapply2 e_fork_stem | repeat eapply2 transitive_red].
  }
  { (* Fork of fork. the upper square in Figure 7.4 *)
    inversion prN; subst.
    (* 3 *) 
    eelim (diamond_t_red (bf @ (△ @ (△ @ M2 @ M3) @ M1) @ △)  M2 _ P); intros. 
    2: eapply s_red_to_t_red; eapply multi_ranked_iff_multi_red; auto_t.
    split_all. 
    assert(x = M2) . apply programs_are_stable2. eapply t_red_to_s_red; eauto. auto. subst.
    exists M2; split; auto_t. eapply t_red_to_s_red; eauto.
    (* 2 *)
    assert(bf1: t_red (bf @ (△ @ (△@ M2 @ M3) @ M1) @ (Node @ M)) (bf @ M3 @ M))
      by eapply bf_fork_fork_stem_red.
    assert(mr1: exists n, multi_ranked t_red1 n (bf @ (△ @ (△@ M2 @ M3) @ M1) @ (Node @ M)) (bf @ M3 @ M))
    by (eapply multi_ranked_iff_multi_red; eauto).
  elim mr1; clear mr1; intros k mr2. 
  caseEq k; intros; subst.
  assert(forall red t1 t2, multi_ranked red 0 t1 t2 -> t1 = t2) by (intros red t1 t2 aux; inversion aux; auto). 
  assert((bf @ (△ @ (△ @ M2 @ M3) @ M1) @ (△ @ M)) = (bf @ M3 @ M)) by (eapply H1; eauto). 
  inv_out H3.
  assert(forall M, Node @ M <> M). clear. induction M; try discriminate. 
  intro.   inv_out H. tauto.
  cut False; [ tauto | eapply H3; eauto].
  (* 2 *)
  inversion mr2; subst; clear mr2. 
  assert(hap1 (bf @ (△ @ (△ @ M2 @ M3) @ M1) @ (Node @ M)) N). eapply2 program_application2_t_red1. 
  1,2: program_tac.
  elim(program_application2_s_red1 _ _ H0 bf (△ @ (△ @ M2 @ M3) @ M1) (Node @ M));  intros; clear H0; eauto; subst; 
    [eapply2 IHn; program_tac |  | program_tac | program_tac].
  assert(N = N0) by eapply2 hap1_functional; subst. 
  assert(dp1: exists Q, s_red P Q /\ multi_ranked s_red1 h' (bf @ M3 @ M) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. apply t_red_to_s_red.
  apply multi_ranked_iff_multi_red; eauto.
  elim dp1; clear dp1; intros P1 (?&?). 
  assert(factorable P1) by (eapply t_red_preserves_factorable; eauto; eapply2 s_red_to_t_red). 
(* the middle square in Figure 7.5 *) 
  assert(eval1: exists Q : Tree, branch_first_eval M3 M Q /\ s_red P1 Q) by (eapply2 IHn; lia). 
  elim eval1; clear eval1; intros Q2 (?&?).
  assert(t_red (bf@M3 @ M) Q2) by eapply2 branch_first_eval_to_bf.
  assert(program Q2) by eapply2 branch_first_program.
  exists Q2; split; auto_t. eapply transitive_red; eauto. 
  (* 1 *)
  assert(bf1: t_red (bf @ (△ @ (△@ M2 @ M3) @ M1) @ (Node @ M @ N1)) (bf @ (bf @ M1 @ M) @ N1))
      by eapply bf_fork_fork_fork_red.
  assert(mr1: exists n, multi_ranked t_red1 n  (bf @ (△ @ (△@ M2 @ M3) @ M1) @ (Node @ M @ N1)) (bf @ (bf @ M1 @ M) @ N1))
    by (eapply multi_ranked_iff_multi_red; eauto). (* ; eapply t_red_to_s_red; eauto). *)  split_all.
  clear bf1. 
  caseEq x; intros; subst.
  assert(forall red t1 t2, multi_ranked red 0 t1 t2 -> t1 = t2) by (intros red t1 t2 aux; inversion aux; auto). 
  assert((bf @ (△ @ (△ @ M2 @ M3) @ M1) @ (△ @ M @ N1)) = (bf @ (bf @ M1 @ M) @ N1)) by (eapply H4; eauto). 
  inv_out H5.
  (* 1 *)
  inversion H3; subst; clear H3.
  assert(hap1 (bf @ (△ @ (△ @ M2 @ M3) @ M1) @ (Node @ M @ N1)) N).  eapply2 program_application2_t_red1. 
  1,2: program_tac.
  elim(program_application2_s_red1 _ _ H0 bf (△ @ (△ @ M2 @ M3) @ M1) (Node @ M @ N1));  intros; clear H0; eauto; subst; 
    [eapply2 IHn; program_tac |  | program_tac | program_tac].
  assert(N = N0) by eapply2 hap1_functional; subst. 
  assert(dp1: exists Q, s_red P Q /\ multi_ranked s_red1 h'  (bf @ (bf @ M1 @ M) @ N1) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. apply t_red_to_s_red.
  apply multi_ranked_iff_multi_red; eauto.
  elim dp1; clear dp1; intros P1 (?&?). 
  assert(factorable P1) by (eapply t_red_preserves_factorable; eauto; eapply2 s_red_to_t_red). 
  (* the middle square in Figure 7.5 *)
  clear prN H5.
  eelim needy_s_red_factorable; intros.
  2: eapply H6. 2: eauto. 2: eapply bf_needy. split_all.
  eelim IHn; intros.   2: eapply H9. 2-4: eauto. 2: lia. split_all.
  assert(t_red (bf@M1 @ M) x0) by eapply2 branch_first_eval_to_bf.
  assert(program x0) by eapply2 branch_first_program. 
  assert(eval2: exists Q3 : Tree, branch_first_eval M1 M Q3 /\ s_red x Q3) by eapply2 IHn.
  elim eval2; clear eval2; intros Q3 (?&?).
  assert(t_red (bf @ M1 @ M) Q3) by (eapply branch_first_eval_to_bf; eauto).
  assert(program Q3) by (eapply branch_first_program; eauto).
  assert(dp3: exists Q, s_red P1 Q /\ multi_ranked s_red1 h'  (bf @ Q3 @ N1) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  eapply t_red_to_s_red. aptac. aptac. zerotac. eauto. zerotac. zerotac. zerotac. 
  elim dp3; clear dp3; intros P3 (?&?).
  (* Finally ... *)
  assert(eval3: exists Q : Tree, branch_first_eval Q3 N1 Q /\ s_red P3 Q)  by
  (eapply2 IHn; eapply t_red_preserves_factorable; [ eapply2 s_red_to_t_red | auto]). 
  elim eval3; clear eval3; intros val (?&?).
  exists val; split; eauto; [ eapply2 e_fork_fork_fork | repeat eapply2 transitive_red].
  Unshelve.
  eapply bf_fork_fork_leaf_red. 
  }
  }
Qed.


Theorem branch_first_eval_iff_bf:
  forall M N P, program M -> program N -> program P -> (branch_first_eval M N P <-> t_red (bf @ M @ N) P).
Proof.
  intros; split; [ apply branch_first_eval_to_bf; auto | ]. 
  intros; eelim bf_to_branch_first_eval; intros; eauto.
  2: eapply programs_are_factorable; eauto.
  split_all.
  replace P with x; auto.
  eapply programs_are_stable2; auto. eapply t_red_to_s_red; eauto.
Qed.
