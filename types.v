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
(*              Tree Types for Tree-Calculus                          *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


(* adapted from SKQ_contexts_1001.v *) 


Require Import String Arith Lia Bool List Nat Datatypes.
Require Import terms.

Open Scope string_scope.
Open Scope nat_scope.

Set Default Proof Using "Type".


Inductive dtype : Set :=
  Var :  nat -> dtype (* false if expecting  a function type *) 
| Quant : dtype -> dtype
| Funty : dtype -> dtype -> dtype 
| Leaf : dtype
| Stem : dtype -> dtype
| Fork : dtype -> dtype -> dtype
| Asf : dtype -> dtype 
. 


(* Principal types of programs show their structure as a binary tree *) 


  
Fixpoint  program_type p :=
  match p with
  | Node => Leaf
  | p1 @ p2 =>
    match program_type p1 with
      Leaf => Stem (program_type p2)
    | Stem ty1 => Fork ty1 (program_type p2)
    | _ => Funty Leaf Leaf  (* dummy value *) 
    end
  | _ => Funty Leaf Leaf (* dummy value *) 
  end.


(* Pattern-matching lemmas for comparing 2 naturals 
   Similar to lemmas in Compare_dec *)

Definition test : forall n m : nat, {n <= m} + {n > m}.
Proof.
simple induction n; simple induction m; simpl in |- *; auto with arith.
intros m' H'; elim (H m'); auto with arith.
Defined.
(* Transparent test. *)

Definition le_lt : forall n m : nat, n <= m -> {n < m} + {n = m}.
Proof.
simple induction n; simple induction m; simpl in |- *; auto with arith.
intros m' H1 H2; elim (H m'); auto with arith.
Defined.
(* Transparent le_lt. *)

Definition compare : forall n m : nat, {n < m} + {n = m} + {n > m}.
Proof.
intros n m; elim (test n m); auto with arith.
left; apply le_lt; trivial with arith.
Defined.

(* Lifting *)

Definition relocate (i k n : nat) :=
  match test k i with
   (* k<=i *) | left _ => n+i
   (* k>i  *) | _ => i
  end.

Lemma relocate_null :
forall (n n0 : nat), relocate n n0 0 = n.
Proof. intros; unfold relocate; case (test n0 n); intro; auto with arith. Qed.

Lemma relocate_lessthan : forall m n k, m<=k -> relocate k m n = (n+k). 
Proof. intros; unfold relocate. elim(test m k); intros; auto. lia.  Qed.

Lemma relocate_greaterthan : forall m n k, m>k -> relocate k m n = k. 
Proof. intros; unfold relocate. elim(test m k); intros; auto; lia.  Qed. 

Ltac relocate_lt := 
try (rewrite relocate_lessthan; [| lia]; relocate_lt); 
try (rewrite relocate_greaterthan; [| lia]; relocate_lt);
try(rewrite relocate_null). 


Lemma relocate_zero_succ :
forall n k, relocate 0 (S n) k = 0.
Proof.  auto. Qed.

Lemma relocate_succ :
forall n n0 k, relocate (S n) (S n0) k = S(relocate n n0 k).
Proof. 
intros; unfold relocate. elim(test(S n0) (S n)); elim(test n0 n); intros; auto; lia. 
Qed. 

Lemma relocate_mono : forall M N n k, relocate M n k = relocate N n k -> M=N. 
Proof. intros M N n k; unfold relocate; elim(test n M); elim(test n N); intros; auto; lia. Qed. 

Lemma relocate_null2 :
forall n k, relocate 0 (S n) k = 0.
Proof. intros; auto; lia.  Qed. 


Definition relocatek1 k i := relocate i k 1. 


Lemma relocatek10:  forall fixed, map (relocatek1 0) fixed = map S fixed.
Proof. induction fixed; simpl; auto; f_equal; auto; unfold relocatek1; rewrite relocate_lessthan; lia. Qed. 


Ltac relocate_tac :=
  (rewrite relocate_lessthan; [ | lia])
  || (rewrite relocate_greaterthan; [ | lia]).


Lemma map_relocate: forall ns k,  (map (fun i : nat => relocate i 0 k) ns) = map (add k) ns.
Proof.  induction ns; intros; simpl; f_equal; auto; rewrite relocate_lessthan; try lia. Qed.


Fixpoint lift_rec (L : dtype) : nat -> nat -> dtype :=
  fun k n => 
  match L with
  | Var i => Var (relocate i k n)
  | Leaf => Leaf
  | Stem ty => Stem (lift_rec ty k n)
  | Fork ty1 ty2 => Fork (lift_rec ty1 k n) (lift_rec ty2 k n)
  | Funty ty1 ty2 => Funty (lift_rec ty1 k n) (lift_rec ty2 k n)
  | Quant ty => Quant (lift_rec ty (S k) n)
  | Asf ty => Asf (lift_rec ty k n) 
  end.

Definition lift (n : nat) (ty : dtype) := lift_rec ty 0 n.


(* Lifting lemmas *)


Lemma restore_lift: forall ty k, lift_rec ty 0 k = lift k ty. Proof. auto. Qed. 

Lemma lift_stem: forall k ty, lift k (Stem ty) = Stem (lift k ty). Proof. auto. Qed. 


Lemma lift_rec_null_term : 
forall (U : dtype)(n: nat), lift_rec U n 0 = U.
Proof. simple induction U; intros; simpl; f_equal; auto; relocate_lt; auto. Qed. 

Lemma lift1 :
 forall (U : dtype) (j i k : nat),
 lift_rec (lift_rec U i j) (j + i) k = lift_rec U i (j + k).
Proof.
simple induction U; intros; simpl in |- *; f_equal; auto. 
unfold relocate. 
elim (test i n); elim (test (j+i) (j+ n)); intros; try lia. 
elim (test (j + i) n); split_all; try lia. 
replace (S(j+i)) with (j + (S i)) by lia. rewrite H;  auto. 
Qed. 

Lemma lift_lift_rec :
 forall (U : dtype) (k p n i : nat),
 i <= n ->
 lift_rec (lift_rec U i p) (p + n) k = lift_rec (lift_rec U n k) i p.
Proof.
simple induction U; simpl in |- *;  intros; f_equal; auto.
(* Var *) 
unfold relocate.
elim(test i n); intros; try lia. 
elim(test n0 n); intros; try lia. 
elim(test (p+n0) (p+n)); intros; try lia. 
elim(test i (k+n)); intros; try lia. 
assert(k+(p+n) = p+ (k+n)) by lia. 
rewrite H0; auto. 
elim(test (p+n0) (p+n)); intros; try lia. 
elim(test i n); intros; try lia. 
elim(test n0 n); intros; try lia. 
elim(test (p+n0) n); intros; try lia. 
elim(test i n); intros; try lia. 
replace (S (p+n)) with (p + (S n)) by lia. rewrite H; auto; lia. 
Qed. 


Lemma lift_lift_term :
 forall (U : dtype) (k p n : nat),
 lift_rec (lift p U) (p+ n) k = lift p (lift_rec U n k).
Proof.
unfold lift in |- *; intros; apply lift_lift_rec; trivial with arith.
Qed.

Lemma liftrecO : forall (U : dtype) (n : nat), lift_rec U n 0 = U.
Proof.
simple induction U; simpl in |- *; intros; intros; relocate_lt; congruence. 
Qed.

Lemma liftO : forall (U : dtype) , lift 0 U = U.
Proof.
unfold lift in |- *; intros; apply liftrecO.
Qed.

Lemma lift_rec_lift_rec :
 forall (U : dtype) (n p k i : nat),
 k <= i + n ->
 i <= k -> lift_rec (lift_rec U i n) k p = lift_rec U i (p + n).

Proof.
simple induction U; intros; simpl; f_equal; auto.
(* Var *) 
unfold relocate. 
elim(test i n); intros; try lia. 
elim(test k (n0 + n)); intros; try lia.
elim(test k n); intros; try lia. 
(* Ap *)
rewrite H; intros; try lia; auto. 
Qed. 

Lemma lift_rec_lift :
 forall (U : dtype)  (n p k i : nat),
 k <= n -> lift_rec (lift  n U)  k p = lift (p + n) U.
Proof.
unfold lift in |- *; intros; rewrite lift_rec_lift_rec; trivial with arith.
Qed.

Lemma lift_rec_lift2 : 
forall M n k, lift_rec (lift 1 M) (S n) k = lift 1 (lift_rec M n k).
Proof.
intros.
unfold lift. 
replace (S n) with (1+n) by lia.
rewrite lift_lift_rec; auto; lia.
Qed.

Lemma lift_rec_funty:
  forall M N n k, lift_rec (Funty M N) n k = Funty (lift_rec M n k) (lift_rec N n k). 
Proof. auto. Qed. 
Lemma lift_rec_var: forall i n k, lift_rec (Var i) n k = Var (relocate i n k). 
Proof. auto. Qed. 


Lemma lift_rec_null : 
forall (U : dtype) (n: nat), lift_rec U n 0 = U.
Proof. simple induction U; intros; simpl; f_equal; auto; rewrite relocate_null; congruence. Qed.

Ltac  lift_tac := 
rewrite ? lift_rec_funty; rewrite ? lift_rec_var; relocate_lt. 

Lemma lift_rec_fork:
  forall uty vty n k, lift_rec (Fork uty vty) n k = Fork (lift_rec uty n k) (lift_rec vty n k). 
Proof. auto. Qed.


Lemma lift_rec_program_type:
  forall p, program p -> forall n k, lift_rec (program_type p) n k = program_type p.
Proof.  intros p pr; induction pr; intros; simpl; f_equal; eauto. Qed. 


(* Substitution *)


Definition insert_Var (N : dtype) (i k : nat) :=
  match compare k i with
  
   (* k<i *) | inleft (left _) => Var (Nat.pred i)
   (* k=i *) | inleft _ => lift k N
   (* k>i *) | _ => Var i
  end.



Lemma insert_Var_lt : forall M n k, n< k -> insert_Var M n k = Var n.
Proof.
induction M; unfold insert_Var; intros;
( elim (compare k n0) ||  elim (compare k n)); intros; auto; elim a; intros; auto; lia. 
Qed. 

Lemma insert_Var_eq : forall M n k, n= k -> insert_Var M n k = lift k M.
Proof.
induction M; unfold insert_Var; intros; auto; 
  ((elim (compare k n0) || elim (compare k n)); intros; auto; [ 
    elim a; intros; auto; lia
  | unfold lift, lift_rec, relocate; elim(test 0 n); intros; auto; try lia]). 
Qed. 


Lemma insert_Var_gt : forall M n k, n> k -> insert_Var M n k = Var (Nat.pred n).
Proof.
induction M; unfold insert_Var; intros; auto;
(elim (compare k n0) || elim (compare k n)); intros; auto; try lia; elim a; intros; auto; try lia. 
Qed. 

Ltac insert_Var_out := 
try (rewrite insert_Var_lt; [|unfold relocate; intros; auto; lia]; insert_Var_out); 
try (rewrite insert_Var_eq; [|unfold relocate; intros; auto; lia]; insert_Var_out); 
try (rewrite insert_Var_gt; [|unfold relocate; intros; auto; lia]; insert_Var_out). 


Fixpoint subst_rec (L : dtype) : dtype -> nat -> dtype :=
  fun (N : dtype) (k : nat) =>
  match L with
  | Var i => insert_Var N i k
  | Leaf => Leaf
  | Stem M => Stem (subst_rec M N k)
  | Fork M M' => Fork (subst_rec M N k) (subst_rec M' N k)                     
  | Funty M M' => Funty (subst_rec M N k) (subst_rec M' N k)
  | Quant M => Quant (subst_rec M N (S k))
  | Asf M => Asf (subst_rec M N k)
  end.

Lemma subst_rec_var: forall i N k,  subst_rec (Var i) N k = insert_Var N i k.
Proof.  auto. Qed. 
                                                      
Lemma subst_rec_funty: 
  forall M1 M2 N k,
    subst_rec (Funty M1 M2) N k = Funty (subst_rec M1 N k) (subst_rec M2 N k).
Proof.  auto. Qed. 

Lemma subst_rec_fork:
  forall ty1 ty2 uty k, subst_rec (Fork ty1 ty2) uty k = Fork (subst_rec ty1 uty k) (subst_rec ty2 uty k). 
Proof. auto. Qed.


Definition subst (M N : dtype) := subst_rec M N 0.

(* The three cases of substitution of U for (Var n) *)

Lemma subst_eq :
 forall (M U : dtype) (n : nat), subst_rec (Var n) U n = lift n U .
Proof.
simpl in |- *; unfold insert_Var in |- *; intros. 
elim (compare n n); intro P; try lia. 
elim P; intro Q; simpl in |- *; trivial with arith; try lia.
Qed.

Lemma subst_gt :
 forall (M U : dtype) (n p : nat),
 n > p -> subst_rec (Var n) U p = Var (Nat.pred n).
Proof.
simpl in |- *; unfold insert_Var in |- *.
intros; elim (compare p n); intro P.
elim P; intro Q; trivial with arith.
absurd (n > p); trivial with arith; rewrite Q; trivial with arith.
absurd (n > p); auto with arith.
Qed. 

Lemma subst_lt :
 forall (M U : dtype) (n p : nat), p > n -> subst_rec (Var n) U p = Var n.
Proof.
simpl in |- *; unfold insert_Var in |- *.
intros; elim (compare p n); intro P; trivial with arith.
absurd (p > n); trivial with arith; elim P; intro Q; auto with arith.
rewrite Q; trivial with arith.
Qed.



(* Substitution lemma *)

Lemma lift_rec_subst_rec :
 forall (V U : dtype) (k p n : nat),
 lift_rec (subst_rec V U p) (p + n) k =
 subst_rec (lift_rec V (S (p + n)) k) (lift_rec U n k) p.
Proof.
simple induction V; intros;  simpl; auto.
(* 5 Var *)
unfold insert_Var, relocate.
elim (test (S(p + n0)) n); elim (compare p n); intros.
elim a; elim(compare p (k+n)); intros; simpl.  
elim a1; intros; try lia.
unfold relocate. 
elim(test (p+n0) (Nat.pred n)); elim a1; intros; try lia. 
replace (k + Nat.pred n) with (Nat.pred (k + n)) by lia; auto.
all: try lia. 
elim a; intros; simpl.
unfold relocate. elim(test(p+n0) (Nat.pred n)); intros; auto; try lia. 
unfold lift.
rewrite lift_lift_rec; auto; try lia. 
simpl; unfold relocate. 
elim(test (p+n0) n); intros; auto; lia.
(* 4 *)
replace (S (p+n)) with (S p + n) by lia; rewrite H; auto. 
all: f_equal; auto.
Qed. 


Lemma lift_subst :
 forall (U V : dtype) (k n : nat),
 lift_rec (subst U V) n k =
 subst (lift_rec U (S n) k) (lift_rec V n k).
Proof.
unfold subst in |- *; intros.
replace n with (0 + n).
rewrite lift_rec_subst_rec; trivial with arith.
auto. 
Qed.


Ltac insert_Var_tac :=
  (rewrite insert_Var_lt; [ | lia])
  || (rewrite insert_Var_eq; [ | lia])
  || (rewrite insert_Var_gt; [ | lia]);
  unfold lift; rewrite ? lift_rec_null.



Lemma subst_rec_lift_rec :
 forall (U V : dtype) (p q n : nat),
 q <= p + n ->
 n <= q -> subst_rec (lift_rec U n (S p)) V q = lift_rec U n p.
Proof.
simple induction U; intros; simpl in |- *; intros; f_equal; auto. 
unfold insert_Var.
unfold relocate. elim(test n0 n); intros. 
elim(compare q (S p+n)); intros; try lia. 
elim a0; intros; try lia. 
f_equal; lia.
elim(compare q n); intros; try lia. 
elim a; intros; auto; try lia.  auto. 
(* 1 *) 
rewrite H; intros; try lia; auto; rewrite H0; auto; lia.
Qed.


Ltac var_tac :=
  unfold subst, lift; refold lift_rec; refold subst_rec;
  repeat (rewrite subst_rec_lift_rec;  [ | lia | lia]);
  repeat relocate_tac; repeat insert_Var_tac;
    unfold lift; rewrite ? lift_rec_null.


Lemma  subst_rec_lift_rec0 :
  forall ty k p, subst_rec (lift_rec ty (S k) (S p)) (Var 0) k = lift_rec ty (S k) p.
Proof.
  induction ty; intros; simpl; f_equal; auto.
  assert(S k <= n \/ S k > n) by lia; disjunction_tac; repeat relocate_tac.
  insert_Var_tac; simpl; auto. 
  assert(k = n \/ k > n) by lia; disjunction_tac; insert_Var_tac; simpl; auto; var_tac;  f_equal; lia. 
Qed. 


Lemma subst_rec_lift_rec1 :
 forall (U V : dtype) (n p k : nat),
 k <= n ->
 subst_rec (lift_rec U k p) V (p + n) =
 lift_rec (subst_rec U V n) k p.
Proof.
simple induction U; intros; simpl in |- *; intros; auto.
(* 6 Var *) 
unfold insert_Var, relocate. 
elim(test k n); intros. 
elim(compare n0 n); intros; try lia. 
elim a0; intros; try lia. 
elim(compare (p+n0) (p+n)); intros. 
elim a2; intros; simpl; auto; try lia. 
unfold relocate. 
elim(test k (Nat.pred n)); intros; try lia. 
f_equal; lia.
simpl. unfold relocate; simpl.
elim(test k (Nat.pred n)); intros; try lia. 
subst.
elim(compare (p+n) (p+n)); intros. 
elim a1; intros; try lia. 
unfold lift. rewrite lift_rec_lift_rec; intros; auto; try lia.  
unfold lift. rewrite lift_rec_lift_rec; intros; try lia.  
elim(compare (p+n0) (p+n)); intros. 
elim a0; intros; simpl; try lia. 
simpl; unfold relocate. 
elim(test k n); intros; auto; try lia. 
elim(compare (p+n0) n); intros; try lia. 
elim a; intros; try lia. 
elim(compare n0 n); intros; try lia. 
elim a; intros; try lia. 
simpl; unfold relocate. 
elim(test k n); intros; auto; try lia.
(* 5 *) 
replace (S(p+n)) with (p + S n) by lia; rewrite H; intros;  auto; try lia; rewrite H0; intros. 
all: f_equal; auto.
Qed. 

Lemma subst_rec_lift1 :
 forall (U V : dtype) (n p : nat),
 subst_rec (lift p U) V (p + n) = lift p (subst_rec U V n).
Proof.
unfold lift in |- *; intros; rewrite subst_rec_lift_rec1;
 trivial with arith.
Qed.


(* subst_rec_subst_rec *)

Lemma subst_rec_subst_rec :
 forall (V U W : dtype) (p q: nat), q >= p -> 
 subst_rec (subst_rec V U p) W q =
 subst_rec (subst_rec V W (S q)) (subst_rec U W (q-p)) p.
Proof.
simple induction V;  intros; simpl; auto. 
(* 6 *)
assert(n <p \/ n=p \/ n> p) by lia; disjunction_tac; insert_Var_out; simpl; auto; insert_Var_out; auto.
unfold lift. replace q with (p + (q-p)) by lia. rewrite subst_rec_lift_rec1; auto; try lia. 
repeat f_equal; lia.
assert(n < S q \/ n=S q \/ n>  S q) by lia; disjunction_tac; insert_Var_out; simpl; auto; insert_Var_out; auto.
unfold lift; 
rewrite subst_rec_lift_rec; auto; try lia. 
(* 5 *)
all: f_equal; auto. 
(* 1 *)
rewrite H; try lia; repeat f_equal; lia.
Qed.


Lemma subst_rec_subst_0 :
 forall (U V W : dtype) (n : nat),
 subst_rec (subst_rec V U 0) W n =
 subst_rec (subst_rec V W (S n)) (subst_rec U W n) 0.
Proof.
intros; pattern n at 1 3 in |- *.
replace n with (0 + n) by trivial with arith.
simpl. rewrite (subst_rec_subst_rec V U W 0 n); trivial with arith.
f_equal; f_equal; lia. lia.
Qed.


(**************************)
(* The Substitution Lemma *)
(**************************)

Lemma substitution :
 forall (U V W : dtype) (n : nat),
 subst_rec (subst U V) W n =
 subst (subst_rec U W (S n)) (subst_rec V W n).
Proof.
unfold subst in |- *; intros; apply subst_rec_subst_0; trivial with arith.
Qed.

(* to show (\ t)0 -> t  *) 


Lemma subst_lift_null :
forall (W V : dtype)(n : nat), subst_rec (lift_rec W n 1) V n = W.
Proof.
simple induction W; intros; simpl; auto. 
unfold insert_Var, relocate. 
elim(test n0 n); intros; simpl. 
elim(compare n0 (S n)); intros.
elim a0; intros; auto; lia. 
lia. 
elim(compare n0 n); intros.
elim a; intros. lia. 
lia.
auto.
all: f_equal; auto.

Qed. 


(* more  Properties *) 



Lemma subst_rec_lift2 : 
forall M N n , subst_rec (lift 1 M) N (S n)  = lift 1 (subst_rec M N n).
Proof.
intros.
unfold lift. 
replace (S n) with (1+n) by lia.
rewrite subst_rec_lift_rec1; auto. 
lia.
Qed.


Ltac  subst_tac := 
unfold subst; 
rewrite ? subst_rec_funty; rewrite ? subst_rec_var; 
rewrite ? subst_rec_lift_rec; try lia; rewrite ? lift_rec_null; 
unfold subst_rec; fold subst_rec; insert_Var_out; unfold Nat.pred.  


Lemma lift0: forall ty, lift 0 ty = ty. Proof. intro; unfold lift; rewrite lift_rec_null; auto. Qed. 


Lemma lift_rec_subst_rec1:
  forall ty u n k,  k<= n -> lift_rec(subst_rec ty u n) k 1 = subst_rec (lift_rec ty k 1) u (S n). 
Proof.
  induction ty; intros; simpl; auto;  [
  | rewrite IHty; auto
  | rewrite IHty1; auto; rewrite IHty2
  | rewrite IHty; auto
  | rewrite IHty1; auto; rewrite IHty2
  | rewrite IHty; auto
] ; auto; try lia.
  assert(n < n0 \/ n= n0 \/ n> n0) by lia.
  disjunction_tac. 
  rewrite insert_Var_lt; simpl; auto. 
  assert(k<= n \/ k>n) by lia.
  inv_out H0.
  rewrite ! relocate_lessthan; auto.
  rewrite insert_Var_lt; auto; lia.
  rewrite ! relocate_greaterthan; auto.
  rewrite insert_Var_lt; auto; lia.
  rewrite insert_Var_eq; auto.
  rewrite ! relocate_lessthan; auto.
  rewrite insert_Var_eq; auto; try lia.
  rewrite lift_rec_lift. f_equal; lia. 
  apply 0.
  auto.
  rewrite ! relocate_lessthan; auto; try lia. 
  rewrite ! insert_Var_gt; auto; try lia; simpl; auto.
  rewrite ! relocate_lessthan; auto; try lia.
  f_equal; lia.
Qed.



Lemma subst_rec_program_type:
  forall p, program p -> forall ty k, subst_rec (program_type p) ty k = program_type p.
Proof.  intros p pr; induction pr; intros; simpl; f_equal; eauto. Qed. 



(* Contexts *)

Fixpoint get x (gamma: list (string * dtype)) :=
  match gamma with
  | (s,ty)::gamma1 => if (s =? x)%string then Some ty else get x gamma1
  | _ => None
  end.

Definition lift_rec_context n k := map (fun (p:string * dtype)  => (fst p, lift_rec (snd p) n k)).
Definition lift_context := lift_rec_context 0. 

Lemma lift_lift_term_context:
  forall gamma (k p n : nat), lift_rec_context (p + n) k (lift_context p gamma) =
                              lift_context p (lift_rec_context n k gamma).
Proof.
  induction gamma; intros; simpl; auto.
  caseEq a; intros; subst; simpl.
  replace (lift_rec (lift_rec d 0 p) (p+n) k) with (lift_rec (lift p d) (p+n) k) by auto.
  rewrite lift_lift_term; auto. rewrite IHgamma; auto. 
Qed.

  
 Lemma lift_rec_lift_context: 
    forall gamma  (n p k : nat), nat -> k <= n -> lift_rec_context k p  (lift_context n gamma)
                                                  = lift_context (p + n) gamma. 
Proof.
  induction gamma; intros; simpl; auto.
  caseEq a; intros; subst; simpl.
  replace (lift_rec (lift_rec d 0 n) k p) with (lift_rec (lift n d) k p) by auto.
  rewrite lift_rec_lift; auto. rewrite IHgamma; auto. 
Qed.


Lemma lift_rec_lift2_context:
  forall gamma (n k : nat), lift_rec_context (S n) k (lift_context 1 gamma)  =
                            lift_context 1 (lift_rec_context n k gamma).
Proof.
  induction gamma; intros; simpl; auto.
  caseEq a; intros; subst; simpl.
  replace (lift_rec (lift_rec d 0 1) (S n) k) with (lift_rec (lift 1 d) (S n) k) by auto.
  rewrite lift_rec_lift2.  rewrite IHgamma. auto. 
Qed.

  

Lemma lift_context_zero:
  forall gamma, lift_context 0 gamma = gamma.
Proof.
  induction gamma; intros; simpl; f_equal; auto.
  unfold lift; rewrite lift_rec_null; caseEq a; intros; auto. 
Qed.

Lemma lift_context_plus:
  forall gamma m n, lift_context m (lift_context n gamma) = lift_context (m+n) gamma.
Proof.
  induction gamma; intros; simpl; f_equal; auto.
  rewrite lift_rec_lift_rec; try lia; auto.
Qed.

Definition subst_rec_context uty k := map (fun (p:string * dtype)  => (fst p, subst_rec (snd p) uty k)).


Lemma subst_rec_lift_rec_context:
  forall gamma V (p q : nat), q <= p  -> 
    subst_rec_context V q (lift_context (S p) gamma) = lift_context p gamma. 
Proof.
  induction gamma; intros; simpl; unfold lift; f_equal; auto. rewrite subst_rec_lift_rec; auto; try lia. 
Qed.

Lemma get_lift_rec:
  forall gamma n k x, get x (lift_rec_context n k gamma) =
                      match get x gamma with
                      | Some ty => Some (lift_rec ty n k)
                      | None => None
                      end.
Proof.
  induction gamma; intros; simpl in *; try discriminate; auto.
  caseEq a; intros; subst; simpl; auto; caseEq (s=?x)%string; intros; auto. 
Qed.

Lemma get_subst_rec:
  forall gamma u k x, get x (subst_rec_context u k gamma) =
                         match get x gamma with
                         | Some ty => Some (subst_rec ty u k)
                         | _ => None
                         end.
Proof.
  induction gamma; intros; simpl in *; try discriminate; auto.
  caseEq a; intros; subst; simpl; auto; caseEq (s=?x)%string; intros; auto. 
Qed.


Fixpoint normal_type gamma t :=
  match t with
  | Ref x => get x gamma
  | Node => Some Leaf
  | Node @ t1 => match normal_type gamma t1 with | Some ty => Some (Stem ty) | _ => None end
  | Node @ t1 @ t2 =>
    match (normal_type gamma t1, normal_type gamma t2) with
    | (Some ty1, Some ty2) => Some (Fork ty1 ty2)
    | (_,_) => None
    end
  | _ => None
  end. 




(* Quantification *)


Fixpoint quant n ty :=
  match n with
  | 0 => ty
  | S n1 => quant n1 (Quant ty)
  end.


Lemma quant0: forall ty, ty = quant 0 ty. Proof. auto. Qed.

Lemma quant_succ: forall n ty, quant n (Quant ty) = Quant (quant n ty).
Proof.  induction n; intros; simpl; auto. Qed. 

Lemma quant_plus: forall m n ty, quant (m+n) ty = quant m (quant n ty).
Proof.  induction m; intros; simpl; auto. rewrite IHm. rewrite quant_succ; auto. Qed. 

Lemma quant_succ2: forall n ty, Quant (quant n ty) = quant (S n) ty.
Proof. intros; simpl; rewrite quant_succ; auto. Qed. 


Lemma quant_succ3: forall k ty, quant k (Quant ty) = quant (S k) ty.  Proof. auto. Qed. 


Lemma lift_rec_preserves_quant :
  forall n ty p k, lift_rec (quant n ty) p k = quant n (lift_rec ty (n+p) k).
Proof.
  induction n; intros; simpl; auto; rewrite ! quant_succ; simpl; f_equal; auto;
  rewrite IHn; f_equal; f_equal; lia. 
Qed.


Lemma subst_rec_preserves_quant :
  forall n ty uty k, subst_rec (quant n ty) uty k = quant n (subst_rec ty uty (n+k)).
Proof.
  induction n; intros; simpl; auto; rewrite ! quant_succ; simpl; f_equal; auto.
  rewrite IHn; f_equal; f_equal; lia. 
Qed.

 
Lemma subst_preserves_quant :
  forall n ty uty, subst (quant n ty) uty = quant n (subst_rec ty uty n).
Proof. intros; unfold subst; rewrite subst_rec_preserves_quant; repeat f_equal; lia. Qed.




Lemma quant_mono:
  forall m n ty1 ty2, quant m ty1 = quant n ty2 ->
                                  (n>= m /\ ty1 = quant (n-m) ty2) \/ exists ty, ty2 = Quant ty. 
Proof.
  induction m; intros; subst; simpl in *; subst.
  left; split; [ lia | f_equal; lia]. 
  rewrite quant_succ in *.   caseEq n; intros; subst; simpl in *; inv_out H; eauto.
  rewrite quant_succ in *; inv_out H1. eelim IHm; intros; eauto; split_all;
  left; split; auto; lia. 
Qed.
  


Lemma subst_rec_quant: forall n ty uty k, subst_rec (quant n ty) uty k = quant n (subst_rec ty uty (n+k)).
Proof. induction n; intros; simpl; auto; rewrite IHn; simpl; f_equal; lia. Qed. 

Lemma subst_quant: forall n ty uty, subst (quant n ty) uty = quant n (subst_rec ty uty n).
Proof. intros; unfold subst; rewrite subst_rec_quant; auto; repeat f_equal; lia. Qed. 


Lemma quant_mono2:
  forall n2 ty2 n1 ty1,
    quant n1 ty1 = quant n2 ty2 ->
    (forall ty, ty1 <> Quant ty) -> (forall ty, ty2 <> Quant ty) ->
    n1 = n2 /\ ty1 = ty2.
Proof.
  induction n2; intros; simpl in *.
  caseEq n1; intros; subst; simpl in *; auto; eelim (H1 (quant n ty1)); intros;   rewrite quant_succ; auto.
  caseEq n1; intros; subst; simpl in *; auto; subst.
  assert(quant n2 (Quant ty2) <> Quant (quant n2 ty2)). eapply H0. rewrite quant_succ in *; congruence.
  rewrite quant_succ in *; inv_out H.   eelim IHn2; intros; eauto.
  rewrite quant_succ in *; inv_out H3; auto.   
Qed.


Ltac no_quant2_tac :=
   rewrite ? quant_succ2 in *; 
   eelim quant_mono2; intros;   [ | eauto | repeat intro; discriminate | repeat intro; discriminate ];
   try discriminate.


Lemma quant_plus2: forall m n ty,  quant(m+n) ty = quant n (quant m ty).
Proof. intros; replace (m+n) with (n + m) by lia; eapply quant_plus. Qed. 



Ltac no_quant :=
  split_all;
  match goal with
  | H : _ = quant ?k _ |- _ => caseEq k; intros; subst; simpl in *; rewrite ? quant_succ in *; inv_out H
  | H : quant ?k _ = _ |- _ => caseEq k; intros; subst; simpl in *; rewrite ? quant_succ in *; inv_out H
  | _ => idtac
           end. 


(* Quantification *)


Fixpoint quantf n ty :=
  match n with
  | 0 => ty
  | S n1 => quantf n1 (Asf ty)
  end.


Lemma quantf0: forall ty, ty = quantf 0 ty. Proof. auto. Qed.

Lemma quantf_succ: forall n ty, quantf n (Asf ty) = Asf (quantf n ty).
Proof.  induction n; intros; simpl; auto. Qed. 

Lemma quantf_plus: forall m n ty, quantf (m+n) ty = quantf m (quantf n ty).
Proof.  induction m; intros; simpl; auto. rewrite IHm. rewrite quantf_succ; auto. Qed. 

Lemma quantf_succ2: forall n ty, Asf (quantf n ty) = quantf (S n) ty.
Proof. intros; simpl; rewrite quantf_succ; auto. Qed. 


Lemma quantf_succ3: forall k ty, quantf k (Asf ty) = quantf (S k) ty.  Proof. auto. Qed. 


Lemma lift_rec_preserves_quantf :
  forall n ty p k, lift_rec (quantf n ty) p k = quantf n (lift_rec ty p k).
Proof.
  induction n; intros; simpl; auto; rewrite ! quantf_succ; simpl; f_equal; auto;
  rewrite IHn; f_equal; f_equal; lia. 
Qed.


Lemma subst_rec_preserves_quantf :
  forall n ty uty k, subst_rec (quantf n ty) uty k = quantf n (subst_rec ty uty k).
Proof.  induction n; intros; simpl; auto; rewrite ! quantf_succ; simpl; f_equal; auto. Qed.

 
Lemma subst_preserves_quantf :
  forall n ty uty, subst (quantf n ty) uty = quantf n (subst ty uty).
Proof. intros; unfold subst; rewrite subst_rec_preserves_quantf; auto. Qed.




Lemma quantf_mono:
  forall m n ty1 ty2, quantf m ty1 = quantf n ty2 ->
                                  (n>= m /\ ty1 = quantf (n-m) ty2) \/ exists ty, ty2 = Asf ty. 
Proof.
  induction m; intros; subst; simpl in *; subst.
  left; split; [ lia | f_equal; lia]. 
  rewrite quantf_succ in *.   caseEq n; intros; subst; simpl in *; inv_out H; eauto.
  rewrite quantf_succ in *; inv_out H1. eelim IHm; intros; eauto; split_all;
  left; split; auto; lia. 
Qed.
  


Lemma quantf_mono2:
  forall n2 ty2 n1 ty1,
    quantf n1 ty1 = quantf n2 ty2 ->
    (forall ty, ty1 <> Asf ty) -> (forall ty, ty2 <> Asf ty) ->
    n1 = n2 /\ ty1 = ty2.
Proof.
  induction n2; intros; simpl in *.
  caseEq n1; intros; subst; simpl in *; auto; eelim (H1 (quantf n ty1)); intros;   rewrite quantf_succ; auto.
  caseEq n1; intros; subst; simpl in *; auto; subst.
  assert(quantf n2 (Asf ty2) <> Asf (quantf n2 ty2)). eapply H0. rewrite quantf_succ in *; congruence.
  rewrite quantf_succ in *; inv_out H.   eelim IHn2; intros; eauto.
  rewrite quantf_succ in *; inv_out H3; auto.   
Qed.


Ltac no_quantf2_tac :=
   rewrite ? quantf_succ2 in *; 
   eelim quantf_mono2; intros;   [ | eauto | repeat intro; discriminate | repeat intro; discriminate ];
   try discriminate.




Ltac no_quantf :=
  split_all;
  match goal with
  | H : _ = quantf ?k _ |- _ => caseEq k; intros; subst; simpl in *; rewrite ? quantf_succ in *; inv_out H
  | H : quantf ?k _ = _ |- _ => caseEq k; intros; subst; simpl in *; rewrite ? quantf_succ in *; inv_out H
  | _ => idtac
           end. 


(*** quanta *)


Lemma quanta_cases: 
  forall (bs: list bool),
    bs = nil \/ bs = app (removelast bs) (true :: nil) \/ bs = app (removelast bs) (false :: nil).  
Proof.
  intros.
  assert(bs = nil \/ bs = app (removelast bs) (last bs true :: nil)). 
  caseEq bs; intros; subst; auto; right; (rewrite <- app_removelast_last; auto; discriminate). 
  disjunction_tac; auto; right;
    rewrite H0 at 1; caseEq (last bs true); intros; subst; auto; rewrite H in *; auto. 
Qed.


Fixpoint quanta bs ty :=
  match bs with
    nil => ty
  | true :: bs1 => quanta bs1 (Quant ty)
  | false :: bs1 => quanta bs1 (Asf ty)
  end.

Fixpoint quant_count bs :=
  match bs with
    nil => 0
  | true :: bs1 => S (quant_count bs1)
  | false :: bs1 => quant_count bs1
  end.



Lemma  quanta_is_quant:
  forall bs uty ty,
    Quant uty = quanta bs ty -> bs = nil \/
                                (exists bs1, bs = app bs1 (true :: nil) /\ uty = quanta bs1 ty).
Proof.
  induction bs; intros; simpl in *; auto. 
  caseEq a; intros; subst; auto; eelim IHbs; intros; eauto; subst; simpl in *.
  inv_out H. right; exists nil; auto.
  split_all.   right; exists (true :: x); simpl; auto. discriminate. 
  split_all.   right; exists (false :: x); split;  simpl; auto.
Qed. 
 
Lemma  quanta_is_asf:
  forall bs uty ty,
    Asf uty = quanta bs ty -> bs = nil \/
                              (exists bs1, bs = app bs1 (false :: nil) /\ uty = quanta bs1 ty).
Proof.
  induction bs; intros; simpl in *; auto. 
  caseEq a; intros; subst; auto; eelim IHbs; intros; eauto; subst; simpl in *. 
  discriminate. 
  split_all.   right; exists (true :: x); simpl; auto.
  inv_out H. right; exists nil; auto. 
  split_all.   right; exists (false :: x); split; simpl; auto.
Qed.



 
Lemma quant_count_app: forall bs1 bs2, quant_count (bs1 ++ bs2) = quant_count bs1 + (quant_count bs2). 
Proof. induction bs1; intros; simpl; auto; rewrite IHbs1; caseEq a; intros; subst; simpl; auto. Qed.

Lemma quanta_not_leaf: forall bs ty2, Leaf = quanta bs ty2 -> bs = nil.
Proof.
  induction bs; intros; simpl in *; auto_t; caseEq a; intros; subst; auto; no_quant;
    assert(bs = nil) by eauto; subst; simpl in *; discriminate.
Qed.

Lemma quanta_not_stem: forall bs ty1 ty2, Stem ty1 = quanta bs ty2 -> bs = nil.
Proof.
  induction bs; intros; simpl in *; auto_t; caseEq a; intros; subst; auto; no_quant;
    assert(bs = nil) by eauto; subst; simpl in *; discriminate.
Qed.

Lemma quanta_not_fork: forall bs uty1 vty1 ty2, Fork uty1 vty1 = quanta bs ty2 -> bs = nil.
Proof.
  induction bs; intros; simpl in *; auto_t; caseEq a; intros; subst; auto; no_quant;
    assert(bs = nil) by eauto; subst; simpl in *; discriminate.
Qed.

Lemma quanta_not_funty: forall bs uty1 vty1 ty2, Funty uty1 vty1 = quanta bs ty2 -> bs = nil.
Proof.
  induction bs; intros; simpl in *; auto_t; caseEq a; intros; subst; auto; no_quant;
    assert(bs = nil) by eauto; subst; simpl in *; discriminate.
Qed.


Ltac no_quanta := 
  split_all;
  match goal with
  | H : Leaf = quanta ?bs _ |- _ => assert (bs = nil) by (eapply quanta_not_leaf; eauto); subst; simpl in *
  | H : Stem _ = quanta ?bs _ |- _ => assert (bs = nil) by (eapply quanta_not_stem; eauto); subst; simpl in *
  | H : Fork _ _ = quanta ?bs _ |- _ => assert (bs = nil) by (eapply quanta_not_fork; eauto); subst; simpl in *
  | H : Funty _ _ = quanta ?bs _ |- _ => assert (bs = nil) by (eapply quanta_not_funty; eauto); subst; simpl in *
 | _ => idtac
  end; try discriminate. 




Lemma lift_rec_preserves_quanta :
  forall bs ty p k, lift_rec (quanta bs ty) p k = quanta bs (lift_rec ty (quant_count bs +p) k).
Proof. induction bs; intros; simpl; auto; caseEq a; intros; subst; simpl; rewrite IHbs; simpl; auto. Qed.


Lemma subst_rec_preserves_quanta :
  forall bs ty uty k, subst_rec (quanta bs ty) uty k = quanta bs (subst_rec ty uty (quant_count bs+k)).
Proof. induction bs; intros; simpl; auto; caseEq a; intros; subst; simpl; rewrite IHbs; simpl; auto. Qed.

Lemma quanta_app: forall bs1 bs2 ty, quanta (bs1  ++ bs2) ty = quanta bs2 (quanta bs1 ty).
Proof.  induction bs1; intros; simpl; auto; caseEq a; intros; simpl; rewrite IHbs1; auto. Qed. 


Lemma quant_as_quanta: forall n ty, quant n ty = quanta (iter n (cons true) nil) ty. 
Proof.  induction n; intros; simpl; auto. Qed. 

Lemma quantf_as_quanta: forall n ty, quantf n ty = quanta (iter n (cons false) nil) ty. 
Proof.  induction n; intros; simpl; auto. Qed. 

Lemma quant_count_iter_true: forall n, quant_count (iter n (cons true) nil) = n.
Proof. induction n; intros; simpl; auto. Qed. 
  
Lemma quant_count_iter_false: forall n, quant_count (iter n (cons false) nil) = 0.
Proof. induction n; intros; auto. Qed. 
  



Fixpoint quant_to_quanta n :=
  match n with
  | 0 => nil
  | S n1 => true :: (quant_to_quanta n1)
  end.

Lemma quant_count_quant_to_quanta: forall n, quant_count (quant_to_quanta n) = n.
Proof.  induction n; intros; simpl; auto. Qed.

Lemma quanta_to_quant: forall n ty, quanta (quant_to_quanta n) ty = quant n ty. 
Proof. induction n; intros; simpl; auto; rewrite quant_succ; f_equal; auto. Qed. 


(* 
Covariance 

When checking subtyping, types in covariant position may be assumed to be tree types.
 *)




Fixpoint variant pos k ty :=
  (* pos is true if looking for covariance of general variables. 
Doubly-contravariant positions are covariant. *) 
  match ty with
  | Var n => if k=?n then pos else true
  | Quant ty1 => variant pos (S k) ty1
  | Funty ty1 ty2 => variant (negb pos) k ty1 && variant pos k ty2
  | Leaf => true
  | Stem ty1 => variant pos k ty1
  | Fork ty1 ty2 => variant pos k ty1 && variant pos k ty2
  | Asf ty1 => variant pos k ty1
   end.


Definition covariant ty := variant true 0 ty = true.



Lemma lift_rec_preserves_variant:
  forall ty pos k n p, variant pos (relocate k n p) (lift_rec ty n p) = variant pos k ty. 
Proof.
  induction ty; intros; simpl; auto.
  caseEq (relocate k n0 p =? relocate n n0 p); intros. 
  assert(relocate k n0 p = relocate n n0 p) by (eapply Nat.eqb_eq; auto).
  assert(k=n) by (eapply relocate_mono; eauto). subst. rewrite Nat.eqb_refl; auto.
  caseEq (k=?n); intros; auto.
  assert(k=n) by (apply Nat.eqb_eq; auto). subst. rewrite Nat.eqb_refl in *. discriminate.
  rewrite <- relocate_succ; eapply IHty.
  rewrite ! IHty1; rewrite IHty2; auto.
  rewrite ! IHty1; rewrite ! IHty2; auto.
Qed.

 

Lemma lift_rec_preserves_variant2:
  forall (ty : dtype) (pos : bool) (n p : nat),
  variant pos n (lift_rec ty n (S p)) = true. 
Proof.
  induction ty; intros; simpl; eauto.
  assert(n0 <= n \/ n0 > n) by lia; disjunction_tac; relocate_tac.
  assert(n0  =? (S p + n) = false). eapply Nat.eqb_neq; lia.  rewrite H; auto. 
  assert(n0  =? n = false). eapply Nat.eqb_neq; lia.  rewrite H; auto. 
  rewrite ! IHty1; rewrite IHty2; auto. 
  rewrite ! IHty1; rewrite ! IHty2; auto. 
Qed.


Lemma lift_rec_preserves_variant3:
  forall (ty : dtype) (pos : bool) (k p n  : nat),
    p <= k -> k < p+n -> variant pos k (lift_rec ty p n) = true.
Proof.
  induction ty; intros; simpl; auto.
  (* 5 *) 
  assert(p<= n \/ p>n) by lia; disjunction_tac; relocate_tac.
  assert(k =? n0 + n = false) by (apply Nat.eqb_neq; lia). rewrite H1; auto. 
  assert(k=? n = false) by (eapply Nat.eqb_neq; lia).   rewrite H1; auto.
  (* 4 *)
  rewrite IHty; auto; try lia.
  rewrite ! IHty1; auto; try lia; rewrite IHty2; auto; try lia.
  rewrite ! IHty1; auto; try lia; rewrite ! IHty2; auto; try lia.
Qed.

Lemma subst_rec_preserves_variant:
  forall (ty uty : dtype) (pos : bool) (k p : nat),
    variant pos (S (k+ p)) ty = true -> variant true k uty = true -> variant false k uty = true ->
    variant pos (k+p) (subst_rec ty uty p) = true.
Proof.
  induction ty; intros; simpl in *; auto; rewrite ? andb_true_iff in *; split_all; eauto.
  2: replace (S (k+p)) with (k + S p) in * by lia;   rewrite IHty; auto.
  (* 1 *)
  assert(p<n \/ p=n \/ p>n) by lia; disjunction_tac; insert_Var_tac;
    caseEq n; intros; subst; simpl; auto; try lia.
  (* 4 *)
  rewrite lift_rec_null in *; rewrite plus_0_r; caseEq pos; intros; subst; auto.
  (* 3 *)
  replace (k + S n0) with (relocate k 0 (S n0)) by (relocate_tac; lia). 
  rewrite lift_rec_preserves_variant.  caseEq pos; intros; subst; auto.
  (* 2 *)
  assert(k+p =? 0 = false) by (eapply Nat.eqb_neq; lia); rewrite H3; auto. 
  assert(k+p =? S n0 = false) by (eapply Nat.eqb_neq; lia); rewrite H3; auto. 
Qed.

Lemma subst_rec_preserves_variant2:
  forall (ty uty : dtype) (pos : bool) (k p : nat),
    variant pos k ty = true -> 
    variant pos k (subst_rec ty uty (k+ S p)) = true.
Proof.
  induction ty; intros; simpl in *; auto. 
  (* 5 *)
  all: cycle 1.
  replace (S (k+ S p)) with (S k + S p) in * by lia.   rewrite IHty; auto.
  (* 4 *)
  all: rewrite ? andb_true_iff in *; split_all; eauto.
  (* 1 *)
  assert(k + S p<n \/ k + S p=n \/ k + S p>n) by lia; disjunction_tac; insert_Var_tac; simpl. 
  assert(k=? Nat.pred n = false) by (eapply Nat.eqb_neq; lia). rewrite H0; auto.
  rewrite lift_rec_preserves_variant3; auto; try lia.
  auto.
Qed.


Lemma lift_rec_makes_invariant:
  forall ty pos n p k, variant pos (n+p) (lift_rec ty p (S n + k)) = true.
Proof.
  induction ty; intros; simpl; auto. 
  assert(p <= n \/ p>n) by lia; disjunction_tac; relocate_tac.
  assert(n0 +p =? S (n0 + k) +n = false). eapply Nat.eqb_neq; lia.  rewrite H; auto. 
  assert(n0 +p =? n = false). eapply Nat.eqb_neq; lia.  rewrite H; auto. 
  replace (S (n+p)) with (n + S p) by lia; eapply IHty. 
  assert(variant (negb pos) (n + p) (lift_rec ty1 p (S (n + k))) = true). eapply IHty1. rewrite H.
  all: replace (S (n+k)) with (S n + k) by lia.
  rewrite ! IHty2; auto.
  rewrite ! IHty;  auto.
  rewrite ! IHty1. rewrite ! IHty2.  auto.
  rewrite ! IHty;  auto.
Qed.


Lemma subst_rec_preserves_invariant :
  forall ty k uty vty,
    variant true k ty = true -> variant false k ty = true -> subst_rec ty uty k = subst_rec ty vty k.
Proof.
  induction ty; intros; simpl in *; eauto.
  caseEq (k=?n); intros; rewrite H1 in *; try discriminate. 
  assert(k<n \/ k=n \/ k>n) by lia; disjunction_tac; repeat insert_Var_tac; eauto; try lia. 
  rewrite Nat.eqb_refl in *; discriminate. 
  f_equal; eauto.
  all: rewrite ? andb_true_iff in *; split_all; f_equal; eauto.
Qed.



Lemma variant_lift_rec_miss: forall ty pos m n k, variant pos (m+k) (lift_rec ty m (S (n +k))) = true.
Proof.
  induction ty; intros; unfold subst; simpl; eauto.
  assert(m<= n \/ m >n) by lia; disjunction_tac; relocate_tac. 
  caseEq ( m + k =? S (n0 + k) + n); intros; auto;
    assert( m + k = S (n0 + k) + n) by (eapply Nat.eqb_eq; eauto);  lia.
  caseEq ( m + k =? n); intros; auto;
    assert( m + k = n) by (eapply Nat.eqb_eq; eauto);  lia.
  replace (S (m + k)) with (S m + k) by lia; eapply IHty.   
  rewrite ! IHty1; rewrite IHty2; auto.
  rewrite ! IHty1; rewrite ! IHty2; auto.
Qed.


Lemma variant_subst_rec_miss:
  forall ty pos ty0 n k,
    variant pos k ty = true -> variant pos k (subst_rec ty ty0 (S (n+k))) = true.
Proof.
  induction ty; intros; simpl in *; eauto.
  (* 6 *)
  caseEq (k=?n); intros;  rewrite H0 in *; simpl in *; eauto. subst. 
  assert(k=n) by (eapply Nat.eqb_eq; eauto); subst. insert_Var_tac; simpl; eauto. rewrite H0; auto.
  assert(S (n0 + k) < n \/ S (n0+k) = n \/ S (n0+k) > n) by lia; disjunction_tac; insert_Var_tac.
  simpl.   assert(k =? Nat.pred n = false). eapply Nat.eqb_neq. lia. rewrite H1; auto.
  replace k with (0+k) at 1 by lia; eapply variant_lift_rec_miss. simpl. rewrite H0; auto. 
  (* 5 *)
  replace (S (n+k)) with (n + S k) by lia; eapply IHty; eauto.
  (* 4 *)
  all: rewrite ! andb_true_iff in *; split_all; eauto.
Qed.



 
Lemma variant_program_type: forall p pos k, variant pos k (program_type p) = true. 
Proof.
  induction p; intros; simpl; eauto.
  caseEq (program_type p1); intros; simpl; eauto.
  rewrite IHp2; rewrite andb_true_r.
  caseEq p1; intros; subst; simpl in *; try discriminate.
  caseEq (program_type t); intros; rewrite H0 in *; try discriminate. 
  inv_out H.
  assert(variant pos k (Stem (program_type t0)) = true) by auto. auto. 
Qed.


 
