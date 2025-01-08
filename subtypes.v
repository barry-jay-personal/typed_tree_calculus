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
(*                     Subtyping                                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)




Require Import String Arith Lia Bool List Nat.
Require Import terms types.

Open Scope string_scope.
Open Scope nat_scope.

Set Default Proof Using "Type".


(*** Subtyping *) 


Definition omega21_ty := program_type omega21.
Definition omega22_ty := program_type omega22. 
Definition omega2_ty := (Fork (Stem omega21_ty) omega22_ty).

Definition eval_ty := quant 1 (Funty (Var 0) (Asf (Var 0))).
Definition eager_ty := quant 2 (Funty (Funty (Var 0) (Var 1)) (Funty (Var 0) (Var 1))).

Definition bfff_aug uty := Fork (Stem (Fork Leaf eval_ty)) (Asf uty).
Definition bffs_aug uty := Fork (Stem (Fork Leaf eager_ty)) (bfff_aug uty). 


Inductive subtype : dtype -> dtype -> Prop :=
  (* a pre-order *) 
| sub_zero : forall ty, subtype ty ty
| sub_trans : forall ty1 ty2 ty3, subtype ty1 ty2 -> subtype ty2 ty3 -> subtype ty1 ty3
  (* a congruence, except for contravariance in function types *) 
| sub_stem : forall uty1 uty2, subtype uty1 uty2 -> subtype (Stem uty1) (Stem uty2)
| sub_fork : forall uty1 uty2 vty1 vty2, subtype uty1 uty2 -> subtype vty1 vty2 ->
                                         subtype (Fork uty1 vty1) (Fork uty2 vty2)
| sub_asf : forall uty1 uty2, subtype uty1 uty2 -> subtype (Asf uty1) (Asf uty2)
| sub_funty : forall uty1 uty2 vty1 vty2, subtype uty2 uty1 -> subtype vty1 vty2 ->
                                          subtype (Funty uty1 vty1) (Funty uty2 vty2)
| sub_quant : forall vty1 vty2,  subtype vty1 vty2 -> subtype (Quant vty1) (Quant vty2)
  (* commuting with quantifiers *)  
| sub_quant_stem: forall uty, subtype (Quant (Stem uty)) (Stem (Quant uty))
| sub_quant_fork: forall uty vty, subtype (Quant (Fork uty vty)) (Fork (Quant uty) (Quant vty))
| sub_quant_asf: forall uty, subtype (Quant (Asf uty)) (Asf (Quant uty))
| sub_dist: forall uty vty, subtype (Quant (Funty uty vty)) (Funty (Quant uty) (Quant vty))
  (* instantiating and introducing quantifiers *) 
| sub_inst : forall ty u,  subtype (Quant ty) (subst ty u)
| sub_lift: forall ty, subtype ty (Quant (lift 1 ty))                               
(* building trees *)
| sub_leaf_fun:forall uty,  subtype Leaf (Funty uty (Stem uty))
| sub_stem_fun: forall uty vty, subtype (Stem uty) (Funty vty (Fork uty vty))
(* reduction rules *)
| sub_fork_leaf: forall uty vty, subtype (Fork Leaf uty) (Funty vty uty)
| sub_fork_stem: forall uty vty wty,
    subtype (Fork (Stem (Funty uty (Funty vty wty))) (Funty uty vty)) (Funty uty wty)
| sub_fork_fork_leaf: forall uty vty wty,
    subtype (Fork (Fork uty vty) wty) (Funty Leaf uty)
| sub_fork_fork_stem:
    forall uty vty1 vty2 wty,
      subtype (Fork (Fork uty (Funty vty1 vty2)) wty) (Funty (Stem vty1) vty2)
| sub_fork_fork_fork:
    forall uty vty wty1 wty2 wty3,
      subtype (Fork (Fork uty vty) (Funty wty1 (Funty wty2 wty3))) (Funty (Fork wty1 wty2) wty3)
(* recursion *)
| sub_recursion:
    forall k uty vty,
      subtype omega2_ty
              (Funty
                 omega2_ty
                 (Funty
                    (Funty (quant k (Funty uty vty)) (quant k (Funty uty vty)))
                    (quant k (Funty uty vty)))) 
| sub_tree: forall ty uty,
    covariant ty -> 
    subtype (Fork
               (Fork
                  (subst ty Leaf)
                  (quant 1 (Funty (Var 0) (subst (lift_rec ty 1 1) (Stem (Var 0))))))
               (quant
                  2
                  (Funty
                     (Var 1)
                     (Funty (Var 0) (subst (lift_rec ty 1 2) (Fork (Var 1) (Var 0)))))
            ))
            (Funty uty (subst ty uty))
| sub_to_asf: forall ty, subtype ty (Asf ty)
| sub_from_asf: forall uty vty, subtype (Asf (Funty uty vty)) (Funty uty vty)
| sub_bffs: forall uty vty, subtype (Fork (Stem (bffs_aug uty)) (Asf vty)) (Asf (Fork (Stem uty) vty))
| sub_bfff : forall uty vty wty, subtype (Fork (Fork uty (Asf vty)) (bfff_aug wty))
                                         (Asf (Fork (Fork uty vty) wty))
.


Global Hint Constructors subtype : TreeHintDb.


Ltac var_tac :=
  unfold subst, lift; refold lift_rec; refold subst_rec;
  repeat (rewrite subst_rec_lift_rec;  [ | lia | lia]);
  repeat relocate_tac; repeat insert_Var_tac;
    unfold lift; rewrite ? lift_rec_null; try eapply sub_zero.

Ltac sub_funty_tac :=
  (eapply sub_funty; [ eapply sub_zero | ])
  || (eapply sub_funty; [ | eapply sub_zero ]).


Ltac subst_tac :=  eapply sub_trans; [ eapply sub_inst | var_tac].



Lemma subtype_quant:
  forall n uty vty,  subtype uty vty -> subtype (quant n uty) (quant n vty).
Proof.  induction n; intros; simpl in *; auto; eapply IHn; auto_t. Qed. 

Lemma subtype_quanta: forall bs ty1 ty2, subtype ty1 ty2 -> subtype (quanta bs ty1) (quanta bs ty2).
Proof. induction bs; intros; simpl; auto_t; caseEq a; intros; simpl; auto_t. Qed. 

Lemma subtype_dist: forall n uty vty,  subtype (quant n (Funty uty vty)) (Funty (quant n uty) (quant n vty)).
Proof.
  induction n; intros; simpl in *; try eapply sub_zero;
    eapply sub_trans; [ eapply subtype_quant; eapply sub_dist | apply IHn].
Qed.

Lemma subtype_quant_to_quanta: forall bs ty,  subtype (quant (quant_count bs) ty) (quanta bs ty).
Proof.
  induction bs; intros; simpl; auto_t; caseEq a; intros; subst; simpl; auto;
    eapply sub_trans; [ eapply subtype_quant; eapply sub_to_asf | eauto].
Qed. 


Lemma lift_rec_preserves_subtype:
  forall ty1 ty2, subtype ty1 ty2 -> forall n k, subtype (lift_rec ty1 n k) (lift_rec ty2 n k).
Proof.
  intros ty1 ty2 s; induction s; intros; refold lift_rec; try relocate_tac;
    unfold lift; rewrite ? lift_lift_rec; try lia; eauto 2 with TreeHintDb.  
  - subst_tac; replace n with (0+n) at 2 by lia; rewrite lift_rec_subst_rec; var_tac. 
  - replace (lift_rec omega2_ty n k0) with omega2_ty by (cbv; auto);
      rewrite ! lift_rec_preserves_quant; eapply sub_recursion.
  - var_tac;
      eapply sub_trans; [
        eapply sub_trans; [ | eapply sub_tree] |
        sub_funty_tac; unfold subst; replace n with (0+n) at 2 by lia; rewrite lift_rec_subst_rec; eapply sub_zero]; [
      |
        unfold covariant in *; simpl; replace 0 with (relocate 0 (S n) k) by auto;
        rewrite lift_rec_preserves_variant; auto];
      eapply sub_fork; [ eapply sub_fork; [  
  simpl; unfold subst; replace n with (0+n) at 1 by lia; rewrite lift_rec_subst_rec; eapply sub_zero |
  simpl; var_tac; replace (S n) with (0+ S n) at 1 by lia; 
  rewrite lift_rec_subst_rec; try lia; simpl;
  rewrite (lift_lift_rec); try lia; var_tac] | ];
  unfold subst; simpl; var_tac; replace (S (S n)) with (0+ S (S n)) at 1 by lia; 
      rewrite lift_rec_subst_rec; try lia; simpl; var_tac;
      replace (S (S (S n))) with (2 + S n) by lia; rewrite (lift_lift_rec); try lia; var_tac.
  - unfold bffs_aug, bfff_aug; simpl; var_tac;  eapply sub_bffs.
  - unfold bffs_aug, bfff_aug; simpl; var_tac;  eapply sub_bfff.
Qed.


Lemma subst_rec_preserves_subtype:
  forall uty vty, subtype uty vty -> forall ty k, subtype (subst_rec uty ty k) (subst_rec vty ty k).
Proof.
  intros ty1 ty2 s; induction s; intros; unfold lift;
    refold subst_rec; try insert_Var_tac; 
    unfold lift; rewrite ? subst_rec_lift_rec1; try lia; eauto 2 with TreeHintDb.
  - subst_tac; eapply sub_trans; [ | rewrite subst_rec_subst_rec; try lia]; eapply sub_zero. 
  - replace (subst_rec omega2_ty ty k0) with omega2_ty by (cbv; auto);
      rewrite ! subst_rec_preserves_quant; eapply sub_recursion.
  - unfold subst; rewrite subst_rec_subst_rec; try lia;
      replace (k-0) with k by lia;
      eapply sub_trans; [ eapply sub_trans; [ | eapply sub_tree] |]; [
        eapply sub_fork; [
          eapply sub_fork; [
            simpl; eapply sub_zero |
            simpl; var_tac; rewrite subst_rec_subst_rec; try lia; simpl; var_tac;
            rewrite subst_rec_lift_rec1; try lia; simpl; eapply sub_zero] |];
        simpl; var_tac;  rewrite subst_rec_subst_rec; try lia; simpl; var_tac;
        replace (S (S (S k))) with (2 + S k) by lia;
        rewrite subst_rec_lift_rec1; try lia; simpl; eapply sub_zero | 
        unfold covariant in *; replace k with (k+0) by lia; rewrite variant_subst_rec_miss; auto |
        sub_funty_tac; unfold subst; rewrite (subst_rec_subst_rec _ uty); try lia;
        replace (k-0) with k by lia; eapply sub_zero].
  - unfold bffs_aug, bfff_aug; simpl; var_tac;  eapply sub_bffs.
  - unfold bffs_aug, bfff_aug; simpl; var_tac;  eapply sub_bfff.
 Qed.


Lemma subtype_lift: forall n ty, subtype ty (quant n (lift n ty)).
Proof.
  induction n; intros; subst; simpl.
  - unfold lift; rewrite lift_rec_null; auto_t.
  - replace (S n) with (1+n) by auto; eapply sub_trans; [
        eapply sub_lift | ];
      replace (quant n (Quant (lift (1+n) ty))) with (quant n (lift n (Quant (lift 1 ty)))); [ 
        eapply IHn |
        unfold lift; simpl; rewrite lift_rec_lift_rec; try lia; repeat f_equal; lia].
Qed. 


Lemma subtype_lift2 : forall n ty, subtype (quant n (lift n ty)) ty.
Proof.
  induction n; intros.
  - unfold lift; rewrite lift_rec_null; simpl; apply sub_zero. 
  - unfold lift; simpl; replace (S n) with (1+n) by lia; erewrite <- lift_rec_lift_rec. 
    + instantiate(1:= 0); eapply sub_trans; [ eapply subtype_quant; eapply sub_inst |];
        unfold subst; rewrite subst_rec_lift_rec; try lia.
      rewrite lift_rec_null; eapply  IHn.
    + lia.  
    + lia.
Unshelve. apply Leaf.
Qed.


Lemma subtype_lift3: forall (n : nat) (ty : dtype), subtype (lift n (quant n ty)) ty. 
Proof.
  induction n; intros; unfold lift; simpl.
  - rewrite lift_rec_null; apply sub_zero.
  - replace (S n) with (1+n) by lia;
      erewrite <- lift_rec_lift_rec.
    + replace (1+n) with (n+1) by lia;  eapply sub_trans; [
          eapply lift_rec_preserves_subtype; eapply IHn |]. 
      simpl; eapply sub_trans; [ eapply sub_inst | ];
        unfold subst; simpl; rewrite subst_rec_lift_rec0; try lia;
        rewrite lift_rec_null; apply sub_zero.
    + lia.
    + lia.
Qed.

Lemma subtype_lift4 : forall n ty,  subtype (quant n (lift_rec ty n n)) ty.
Proof.
  intros;
    replace (quant n (lift_rec ty n n)) with (lift n (quant n ty))
    by (unfold lift; rewrite lift_rec_preserves_quant; f_equal; f_equal; lia);
    eapply subtype_lift3. 
Qed.


Lemma  subtype_quant_stem: forall k uty, subtype (quant k (Stem uty)) (Stem (quant k uty)). 
Proof.
  induction k; intros; simpl.
  - eapply sub_zero.
  - eapply sub_trans; [ eapply subtype_quant; eapply sub_quant_stem | eauto].
Qed.


Lemma subtype_quant_fork:
  forall k uty vty,  subtype (quant k (Fork uty vty)) (Fork (quant k uty) (quant k vty)). 
Proof.
  induction k; intros; simpl; try eapply sub_zero; 
  eapply sub_trans; [ eapply subtype_quant; eapply sub_quant_fork | eauto].
Qed.



Lemma asf_Quant_commute: forall ty, subtype (Asf (Quant ty)) (Quant (Asf ty)) .
Proof.
  intros; eapply sub_trans; [ eapply sub_lift |];
    eapply sub_quant; unfold lift; simpl;
    eapply sub_asf; eapply sub_trans; [ eapply sub_inst |];
    unfold subst; simpl;  erewrite subst_rec_lift_rec0; rewrite lift_rec_null;  apply sub_zero. 
Qed.

Lemma subtype_asf_quanta: forall bs ty, subtype (Asf (quanta bs ty)) (quanta bs (Asf ty)).
Proof.
  induction bs; intros; simpl; auto_t; caseEq a; intros; simpl; [
      eapply sub_trans; [ eapply IHbs |]; eapply subtype_quanta; eapply asf_Quant_commute |
  eapply IHbs].
  Qed. 
  
Lemma subtype_quanta_asf: forall bs ty, subtype (quanta bs (Asf ty))  (Asf (quanta bs ty)) .
Proof.
  induction bs; intros; simpl; auto_t; caseEq a; intros; simpl; [
      eapply sub_trans; [ | eapply IHbs]; eapply subtype_quanta; eapply sub_quant_asf |
  eapply IHbs].
  Qed. 
  
Lemma subtype_quant_asf: forall n ty, subtype (quant n (Asf ty))  (Asf (quant n ty)) .
Proof.
  induction n; intros; simpl; auto_t; eapply sub_trans; [ | eapply IHn]; eapply subtype_quant; eapply sub_quant_asf. 
  Qed. 
  
Lemma subtype_quanta_to_quant_count:
  forall bs bs2 uty vty,
    subtype (quanta bs (quanta bs2 (Funty uty vty))) (quant (quant_count bs) (quanta bs2 (Funty uty vty))).
Proof.
  induction bs; intros; simpl; auto_t; caseEq a; intros; subst; simpl.
  - replace (Quant (quanta bs2 (Funty uty vty))) with (quanta (app bs2 (true :: nil)) (Funty uty vty)) by
      (rewrite quanta_app; simpl; auto); eapply IHbs.
  - replace (Asf (quanta bs2 (Funty uty vty))) with (quanta (app bs2 (false :: nil)) (Funty uty vty)) by
      (rewrite quanta_app; simpl; auto);
      eapply sub_trans; [ eapply IHbs |];
      eapply subtype_quant; rewrite quanta_app; simpl;
      eapply sub_trans; [ eapply subtype_asf_quanta | eapply subtype_quanta; auto_t]. 
Qed.

Lemma quanta_leaf: forall bs, subtype Leaf (quanta bs Leaf).
Proof.
  induction bs; intros; simpl in *.
  - eapply sub_zero.
  - caseEq a; intros; subst; (eapply sub_trans; [ eapply IHbs | eapply subtype_quanta]).
    + replace Leaf with (lift 1 Leaf) at 2 by auto;  eapply sub_lift.
    + auto_t. 
Qed.

Lemma subtype_quant_to_quanta2: forall n ty, quant n ty = quanta (iter n (cons true) nil) ty.
Proof. induction n; intros; simpl; auto.   Qed. 

Lemma subtype_quant_quantf: forall m n ty,  subtype (quant m (quantf n ty)) (quantf n (quant m ty)).
Proof.
  induction m; intros; simpl; auto_t;  eapply sub_trans; [ | eapply IHm];
    eapply subtype_quant;
    clear; induction n; intros; simpl; auto_t;
    rewrite 2 quantf_succ;
    eapply sub_trans; [ eapply sub_quant_asf | eapply sub_asf; eauto]. 
Qed.

Lemma subtype_quantf: forall n ty1 ty2, subtype ty1 ty2 -> subtype (quantf n ty1) (quantf n ty2).
Proof.  induction n; intros; simpl; auto_t. Qed. 
  
Lemma subtype_quantf_Quant: forall n ty,  subtype (quantf n (Quant  ty)) (Quant (quantf n ty)).
Proof.
  intros; eapply sub_trans; [ eapply sub_lift |];
    eapply sub_quant;
    unfold lift; rewrite lift_rec_preserves_quantf; eapply subtype_quantf;
    replace Quant with (quant 1) by auto;
    eapply subtype_lift3. 
Qed.



Lemma subtype_leaf_fork:
  forall uty vty, subtype Leaf (Funty uty (Funty vty (Fork uty vty))).
Proof. auto_t. Qed.




Ltac fn_of_leaf_tac := eapply sub_trans;
   [ eapply sub_fork_leaf | repeat sub_funty_tac ].

Ltac sub_fork_tac :=  eapply sub_trans; [  eapply sub_fork ; [ eapply sub_stem |] | eapply sub_fork_stem]. 
Ltac stem_fork_tac := eapply sub_stem_fun.
Ltac subtype_leaf_stem_tac := eapply sub_leaf_fun.
Ltac subtype_leaf_fork_tac := eapply subtype_leaf_fork; repeat sub_funty_tac.
Ltac dist_tac := eapply sub_trans; [ eapply subtype_dist | eapply sub_funty].
Ltac sub_fun_tac := (eapply sub_funty; [ eapply sub_zero | ]) || (eapply sub_funty; [ | eapply sub_zero ]) .

Ltac qlift_tac:=
  eapply sub_trans; [ eapply subtype_quant;  eapply sub_trans; [ eapply sub_lift | eapply sub_zero] |].

Ltac split_all :=
  intros;
   match goal with
   | H:_ /\ _ |- _ => inversion_clear H; split_all
   | H:exists _, _ |- _ => inversion H; clear H; split_all
   | _ => try (split; split_all); subst; try contradiction
   end; try congruence.


Ltac sub_fork2_tac :=
    (eapply sub_zero 
    || sub_fork_tac
    || fn_of_leaf_tac
    || sub_funty_tac
    || eapply sub_leaf_fun
    || eapply subtype_leaf_fork
    || stem_fork_tac
    || subtype_leaf_stem_tac);
    var_tac; repeat sub_funty_tac
.


Lemma stem_Quant_commute: forall ty, subtype (Stem (Quant ty)) (Quant (Stem ty)) .
Proof.
  intros; eapply sub_trans; [ eapply sub_lift |];
    eapply sub_quant; unfold lift; simpl;
    eapply sub_stem;
    eapply sub_trans; [ eapply sub_inst |];
    unfold subst; simpl; erewrite subst_rec_lift_rec0; rewrite lift_rec_null; apply sub_zero. 
Qed.


Lemma stem_quant_commute: forall k ty, subtype (Stem (quant k ty)) (quant k (Stem ty)) .
Proof.
  induction k; intros; simpl; try eapply sub_zero;
    rewrite ! quant_succ;
    eapply sub_trans; [ eapply stem_Quant_commute |];
    eapply sub_quant;   eauto.
Qed.


Lemma asf_quant_commute: forall k ty, subtype (Asf (quant k ty)) (quant k (Asf ty)) .
Proof.
  induction k; intros; simpl; try eapply sub_zero;
    rewrite ! quant_succ;
    eapply sub_trans; [ eapply asf_Quant_commute |];
    eapply sub_quant;   eauto.
Qed.


Lemma fork_Quant_commute: forall ty1 ty2, subtype (Fork (Quant ty1) (Quant ty2)) (Quant (Fork ty1 ty2)) .
Proof.
  intros; eapply sub_trans; [ eapply sub_lift |];
    eapply sub_quant; unfold lift; simpl;
  eapply sub_fork; (eapply sub_trans; [ eapply sub_inst |
  unfold subst;  erewrite subst_rec_lift_rec0; rewrite lift_rec_null; apply sub_zero]).
Qed. 


Lemma fork_quant_commute:
  forall k ty1 ty2, subtype (Fork(quant k ty1)(quant k ty2)) (quant k (Fork ty1 ty2)).
Proof.
  induction k; intros; simpl; try eapply sub_zero;
    rewrite ! quant_succ;
    replace (S (k + S k)) with (2 + (k+k)) by lia;
    eapply sub_trans; [ eapply fork_Quant_commute |]; 
    eapply sub_quant;   eauto.
Qed.


Lemma subtype_quant_leaf: forall k, subtype (quant k Leaf) Leaf.
Proof.
  induction k; intros; simpl; try eapply sub_zero;
    replace (S k) with (1+k) by lia; eapply sub_trans; [ eapply subtype_quant; eapply sub_inst |
  unfold subst; simpl; eauto]. 
  Unshelve. apply Leaf.
Qed.

Lemma subtype_leaf_quant: forall k, subtype Leaf (quant k Leaf).
Proof.
  induction k; intros; simpl; try eapply sub_zero;
    replace (S k) with (k+1) by lia; eapply sub_trans; [  eapply IHk | eapply subtype_quant; 
  eapply sub_trans; [ eapply sub_lift | unfold lift; simpl; eapply sub_zero]]. 
Qed.



Lemma subtype_Kty: forall uty vty, subtype (Stem Leaf) (Funty uty (Funty vty uty)).
Proof.  intros; auto_t. Qed. 
