Add LoadPath "../../Tree_Calculus_Proofs" as Reflective.
Require Import Nat String.
Require Import to_tikz_2021.


Definition outer := wait self_apply_k (Node).
Definition body :=  (S1 (K @ Ref "f") @ wait1 self_apply_k).


Compute (internal_to_tikz get_color (fun s => "south") "black" 2 2 50 10  0 200 0 outer). 
Compute (internal_to_tikz get_color txt_anchor "black" 2 2 50 10 11 180 100 body). 







Require Import terms to_tikz.

Set Default Proof Using "Type".

Open Scope string_scope.
Global Open Scope tree_scope.

Print Z. 
Definition outer := wait self_apply_k (Node).
Definition body :=  (S1 (K @ Ref "f") @ wait1 self_apply_k).

Print wait1.

Compute (internal_to_tikz get_color (fun s => "south") "black" 2 2 50 10  true 0 200 0 0 outer). 
Compute (internal_to_tikz get_color txt_anchor "black" 2 2 50 10 true 11 180 100 0 body). 

(* 
Definition target := Eval cbv in Y2(Ref "f").

(* Print target. *) 

Definition left_branch :=   △ @ (△ @ (△ @ (△ @ △) @ (△ @ △))). 

Definition middle_branch := 
 (△ @
  (△ @ △ @
   (△ @
    (△ @
     (△ @
      (△ @
       (△ @
        (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ △) @ (△ @ △))) @ (△ @ (△ @ △) @ (△ @ △)))))) @
        (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
      (△ @ △ @ (△ @ (△ @ (△ @ (△ @ △) @ (△ @ △))))))) @
    (△ @ △ @
       (△ @ (△ @ (△ @ △ @ Ref "f")) @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △))))))).

 Definition right_branch := 
 (△ @ △ @ (△ @ (△ @ (△ @ (△ @ △) @ (△ @ △))) @ (△ @ (△ @ △) @ (△ @ △)))). 
 
Print Z. 

Compute (internal_to_tikz get_color txt_anchor "black" 7 2 50 10 10 250 0 left_branch). 
Compute (internal_to_tikz get_color txt_anchor "black" 7 2 50 10 10 210 10 middle_branch). 
Compute (internal_to_tikz get_color txt_anchor "black" 7 2 50 10 10 140 100 right_branch). 

(* Compute(" \node[rounded rectangle, draw] (573) at ($ (f) + (332:4) $){f};\draw [o=3/2pt] (f.center)--(573);").
*) 

wait self_apply (d (wait1 self_apply) @ (K @ f))
*) 
