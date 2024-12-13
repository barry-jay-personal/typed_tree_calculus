This directory contains the Coq verification of the theorems in the
paper "Typed Program Analysis Without Encodings" written by Barry Jay.
Theorem names are identical in the paper and this implementation.
The list of source files can be found in _CoqProject, used by the make files to do the verification.
The directoty also includes some experimental files that are not used in the paper
(and won't compile if you try).

terms.v covers all of the examples and their behaviour under reduction.
rewriting_theorems.v covers the properties of rewriting required to show
that bf represents the breadth-first evaluation strategy.
types.v introduces the types and handles the deBruijn indices
subtypes.v introduces subtyping
derive.v introduces type derivation
typed_lambda.v, typed_recursion.v, typed_triage.v, and typed_evaluator.v
   type all of the examples
classify.v classifies subtyping according to the structure of the subtype 
classify_derive.v classifies type derivations
reduction_preserves_typing.v shows that reduction preserves typing
