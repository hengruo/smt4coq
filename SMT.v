Declare ML Module "smt4coq".

Local Axiom by_smt: forall P:Prop, P.

Ltac smt4coq := intros;smt;apply by_smt.
