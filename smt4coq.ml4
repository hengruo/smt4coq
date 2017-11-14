(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "smt4coq"

open Solver

TACTIC EXTEND smt
| [ "smt"] ->
    [ Solver.solve () ]
END;;

TACTIC EXTEND prtcoq
| [ "print" "z3" ] ->
    [ Solver.print_z3 () ]
END;;

TACTIC EXTEND prtz3
| [ "print" "coq" ] ->
    [ Solver.print_coq () ]
END;;