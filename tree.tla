(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
CONSTANT N


(***************************************************************************
--algorithm GrowTree {
    variables left = <<>>; right = <<>>;
    { while (TRUE) {
        with(x \in 1..N \ Nodes(left, right)) {
            left := [left EXCEPT ![0] = x]
        }
    }}
    
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES left, right

vars == << left, right >>

Init == (* Global variables *)
        /\ left = <<>>
        /\ right = <<>>

Next == /\ \E x \in 1..N \ Nodes(left, right):
             left' = [left EXCEPT ![0] = x]
        /\ right' = right

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Jun 30 20:43:37 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
