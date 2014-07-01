(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers
CONSTANT N


(***************************************************************************
--algorithm GrowTree {
    variables left = <<>>; right = <<>>;
    
    define {
        NodesOf(R) == { r[1]: r \in R} \union { r[2] : r \in R }
        Nodes(l, r) == NodesOf(l) \union NodesOf(r)
    }
    
    { while (TRUE) {
        with(child \in 1..N \ Nodes(left, right);
             parent \in Nodes(left, right);
             side \in { left, right} ) {
             
            side := [side EXCEPT ![child] = parent]
        }
    }}
    
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES left, right

(* define statement *)
NodesOf(R) == { r[1]: r \in R} \union { r[2] : r \in R }
Nodes(l, r) == NodesOf(l) \union NodesOf(r)


vars == << left, right >>

Init == (* Global variables *)
        /\ left = <<>>
        /\ right = <<>>

Next == /\ \E child \in 1..N \ Nodes(left, right):
             \E parent \in Nodes(left, right):
               \E side \in { left, right}:
                 side' = [side EXCEPT ![child] = parent]
        /\ UNCHANGED << left, right >>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Jun 30 20:58:11 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
