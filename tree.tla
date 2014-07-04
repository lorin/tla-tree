(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers
CONSTANT N

(***************************************************************************
--algorithm GrowTree {
    variables nodes = {}, left = {}, right = {};

    process (EmptyTree = 0) {
        e: while(TRUE) {
            await (nodes = {});
            with (x \in 1..N) {
                nodes := nodes \union {x}
            }
        }
    }

    process (Insert = 1) {
        i: while(TRUE) {
            await (nodes /= {});
            with (x \in 1..N \ nodes;
                  parent \in nodes) {
                nodes := nodes \union {x};
                either left := left \union { <<x, parent>> }
                or     right := right \union { <<x, parent>> }
            }
        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES nodes, left, right

vars == << nodes, left, right >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ nodes = {}
        /\ left = {}
        /\ right = {}

EmptyTree == /\ (nodes = {})
             /\ \E x \in 1..N:
                  nodes' = (nodes \union {x})
             /\ UNCHANGED << left, right >>

Insert == /\ (nodes /= {})
          /\ \E x \in 1..N \ nodes:
               \E parent \in nodes:
                 /\ nodes' = (nodes \union {x})
                 /\ \/ /\ left' = (left \union { <<x, parent>> })
                       /\ right' = right
                    \/ /\ right' = (right \union { <<x, parent>> })
                       /\ left' = left

Next == EmptyTree \/ Insert

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Jun 30 21:17:32 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
