-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Integers
CONSTANT EmptyFunction,N

(***************************************************************************
--algorithm GrowTree {
    variables nodes={}, parent=EmptyFunction;
    

    process(EmptyTree=0) {
        e: while(TRUE) {
            await(nodes={});
            with(x \in 1..N) {
                nodes := nodes \union {x}
            }
        }
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES nodes, parent

vars == << nodes, parent >>

ProcSet == {0}

Init == (* Global variables *)
        /\ nodes = {}
        /\ parent = EmptyFunction

EmptyTree == /\ (nodes={})
             /\ \E x \in 1..N:
                  nodes' = (nodes \union {x})
             /\ UNCHANGED parent

Next == EmptyTree

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Jul 27 11:01:13 EDT 2014 by lorinhochstein
\* Created Sun Jul 27 10:46:39 EDT 2014 by lorinhochstein
