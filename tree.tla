(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers
CONSTANT N

(***************************************************************************
--algorithm GrowTree {
    variables nodes = {};

    process (EmptyTree = 0) {
        e: while(TRUE) {
            await (nodes = {});
            with (x \in 1..N) {
                nodes := nodes \union {x}
            }
        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES nodes, left, right

(* define statement *)
NodesOf(R) == { r[1]: r \in R} \union { r[2] : r \in R }



R ** S == LET T == {rs \in R\X S : rs[1][2] = rs[2][1]}
          IN  {<<x[1][1], x[2][2]>> : x \in T}

TC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(R))





IsATree(l, r) ==
    nodes = {} \/
    \E root \in nodes : \A x \in nodes \ {root} : <<x, root>> \in TC(l \union r)


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

Insert == /\ (nodes =/= {})
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
