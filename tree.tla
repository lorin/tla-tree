(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers, FiniteSets, Sequences
CONSTANT N

(***************************************************************************
--algorithm GrowTree {
    variables nodes = {}, left = {}, right = {};

    define {

        (* Define transitive closure, from 9.6.2 of Lamport's Hyperbook.
           We use Cardinality(R)+1 to catch cycles *)

        R ** S == LET T == {rs \in R \X S : rs[1][2] = rs[2][1]}
                  IN  {<<x[1][1], x[2][2]>> : x \in T}

        TC(R) ==
            LET RECURSIVE STC(_)
                STC(n) == IF n=1 THEN R
                                 ELSE STC(n-1) \union STC(n-1)**R
            IN IF R={} THEN {} ELSE STC(Cardinality(R)+1)


        (* It's a tree if there's a root: a node that is reachable
           from all other nodes. Also, need to verify there are
           no cycles. *)

        Empty == nodes = {}

        AllNodesReachable ==
            \E root \in nodes : \A x \in nodes \ {root} :
                <<x, root>> \in TC(left \union right)

        HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)

        IsATree == Empty \/ (AllNodesReachable /\ ~HasACycle)

        (* In-order traversal *)
        LeftChild(node) ==
            IF \E x : <<x, node>> \in left THEN CHOOSE x : <<x, node>> \in left
            ELSE {}

        RightChild(node) ==
            IF \E x : <<x, node>> \in right THEN CHOOSE x : <<x, node>> \in right
            ELSE {}

        RECURSIVE TraverseRec(_)
        TraverseRec(node) ==
            IF node={} THEN <<>>
            ELSE LET leftseq == TraverseRec(LeftChild(node))
                     rightseq == TraverseRec(RightChild(node)) IN
                Append(leftseq, node) \o rightseq

        Root == CHOOSE root : \A x \in nodes \ {root} : <<x, root>> \in TC(left \union right)

        Traverse == IF nodes = {} THEN <<>>
                    ELSE TraverseRec(Root)

    }

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

(* define statement *)
R ** S == LET T == {rs \in R \X S : rs[1][2] = rs[2][1]}
          IN  {<<x[1][1], x[2][2]>> : x \in T}

TC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(R)+1)






Empty == nodes = {}

AllNodesReachable ==
    \E root \in nodes : \A x \in nodes \ {root} :
        <<x, root>> \in TC(left \union right)

HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)

IsATree == Empty \/ (AllNodesReachable /\ ~HasACycle)


LeftChild(node) ==
    IF \E x : <<x, node>> \in left THEN CHOOSE x : <<x, node>> \in left
    ELSE {}

RightChild(node) ==
    IF \E x : <<x, node>> \in right THEN CHOOSE x : <<x, node>> \in right
    ELSE {}

Traverse(node) ==
    IF n={} THEN <<>>
    ELSE Append(Traverse(LeftChild(node), node)) \o Traverse(RightChild(node))


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
