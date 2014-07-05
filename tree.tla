(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers, FiniteSets, Sequences
CONSTANT N, NoValue

(***************************************************************************
--algorithm GrowTree {
    variables nodes = {}, left = {}, right = {}, root = NoValue;

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
           no cycles, and that there is at most one left-child
           and right-child. *)

        TreeIsEmpty == nodes = {}

        AllNodesReachable ==
            \E y \in nodes : \A x \in nodes \ {y} :
                <<x, y>> \in TC(left \union right)

        HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)

        OneToOne(rel) == \A x,y,z \in nodes :
            (<<x,z>> \in rel /\ <<y,z>> \in rel) => x=y

        IsATree == TreeIsEmpty \/ (/\ AllNodesReachable
                                   /\ ~HasACycle
                                   /\ OneToOne(left)
                                   /\ OneToOne(right))


        (* In-order traversal *)
        Traverse ==
            LET Child(parent, side) ==
                    IF \E x \in nodes : <<x, parent>> \in side THEN
                         CHOOSE x \in nodes : <<x, parent>> \in side
                    ELSE NoValue
                RECURSIVE TraverseRec(_)
                TraverseRec(node) ==
                    IF node=NoValue THEN <<>>
                    ELSE LET leftseq == TraverseRec(Child(node, left))
                             rightseq == TraverseRec(Child(node, right))
                         IN Append(leftseq, node) \o rightseq
            IN IF TreeIsEmpty THEN <<>> ELSE TraverseRec(root)

        IsSorted(seq) == \A i,j \in 1..Cardinality(nodes) : (i < j) => seq[i] < seq[j]
    }

    process (EmptyTree = 0) {
        e: while(TRUE) {
            await (TreeIsEmpty);
            with (x \in 1..N) {
                root := x;
                nodes := nodes \union {x}
            }
        }
    }

    process (Insert=1) {
        il: while(TRUE) {
            await (~TreeIsEmpty);
            with (x \in 1..N \ nodes;
                  parent = CHOOSE parent \in nodes:
                    (x < parent /\ \lnot \E y \in nodes : <<y, parent>> \in left) \/
                    (x > parent /\ \lnot \E y \in nodes : <<y, parent>> \in right) ) {
                nodes := nodes \union {x};
                if (x < parent)
                    left := left \union <<x,parent>>
                else
                    right := right \union <<x,parent>>

            }

        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES nodes, left, right, root

(* define statement *)
R ** S == LET T == {rs \in R \X S : rs[1][2] = rs[2][1]}
          IN  {<<x[1][1], x[2][2]>> : x \in T}

TC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(R)+1)







TreeIsEmpty == nodes = {}

AllNodesReachable ==
    \E y \in nodes : \A x \in nodes \ {y} :
        <<x, y>> \in TC(left \union right)

HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)

OneToOne(rel) == \A x,y,z \in nodes :
    (<<x,z>> \in rel /\ <<y,z>> \in rel) => x=y

IsATree == TreeIsEmpty \/ (/\ AllNodesReachable
                           /\ ~HasACycle
                           /\ OneToOne(left)
                           /\ OneToOne(right))



Traverse ==
    LET Child(parent, side) ==
            IF \E x \in nodes : <<x, parent>> \in side THEN
                 CHOOSE x \in nodes : <<x, parent>> \in side
            ELSE NoValue
        RECURSIVE TraverseRec(_)
        TraverseRec(node) ==
            IF node=NoValue THEN <<>>
            ELSE LET leftseq == TraverseRec(Child(node, left))
                     rightseq == TraverseRec(Child(node, right))
                 IN Append(leftseq, node) \o rightseq
    IN IF TreeIsEmpty THEN <<>> ELSE TraverseRec(root)

IsSorted(seq) == \A i,j \in 1..Cardinality(nodes) : (i < j) => seq[i] < seq[j]


vars == << nodes, left, right, root >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ nodes = {}
        /\ left = {}
        /\ right = {}
        /\ root = NoValue

EmptyTree == /\ (TreeIsEmpty)
             /\ \E x \in 1..N:
                  /\ root' = x
                  /\ nodes' = (nodes \union {x})
             /\ UNCHANGED << left, right >>

InsertLeft == /\ (~TreeIsEmpty)
              /\ \E x \in 1..N \ nodes:
                   LET parent ==        CHOOSE parent \in nodes :
                                 \lnot \E y \in nodes : <<y, parent>> \in left IN
                     /\ nodes' = (nodes \union {x})
                     /\ left' = (left \union { <<x, parent>> })
              /\ UNCHANGED << right, root >>

InsertRight == /\ (~TreeIsEmpty)
               /\ \E x \in 1..N \ nodes:
                    LET parent ==        CHOOSE parent \in nodes :
                                  \lnot \E y \in nodes : <<y, parent>> \in right IN
                      /\ nodes' = (nodes \union {x})
                      /\ right' = (right \union { <<x, parent>> })
               /\ UNCHANGED << left, root >>

Next == EmptyTree \/ InsertLeft \/ InsertRight

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jul 04 18:32:03 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
