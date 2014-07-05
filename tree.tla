(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers, FiniteSets, Sequences
CONSTANT N, NoValue

(***************************************************************************
--algorithm GrowTree {
    variables nodes = {}, left = {}, right = {}, root = NoValue, traversal = <<>>;

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

        TreeIsEmpty == nodes = {}

        AllNodesReachable ==
            \E y \in nodes : \A x \in nodes \ {y} :
                <<x, y>> \in TC(left \union right)

        HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)

        IsATree == TreeIsEmpty \/ (AllNodesReachable /\ ~HasACycle)

        (* In-order traversal *)
        Traverse ==
            LET LeftChild(node) ==
                    IF \E x \in nodes: <<x, node>> \in left THEN CHOOSE x : <<x, node>> \in left
                    ELSE NoValue
                RightChild(node) ==
                    IF \E x \in nodes: <<x, node>> \in right THEN CHOOSE x : <<x, node>> \in right
                    ELSE NoValue
                RECURSIVE TraverseRec(_)
                TraverseRec(node) ==
                    IF node=NoValue THEN <<>>
                    ELSE LET leftseq == TraverseRec(LeftChild(node))
                             rightseq == TraverseRec(RightChild(node))
                         IN Append(leftseq, node) \o rightseq
            IN IF TreeIsEmpty THEN <<>> ELSE TraverseRec(root)

        IsSorted(seq) == \A i,j \in 1..Cardinality(nodes) : (i < j) => seq[i] < seq[j]
    }

    process (EmptyTree = 0) {
        e: while(TRUE) {
            await (TreeIsEmpty);
            with (x \in 1..N) {
                root := x;
                nodes := nodes \union {x};
                traversal := Traverse
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
                or     right := right \union { <<x, parent>> };
                traversal := Traverse
            }
        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES nodes, left, right, root, traversal

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
    \E y \in nodes : \A x \in nodes \ {y} :
        <<x, y>> \in TC(left \union right)

HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)

IsATree == Empty \/ (AllNodesReachable /\ ~HasACycle)


LeftChild(node) ==
    IF \E x \in nodes: <<x, node>> \in left THEN CHOOSE x : <<x, node>> \in left
    ELSE NoValue

RightChild(node) ==
    IF \E x \in nodes: <<x, node>> \in right THEN CHOOSE x : <<x, node>> \in right
    ELSE NoValue

Traverse ==
    LET RECURSIVE TraverseRec(_)
        TraverseRec(node) ==
            IF node=NoValue THEN <<>>
            ELSE LET leftseq == TraverseRec(LeftChild(node))
                     rightseq == TraverseRec(RightChild(node))
                 IN Append(leftseq, node) \o rightseq
    IN IF nodes = {} THEN <<>> ELSE TraverseRec(root)


vars == << nodes, left, right, root, traversal >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ nodes = {}
        /\ left = {}
        /\ right = {}
        /\ root = NoValue
        /\ traversal = <<>>

EmptyTree == /\ (nodes = {})
             /\ \E x \in 1..N:
                  /\ root' = x
                  /\ nodes' = (nodes \union {x})
                  /\ traversal' = Traverse
             /\ UNCHANGED << left, right >>

Insert == /\ (nodes /= {})
          /\ \E x \in 1..N \ nodes:
               \E parent \in nodes:
                 /\ nodes' = (nodes \union {x})
                 /\ \/ /\ left' = (left \union { <<x, parent>> })
                       /\ right' = right
                    \/ /\ right' = (right \union { <<x, parent>> })
                       /\ left' = left
                 /\ traversal' = Traverse
          /\ root' = root

Next == EmptyTree \/ Insert

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jul 04 18:32:03 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
