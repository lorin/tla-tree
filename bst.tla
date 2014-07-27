-------------------------------- MODULE bst --------------------------------
(* This is an exercise in using TLA+ to model binary search trees *)
EXTENDS Sequences, tree
CONSTANT N, NoValue

(***************************************************************************
--algorithm GrowTree {
    variables nodes = {}, left = {}, right = {}, root = NoValue;

    define {

        TypeOK == /\ \A x \in nodes : x \in Nat
                  /\ \A x \in left : x \in nodes \X nodes
                  /\ \A x \in right : x \in nodes \X nodes
                  /\ (root = NoValue \/ root \in Nat)


        (* It's a tree if there's a root: a node that is reachable
           from all other nodes. Also, need to verify there are
           no cycles, and that there is at most one left-child
           and right-child. *)

        TreeIsEmpty == nodes = {}

        AllNodesReachable ==
            \E y \in nodes : \A x \in nodes \ {y} :
                <<x, y>> \in TC(left \union right)

        HasACycle == \E x \in nodes : <<x, x>> \in TC(left \union right)


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

        IsSorted(seq) == \A i,j \in 1..Len(seq) : (i < j) => seq[i] < seq[j]
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
                  parent = CHOOSE parent \in nodes :
                    LET Childless(pt, side) == \lnot \E y \in nodes : <<y,pt>> \in side
                    IN (/\ x < parent
                        /\ Childless(parent, left)
                        /\ HasBstProperty(nodes \union {x},
                                          left \union {<<x,parent>>},
                                          right))
                    \/ (/\ x > parent
                        /\ Childless(parent, right)
                        /\ HasBstProperty(nodes \union {x},
                                          left,
                                          right \union {<<x,parent>>}))) {
                nodes := nodes \union {x};
                if (x < parent)
                    left := left \union {<<x,parent>>}
                else
                    right := right \union {<<x,parent>>}

            }
        }
    }
}
 ***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Sat Jul 05 21:38:03 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein