-------------------------------- MODULE avl --------------------------------
(* This is an exercise in using TLA+ to model AVL trees *)
EXTENDS Sequences, tree
CONSTANT N, NoValue


(***************************************************************************
--algorithm AvlBalance {

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
\* BEGIN TRANSLATION
VARIABLES nodes, left, right, root

(* define statement *)
TypeOK == /\ \A x \in nodes : x \in Nat
          /\ \A x \in left : x \in nodes \X nodes
          /\ \A x \in right : x \in nodes \X nodes
          /\ (root = NoValue \/ root \in Nat)




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


Inv(rel) == { <<r[2], r[1]>> : r \in rel }

LeftDesc(ns, lrel, rrel, node) ==
    LET rel == (lrel \union rrel) \ {r \in rrel : r[2]=node}
    IN { x \in ns : <<node, x>> \in TC(Inv(rel)) }

RightDesc(ns, lrel, rrel, node) ==
    LET rel == (lrel \union rrel) \ {r \in lrel : r[2]=node}
    IN { x \in ns : <<node, x>> \in TC(Inv(rel)) }

HasBstProperty(nodeset,lrel,rrel) ==
    \A n \in nodeset:
        /\ \A x \in LeftDesc(nodeset, lrel, rrel, n) : n>x
        /\ \A x \in RightDesc(nodeset, lrel, rrel, n) : n<x

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

IsSorted(seq) == \A i,j \in 1..Len(seq) : (i < j) => seq[i] < seq[j]


IsBalanced(nodeset,lrel,rrel) ==
    \A n \in nodeset:
        LET ldesc == LeftDesc(nodeset, lrel, rrel,n)
            rdesc == RightDesc(nodeset, lrel, rrel,n)
            diff == Cardinality(ldesc) - Cardinality(rdesc)
            abs(x) == IF x<0 THEN -x ELSE x
        IN abs(diff) \leq 1


vars == << nodes, left, right, root >>

ProcSet == {0} \cup {1}

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

Insert == /\ (~TreeIsEmpty)
          /\ \E x \in 1..N \ nodes:
               LET parent ==        CHOOSE parent \in nodes :
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
                                                   right \union {<<x,parent>>})) IN
                 /\ nodes' = (nodes \union {x})
                 /\ IF x < parent
                       THEN /\ left' = (left \union {<<x,parent>>})
                            /\ right' = right
                       ELSE /\ right' = (right \union {<<x,parent>>})
                            /\ left' = left
          /\ root' = root

Next == EmptyTree \/ Insert

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Jul 05 20:10:39 EDT 2014 by lorinhochstein
\* Created Sat Jul 05 20:08:11 EDT 2014 by lorinhochstein
