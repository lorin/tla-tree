-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Naturals, Sequences
CONSTANT Val
VARIABLES nodes, parent, left, right

BTree == INSTANCE BinaryTree
NoVal == BTree!NoVal

TypeInvariant == /\ BTree!TypeInvariant
                 /\ nodes \subseteq Nat



(* In-order traversal *)


Traverse ==
    LET 
    root == CHOOSE n \in nodes : parent[n]=NoVal
    Child(p, side) ==
        IF \E x \in nodes : parent[x]=p /\ x \in side THEN 
        CHOOSE x \in nodes : parent[x]=p /\ x \in side
        ELSE NoVal

    RECURSIVE TraverseRec(_)
    TraverseRec(node) ==
        IF node=NoVal THEN <<>>
        ELSE LET leftseq == TraverseRec(Child(node, left))
                 rightseq == TraverseRec(Child(node, right))
             IN Append(leftseq, node) \o rightseq
    IN IF nodes={} THEN <<>> ELSE TraverseRec(root)

IsSorted(seq) == \A i,j \in 1..Len(seq) : (i < j) => seq[i] < seq[j]

TraverseIsSorted == IsSorted(Traverse)

Init == BTree!Init
Next == BTree!Next
Spec == Init /\ [][Next]_<<nodes,parent,left,right>>



=============================================================================
\* Modification History
\* Last modified Mon Oct 13 11:18:56 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 21:26:10 EDT 2014 by lorinhochstein
