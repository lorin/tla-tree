----------------------------- MODULE BinaryTree -----------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Val
VARIABLES nodes, parent, left, right

NaryTree == INSTANCE Tree

MaxTwoChildren == \A n \in nodes :
    Cardinality({x \in DOMAIN parent : n=parent[x]}) \leq 2

TypeInvariant == /\ NaryTree!TypeInvariant
                 /\ MaxTwoChildren

NoCycles == NaryTree!NoCycles
SingleRoot == NaryTree!SingleRoot
                 
InsertLeft(v) == /\ v \notin nodes
                 /\ \E p \in nodes : \neg \E x \in left : parent[x]=p
                 /\ nodes' = nodes \union {v}
                 /\ left' = left \union {v}
                 /\ LET p == CHOOSE p \in nodes : \neg \E x \in left : parent[x]=p
                    IN parent'= parent @@ (v :> p)
                 
                 
InsertRight(v) == /\ v \notin nodes
                  /\ \E p \in nodes : \neg \E x \in right : parent[x]=p
                  /\ nodes' = nodes \union {v}
                  /\ right' = right \union {v}
                  /\ LET p == CHOOSE p \in nodes : \neg \E x \in right : parent[x]=p
                     IN parent'= parent @@ (v :> p)

Insert(v) == InsertLeft(v) \/ InsertRight(v)

Init == /\ NaryTree!Init
        /\ left={}
        /\ right={} 
Next == \E v \in Val: Insert(v)
Spec == Init /\ [][Next]_<<nodes, parent, left, right>>

=============================================================================
\* Modification History
\* Last modified Sun Oct 12 21:24:11 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 20:56:35 EDT 2014 by lorinhochstein
