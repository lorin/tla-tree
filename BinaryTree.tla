----------------------------- MODULE BinaryTree -----------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Val
VARIABLES nodes, parent, left, right

NaryTree == INSTANCE Tree
NoVal == NaryTree!NoVal

MaxTwoChildren == \A n \in nodes :
    Cardinality({x \in DOMAIN parent : n=parent[x]}) \leq 2

TypeInvariant == /\ NaryTree!TypeInvariant
                 /\ MaxTwoChildren

NoCycles == NaryTree!NoCycles
SingleRoot == NaryTree!SingleRoot

AddRoot(v) == /\ nodes = {}
              /\ nodes' = {v}
              /\ parent' = (v :> NoVal)
              /\ UNCHANGED <<left, right>>

                 
InsertLeft(v) == /\ v \notin nodes
                 /\ \E p \in nodes : \neg \E x \in left : parent[x]=p
                 /\ nodes' = nodes \union {v}
                 /\ left' = left \union {v}
                 /\ LET p == CHOOSE p \in nodes : \neg \E x \in left : parent[x]=p
                    IN parent'= parent @@ (v :> p)
                 /\ UNCHANGED right
                 
                 
InsertRight(v) == /\ v \notin nodes
                  /\ \E p \in nodes : \neg \E x \in right : parent[x]=p
                  /\ nodes' = nodes \union {v}
                  /\ right' = right \union {v}
                  /\ LET p == CHOOSE p \in nodes : \neg \E x \in right : parent[x]=p
                     IN parent'= parent @@ (v :> p)
                  /\ UNCHANGED left

FullTree == /\ nodes=Val
            /\ UNCHANGED<<nodes, parent, left, right>>


Insert(v) == AddRoot(v) \/ InsertLeft(v) \/ InsertRight(v) \/ FullTree

Init == /\ NaryTree!Init
        /\ left={}
        /\ right={} 
Next == \E v \in Val: Insert(v)
Spec == Init /\ [][Next]_<<nodes, parent, left, right>>

=============================================================================
\* Modification History
\* Last modified Mon Oct 13 11:16:19 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 20:56:35 EDT 2014 by lorinhochstein
