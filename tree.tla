-------------------------------- MODULE Tree --------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Val \* Set of values nodes can take
VARIABLES nodes, parent \* Set of nodes, function that takes node to parent

NoVal == CHOOSE v: v \notin Val \* root's parent is NoVal

TypeInvariant == /\ nodes \subseteq Val
                 /\ parent \in [nodes -> nodes \union {NoVal}]

(* Transitive closure, taken from Lamport's hyperbook, S 9.6.2 *) 


R**S == LET T == {rs \in R \times S : rs[1][2] = rs[2][1]}
        IN {<<x[1][1],x[2][2]>> : x \in T}
        
NodesOf(R) == { r[1] : r \in R } \union { r[2] : r \in R }


SimpleTC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(NodesOf(R))+1) \* We add 1 to catch cycles
  
(* Convert a function to a relation *)  
Relation(f) == {<<x, f[x]>> : x \in DOMAIN f }

(* Transitive closure, taking a function as an argument *)
TC(f) == SimpleTC(Relation(f))

NoCycles == \lnot \E n \in nodes : <<n,n>> \in TC(parent)
SingleRoot == \/ nodes={} 
              \/ \E root \in nodes : \A n \in nodes \ {root} :
                 <<n, root>> \in TC(parent)

Init == /\ nodes={}
        /\ parent= << >>
Insert(v) == /\ v \notin nodes
             /\ nodes' = nodes \union {v}
             /\ parent' = parent @@ ( v :> IF nodes={}
                                           THEN NoVal 
                                           ELSE CHOOSE p \in nodes : TRUE )

AddCycle == /\ Cardinality(nodes)>1
            /\ LET x == CHOOSE x \in nodes : parent[x] /= NoVal
               IN parent'=[parent EXCEPT ![x] = CHOOSE y \in nodes : TRUE]
            /\ UNCHANGED nodes

AddRoot(v) == /\ v \notin nodes
              /\ nodes' = nodes \union {v}
              /\ parent' = parent @@ (v :> NoVal)
           

Next == \/ \E v \in Val : Insert(v)
Spec == Init /\ [][Next]_<<nodes,parent>>
-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ NoCycles /\ SingleRoot)
=============================================================================
\* Modification History
\* Last modified Sun Oct 12 20:54:40 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 19:00:22 EDT 2014 by lorinhochstein
