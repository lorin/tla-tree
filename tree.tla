-------------------------------- MODULE Tree --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Val \* Set of values nodes can take
VARIABLES nodes, parent \* Set of nodes, function that takes node to parent

NoVal == CHOOSE v: v \notin Val \* root's parent is NoVal

TypeInvariant == /\ nodes \subseteq Val
                 /\ parent \in [nodes -> nodes \union {NoVal}]

(* Transitive closure 

Taken from Lamport's hyperbook, S 9.6.2 
*) 

(* Relation composition *)
R**S == LET T == {rs \in R \times S : rs[1][2] = rs[2][1]}
        IN {<<x[1][1],x[2][2]>> : x \in T}
        
NodesOf(R) == { r[1] : r \in R } \union { r[2] : r \in R }

(* Transitive closure
We add 1 to cardinality to catch cycles
*)

SimpleTC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(NodesOf(R))+1)
  
(* Convert a function to a relation *)  
Relation(f) == {x \in DOMAIN f: <<x, f[x]>> }

(* Transitive closure, taking a function as an argument *)
TC(f) == SimpleTC(Relation(f))

NoCycles == \lnot \E n \in nodes : <<n,n>> \in TC(parent)
SingleRoot == \E root \in nodes : \A n \in nodes \ {root} :
                <<n, root>> \in TC(parent)

Init == /\ nodes={}
        /\ parent= << >>
Insert(v) == /\ v \notin nodes
             /\ nodes' = nodes \union {v}
             /\ parent' = [parent EXCEPT ![v] = 
                            IF nodes={} THEN NoVal
                                        ELSE CHOOSE p:p \in nodes]
Next == \E v \in Val : Insert(v)
Spec == Init /\ [][Next]_<<nodes,parent>>
-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ NoCycles /\ SingleRoot)

=============================================================================
\* Modification History
\* Last modified Sun Oct 12 19:23:56 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 19:00:22 EDT 2014 by lorinhochstein
