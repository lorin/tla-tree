(* This is an exercise in using TLA+ to model binary search trees *)
-------------------------------- MODULE tree --------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N




(***************************************************************************
--algorithm GrowTree {
    variables left = {}; right = {};
    
    define {
        NodesOf(R) == { r[1]: r \in R} \union { r[2] : r \in R }
        Nodes(l, r) == NodesOf(l) \union NodesOf(r)
        
        \* Define transitive closure, from 9.6.2 of Lamport's Hyperbook
        
        R ** S == LET T == {rs \in R\X S : rs[1][2] = rs[2][1]}
                  IN  {<<x[1][1], x[2][2]>> : x \in T} 
                  
        TC(R) ==
            LET RECURSIVE STC(_)
                STC(n) == IF n=1 THEN R
                                 ELSE STC(n-1) \union STC(n-1)**R
            IN IF R={} THEN {} ELSE STC(Cardinality(R))
     
        
        \* It's a tree if there's a root: a node that is reachable
        \* from all other nodes 
        
        IsATree(l, r) ==
            LET elts == Nodes(l,r)
            IN  \E root \in elts : \A x \in elts \ {root} : <<x, root>> \in TC(l \union r)   
       
    }
    
    { while (TRUE) {
        with(child \in 1..N \ Nodes(left, right);
             parent \in Nodes(left, right);
             side \in { left, right} ) {
             
              side := side \union { <<child, parent>> } 
          
        }
    }}
    
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES left, right

(* define statement *)
NodesOf(R) == { r[1]: r \in R} \union { r[2] : r \in R }
Nodes(l, r) == NodesOf(l) \union NodesOf(r)



R ** S == LET T == {rs \in R\X S : rs[1][2] = rs[2][1]}
          IN  {<<x[1][1], x[2][2]>> : x \in T}

TC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(R))





IsATree(l, r) ==
    LET elts == Nodes(l,r)
    IN  \E root \in elts : \A x \in elts \ {root} : <<x, root>> \in TC(l \union r)


vars == << left, right >>

Init == (* Global variables *)
        /\ left = {}
        /\ right = {}

Next == /\ \E child \in 1..N \ Nodes(left, right):
             \E parent \in Nodes(left, right):
               \E side \in { left, right}:
                 side' = (side \union { <<child, parent>> })
        /\ UNCHANGED << left, right >>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Jun 30 21:17:32 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
