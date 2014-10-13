----------------------------- MODULE BinaryTree -----------------------------
EXTENDS Naturals, FiniteSets
CONSTANT Val
VARIABLES nodes, parent, left, right

NaryTree == INSTANCE Tree

MaxTwoChildren == \A n \in nodes :
    Cardinality({x \in DOMAIN parent : n=parent[x]}) \leq 2

TypeInvariant == /\ NaryTree!TypeInvariant
                 /\ MaxTwoChildren

Init == /\ NaryTree!Init
        /\ left={}
        /\ right={} 
Next == /\ NaryTree!Next
        /\ UNCHANGED <<left, right>>
Spec == Init /\ [][Next]_<<nodes, parent, left, right>>

=============================================================================
\* Modification History
\* Last modified Sun Oct 12 21:11:13 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 20:56:35 EDT 2014 by lorinhochstein
