-------------------------------- MODULE tree --------------------------------
(* This is an exercise in using TLA+ to model binary search trees *)
EXTENDS FiniteSets, util

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

IsBalanced(nodeset,lrel,rrel) ==
    \A n \in nodeset:
        LET ldesc == LeftDesc(nodeset, lrel, rrel,n)
            rdesc == RightDesc(nodeset, lrel, rrel,n)
            diff == Cardinality(ldesc) - Cardinality(rdesc)
            abs(x) == IF x<0 THEN -x ELSE x
        IN abs(diff) \leq 1
=============================================================================
\* Modification History
\* Last modified Sat Jul 05 21:38:03 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
