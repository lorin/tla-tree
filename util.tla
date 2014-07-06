-------------------------------- MODULE util --------------------------------
(* Some generic utility operators *)


\* True if a relation is one-to-one
OneToOne(rel) == \A x,y,z \in nodes :
    (<<x,z>> \in rel /\ <<y,z>> \in rel) => x=y

\* Invert a binary relation
Inv(rel) == { <<r[2], r[1]>> : r \in rel }

(* Define transitive closure, from 9.6.2 of Lamport's Hyperbook.
   We use Cardinality(R)+1 to catch cycles *)

\* First, we need composition
R ** S == LET T == {rs \in R \X S : rs[1][2] = rs[2][1]}
          IN  {<<x[1][1], x[2][2]>> : x \in T}

TC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(R)+1)


=============================================================================
