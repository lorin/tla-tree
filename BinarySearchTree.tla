-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Integers, FiniteSets, TLC
CONSTANT Left, Right, N, EmptyFunction

(* Define transitive closure, from 9.6.2 of Lamport's Hyperbook. *)

\* First, we need composition
R ** S == LET T == {rs \in R \X S : rs[1][2] = rs[2][1]}
          IN  {<<x[1][1], x[2][2]>> : x \in T}

TC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(R))

(***************************************************************************
--algorithm GrowTree {
  variables n={}, p=EmptyFunction;

  define {

    TypeOK == /\ n \in SUBSET 1..N
              /\ p \in [1..N -> 1..N \X {Left, Right}] \union {EmptyFunction}

    IsBinaryTree(nodes, parent) ==
      \A x,y \in DOMAIN parent : (parent[x]=parent[y]) => (x=y)

    \* Use transitive closure of the parent->child relation
    Descendents(root, parent) ==
      LET nodes == DOMAIN parent
          rel == { <<parent[x][1], x>> : x \in nodes }
      IN { x \in nodes : <<root, x>> \in TC(rel) }

    SideDescendents(x, parent, side) ==
      LET c == { y \in DOMAIN parent : parent[y] = <<x,side>> }
      IN UNION { \A root \in c : Descendents(root, parent) }

    HasBstProperty(nodes, parent) == \A root \in nodes :
      ((\A x \in SideDescendents(root, parent, Left)  : root>x)  /\
       (\A x \in SideDescendents(root, parent, Right) : root<x))

    IsBinarySearchTree(nodes, parent) ==
      IsBinaryTree(nodes, parent) /\ HasBstProperty(nodes, parent)

  }

  process(EmptyTree=0) {
    e: while(n={}) {
      with(x \in 1..N) {
        n:= n \union {x}
      }
    }
  }
  process(Insert=1) {
    i: while(n /= 1..N) {
      await(n /={});
      with(x \in 1..N \ n,
           y = CHOOSE y \in n \X {Left, Right} :
            IsBinarySearchTree(n \union {x}, p @@ x :> y)) {
        n := n \union {x};
        p := p @@ x :> y
      }
    }
  }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES n, p, pc

(* define statement *)
TypeOK == /\ n \in SUBSET 1..N
          /\ p \in [1..N -> 1..N \X {Left, Right}] \union {EmptyFunction}

IsBinaryTree(nodes, parent) ==
  \A x,y \in DOMAIN parent : (parent[x]=parent[y]) => (x=y)


Descendents(root, parent) ==
  LET nodes == DOMAIN parent
      rel == { <<parent[x][1], x>> : x \in nodes }
  IN { x \in nodes : <<root, x>> \in TC(rel) }

SideDescendents(x, parent, side) ==
  LET c == { y \in DOMAIN parent : parent[y] = <<x,side>> }
  IN UNION { \A root \in c : Descendents(root, parent) }

HasBstProperty(nodes, parent) == \A root \in nodes :
  ((\A x \in SideDescendents(root, parent, Left)  : root>x)  /\
   (\A x \in SideDescendents(root, parent, Right) : root<x))

IsBinarySearchTree(nodes, parent) ==
  IsBinaryTree(nodes, parent) /\ HasBstProperty(nodes, parent)


vars == << n, p, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ n = {}
        /\ p = EmptyFunction
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "e"
                                        [] self = 1 -> "i"]

e == /\ pc[0] = "e"
     /\ IF n={}
           THEN /\ \E x \in 1..N:
                     n' = (n \union {x})
                /\ pc' = [pc EXCEPT ![0] = "e"]
           ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                /\ n' = n
     /\ p' = p

EmptyTree == e

i == /\ pc[1] = "i"
     /\ IF n /= 1..N
           THEN /\ (n /={})
                /\ \E x \in 1..N \ n:
                     LET y ==    CHOOSE y \in n \X {Left, Right} :
                              IsBinarySearchTree(n \union {x}, p @@ x :> y) IN
                       /\ n' = (n \union {x})
                       /\ p' = (p @@ x :> y)
                /\ pc' = [pc EXCEPT ![1] = "i"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                /\ UNCHANGED << n, p >>

Insert == i

Next == EmptyTree \/ Insert
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Jul 27 11:56:02 EDT 2014 by lorinhochstein
\* Created Sun Jul 27 10:46:39 EDT 2014 by lorinhochstein
