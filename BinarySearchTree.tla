-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Integers
CONSTANT Left, Right, EmptyFunction, N

(***************************************************************************
--algorithm GrowTree {
  variables n={}, p=EmptyFunction;

  define {

    TypeOK == /\ n \in 1..N
              /\ p \in [1..N -> 1..N \X {Left, Right}]

    IsBinaryTree(nodes, parent) ==
      \A x,y \in nodes : (parent[x]=parent[y]) => (x=y)

    Descendents(x, parent) == {}

    SideDescendents(x, parent, side) ==
      LET c == { y \in DOMAIN parent : p[y] = <<x,side>> }
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
            IsBinarySearchTree(n \union {x}, [p EXCEPT ![x] = y])) {
        n := n \union {x};
        p := [p EXCEPT ![x] = y]
      }
    }
  }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES n, p, pc

(* define statement *)
TypeOK == /\ n \in 1..N
          /\ p \in [1..N -> 1..N \X {Left, Right}]

IsBinaryTree(nodes, parent) ==
  \A x,y \in nodes : (parent[x]=parent[y]) => (x=y)

Descendents(x, parent) == {}

SideDescendents(x, parent, side) ==
  LET c == { y \in DOMAIN parent : p[y] = <<x,side>> }
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
                              IsBinarySearchTree(n \union {x}, [p EXCEPT ![x] = y]) IN
                       /\ n' = (n \union {x})
                       /\ p' = [p EXCEPT ![x] = y]
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
