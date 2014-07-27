-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Integers
CONSTANT Left, Right, EmptyFunction, N

(***************************************************************************
--algorithm GrowTree {
  variables nodes={}, parent=EmptyFunction;

  define {
    IsBinaryTree(n,p) == \A x,y \in n : (p[x]=p[y]) => (x=y)

    SideDescendents(x,p,side) ==
      UNION { \A y \in DOMAIN p : p[y] = <<x,side>> : Descendents(y)}

    HasBstProperty(n, p) == \A x \in n :
      ((\A y \in SideDescendents(x, p, Left)  : x>y)  /\
       (\A y \in SideDescendents(x, p, Right) : x<y))

    IsBinarySearchTree(n, p) == IsBinaryTree(n, p) /\ HasBstProperty(n, p)

  }

  process(EmptyTree=0) {
    e: while(nodes={}) {
      with(x \in 1..N) {
        nodes := nodes \union {x}
      }
    }
  }
  process(Insert=1) {
    i: while(nodes /= 1..N) {
      await(nodes/={});
      with(x \in 1..N \ nodes,
           y = CHOOSE y \in nodes \X {Left, Right} :
            IsBinarySearchTree(nodes \union {x}, [parent EXCEPT ![x] = y])) {
        nodes := nodes \union {x};
        parent := [parent EXCEPT ![x] = y]
      }
    }
  }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES nodes, parent, pc

(* define statement *)
IsBinaryTree(n,p) == \A x,y \in n : (p[x]=p[y]) => (x=y)

Children(x,p,side) == {}

HasBstProperty(n, p) == \A x \in n :
  ((\A y \in Children(x, p, Left)  : x>y)  /\
   (\A y \in Children(x, p, Right) : x<y))

IsBinarySearchTree(n, p) == IsBinaryTree(n, p) /\ HasBstProperty(n, p)


vars == << nodes, parent, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ nodes = {}
        /\ parent = EmptyFunction
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "e"
                                        [] self = 1 -> "i"]

e == /\ pc[0] = "e"
     /\ IF nodes={}
           THEN /\ \E x \in 1..N:
                     nodes' = (nodes \union {x})
                /\ pc' = [pc EXCEPT ![0] = "e"]
           ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                /\ nodes' = nodes
     /\ UNCHANGED parent

EmptyTree == e

i == /\ pc[1] = "i"
     /\ IF nodes /= 1..N
           THEN /\ (nodes/={})
                /\ \E x \in 1..N \ nodes:
                     LET y ==    CHOOSE y \in nodes \X {Left, Right} :
                              IsBinarySearchTree(nodes, parent) IN
                       /\ nodes' = (nodes \union {x})
                       /\ parent' = [parent EXCEPT ![x] = y]
                /\ pc' = [pc EXCEPT ![1] = "i"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                /\ UNCHANGED << nodes, parent >>

Insert == i

Next == EmptyTree \/ Insert
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Jul 27 11:33:18 EDT 2014 by lorinhochstein
\* Created Sun Jul 27 10:46:39 EDT 2014 by lorinhochstein
