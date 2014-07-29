-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC
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

    TypeOK == /\ n \in SUBSET (1..N)
              /\ DOMAIN p \in SUBSET (1..N)
              /\ \A x \in DOMAIN p : p[x] \in (1..N) \X {Left, Right}

    IsBinaryTree(nodes, parent) ==
      \A x,y \in DOMAIN parent : (parent[x]=parent[y]) => (x=y)

    \* Use transitive closure of the parent->child relation
    Descendents(root, parent) ==
      LET nodes == DOMAIN parent
          rel == { <<parent[x][1], x>> : x \in nodes }
      IN { x \in nodes : <<root, x>> \in TC(rel) }

    (* Returns a set that contains the left or right child element of the
       specified node, or an empty set if there's no corresponding child *)
    Child(node, parent, side) ==
      { x \in DOMAIN parent : parent[x] = <<node, side>> }

    SideDescendents(x, parent, side) ==
      Child(x, parent, side) \union
      UNION { Descendents(root, parent) : root \in Child(x, parent, side)}

    HasBstProperty(nodes, parent) == \A root \in nodes :
      ((\A x \in SideDescendents(root, parent, Left)  : root>x)  /\
       (\A x \in SideDescendents(root, parent, Right) : root<x))

    IsBinarySearchTree(nodes, parent) ==
      IsBinaryTree(nodes, parent) /\ HasBstProperty(nodes, parent)

    (* Returns a set that contains the root, or empty set if no root *)
    Root(nodes, parent) == nodes \ DOMAIN parent

    (* In-order traversal *)
    Traverse ==
      LET RECURSIVE TraverseRec(_, _)
          TraverseRec(nset, parent) ==
           IF nset={} THEN <<>>
           ELSE LET node==CHOOSE x \in nset : TRUE
                    leftseq  == TraverseRec(Child(node, parent, Left), parent)
                    rightseq == TraverseRec(Child(node, parent, Right), parent)
                IN Append(leftseq, node) \o rightseq
      IN TraverseRec(Root(n, p), p)

    IsSorted(seq) == \A i,j \in 1..Len(seq) : (i < j) => seq[i] < seq[j]


    \* Generate a path that goes from the node to the root
    RECURSIVE Path(_, _, _)
    Path(node, root, parent) ==
      IF node=root THEN <<root>>
      ELSE <<node>> \o Path(parent[node][1], root, parent)

    LongestPath(root, parent) ==
      LET nodes==Descendents(root, parent) \union {root}
          leaf==CHOOSE x \in nodes : \A y \in nodes :
            Len(Path(x, root, parent)) \geq Len(Path(y, root, parent))
      IN Len(Path(leaf, root, parent))


    (* Takes as argument a set, roots, that is either empty or
       contains a single element *)
    Height(roots, parent) ==
      IF roots={} THEN 0
      ELSE LongestPath(CHOOSE root \in roots : TRUE, parent)

    BalanceFactor(x, parent) ==
        LET hleft  == Height(Child(x, parent, Left), parent)
            hright == Height(Child(x, parent, Right), parent)
        IN hleft-hright


    NodeIsBalanced(x, parent) ==
        LET hdiff == BalanceFactor(x, parent)
        IN hdiff \geq -1 /\ hdiff \leq 1

    TreeIsBalanced(nodes, parent) ==
      \A x \in nodes: NodeIsBalanced(x, parent)

    UnbalancedNode(nodes, parent) ==
      CHOOSE x \in nodes :
        /\ ~NodeIsBalanced(x, parent)
        /\ \y \in Descendents(x, parent) : NodeIsBalanced(y, parent)

  }

  process(EmptyTree=0) {
    e: await(n={});
       with(x \in 1..N) {
         n:= n \union {x}
      }
  }

  process(Insert=1) {
    i: while(PrintT(Traverse) /\ n /= 1..N) {
      await(n /= {});
      with(x \in 1..N \ n,
           y = CHOOSE y \in n \X {Left, Right} :
            IsBinarySearchTree(n \union {x}, p @@ x :> y)) {
        n := n \union {x};
        p := p @@ x :> y
      }
    }
  }

  (* Tree balance violations
      1. Insertion to left subtree of left child
      2. Insertion to right subtree of left child
      3. Insertion to left subtree of right child
      4. Insertion to right subtree of right child
   *)

  process(SingleRotateWithLeft=2) {
    srwl: while(TRUE) {
      await(
       /\ ~TreeIsBalanced(n, p)
       /\ \E x \in n :
        (/\ BalanceFactor(x, p)<1
         /\ \A y \in Child(x, p, Left) : NodeIsBalanced(y, p)
         /\ \A y \in Child(x, p, Right) : NodeIsBalanced(y, p)));
      with(x = CHOOSE x \in n :
            (/\ BalanceFactor(x, p)<1
             /\ \A y \in Child(x, p, Left) : NodeIsBalanced(y, p)
             /\ \A y \in Child(x, p, Right) : NodeIsBalanced(y, p)),
           cx = CHOOSE y \in Child(x, p, Left) : TRUE,
           px = p[x][1]) {
        p := [p EXCEPT ![x]=<<cx,Right>>]
        \* p := [p EXCEPT ![x]=<<cx,Right>>,![cx]=p[x]]
      }
    }
  }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES n, p, pc

(* define statement *)
TypeOK == /\ n \in SUBSET (1..N)
          /\ DOMAIN p \in SUBSET (1..N)
          /\ \A x \in DOMAIN p : p[x] \in (1..N) \X {Left, Right}

IsBinaryTree(nodes, parent) ==
  \A x,y \in DOMAIN parent : (parent[x]=parent[y]) => (x=y)


Descendents(root, parent) ==
  LET nodes == DOMAIN parent
      rel == { <<parent[x][1], x>> : x \in nodes }
  IN { x \in nodes : <<root, x>> \in TC(rel) }



Child(node, parent, side) ==
  { x \in DOMAIN parent : parent[x] = <<node, side>> }

SideDescendents(x, parent, side) ==
  Child(x, parent, side) \union
  UNION { Descendents(root, parent) : root \in Child(x, parent, side)}

HasBstProperty(nodes, parent) == \A root \in nodes :
  ((\A x \in SideDescendents(root, parent, Left)  : root>x)  /\
   (\A x \in SideDescendents(root, parent, Right) : root<x))

IsBinarySearchTree(nodes, parent) ==
  IsBinaryTree(nodes, parent) /\ HasBstProperty(nodes, parent)


Root(nodes, parent) == nodes \ DOMAIN parent


Traverse ==
  LET RECURSIVE TraverseRec(_, _)
      TraverseRec(nset, parent) ==
       IF nset={} THEN <<>>
       ELSE LET node==CHOOSE x \in nset : TRUE
                leftseq  == TraverseRec(Child(node, parent, Left), parent)
                rightseq == TraverseRec(Child(node, parent, Right), parent)
            IN Append(leftseq, node) \o rightseq
  IN TraverseRec(Root(n, p), p)

IsSorted(seq) == \A i,j \in 1..Len(seq) : (i < j) => seq[i] < seq[j]



RECURSIVE Path(_, _, _)
Path(node, root, parent) ==
  IF node=root THEN <<root>>
  ELSE <<node>> \o Path(parent[node][1], root, parent)

LongestPath(root, parent) ==
  LET nodes==Descendents(root, parent) \union {root}
      leaf==CHOOSE x \in nodes : \A y \in nodes :
        Len(Path(x, root, parent)) \geq Len(Path(y, root, parent))
  IN Len(Path(leaf, root, parent))




Height(roots, parent) ==
  IF roots={} THEN 0
  ELSE LongestPath(CHOOSE root \in roots : TRUE, parent)

BalanceFactor(x, parent) ==
    LET hleft  == Height(Child(x, parent, Left), parent)
        hright == Height(Child(x, parent, Right), parent)
    IN hleft-hright


NodeIsBalanced(x, parent) ==
    LET hdiff == BalanceFactor(x, parent)
    IN hdiff \geq -1 /\ hdiff \leq 1

TreeIsBalanced(nodes, parent) ==
  \A x \in nodes: NodeIsBalanced(x, parent)


vars == << n, p, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ n = {}
        /\ p = EmptyFunction
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "e"
                                        [] self = 1 -> "i"
                                        [] self = 2 -> "srwl"]

e == /\ pc[0] = "e"
     /\ (n={})
     /\ \E x \in 1..N:
          n' = (n \union {x})
     /\ pc' = [pc EXCEPT ![0] = "Done"]
     /\ p' = p

EmptyTree == e

i == /\ pc[1] = "i"
     /\ IF PrintT(Traverse) /\ n /= 1..N
           THEN /\ (n /= {})
                /\ \E x \in 1..N \ n:
                     LET y ==    CHOOSE y \in n \X {Left, Right} :
                              IsBinarySearchTree(n \union {x}, p @@ x :> y) IN
                       /\ n' = (n \union {x})
                       /\ p' = (p @@ x :> y)
                /\ pc' = [pc EXCEPT ![1] = "i"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                /\ UNCHANGED << n, p >>

Insert == i

srwl == /\ pc[2] = "srwl"
        /\     (
           /\ ~TreeIsBalanced(n, p)
           /\ \E x \in n :
            (/\ BalanceFactor(x, p)<1
             /\ \A y \in Child(x, parent, Left) : NodeIsBlanced(y, parent)
             /\ \A y \in Child(x, parent, Right) : NodeIsBlanced(y, parent)))
        /\ LET x ==    CHOOSE x in n :
                    (/\ BalanceFactor(x, p)<1
                     /\ \A y \in Child(x, parent, Left) : NodeIsBlanced(y, parent)
                     /\ \A y \in Child(x, parent, Right) : NodeIsBlanced(y, parent)) IN
             LET cx == CHOOSE y \in Child(x, parent, Left) IN
               LET px == p[x][1] IN
                 p' = p
        /\ pc' = [pc EXCEPT ![2] = "srwl"]
        /\ n' = n

SingleRotateWithLeft == srwl

Next == EmptyTree \/ Insert \/ SingleRotateWithLeft

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Jul 27 17:55:35 EDT 2014 by lorinhochstein
\* Created Sun Jul 27 10:46:39 EDT 2014 by lorinhochstein
