(* This is an exercise in using TLA+ to model algorithms of binary search trees *)
-------------------------------- MODULE tree --------------------------------

EXTENDS Integers
CONSTANT Empty, N

\* We model trees as records.





(***************************************************************************
--fair algorithm GrowBinaryTree {
variable tree = Empty;

define {
RECURSIVE isTree(_)
isTree(t) == \/ t = Empty
             \/ ( /\ t.value \in Nat
                  /\ isTree(t.left)
                  /\ isTree(t.right))

TypeOK == isTree(tree)

RECURSIVE insert(_, _)
insert(t, n) == CASE t = Empty  -> [value |-> n, left |-> Empty, right |-> Empty ] []
                     n < t.value -> [value |-> n, left |-> insert(t.left, n), right |-> t.right] []
                     OTHER      -> [value |-> n, left |-> t.left, right |-> insert(t.right, n)]

max(x, y) == IF (x>y) THEN x ELSE y

abs(x) == max(x, -x)


RECURSIVE depth(_)
depth(t) == IF (t = Empty) THEN 0 ELSE 1 + max(depth(t.left), depth(t.right))

isBalanced(t) == \/ t = Empty
                 \/ abs(depth(t.left) - depth(t.right)) \leq 1
}

{ while(TRUE)
    { with (x \in 1..N)
        { tree := insert(tree, x)
        }
    }
}

}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE tree

(* define statement *)
RECURSIVE isTree(_)
isTree(t) == \/ t = Empty
             \/ ( /\ t.value \in Nat
                  /\ isTree(t.left)
                  /\ isTree(t.right))

TypeOK == isTree(tree)

RECURSIVE insert(_, _)
insert(t, n) == CASE t = Empty  -> [value |-> n, left |-> Empty, right |-> Empty ] []
                     n < t.value -> [value |-> n, left |-> insert(t.left, n), right |-> t.right] []
                     OTHER      -> [value |-> n, left |-> t.left, right |-> insert(t.right, n)]

max(x, y) == IF (x>y) THEN x ELSE y

abs(x) == max(x, -x)


RECURSIVE depth(_)
depth(t) == IF (t = Empty) THEN 0 ELSE 1 + max(depth(t.left), depth(t.right))

isBalanced(t) == \/ t = Empty
                 \/ abs(depth(t.left) - depth(t.right)) \leq 1


vars == << tree >>

Init == (* Global variables *)
        /\ tree = Empty

Next == \E x \in 1..N:
          tree' = insert(tree, x)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Sat Jun 21 19:14:24 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
