(* This is an exercise in using TLA+ to model algorithms of binary search trees *)
-------------------------------- MODULE tree --------------------------------

EXTENDS Integers
CONSTANT Empty

\* We model trees as records.

RECURSIVE isTree(_)

isTree(t) == \/ t = Empty
             \/ ( /\ t.value \in Nat
                  /\ isTree(t.left)
                  /\ isTree(t.right))

RECURSIVE insert(_, _)
insert(t, n) == CASE t = Empty  -> [value |-> n, left |-> Empty, right |-> Empty ] []
                     n < t.left -> [value |-> n, left |-> insert(t.left, n), right |-> t.right] []
                     OTHER      -> [value |-> n, left |-> t.left, right |-> insert(t.right, n)]

(***************************************************************************
--algorithm GrowBinaryTree {

variable tree = Empty;

{ while(TRUE)
    { with (x \in Nat)
        { tree := insert(tree, x)
        }
    }
}

}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE tree

vars == << tree >>

Init == (* Global variables *)
        /\ tree = Empty

Next == \E x \in Nat:
          tree' = insert(tree, x)

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Jun 20 20:14:13 EDT 2014 by lorinhochstein
\* Created Fri Jun 20 19:55:21 EDT 2014 by lorinhochstein
