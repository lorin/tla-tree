-------------------------------- MODULE Tree --------------------------------

CONSTANTS Val \* Set of values nodes can take
VARIABLES nodes, parent \* Set of nodes, function that takes node to parent

NoVal == CHOOSE v: v \notin Val
TypeInvariant == /\ nodes \subseteq Val
                 /\ parent \in [nodes -> nodes \union {NoVal}]

=============================================================================
\* Modification History
\* Last modified Sun Oct 12 19:02:58 EDT 2014 by lorinhochstein
\* Created Sun Oct 12 19:00:22 EDT 2014 by lorinhochstein
