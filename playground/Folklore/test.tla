---- MODULE test ----
EXTENDS TLC, Integers

VARIABLES
    \* @type: Bool;
    a,
    \* @type: Int -> Bool;
    b

Init == 
    /\ b \in [1..10->{TRUE,FALSE}]
    /\ a \in {TRUE,FALSE} /\ (\A x \in 1..10: b[x]) => a

Next == UNCHANGED <<a, b>>
====