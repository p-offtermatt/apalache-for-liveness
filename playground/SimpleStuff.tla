---- MODULE SimpleStuff ----
EXTENDS TLC, Integers, Sequences

CONSTANTS
    \* @type: Int;
    A_START,
    \* @type: Int;
    B_START,
    \* @type: Bool;
    hasLoop

VARIABLES 
    \* @typeAlias: STATE = [ a: Int, b: Int];
    \* @type: Int;
    a,
    \* @type: Int;
    b,
    \* @type: Int;
    loop_a,
    \* @type: Int;
    loop_b,
    \* @type: Bool;
    isEnd,
    \* @type: Bool;
    loopStarted


ConstInit == 
    /\ A_START \in {5, 6}
    /\ B_START \in {3, 4}
    /\ hasLoop \in {TRUE, FALSE}

Init == 
    /\ a = A_START 
    /\ b = B_START 
    /\ isEnd = FALSE 
    /\ loopStarted = FALSE
    \* initial values for the loop variables do not matter:
    \* if the trace has a loop, they will be set when StartLoop is used.
    \* If not, their values do not matter. 
    /\ loop_a = 0
    /\ loop_b = 0

loop_vars == << loop_a, loop_b, loopStarted >>

Step == 
    /\ a' = a + b 
    /\ b' = a 
    /\ UNCHANGED <<isEnd, loop_vars>>
Reset == 
    /\ a' = A_START
    /\ b' = B_START 
    /\ UNCHANGED <<isEnd, loop_vars>>

Stutter == UNCHANGED <<a, b, isEnd, loop_vars>>

EndRun == 
    /\ hasLoop => (loopStarted /\ loop_a = a /\ loop_b = b)
    /\ isEnd' = TRUE 
    /\ UNCHANGED <<a, b, loop_vars>>

StartLoop == 
    /\ loopStarted' = TRUE 
    /\ loop_a' = a 
    /\ loop_b' = b 
    /\ UNCHANGED <<a, b, isEnd>>

Next == 
    \/ ~isEnd /\ Step
    \/ ~isEnd /\ Reset
    \/ isEnd /\ Stutter
    \/ ~isEnd /\ EndRun
    \/ hasLoop /\ StartLoop

EndMeansVariablesAreDifferent ==
    /\ (a >= 20 /\ hasLoop) => (isEnd => (loop_a /= a))

====