### Apalache For Liveness
This repository contains experiments and notes
about using encodings to allow Apalache to
handle liveness properties.

## Background information

Some information can be found in [the PDR on temporal encodings][]

## Approaches

There are broadly two approaches for
checking temporal properties with Apalache:
1. Using trace invariants
2. Using encodings with extra propositional variables

These approaches will be explained on a spec that models a
[termination detection algorithm](playground/EWD/EWD998.tla)

## Using trace invariants

There are two variants of the specification with trace invariants.
One with an extra variable that indicates whether the loop has started,
and one where the start index of the loop is determined by quantification
over indices.

### [Trace invariant with loop indicator variable](playground/EWD/EWD998_trace.tla)

Here, an extra variable is added to the state:
```
 \* @type: Bool;
 InLoop
```
When `InLoop` is true, this indicates that the current state is on the loop.
The variable is initialized like this:

```
AuxInit ==
  /\ InLoop \in {TRUE, FALSE}
```

It is manipulated like this in the `Next` predicate:

```
AuxNext ==
  InLoop' \in {TRUE, FALSE} /\ (InLoop' = FALSE => InLoop = FALSE)
```

Notably, there is a logically equivalent, yet
much slower way to adjust the variable:
```
AuxNext == (* much slower *)
    \/  /\ ~InLoop  
        /\ InLoop' \in {TRUE, FALSE}
    \/  InLoop' = InLoop
```
The fast way results in no extra transitions; the slow way doubles the number of transitions of the system.
This is a general trick; instead of control nondeterminism
(logical disjunction or IF-THEN-ELSE constructs),
data nondeterminism paired with constraints on the variable produces fewer transitions.

In this concrete example, exploring the state space to depth 7 took ~10 minutes for the fast version, and >2 hours for the slow version.

### [Trace invariant with buchi automata](playground/EWD/EWD998_buchi.tla)

In this variant, one does not need trace invariants.
Instead, to describe the loop, we have an extra copy of all state variables:

```
(* loop variables *)
  \* @type: Int -> Bool;
  loop_active,     
  \* @type: Int -> Str;
  loop_color,      
  \* @type: Int -> Int;
  loop_counter,    
  \* @type: Int -> Int;
  loop_pending,    
  \* @type: [pos: Int, q: Int, color: Str];
  loop_token,       

...

vars == <<active, color, counter, pending, token>>
loop_vars == <<loop_active, loop_color, loop_counter, loop_pending, loop_token>>
```

We also have a variable to determine whether the loop has started:

```
\* @type: Bool;
  InLoop,
```

These variables are manipulated like this:
```
AuxInit ==
  /\ InLoop \in {TRUE, FALSE}
  /\ loop_vars = vars
  ...
```

```
LoopNext ==
  /\ InLoop' \in {TRUE, FALSE}
  /\ loop_vars' \in {loop_vars, vars'}
  /\ loop_buchi_state' \in {loop_buchi_state, buchi_state'}
  /\ (~InLoop /\ InLoop') => (loop_vars' = vars' /\ loop_buchi_state' = buchi_state')
  /\ (InLoop = InLoop') => (loop_vars' = loop_vars /\ loop_buchi_state' = loop_buchi_state)
  /\ (InLoop) => (InLoop')
```

Note the variable `loop_buchi_state`, which already hints at the next part of the spec.
We have a Buchi automaton encoded in the state machine:
```
BuchiNext ==
  /\ buchi_state' \in {0,1,-1}
  /\ (buchi_state' = 1) =>  \/ (buchi_state = 0 /\ Termination /\ ~terminationDetected)
                            \/ (buchi_state = 1 /\ ~terminationDetected)
  /\ (buchi_state' = 0) => (buchi_state = 0)
```

This Buchi automaton encodes the negation of the property we want to check.
Note this is also a pattern that avoids control nondeterminism and
replaces it by data nondeterminism.
Here, the property was

```
Liveness ==
  [](Termination => <>terminationDetected)
```

Translation can be done e.g. via [Spot's online LTL toolset](https://spot.lrde.epita.fr/app/).
The Buchi automaton for the property looks like this:

![Buchi automaton for the negation of `[](Termination => <>terminationDetected)`](BuchiAutomaton.png)

Now, consider the accepting states of the Buchi automaton.
They are states that we should not see on the loop.
Recall that the automaton encodes the negation of the desired property,
and seeing an accepting state on the loop would thus mean
*not* satisfying the property.

Thus, we have an extra variable

```
\* @type: Bool;
  buchi_acceptingSeen
```

which is manipulated like this:

```
AuxInit ==
  ...
  /\ buchi_acceptingSeen := (InLoop /\ buchi_state = 1)
```
```
AuxNext ==
  ...
  buchi_acceptingSeen' := 
    \/ buchi_acceptingSeen 
    \//\ InLoop'
      /\ buchi_state' = 1
```
Recall that state 1 is the accepting state of the Buchi automaton.

One problem remains with this: We detect whether the system properly encodes a loop as follows:
1) When we choose to set `InLoop` to true,
we record the current state variables and the current state of the Buchi automaton
1) The state variables and Buchi automaton state at the start of the loop should be the same at the end of the loop.

There is one issue with this when the start of the loop is also the end of the loop, e.g. the loop has length 0.
This is completely valid, and it represents the system stuttering indefinitely (if this is not
desired, one can encode a condition like fairness to prohibit stuttering).
However, note that in this case, not only does the original system stutter indefinitely,
but the Buchi automaton also stutters indefinitely, which is not possible.
Note e.g. the example automaton above, which can only
remain in state 1 as long as `~terminationDetected` holds.
To fix this issue, we allow the system to stutter *without* the Buchi automaton stuttering at the same time.
Note that the converse should not be possible, i.e.
we should not explicitly allow the Buchi automaton to stutter while the system moves.
We adjust the next relation like this:
```
Next ==
  (OriginalNext) \/ (UNCHANGED << allButBuchiVars >> /\ BuchiNext)
```

Finally, we need to ensure that any loop we detect
has at least two states, since a loop with a single state implicitly lets the Buchi state stutter.
We can add an additional auxiliary variable to detect this which is set to true one step after the loop has started.

### Tableau encoding

The tableau encoding is explained in Section 3.2 of [linear encodings of bounded ltl][].

There is one major subtlety. The paper assumes that loops need at least one transition, since they don't consider implicit stuttering.
We can do the same by, similar to the last section, allowing stuttering explicitly, at the cost of adding an extra transition.

### To be continued...

[the PDR on temporal encodings]: 017pdr-temporal.md
[linear encodings of bounded ltl]: https://lmcs.episciences.org/2236