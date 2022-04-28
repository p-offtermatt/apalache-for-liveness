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

### To be continued...

[the PDR on temporal encodings]: 017pdr-temporal.md