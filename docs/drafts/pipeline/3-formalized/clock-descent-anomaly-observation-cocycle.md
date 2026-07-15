# Clock-descent anomaly observation cocycle

- **ID:** clock-descent-anomaly-observation-cocycle
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / PHYSICS BRIDGE / GENERAL HTGEOMETRY
- **Source:** anomaly consistency conditions and compositional observer maps
- **Statement:** The clock-descent anomaly of a composite observation is the sum of the pulled-back downstream anomaly and the pushed-forward upstream anomaly; faithful stages make composite consistency equivalent to the remaining local consistency condition.

## Goal

Turn the physics principle that anomalies are compositional consistency defects into a reusable
theorem for the existing clock-observation formalism.  The result must simplify multi-stage
observable arguments rather than merely rename linear-map algebra.

## Gates

- [x] 0 → 1 in-progress: isolated an exact two-stage anomaly law and concrete discharge corollaries
- [x] 1 → 2 fully-proven: proved the cocycle identity, one-stage reductions, faithful-stage equivalences, and a finite Tate-clock consumer
- [x] 2 → 3 formalized: scratch certification, one exact-module build for the missing cache target, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: instantiate a nontrivial analytic observer chain in a hypertranscendental function or `RHTower` model

## Physics sources

- R. Brunetti, M. Dütsch, K. Fredenhagen, and K. Rejzner, *Unitary, anomalous Master Ward Identity and its connections to the Wess-Zumino condition, BV formalism and L-infinity algebras*, arXiv:2210.05908, treats anomalies through a cocycle condition tied to Wess--Zumino consistency.
- R. Brunetti, K. Fredenhagen, and R. Verch, *The generally covariant locality principle -- A new paradigm for local quantum physics*, arXiv:math-ph/0112041, makes covariant maps between observable algebras primary data of locally covariant QFT.

The Lean theorem is a transfer of the compositional consistency principle to the project's linear
clock-descent interface.  It is not claimed to be a theorem proved by either physics paper, nor a
novel physics anomaly classification.

## Exact relation

For source constraint `S`, intermediate shadow `T`, final shadow `R`, and observations
`f : V → O` and `g : O → W`, write

```text
A(S,f,T) = T ∘ f - f ∘ S.
```

Then direct cancellation gives the cocycle law

```text
A(S,g ∘ f,R) = A(T,g,R) ∘ f + g ∘ A(S,f,T).             (1)
```

Equation `(1)` says that the composite comparison has no third, independently chosen defect.
Two faithful-stage consequences make the identity operational:

```text
A(S,f,T)=0 and f onto
  implies  A(S,g∘f,R)=0 iff A(T,g,R)=0;                   (2)

A(T,g,R)=0 and g one-to-one
  implies  A(S,g∘f,R)=0 iff A(S,f,T)=0.                   (3)
```

Thus a global composite consistency hypothesis can discharge a local consistency hypothesis.
The maps are between observable structures; no parameter is interpreted as temporal evolution.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/ClockDescentAnomalyCocycle.lean` proves:

- `clockDescentAnomaly_comp_observation`;
- `clockDescentAnomaly_comp_of_upstream_eq_zero`;
- `clockDescentAnomaly_comp_of_downstream_eq_zero`;
- `clockDescentAnomaly_comp_eq_zero_iff_downstream_of_surjective`;
- `clockDescentAnomaly_comp_eq_zero_iff_upstream_of_injective`;
- `tateClockFiniteObservation_surjective`;
- `tateClockPostObservationAnomaly_eq_zero_iff`.

## Direct corpus application

The finite Tate-clock observation onto a coordinate window is proved surjective.  Consequently,
after an exact source-to-window comparison, exactness of any composite post-observation is
equivalent to exactness of the post-observation itself.  This specializes `(2)` to the existing
general hypertranscendental clock packet and removes a downstream zero-anomaly premise whenever
the corresponding composite premise is already available.

No `RHTower` wrapper is added: the current `RHTower` tree has no concrete use of
`clockDescentAnomaly`, so a specialization there would add no theorem strength.  The reusable
general interface is ready for the first genuine analytic consumer.

## Corpus value

The cocycle theorem consolidates two-stage anomaly expansions, prevents treating local and global
anomalies as independent hypotheses, and supplies exact surjective/injective rewrites.  Its Tate
consumer applies immediately to finite clock windows for arbitrary hypertranscendental functions,
not only zeta.  The result strengthens observational infrastructure but does not by itself produce
an RH source term or close an RH route.

## Status

[PROVED IN LEAN] The exact target and direct source checks pass.  The key declarations depend only
on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  The exact target build
rebuilt the stale direct dependency and the new module only; no full project build, numerical
experiment, or concurrent Lean process was run.
