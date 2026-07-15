# Multi-clock master observability

- **ID:** multi-clock-master-observability
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HTGEOMETRY BRIDGE
- **Source:** constrained quantum systems, superspace, and the master-constraint programme
- **Statement:** For any finite family of periodic isometric clocks, with no pairwise commutativity assumption, total erased observable energy vanishes exactly when the observable value lies in the kernel of the existing finite quantum master constraint.

## Goal

Connect clock observability to the corpus's multi-constraint geometry and discharge its joint
`PhysicalState` hypothesis from one nonnegative scalar equality.  The result models a static
superspace-type constraint surface: the clocks select jointly observable values, but do not define
a temporal flow.

## Gates

- [x] 0 → 1 in-progress: noncommuting multi-clock target and existing master constraint identified
- [x] 1 → 2 fully-proven: finite nonnegative-sum and kernel equivalence proved
- [x] 2 → 3 formalized: exact-module build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: apply to a concrete multi-clock HT or superspace model

## Physics source

- T. Thiemann, *The Phoenix Project: Master Constraint Programme for Loop Quantum Gravity*, arXiv:gr-qc/0305080, combines a family of constraints into one positive master constraint whose kernel is the physical state space.
- B. Dittrich and T. Thiemann, *Testing the Master Constraint Programme for Loop Quantum Gravity I. General Framework*, arXiv:gr-qc/0411138, develops the equivalence between the joint constraint surface and the master constraint.
- J. Zelezny, *Quantum reference frames and their symmetries*, arXiv:2109.01912, gives perspective-neutral constrained systems with two noncommuting constraints.

The new corpus relation is the identification of its finite-clock conditional-variance energy with
the existing finite master-constraint kernel; it is not asserted verbatim by these sources.

## Exact relation

For each clock `i`, let `U_i` be isometric, have nonzero finite period `N_i`, and fix `psi`.  For a
self-adjoint observable `X`, define

```text
E_i(X,psi) = Re <psi,(Phi_i(X^2)-Phi_i(X)^2) psi>,
E(X,psi)   = sum_i E_i(X,psi).
```

Then

```text
E(X,psi) = sum_i ||(1-P_i)X psi||^2 >= 0.
```

No relation between `U_i` and `U_j` is required.  Moreover,

```text
E(X,psi)=0
iff for every i, (U_i-1)(X psi)=0
iff M(X psi)=0,
```

where

```text
M = sum_i (U_i-1)†(U_i-1)
```

is the corpus's finite quantum master constraint.  Therefore one zero-energy hypothesis also
discharges the premise of its Ward-value theorem:

```text
<X psi, M(A(X psi))> = 0.
```

This is an observability intersection theorem, not an evolution equation.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/MultiClockMasterObservability.lean` introduces the two energy
definitions and proves:

- the erased-norm-square formula and nonnegativity for one clock and a finite family;
- `finiteClockFamilyObservabilityEnergy_eq_zero_iff_forall_physical`;
- `finiteClockFamilyObservabilityEnergy_eq_zero_iff_masterPhysical`;
- `finiteClockFamily_zeroEnergy_WardValue_eq_zero`.

## Corpus value

The module is a direct consumer of the general finite-clock theorem and a direct producer for the
existing master-constraint and Ward-value APIs.  It converts a family of operator-kernel premises
into one scalar zero condition while allowing noncommuting constraints, which is the useful form
for superspace and quantum-reference-frame applications.

## Status

[PROVED IN LEAN] The exact-module cache build and touched-file check pass.  The two main exports
depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  No full
project build, numerical experiment, or concurrent Lean process was run.
