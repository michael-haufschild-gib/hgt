# Finite-clock orthogonal observability

- **ID:** finite-clock-orthogonal-observability
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HTGEOMETRY BRIDGE
- **Source:** finite-group averaging and constrained quantum observability
- **Statement:** For every finite-period isometric clock and every stationary state, the expectation of the clock-twirl Kadison defect is exactly the squared norm of the observable component erased by the clock; it vanishes exactly when the observable value is physical, equivalently when its clock commutator vanishes on that state.

## Goal

Turn the finite-clock twirl from an operator-level averaging construction into an exact theorem about
observable values.  The result is general `HTGeometry`: it does not mention zeta, the Riemann tower,
or a Hamiltonian.  It supplies positivity and discharges an existing `PhysicalState` hypothesis from
a scalar equality which later clock and constraint consumers can test directly.

## Gates

- [x] 0 → 1 in-progress: exact finite-clock value relation located
- [x] 1 → 2 fully-proven: Hilbert projection and self-adjointness proof complete
- [x] 2 → 3 formalized: exact-module build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: integrate with the general HT clock-observable theory

## Physics source

- A. K. Hashagen, S. T. Flammia, D. Gross, and J. J. Wallman, *Real Randomized Benchmarking*, arXiv:1801.06121, records the standard finite-group twirl as the Hilbert--Schmidt orthogonal projection onto the commutant.
- A. R. H. Smith, M. P. E. Lock, and P. A. Höhn, *Equivalence of approaches to relational quantum dynamics in relativistic settings*, arXiv:1912.00033, treats physical observables as relational and conditional on a clock within a constrained theory.
- A.-C. de la Hamette, T. D. Galley, P. A. Höhn, L. Loveridge, and M. P. Müller, *Perspective-neutral approach to quantum frame covariance for general symmetry groups*, arXiv:2110.13824, emphasizes that a reference frame resolves only properties invariant under its isotropy group.

The exact norm identity below is the formalized transfer into this corpus; it is not claimed as a
quotation from those papers.

## Exact relation

For a clock `U` with `U†U=1` and `U^N=1`, let `P_N` be its finite gauge average on states and
`Phi_N` its conjugation twirl on observables.  For self-adjoint `X` and a stationary state
`U psi=psi`, define

```text
D_N(X) = Phi_N(X^2) - Phi_N(X)^2.
```

Then

```text
Re <psi,D_N(X) psi> = ||(1-P_N)X psi||^2,
||Phi_N(X) psi||^2 + Re <psi,D_N(X) psi> = ||X psi||^2.
```

Consequently the defect expectation is nonnegative and the following are equivalent:

```text
Re <psi,D_N(X) psi> = 0,
Phi_N(X) psi = X psi,
(U-1)(X psi) = 0,
(UX-XU) psi = 0.
```

Thus the defect is the exact energy of the part of an observable value which the clock cannot
observe.  The theorem concerns the stationary observable structure of a clock, not temporal
evolution.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteClockOrthogonalObservability.lean` proves:

- self-adjointness and orthogonal energy partition for the finite gauge average;
- preservation of self-adjointness by the observable twirl;
- `re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq`;
- `finiteClock_observableValue_energy_partition`;
- `re_inner_finiteCyclicObservableTwirlKadisonDefect_nonneg`;
- exact zero criteria via the retained value, `PhysicalState`, and the clock commutator.

## Corpus value

The zero-defect theorem replaces a previously independent `PhysicalState (U-1) (X psi)` premise by
an exact scalar condition.  `MultiClockMasterObservability.lean` uses it to discharge a whole finite
family of such premises and connect the resulting zero set to the existing master constraint.

## Status

[PROVED IN LEAN] The exact-module cache build and touched-file check pass.  The main exports depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  No full project build,
numerical experiment, or concurrent Lean process was run.
