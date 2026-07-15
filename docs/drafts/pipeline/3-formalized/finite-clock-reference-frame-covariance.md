# Finite clock reference-frame covariance

- **ID:** finite-clock-reference-frame-covariance
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN
- **Source:** physics-first bridge from relational quantum reference-frame changes
- **Statement:** Simultaneous two-sided conjugation of a finite clock and an observable preserves the clock period and commutant condition, and conjugates both the observable twirl and its complete conditional-variance defect.

## Goal

Make finite-clock observability independent of the chosen invertible presentation of the clock.
The theorem applies to the general `HTGeometry` observer structure and introduces no zeta-specific
data.  It prevents later consumers from having to re-prove clock-frame invariance and rules out
frame-dependent vanishing tests for the observability defect.

## Gates

- [x] 0 → 1 in-progress: exact identity and corpus consumer located
- [x] 1 → 2 fully-proven: complete algebraic proof, no open dependency
- [x] 2 → 3 formalized: isolated Lean module check and axiom audit
- [ ] 3 → 4 publication-ready: integrate with a clock-switching or superspace application

## Physics source

- P. A. Höhn and A. Vanrietvelde, *How to switch between relational quantum clocks*, New J. Phys. 22 (2020) 123048, arXiv:1810.04153.  Relational quantum clock changes are implemented through a clock-neutral constrained theory.
- T. Thiemann, *(Quantum) reference frames, relational observables, gauge reduction and physical interpretation*, arXiv:2603.04072.  When a reference-frame transformation is unitarily implementable, relational observables transform covariantly; this does not imply that the physical Hamiltonians associated with different clocks are simple pullbacks of one another.

The transfer to the finite-clock twirl and its Kadison defect is an exact algebraic inference from
these covariance principles, not a claim stated verbatim in either physics source.

## Exact relation

Let `V,W` be inverse frame maps, so `WV=VW=1`, and write `C(A)=VAW`.  Then

`C(A)C(B)=C(AB)` and `C(U)^n=C(U^n)`.

Consequently, for every finite cyclic clock twirl `Φ_N`,

`Φ_{C(U),N}(C(X)) = C(Φ_{U,N}(X))`.

The clock period and observable algebra transform exactly:

`U^N=1 ⇒ C(U)^N=1`,

`C(U)C(X)=C(X)C(U) ⇔ UX=XU`.

For the complete conditional-variance defect

`D_{U,N}(X)=Φ_{U,N}(X²)-Φ_{U,N}(X)²`,

one therefore has

`D_{C(U),N}(C(X)) = C(D_{U,N}(X))`.

Thus defect vanishing and membership in the observable commutant are properties of the clock's
observability structure, not artifacts of its chosen invertible frame.  No temporal parameter,
Hamiltonian evolution, or equality of different physical Hamiltonians is asserted.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteClockReferenceFrameCovariance.lean` proves:

- `twoSidedConjugation_mul` and `twoSidedConjugation_eq_iff`;
- `twoSidedConjugation_pow` and `twoSidedConjugation_period`;
- `finiteCyclicObservableTwirlNumerator_twoSidedConjugation`;
- `finiteCyclicObservableTwirl_twoSidedConjugation`;
- `twoSidedConjugation_commutes_iff`;
- `finiteCyclicObservableTwirlKadisonDefect_twoSidedConjugation`.

Only the inverse identities are needed; the result is therefore algebraically stronger than a
unitary-only statement while remaining applicable to unitary quantum reference-frame changes.

## Status

[PROVED IN LEAN] The exact-module cache build and direct source check pass.  The exported theorem
audit reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  No full
project build, numerical experiment, or concurrent Lean process was run.
