# Constraint-code compression

- **ID:** constraint-code-compression
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HTGEOMETRY BRIDGE
- **Source:** constrained observable algebras and quantum code-subspace compression
- **Statement:** Every outer constraint term `C L + R C` vanishes after compression to a subspace annihilated by `C` on both sides, while a genuine ideal sandwich `L C R` has an exact complement-sector excursion formula.

## Goal

Identify exactly which constraint representatives are invisible after physical compression, at the
operator level rather than only after choosing physical bra and ket vectors, and locate the
obstruction for the full noncommutative two-sided ideal.  This is a general `HTGeometry` result.
The logarithmic Sonin clock is one downstream `RHTower` consumer.

## Gates

- [x] 0 → 1 in-progress: an existing physical-matrix-element theorem and its avoidable self-adjointness hypothesis were isolated
- [x] 1 → 2 fully-proven: outer constraint compression, finite-clock annihilation, and the full-sandwich excursion correction proved
- [x] 2 → 3 formalized: exact-module builds, direct source checks, and axiom audits pass
- [ ] 3 → 4 publication-ready: identify the maximal constraint quotient represented faithfully by a concrete physical compression

## Physics source

- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, arXiv:quant-ph/9604034, characterizes correctable information through the action of operators after restriction to a code subspace.
- C. Bény, A. Kempf, and D. W. Kribs, *Generalization of quantum error correction via the Heisenberg picture*, arXiv:0705.1574, formulates protected information as an observable algebra under compression to a code sector.

The theorems below transfer the code-subspace compression principle to static constraint
relations.  They are not a claim that clock averaging implements a dynamical error-correction
protocol.

## Exact relation

Let `P`, `C`, `A`, `B`, `L`, and `R` be operators.  If

```text
P C = 0,    C P = 0,
B = A + C L + R C,
```

then

```text
P B P = P A P.                                             (1)
```

For a finite-period clock `U`, its cyclic average `P_U` satisfies both annihilation laws by the
left and right geometric telescopes:

```text
P_U (U-1) = 0,    (U-1) P_U = 0.                          (2)
```

Consequently `(1)` applies to every relation with `U-1` at the outer left or right edge.  If `U` is
also an isometry, the cyclic average is self-adjoint, so arbitrary unprojected input vectors
`phi, psi` satisfy

```text
<P_U phi, B P_U psi> = <P_U phi, A P_U psi>.               (3)
```

Unlike the earlier generic Ward-style matrix-element result, `(3)` does not assume that `U-1` is
self-adjoint.

The outer relation in `(1)` is not the full two-sided ideal in a noncommutative operator algebra.
For a genuine sandwich, the exact surviving term is

```text
P (L C R) P
  = (P L (1-P)) C ((1-P) R P).                            (4)
```

Thus a full ideal sandwich vanishes if the return transition `P L (1-P)`, the departure transition
`(1-P) R P`, or the complement compression `(1-P) C (1-P)` vanishes.  Without one of these
conditions, physical compression does not define a representation of the full constraint quotient.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/ConstraintCodeCompression.lean` proves:

- `constraintTwoSidedIdeal_compression_eq_zero`;
- `compression_congr_mod_constraintTwoSidedIdeal`;
- both finite-clock annihilation laws;
- `finiteCyclicGaugeAverage_compression_congr_mod_constraintTwoSidedIdeal`;
- `finiteClock_matrixElement_congr_mod_constraintTwoSidedIdeal`.

The historical declaration names retain `TwoSidedIdeal` for compatibility; their statements cover
the outer relation `C L + R C`, not arbitrary sandwiches.

`formal/GaloisForLFunctions/HTGeometry/ConstraintIdealExcursion.lean` proves:

- `constraint_eq_complement_compression`;
- both complement and transition forms of `(4)`;
- vanishing under no-return, no-departure, or complement-constraint hypotheses.

`formal/GaloisForLFunctions/RHTower/SoninLogConstraintCompression.lean` applies the result to the
involutive logarithmic Fourier-scattering clock, proving equality of compressed Sonin operators
and of invariant-sector matrix elements for outer-equivalent observables, and the exact surviving
excursion formula for a full Sonin constraint sandwich.

## Corpus value

The result discharges a self-adjointness hypothesis from finite-clock representative-independence,
strengthens equality of selected values to equality of compressed operators, and prevents an
incorrect promotion from the outer constraint relation to the full two-sided ideal.  Formula `(4)`
isolates the additional off-sector transition hypotheses needed for a true observable quotient.
The Sonin specialization verifies both the positive result and its exact boundary in `RHTower`.

## Status

[PROVED IN LEAN] The exact-module cache builds and touched-file checks pass.  The general exports
and all Sonin exports use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
axioms.  No full project build, numerical experiment, or concurrent Lean process was run.
