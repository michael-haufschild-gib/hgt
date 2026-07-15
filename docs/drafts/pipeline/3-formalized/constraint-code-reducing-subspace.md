# Constraint-code reducing subspace

- **ID:** constraint-code-reducing-subspace
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / PHYSICS BRIDGE / HYPOTHESIS DISCHARGE
- **Source:** quantum error correction, decoherence-free subspaces, and adjoint leakage blocks
- **Statement:** For a self-adjoint code compression, no departure through `A` is equivalent to no return through `A†`; consequently one leakage premise kills the compressed constraint sandwich `P A† C A P`, and self-adjointness of `C` removes one constraint-annihilation premise as well.

## Goal

Strengthen the full constraint-ideal excursion theorem using the adjoint structure already present
in Hilbert-space clock and code models.  The deliverable is a genuine premise reduction, not a
renaming of the complement-block factorization.

## Gates

- [x] 0 → 1 in-progress: identified paired departure/return and left/right annihilation premises in the existing excursion API
- [x] 1 → 2 fully-proven: proved adjoint leakage pairing, self-adjoint reducing-subspace equivalence, and two sandwich consumers
- [x] 2 → 3 formalized: scratch certification, one exact-module build for the missing cache target, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: instantiate the discharge in a concrete analytic clock-code compression or Sonin operator sandwich

## Physics sources

- D. W. Kribs, R. Laflamme, D. Poulin, and M. Lesosky, *Operator quantum error correction*, arXiv:quant-ph/0504189, unifies subspace codes, decoherence-free subspaces, and noiseless subsystems in an operator framework.
- M. A. Nielsen and D. Poulin, *Algebraic and information-theoretic conditions for operator quantum error-correction*, arXiv:quant-ph/0506069, develops algebraic conditions characterizing operator quantum error correction.

The Lean result is the elementary Hilbert-space block identity needed by this corpus.  It is not
claimed as a novel QEC theorem or as a result proved verbatim in those papers.

## Exact relation

Let `P` be self-adjoint.  Taking adjoints identifies the paired off-diagonal blocks:

```text
(1-P) A P = 0  iff  P A† (1-P) = 0.                       (1)
```

If `A=A†`, equation `(1)` becomes equivalence of no departure and no return.  If in addition
`P²=P`, the two conditions are equivalent to the reducing-subspace relation

```text
P A = A P.                                                (2)
```

Similarly, for self-adjoint `P` and `C`,

```text
P C = 0  iff  C P = 0.                                   (3)
```

The existing excursion identity factors

```text
P (L C R) P = (P L (1-P)) C ((1-P) R P).
```

Putting `L=A†`, `R=A`, and using `(1)` gives

```text
P C = C P = 0, (1-P) A P = 0
  implies P (A† C A) P = 0.                               (4)
```

When `C=C†`, equation `(3)` removes `C P=0` from the premises of `(4)`.  Thus the strongest
consumer needs only self-adjointness of `P,C`, the one-sided constraint relation `P C=0`, and one
no-departure condition.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/ConstraintCodeReducingSubspace.lean` proves:

- `selfAdjointCompression_noDeparture_iff_adjoint_noReturn`;
- `selfAdjointCompression_noDeparture_iff_noReturn`;
- `selfAdjointCompression_mul_eq_zero_iff_mul_selfAdjoint`;
- `orthogonalProjection_noDeparture_iff_commutes_selfAdjoint`;
- `constraintAdjointSandwich_compression_eq_zero_of_noDeparture`;
- `selfAdjointConstraint_adjointSandwich_compression_eq_zero_of_noDeparture`.

## Direct corpus application

The last two declarations consume
`constraintSandwich_compression_eq_zero_of_noReturn` from
`formal/GaloisForLFunctions/HTGeometry/ConstraintIdealExcursion.lean`.  They replace its explicit
no-return premise with the physically natural one-sided preservation condition on `A`.  For a
self-adjoint constraint they also derive the missing right-annihilation hypothesis automatically.

This is a general `HTGeometry` strengthening.  It applies to arbitrary bounded Hilbert-space
constraint codes and hypertranscendental clock models; no zeta or `RHTower` assumption occurs.

## Corpus value

The result halves leakage bookkeeping for self-adjoint observables, converts invariance into the
commutation form used elsewhere in the clock corpus, and supplies a one-sided Kraus-sandwich
vanishing theorem.  It makes the corrected full-ideal excursion surface easier to use in actual
models while preserving its noncommutative boundary.  It does not itself produce an RH source.

## Status

[PROVED IN LEAN] The exact target and direct source checks pass.  The key declarations depend only
on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  The exact target build
replayed one cached module and rebuilt two direct dependencies plus the new target; no full project
build, numerical experiment, or concurrent Lean process was run.
