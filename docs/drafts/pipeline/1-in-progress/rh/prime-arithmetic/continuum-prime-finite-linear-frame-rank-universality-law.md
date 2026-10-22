# Continuum-prime finite linear-frame rank universality law

- **ID:** continuum-prime-finite-linear-frame-rank-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the continuum prime-coherence palette and finite-shadow
  linear-rank classification
- **Statement:** One continuum sparse-prime palette has the property that every injectively
  selected finite coordinate frame, after every finite entrywise-differential-constant linear
  observation, has trivial complete differential relation ideal exactly when the observation
  rows are linearly independent.

## Goal

Convert the infinite relation-free continuum prime family into a coordinate-free finite
observation law. The result must classify every finite rectangular linear frame, not only
invertible square changes and not only one preselected closed-constraint chart.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated cross-tree connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: completed; negative priority result

## Corpus inputs

- `exists_orderPointedContinuumPrimeRelationIdealCircuitUniversality`
- `DifferentialIndependent.comp`
- `differentialIndependent_matrixLinearForms_iff_rowIndependent`
- `differentialIndependent_iff_relationIdeal_eq_bot`

## Proof

**[PROVED HERE]** The prime-coherence relation-ideal circuit theorem supplies an embedding `e`
and proves differential independence, over the finite-prime rational coefficient field, of the
entire family

`F(z,n) = signedPrimeNaturalShiftPalette
  (continuumSparsePrimeOrientation false e z) n`.

Let `coord : n → ((ℕ → Bool) × ℕ)` be any injective finite selection. Differential independence
is stable under injective reindexing, so `F ∘ coord` remains differentially independent.

Let `M : Matrix m n finitePrimeRationalCoefficientField` be arbitrary, with every displayed entry
mapping to a differential constant in the arithmetic-function coordinate field. The exact
finite-shadow rank criterion then gives

`DifferentialIndependent C (matrixLinearForms M (F ∘ coord))`

if and only if the rows of `M` are linearly independent over `C`. Finally,
`differentialIndependent_iff_relationIdeal_eq_bot` replaces differential independence by
equality of the complete differential relation ideal with bottom. All index types and all
rectangular matrices remain universally quantified. No computation is used. ∎

## Strict gain over corpus endpoints

The continuum prime theorem proves infinite differential independence but does not classify
finite linear observations of its coordinates. The finite-shadow theorem classifies a supplied
finite independent family but does not produce an arithmetic continuum palette. Their closure
shows that one coherent prime construction is universal for every finite linear observation:
row rank is the exact and only obstruction to a nontrivial complete differential relation ideal.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ContinuumPrimeFiniteLinearFrameRankUniversalityLaw`
- Main theorem:
  `exists_orderPointedContinuumPrime_finiteLinearFrameRelationRankUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/ContinuumPrimeFiniteLinearFrameRankUniversalityLaw.lean`
- Result: passed warning-free.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after the dependency-closed Lean proof passed. Closest literature found studies
differential-algebraic independence of arithmetic functions and Dirichlet series, plus separate
linear-independence problems for Dirichlet values and exponents. No source located gives the exact
continuum sparse-prime palette with the universal finite rectangular relation-ideal/bare row-rank
classification. This is a negative search result, not a priority claim.

## Log

- 2026-07-23 — terminal-pair scan exposed the common differential relation-ideal interface.
- 2026-07-23 — full theorem reads revealed a stronger finite rectangular-frame law than the
  square covariance endpoint suggested.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — Lean source passed the required exact-file check warning-free and was wired into
  `GaloisForLFunctions/RHTower.lean`.
- 2026-07-23 — post-proof literature audit found arithmetic-function differential-independence
  results, but not the exact continuum-prime finite-frame relation-rank theorem.
