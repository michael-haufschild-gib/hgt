# Pointed Stone prime complete relation-circuit universality law

- **ID:** pointed-stone-prime-complete-relation-circuit-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of pointed Stone sparse-prime realization, coordinate-sign tail
  independence, complete finite-range prime relation ideals, and signed-prime source rigidity
- **Statement:** Every pointed compact metrizable Stone space is homeomorphic to its exact sparse
  recurring prime-pattern chamber.  Every coordinate-independent finite chart has complete affine
  differential-relation classification for every finite-prime-residual tail-linear extension,
  exact pivot basis/rank, and coordinatewise circuit/latent-input hypertranscendence boundaries.

## Goal

Upgrade the corpus's topological Stone-space realization and finite-chart independence theorem to
complete relation-ideal classification for arbitrary tail-linear extensions, while preserving
source rigidity on the same sparse prime coordinates.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: tree source and exact `lake env lean` passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `pointedStoneConstraintHomeomorph`
- `pointedStoneConstraint_sparsePrime_realization`
- `sparseClosedConstraint_tailIndependent_of_coordinateSigns`
- `primeOrientationCoefficientPattern_range_finite`
- `PrimeCoefficientTailPivotPresentation.complete_relationIdeal`
- `PrimeCoefficientTailPivotPresentation.differentialBasis`
- `PrimeCoefficientTailPivotPresentation.differentialBasis_card`
- `signedPrimeSource_finiteDifferentialCircuit_contains_HTAtom`
- `signedPrimeSource_polynomialFirstOrder_law_forces_HT_input`

## Proof

`[PROVED HERE]` For a closed Boolean constraint containing the all-positive pattern, coordinate-sign
linear independence on a finite projection implies tail independence of the corresponding sparse
prime orientations.  Their sign-pattern range is finite.  Hence any family of extra columns whose
displayed pivot residual is supported on finitely many primes completes these coordinates to a
`PrimeCoefficientTailPivotPresentation`.

The tail-pivot master theorem identifies every differential-polynomial relation with the prolonged
affine pivot ideal.  Its basis theorem shows the extra columns do not enlarge the differential
field; its cardinal theorem gives exact rectangular labelled rank.  The prime-supported jet
identity identifies these pivots with the original signed-prime carriers.

Apply this generic finite-chart result to the Nöbeling-coordinate constraint of an arbitrary
pointed light profinite space.  Existing Stone saturation gives both the homeomorphism and exact
recurring-pattern chamber.  Finally apply the two signed-prime source theorems to every coordinate
orientation, yielding finite-circuit hypertranscendental atom extraction and polynomial
first-order latent-input hypertranscendence.

No numerical computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PointedStonePrimeCompleteRelationCircuitUniversalityLaw`
- Main theorem:
  `RHTower.pointedStone_sparsePrime_completeRelationCircuitUniversality`
- Reusable connectors:
  `RHTower.closedConstraintPrimeCoefficientShiftCarrier_primeDirichletSign`,
  `RHTower.closedConstraintPrimeTailPivotPresentation`,
  `RHTower.closedConstraintPrimeTailPivot_completeFiniteExtension`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/PointedStonePrimeCompleteRelationCircuitUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Final axiom audit and module build deferred to final audit.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Stephen G. Simpson, *Symbolic dynamics: entropy = dimension = complexity*
  ([arXiv:1702.04394](https://arxiv.org/abs/1702.04394)), relates subshift entropy, dimension, and
  finite-pattern complexity; it does not realize arbitrary pointed Stone spaces by prime-supported
  differential carriers or classify their complete relation ideals.
- Fryderyk Falniowski, Marcin Kulczycki, Dominik Kwietniak, and Jian Li, *Two results on entropy,
  chaos, and independence in symbolic dynamics*
  ([arXiv:1502.03981](https://arxiv.org/abs/1502.03981)), studies combinatorial independence in
  shift spaces, not differential algebra of sparse Dirichlet carriers.
- Wai Yan Pong, *Applications of differential algebra to algebraic independence of arithmetic
  functions* ([arXiv:1504.03263](https://arxiv.org/abs/1504.03263)), treats algebraic
  independence of arithmetic functions and formal Dirichlet series, but not a Stone-space
  realization with exact finite-extension relation ideals and circuit-source extraction.

Searches combining Stone/profinite realization, symbolic dynamics, sparse prime coefficients,
Dirichlet-series differential algebra, and complete relation ideals found the component subjects
in separate literatures, not the theorem's full topology → recurring prime chamber → affine
relation classification → source-rigidity chain.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Law340's finite-extension classifier exposed a broader compatible tail-independence
  source in the Stone saturation terminal module.
- 2026-07-23 — Generic closed-constraint pivot construction and pointed-Stone specialization
  exact-checked; umbrella import added.
- 2026-07-23 — Post-proof literature audit found symbolic-dynamics and differential-arithmetic
  ingredients separately, not the combined law.
