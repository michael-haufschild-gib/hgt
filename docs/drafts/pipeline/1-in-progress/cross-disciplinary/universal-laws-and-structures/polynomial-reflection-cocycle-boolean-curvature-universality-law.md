# Polynomial-reflection-cocycle Boolean-curvature universality law

- **ID:** polynomial-reflection-cocycle-boolean-curvature-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of polynomial-exponent reflection rigidity and Prouhet
  alternating annihilation
- **Statement:** Every polynomial-exponent reflection cocycle satisfying the corpus reflection
  and vertical-growth hypotheses is continuously curvature-flat and has zero translated Boolean
  logarithmic curvature at every interaction depth at least two, for arbitrary complex basepoint
  and arbitrary edge weights.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `cocycle_exponent_rigidity`
- `cocycle_exponent_curvature_zero`
- `prouhet_alternating_annihilation`
- `Polynomial.natDegree_comp`
- `Polynomial.natDegree_X_add_C`

## Proof

`[PROVED HERE]` Reflection symmetry plus the vertical logarithmic-growth bound gives
`natDegree P ≤ 1` by `cocycle_exponent_rigidity`; the same hypotheses already give vanishing
continuous logarithmic curvature.  Fix a Boolean interaction depth `n ≥ 2`, basepoint `b`, and
edge weights `w`.  Translate the exponent to
`Q(X) = P(X + b)`.  Translation preserves polynomial degree, so
`natDegree Q = natDegree P ≤ 1 < n`.  Prouhet alternating annihilation applied to `Q` gives

`∑_{S ⊆ {0,…,n-1}} (-1)^|S| P(b + ∑_{i∈S} w_i) = 0`.

Exponentiating this zero gives unit multiplicative holonomy.  Since `n`, `b`, and `w` were
arbitrary, every higher Boolean logarithmic curvature vanishes.  No computation is used.

## Strict gain over corpus endpoints

The cocycle endpoint proves only ordinary differential curvature flatness.  The Prouhet endpoint
annihilates an arbitrary polynomial when an external degree bound is supplied.  Their closure
shows that reflection and growth hypotheses alone force simultaneous continuous flatness and
all-depth translated Boolean flatness, with no remaining degree assumption in the conclusion.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PolynomialReflectionCocycleBooleanCurvatureUniversalityLaw`
- Main theorem:
  `polynomialExponentReflectionCocycle_completeCurvatureFlatness`
- Source:
  `formal/GaloisForLFunctions/RHTower/PolynomialReflectionCocycleBooleanCurvatureUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/PolynomialReflectionCocycleBooleanCurvatureUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
polynomial reflection cocycles, conductor curvature, higher finite differences, Boolean
curvature, and Prouhet annihilation found no exact collision.  Closest inspected primary sources
treat the two mechanisms separately:

- J. Byszewski and M. Ulas, *Some identities involving Prouhet-Thue-Morse sequence and its
  relatives*, <https://arxiv.org/abs/1409.8118>, develops translated Prouhet--Thue--Morse
  polynomial sums but has no reflection-cocycle growth hypothesis or continuous/discrete
  curvature conclusion.
- W. Galleas and J. Lamers, *Reflection algebra and functional equations*,
  <https://arxiv.org/abs/1405.4281>, derives reflection-algebra functional equations but does not
  classify scalar polynomial exponents or connect them to all-depth Prouhet annihilation.
- J. M. Maillet and G. Niccoli, *On Separation of Variables for Reflection Algebras*,
  <https://arxiv.org/abs/1904.00852>, studies finite-difference spectral equations for reflection
  algebras, not Boolean finite differences of conductor-type scalar cocycles.

## Log

- 2026-07-23 — Exact-identifier terminal scan exposed the Prouhet/cocycle-rigidity closure.
- 2026-07-23 — Dependency-closed proof completed from existing Lean endpoints.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
