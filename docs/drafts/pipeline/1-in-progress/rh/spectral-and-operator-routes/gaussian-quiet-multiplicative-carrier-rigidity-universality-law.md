# Gaussian-quiet multiplicative carrier rigidity universality law

- **ID:** gaussian-quiet-multiplicative-carrier-rigidity-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of Gaussian quiet-crossing coefficient rigidity,
  multiplicative normalization, and entire identity continuation
- **Statement:** Every entire reflection-symmetric multiplicative Dirichlet carrier satisfying
  the all-scale Gaussian quiet budget is identically `1`.  Only half-plane Dirichlet
  representation is required, and no integrality hypothesis is needed.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `quiet_crossing_rigidity_gaussian`
- `ArithmeticFunction.IsMultiplicative.map_one`
- `symmetric_multiplicative_integral_eq_one`
- analytic identity continuation used by the quiet-crossing cocycle kill laws

## Proof

`[PROVED HERE]` Gaussian quiet-crossing rigidity kills every coefficient `a_n` with `n ≥ 2`.
The zero-index L-series term vanishes definitionally, and multiplicativity fixes `a_1 = 1`, so
the series equals `1` throughout its right half-plane of representation.  The entire carrier and
constant function agree on an open subset; the identity principle extends equality to all of
`ℂ`.  No computation is used.

## Strict gain over corpus endpoints

Gaussian quiet-crossing previously concluded only high-coefficient vanishing.  Existing
multiplicative reflection rigidity requires an everywhere-valid L-series representation and
integer-valued coefficients.  Their closure gives a global carrier classification from a
half-plane representation, replacing integrality by the analytic Gaussian quiet budget.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.GaussianQuietMultiplicativeCarrierRigidityUniversalityLaw`
- Main theorem:
  `gaussianQuiet_symmetricMultiplicativeCarrier_eq_one`
- Source:
  `formal/GaloisForLFunctions/RHTower/GaussianQuietMultiplicativeCarrierRigidityUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/GaussianQuietMultiplicativeCarrierRigidityUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
reflection-symmetric entire multiplicative Dirichlet series, quiet height sequences, Gaussian
budgets, and constant-one rigidity found adjacent Hardy-space and multiplier theory for Dirichlet
series and unrelated Gaussian Phragmén--Lindelöf estimates, but no theorem combining this all-scale
quiet budget with half-plane representation and multiplicative global classification.  Closest
inspected primary sources:

- H. Hedenmalm, P. Lindqvist, and K. Seip, *A Hilbert space of Dirichlet series and systems of
  dilated functions in L²(0,1)*, <https://arxiv.org/abs/math/9512211>.
- F. Bayart, A. Defant, L. Frerick, M. Maestre, and P. Sevilla-Peris, *Multipliers of Dirichlet
  series and monomial series expansions of holomorphic functions in infinitely many variables*,
  <https://arxiv.org/abs/1405.7205>.

## Log

- 2026-07-23 — Quiet-crossing terminal cluster exposed Gaussian coefficient rigidity versus
  multiplicative normalization.
- 2026-07-23 — Dependency-closed proof completed.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
