# Gaussian-quiet cocycle-cancellation inverse-rigidity universality law

- **ID:** gaussian-quiet-cocycle-cancellation-inverse-rigidity-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `reflCocycle_mul`,
  `reflCocycle_eq_one_iff`,
  `ArithmeticFunction.IsMultiplicative.mul`,
  `ArithmeticFunction.LSeries_mul'`,
  `ArithmeticFunction.LSeriesSummable_mul`, and
  `gaussianQuiet_symmetricMultiplicativeCarrier_eq_one`
- **Statement:** Two entire multiplicative Dirichlet carriers whose intrinsic reflection
  cocycles cancel pointwise and whose product obeys the all-scale Gaussian quiet budget are
  pointwise inverses on the whole complex plane.

## Goal

Convert cancellation in the computed reflection-cocycle group into an exact global inverse law
by applying Gaussian quiet rigidity to the Dirichlet-convolution product carrier.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `reflCocycle_mul`
- `reflCocycle_eq_one_iff`
- `ArithmeticFunction.IsMultiplicative.mul`
- `ArithmeticFunction.LSeries_mul'`
- `ArithmeticFunction.LSeriesSummable_mul`
- `gaussianQuiet_symmetricMultiplicativeCarrier_eq_one`

## Proof

**[PROVED HERE]** Let `F` and `G` be entire carriers represented in the same closed right
half-plane by the L-series of multiplicative arithmetic functions `a` and `b`. Put
`C(s) = F(s)G(s)`.

Dirichlet convolution preserves multiplicativity, so `a * b` is multiplicative. Absolute
summability of the two L-series at the common boundary implies summability of the convolution
L-series there. At every point in the right half-plane, summability propagates from the boundary
and the convolution product theorem gives

`C(s) = L(a,s)L(b,s) = L(a * b,s)`.

The carrier product is entire. Multiplicativity of the intrinsic reflection cocycle and the
pointwise cancellation hypothesis give

`reflCocycle C(s) = reflCocycle F(s) reflCocycle G(s) = 1`.

The exact kernel theorem for the totalized cocycle then simultaneously proves that `C(s)` is
nonzero and that `C(1-s) = C(s)`. Hence `C` is reflection-symmetric without any separately
assumed nonvanishing condition.

The stated all-scale Gaussian quiet budget is exactly the budget for `C`. Gaussian-quiet
multiplicative carrier rigidity therefore yields `C(s) = 1` for every complex `s`, i.e.

`F(s)G(s) = 1`

globally. No computation is used. ∎

## Strict gain over corpus endpoints

The reflection-cocycle module classified the kernel of a single carrier and proved cocycle
multiplicativity, but did not turn cancellation between two distinct cocycles into inverse
rigidity. Gaussian quiet rigidity trivialized one already symmetric carrier, but did not derive
that symmetry from computed cocycle data. Their convolution closure says that inverse cocycle
classes plus joint analytic quietness force inverse carriers, with nonvanishing emerging from
cocycle cancellation itself.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.GaussianQuietCocycleCancellationInverseRigidityUniversalityLaw`
- Main theorem:
  `gaussianQuiet_cancellingReflectionCocycles_pointwiseInverse`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/GaussianQuietCocycleCancellationInverseRigidityUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for reflection-cocycle cancellation, products and inverses of multiplicative Dirichlet series,
Gaussian vertical-growth rigidity, and converse theorems found no exact collision. Closest primary
sources:

- J. B. Conrey and A. Ghosh, *On the Selberg class of Dirichlet series: small degrees*,
  <https://arxiv.org/abs/math/9204217>, studies classification expectations from functional
  equations and Euler products, not joint Gaussian quietness or cancellation of intrinsic
  reflection cocycles.
- J. B. Conrey, D. W. Farmer, B. E. Odgers, and N. C. Snaith,
  *A converse theorem for Γ₀(13)*,
  <https://arxiv.org/abs/math/0601549>, classifies a Dirichlet series from a specified functional
  equation and Euler product, not two carriers whose computed cocycles cancel.
- O. Klurman and A. P. Mangerel, *Rigidity Theorems for Multiplicative Functions*,
  <https://arxiv.org/abs/1707.07817>, proves arithmetic rigidity from value gaps and correlations,
  not analytic product rigidity under all-scale Gaussian quietness.

## Log

- 2026-07-23 — fresh theorem-pair closure joined computed cocycle multiplication to Gaussian
  quiet carrier rigidity.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
