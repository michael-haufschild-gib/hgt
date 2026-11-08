# The surface of Spec ℤ

- **ID:** SOSZ
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [review 0811 W14, §2.8a, §2.11](../../../reports/review-0811/obstacles-summary.md)
- **Statement:** construct, or derive the shape of, a two-dimensional object whose Riemann–Roch gives an
  `ℕ`-valued (or log-cardinality-valued) quadratic count with Tate limit `Q` on integer probes.

## Goal

`riemannHypothesis_iff_tateLimit_of_count` makes RH equivalent to a count `K ≥ 0` with
`K(ma)/m² → Q(a)`. Over a curve `K` is `½δ` on `C × C`, a dimension by Riemann–Roch. The task is the
`ℤ`-analogue, defined without `Q`. Lean code: `formal/GaloisForLFunctions/SurfaceOfSpecZ/`.

## Specification forced by the corpus

| Requirement | Source |
|---|---|
| trace (Rosati) type, pairs `ρ` with `1 − ρ̄`; kernel counts are blind | `KernelCountsAreBlindToComplexQuartets` |
| full rank, quadratic; no linear count | `LinearCountsAreDegenerate` |
| asymptotically Hecke invariant | `tateLimit_dilate` |
| integrality of the coefficients, infinite rank; no integral lattice carries a zero at 3 primes | `FrobeniusLatticeRigidity` |
| reads the test beyond its bidegree | LST `bidegree_h1_eq` |
| an exact RR polynomial in `m` with integral intersection numbers has a half-integral Tate limit, so intersection numbers must be real (log-cardinalities plus archimedean terms) | elementary; see C3 |

## Conjecture loop

| # | Conjecture | Status | Insight |
|---|---|---|---|
| C1 | The 𝔽₁-torus `𝔾_m²` with power-map graphs `Γ_n : y = xⁿ` is an honest surface realizing the pole plane: `Γ_m·Γ_n = m + n = 2 min(m,n) + |m − n|` (two 𝔽₁-cusps, `|m−n|` torsion points) | proved (Lean) | the cusp multiplicity `min(m,n)` is the rank of `ℤ[[q]]/(q^m − q^n)`; Bernstein–Kushnirenko gives `|m−n|` as a mixed area of Newton segments |
| C2 | The CS defect of the Frobenius zonotope surface is a sum of squares of integer counts, `2Σ_k(Σ_{n>k}a_n)²`, and normalized it is the first archimedean channel `e^{−|x|/2}` of Weil's kernel | proved (Lean) | toric geometry over 𝔽₁ supplies exactly one archimedean channel, with Hodge index by counting; it has no primes and a continuous (Cauchy) zero density |

## Log
- 2026-11-08 — created; C1, C2 formalized in `SurfaceOfSpecZ/TheFrobeniusZonotopeSurface.lean`
