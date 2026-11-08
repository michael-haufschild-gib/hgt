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
| C2 | The CS defect of the Frobenius zonotope surface is a sum of squares of integer counts, `2Σ_k(Σ_{n>k}a_n)²`, and normalized it is the first archimedean channel `e^{−|x|/2}` of Weil's kernel | proved (Lean) | toric geometry over 𝔽₁ supplies exactly one archimedean channel, with Hodge index by counting and an `ℕ`-valued count whose Tate limit is the defect (`zonotope_tateLimit`); it has no primes and a continuous (Cauchy) zero density |
| C3 | The off-diagonal of Weil's form on atoms at `log m`, `log n` is assembled from the two existing half-products `ℙ¹×ℙ¹` and `ℙ¹_ℤ`: `Γ_m·Γ_n := (m+n) − √(mn)W(m,n) = min/(1 − (min/max)²) + G(m,n)I(m,n)` | proved (Lean) | one 𝔽₁-cusp, the jet tower of the trivial zeros, and the gcd-twisted torsion intersection on `ℙ¹_ℤ`; every local index is ≥ 0, so `Γ_m·Γ_n ≥ min(m,n)`. The sign of Weil's form lives only in the diagonal `Γ_n² = n(2−2g)`, `g = ∞`, which no half-product supplies |
| C4 | The archimedean part comes from a toric metric on `ℙ¹_ℤ` | refuted (Lean) | toric pairings of coprime torsion orbits depend only on the product `mn` (CRT), Weil's on the ratio: `Γ_2·Γ_3 = 18/5`, `Γ_1·Γ_6 = 36/35`. Positive survivor: cusp (integral, toric), primes (torsion, `ℙ¹_ℤ`), jets (neither); `Γ_1·Γ_2 = 4/3 + log 2` |
| C5 | Some Hecke-equivariant geometry with continuous moduli in the boost direction (planar convex bodies and mixed areas, hyperbolic orbital integrals, toric counts) realizes the Frobenius intersections | refuted (Lean) | no continuous kernel `F` with `Γ_m·Γ_n = √(mn)F(log m − log n)`: the primes are jump discontinuities at `log pᵏ` (pairs `(2j+1, j)` against `(2,1)`). The surface must see `n` as an integer, as torsion orbits do; continuous geometries carry only archimedean channels |

## Open after C1–C5

1. The diagonal: a renormalized self-intersection of Frobenius graphs whose sign is Weil's. The
   off-diagonal is a nonnegative Lefschetz count; positivity is the statement that the renormalized
   self-intersection pays it.
2. An arithmetic carrier of the jets `Σ_{k≥1} r^{−2k}` (trivial zeros): integral only at `k = 0`, not
   on `ℙ¹_ℤ` for toric metrics. The full-metric version (rank of Arakelov Green pairings of torsion
   orbits on a genus-zero surface against the infinite rank of the jet kernel) is not yet in Lean.

## Log
- 2026-11-08 — created; C1–C5 formalized in `SurfaceOfSpecZ/` (four modules, standard axioms)
