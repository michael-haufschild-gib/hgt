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

| C6 | Some metric on `O(1)` over `ℙ¹_ℤ` (Green function `−log|z−w| + φ(z) + φ(w)`) carries the jets | refuted (Lean) | torsion pairings `= −I(m,n) + φ(n)P(m) + φ(m)P(n)`: the product formula returns the prime channel with opposite sign, plus rank two; on coprime orders the archimedean Frobenius block on `{2,3,5}×{7,11,13}` is nonsingular. The genus-zero half-product supplies the primes and two archimedean dimensions only |

| C7 | Over `𝔽_{1ⁿ}` the surface has `N(n) = Γ_1·Γ_n = Λ(n) + 1 + 1/(n²−1)` points, and with a finite genus `g` the defect on `⟨Γ_1, Γ_n⟩` is the genus form, nonnegative iff `a(n)² ≤ 4g²n`, `a(n) = n + 1 − N(n)` | proved (Lean) | `a(n) ≥ n − log n − 1`, so every finite genus fails for all large `n`: atomic Frobenius graphs force infinite genus because `Spec ℤ` has `log p` points where a curve has `p + 1 − O(g√p)`. Smoothing the atoms performs the prime number theorem and is what makes the trace `O(√n)` possible |
| C8 | The jets are an archimedean Lefschetz trace | proved (Lean) | `ω(u) = ½(e^{u/2}/(eᵘ−1) + e^{u/2}/(eᵘ+1))`: the trace of the dilation `x ↦ eᵘx` of `ℝ` at its fixed point on even functions; the odd sector gives the trivial zeros `−2k−1` of odd characters. Read on `ℂ^×`: the transversal index of the Frobenius at the unit circle, the circle on which the torsion orbits lie |
| C9 | Hasse–Weil for the smoothed graphs at every degree is RH | in corpus at every real scale (`riemannHypothesis_iff_splineOrbit_hasseWeil`); integer scales `t = log n` open | the cubic spline sees every off-line zero (its transform vanishes only on the real axis), so the smoothed surface is a curve of finite genus `W(B,B)/2` exactly under RH; passing from `t ∈ log ℕ` to all `t` needs a derivative bound `O(e^{t/2})` for the orbit correlation |
| C10 | The Gamma/pole compensation asked by B88 is explicit | proved (Lean) | off the diagonal `W(m,n) = lim_{r→1}(C_∞(m,n) + T̃_r(m,n))` with `T̃_r` the positive gcd-twisted torsion energy of `ℙ¹_ℤ` and `√(mn)C_∞ = (m+n) − min/(1−(min/max)²)` (pole plane minus cusp and jets), positive for distant orders, negative for close ones (`√20 C_∞(4,5) = −19/9`); as a whole form the archimedean channels are the positive Lévy jump count `J` (off-diagonal `−ω`, diagonal `+∞`) plus the constant `Ω(0) < 0` |

## Big picture after C1–C8

The two half-products exist and assemble the whole off-diagonal: `Γ_m·Γ_n` = one `𝔽₁`-cusp (toric,
integral) + the even jets of the dilation (archimedean, real, infinite rank) + torsion collisions over
the primes (`ℙ¹_ℤ`, discontinuous in `log n`). Each local index is nonnegative; Weil's defect is
`(m + n) − Γ_m·Γ_n` off the diagonal. What is missing is the diagonal `Γ_n² = n(2 − 2g)`, whose only
divergence is the jet tower at coincidence: the infinite genus is archimedean. This is Connes' local
trace formula in integer normalization, read from the `𝔽₁`-side; `Spec ℤ ×_{𝔽₁} Spec ℤ` behaves like the
square of the inverse limit of `𝔾_m` under the Frobenii (the adelic solenoid with radial scaling).
For B88 (Gamma/pole compensation of torsion forms at `δ = 0`): C6 shows the compensation cannot be an
Arakelov Green function on `ℙ¹(ℂ)` paired on torsion orbits.

Signs: in Weil's kernel the primes enter as the Abel limit of the torsion log-energy of `ℙ¹_ℤ`, which
is positive before renormalization, and the archimedean channels (cusp and jets) enter negatively.
With atomic graphs the diagonal is `+∞` and carries everything. After smoothing, on probes orthogonal
to the pole plane the prime sum loses its main term together with the pole (the prime number theorem
pairs them), and what is left is the zero sum itself.

## Open after C1–C8

1. The diagonal: a renormalized self-intersection of Frobenius graphs whose sign is Weil's. The
   off-diagonal is a nonnegative Lefschetz count; positivity is the statement that the renormalized
   self-intersection pays it.
2. An arithmetic carrier of the jets `Σ_{k≥1} r^{−2k}` (trivial zeros): integral only at `k = 0`,
   carried by no metric on `ℙ¹_ℤ`; they are the even-sector trace of the dilation of `ℝ` at its fixed
   point, `ω(u) = ½(1/(2 sinh(u/2)) + 1/(2 cosh(u/2)))`, an archimedean object of infinite rank.

## Log
- 2026-11-08 — created; C1–C8, C10 formalized in `SurfaceOfSpecZ/` (seven modules, standard axioms)
