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
| an exact RR polynomial in `m` with integral intersection numbers has a half-integral Tate limit, so intersection numbers must be real (log-cardinalities plus archimedean terms) | elementary |

## Conjecture loop

| # | Conjecture | Status | Insight |
|---|---|---|---|
| C1 | The 𝔽₁-torus `𝔾_m²` with power-map graphs `Γ_n : y = xⁿ` is an honest surface realizing the pole plane: `Γ_m·Γ_n = m + n = 2 min(m,n) + |m − n|` (two 𝔽₁-cusps, `|m−n|` torsion points) | proved (Lean) | the cusp multiplicity `min(m,n)` is the vanishing order of `x^m − xⁿ` at `0`; Bernstein–Kushnirenko gives `|m−n|` as the area spanned by the Newton segments |
| C2 | The CS defect of the Frobenius zonotope surface is a sum of squares of integer counts, `2Σ_k(Σ_{n>k}a_n)²`, and normalized it is the first archimedean channel `e^{−|x|/2}` of Weil's kernel | proved (Lean) | toric geometry over 𝔽₁ supplies exactly one archimedean channel, with Hodge index by counting and an `ℕ`-valued count whose Tate limit is the defect (`zonotope_tateLimit`); it has no primes and a continuous (Cauchy) zero density |
| C3 | The off-diagonal of Weil's form on atoms at `log m`, `log n` is assembled from the two existing half-products `ℙ¹×ℙ¹` and `ℙ¹_ℤ`: `Γ_m·Γ_n := (m+n) − √(mn)W(m,n) = min/(1 − (min/max)²) + G(m,n)I(m,n)` | proved (Lean) | one 𝔽₁-cusp, the jet tower of the trivial zeros, and the gcd-twisted torsion intersection on `ℙ¹_ℤ`; every local index is ≥ 0, so `Γ_m·Γ_n ≥ min(m,n)`. No half-product supplies the diagonal `Γ_n² = n(2−2g)`, `g = ∞` |
| C4 | The archimedean part comes from a toric metric on `ℙ¹_ℤ` | refuted (Lean) | toric pairings of coprime torsion orbits depend only on the product `mn` (CRT), Weil's on the ratio: `Γ_2·Γ_3 = 18/5`, `Γ_1·Γ_6 = 36/35`. Positive survivor: cusp (integral, toric), primes (torsion, `ℙ¹_ℤ`), jets (neither); `Γ_1·Γ_2 = 4/3 + log 2` |
| C5 | Some Hecke-equivariant geometry with continuous moduli in the boost direction (planar convex bodies and mixed areas, hyperbolic orbital integrals, toric counts) realizes the Frobenius intersections | refuted (Lean) | no continuous kernel `F` with `Γ_m·Γ_n = √(mn)F(log m − log n)`: the primes are jump discontinuities at `log pᵏ` (pairs `(2j+1, j)` against `(2,1)`). The surface must see `n` as an integer, as torsion orbits do; continuous geometries carry only archimedean channels |
| C6 | Some metric on `O(1)` over `ℙ¹_ℤ` (Green function `−log|z−w| + φ(z) + φ(w)`) carries the jets | refuted (Lean) | torsion pairings `= −I(m,n) + φ(n)P(m) + φ(m)P(n)`: the product formula returns the prime channel with opposite sign, plus rank two; on coprime orders the archimedean Frobenius block on `{2,3,5}×{7,11,13}` is nonsingular. The genus-zero half-product supplies the primes and two archimedean dimensions only |
| C7 | Over `𝔽_{1ⁿ}` the surface has `N(n) = Γ_1·Γ_n = Λ(n) + 1 + 1/(n²−1)` points, and with a finite genus `g` the defect on `⟨Γ_1, Γ_n⟩` is the genus form, nonnegative iff `a(n)² ≤ 4g²n`, `a(n) = n + 1 − N(n)` | proved (Lean) | `a(n) ≥ n − log n − 1`, so every finite genus fails for all large `n`: atomic Frobenius graphs force infinite genus because `Spec ℤ` has `log p` points where a curve has `p + 1 − O(g√p)`. Smoothing the atoms performs the prime number theorem and is what makes the trace `O(√n)` possible |
| C8 | The jets are an archimedean Lefschetz trace | proved (Lean) | `ω(u) = ½(e^{u/2}/(eᵘ−1) + e^{u/2}/(eᵘ+1))`: the trace of the dilation `x ↦ eᵘx` of `ℝ` at its fixed point on even functions; the odd sector gives the trivial zeros `−2k−1` of odd characters. On `ℂ^×`: the transversal index of the Frobenius at the unit circle, on which the torsion orbits lie. The archimedean part `1 + 1/(n²−1) = q/(q−1)` of `N(n)` (C7) is, at `q = n²`, the groupoid cardinality of `[𝔸¹/𝔾_m](𝔽_q)`: the cusp is the open orbit, the jets are `B𝔾_m`, whose Frobenius traces `q^{−k}` are the trivial zeros; at `q = n` (both parities, `Γ_ℂ`) it is `n/(n−1)` |
| C9 | Hasse–Weil for the smoothed Frobenius graphs at the integer degrees is RH | proved (Lean) | `riemannHypothesis_iff_hasseWeil_integerDegrees`: RH iff `|c_B(log n)| ≤ c_B(0)` for every `n ≥ 1`, the plane `⟨Γ_1, Γ_n⟩` for each integer degree, as for the powers of Frobenius on a curve; the gaps of `log ℕ` shrink like `e^{−t}` while the orbit correlation is Lipschitz with constant `e^{t/2}` (tempered zeros, `C²` spline). Pairs `⟨Γ_m, Γ_n⟩` also (`riemannHypothesis_iff_forall_frobeniusPair_hasseWeil`). Atoms: no finite genus (C7); smoothed: genus `c_B(0)/2` exactly under RH |
| C10 | The Gamma/pole compensation asked by B88 is explicit | proved (Lean) | off the diagonal `W(m,n) = lim_{r→1}(C_∞(m,n) + T̃_r(m,n))` with `T̃_r` the positive gcd-twisted torsion energy of `ℙ¹_ℤ` and `√(mn)C_∞ = (m+n) − min/(1−(min/max)²)` (pole plane minus cusp and jets), positive for distant orders, negative for close ones (`√20 C_∞(4,5) = −19/9`); as a whole form the archimedean channels are the positive Lévy jump count `J` (off-diagonal `−ω`, diagonal `+∞`) plus the constant `Ω(0) < 0` |
| C11 | Crude Hasse–Weil at the integer degrees self-improves | proved (Lean) | `|c_B(log n)| ≤ K n^σ` for all `n` iff zero width `≤ σ` (`zetaZeroWidth_le_iff_crude_integerDegrees`); `σ = 0`, any constant `K`, is RH (`riemannHypothesis_iff_bounded_integerDegrees`). The curve's self-improvement (power sums) is free for the smoothed graphs; the whole difficulty is the crude bound at every degree — Stepanov's step |
| C12 | A sparse set of degrees decides RH | proved (Lean) | any `D ⊂ ℕ` with gaps `O(√x)` (`riemannHypothesis_iff_hasseWeil_of_sqrtGaps`), e.g. the squares (`riemannHypothesis_iff_hasseWeil_squareDegrees`). The gap exponent `½` is the critical abscissa: gaps `O(x^θ)`, `θ > ½`, control the orbit only to `e^{(θ−½)t}`. The primes (gaps `O(√p log p)` under RH, `O(p^{0.525})` unconditionally) sit just above it |
| C13 | The count door is decided plane by plane | proved (Lean) | `riemannHypothesis_iff_planeCounts`: RH iff for every `n ≥ 1` some `K_n : ℤ² → ℕ` has Tate limit `δ_n(x,y) = c_B(0)x² + 2c_B(log n)xy + c_B(0)y²`, the defect of `xΓ_1 + yΓ_n`. A binary count per integer degree replaces counts on every `ℤᴺ`; on `C × C` the plane `⟨Δ, Γ_{Fⁿ}⟩` carries the integral genus form. The count still has to be found without `c_B` |
| C14 | The prime degrees decide RH | proved (Lean) | `riemannHypothesis_iff_forall_primePair_hasseWeil`: Hasse–Weil on every plane `⟨Γ_p, Γ_q⟩` of two smoothed graphs of prime degree is RH; the log-ratios of primes are dense by the prime number theorem (prime in `(x,(1+ε)x)`), so no gap condition is needed for pairs, in contrast with the one-sided planes `⟨Γ_1, Γ_p⟩` of C12 |
| C15 | The diagonal of the atomic graphs admits a renormalization of bounded growth | refuted (Lean) | on the degrees `[N, 2N)` the genus must satisfy `N(log N − 17)/16 ≤ g` (`genus_ge_of_genusDefect_nonneg`), and `g ≥ N(4 log N + 6)` suffices (`genusDefect_nonneg_of_le`): order `N log N`, against `√n` from the planes `⟨Γ_1, Γ_n⟩` (C7). Inside a dyadic block no degree divides another, so no torsion orbits meet and `Γ_m·Γ_n` is the jets alone, between `N²/(4|m−n|)` and `4N²/|m−n|`; the defect is a negative harmonic matrix. The divergence of the diagonal is the logarithmic singularity of the archimedean kernel at the atom spacing `1/N` |
| C16 | Hasse–Weil on the one-sided prime planes `⟨Γ_1, Γ_p⟩` decides RH | partial (Lean) | degrees with gaps `O(x^θ)` give `zetaZeroWidth ≤ θ − ½` (`zetaZeroWidth_le_of_hasseWeil_of_powGaps`); Huxley's `θ > 7/12` gives width `≤ 1/12` from the prime planes (`zetaZeroWidth_le_of_hasseWeil_primeDegrees`). Classically width `σ` gives prime gaps `x^{½+σ+ε}`: the transfer between Hasse–Weil at the primes and prime gaps is the identity on exponents, so this route reaches RH exactly at gaps `x^{½+o(1)}`; the pairs `⟨Γ_p, Γ_q⟩` (C14) avoid gaps entirely |
| C17 | The atomic surface truncated at degree `N` satisfies the Hodge index with a finite genus | proved (Lean), unconditional | `genusDefect_Icc_nonneg_of_le`: genus `4N(1 + log N)` suffices on all `Σ_{n ≤ N} x_nΓ_n`; `genus_ge_of_genusDefect_Icc_nonneg`: `⌊N/2⌋(log⌊N/2⌋ − 17)/16` is necessary. Channel by channel: `Γ_m·Γ_n = √(mn)(ω + w)`; jets `ω ≤ N/|m−n|` (row sums `2N(1 + log N)`), primes `w ≤ 2` (row sums `2N`), pole rank two (`≥ −N(2 + log N)Σnx²`). The atomic genus is archimedean; the primes, where the zeros enter, are of lower order `O(N)`, so atoms cannot see RH |
| C18 | One side of the crude bound at the integer degrees suffices (Bombieri–Stepanov) | proved (Lean) | `riemannHypothesis_iff_bddBelow_integerDegrees`: RH iff `c_B(log n) ≥ −K` for all `n` — an upper bound on the smoothed point counts, the side Stepanov's method gives on a curve; `riemannHypothesis_iff_bddAbove_integerDegrees`: RH iff `c_B(log n) ≤ K`. Pringsheim's theorem for `Σ(Cq^{n/2} + a_n)Tⁿ` becomes Landau's for `K ± c_B` (`evenCoeff_eq_zero_of_two_re_lagStructure_ge`), with "no real Frobenius eigenvalue above `√q`" replaced by "no real zero of `ζ` in the strip" |
| C19 | The prime channel of the atomic surface is of lower order than the jets | proved (Lean), unconditional | in `y_n = √n x_n` the prime kernel `w(m, nt) = Λ(t)/√t` is the Hecke operator `Σ_t Λ(t)t^{−1/2}(T_t + T_t*)`; on `[1, N]` its form is `≤ (log N + log 4 + 4)Σy²` (`primeChannel_le`: weighted Schur test with weights `n^{−1/2}`, row sums `log(N/n) + O(1)` by Mertens plus `Σ_{t∣n}Λ(t) = log n`) and `≥ log M(log M − log 4 − 4)` at `y_n = n^{−1/2}` with energy `≤ 1 + log N`, `M = ⌊√N⌋` (`primeChannel_ge`). Spectral radius `≍ log N`, the pole of `ζ` at `1`, against `N log N` for the jets: at atom spacing `1/N` the archimedean channel is `N` times larger, and the zeros enter neither at leading order |
| C20 | The Stepanov side of C18 works for every zero configuration | refuted (Lean); positive survivor proved | survivor `onLine_of_two_re_lagStructure_ge`: for a tempered configuration without real zeros, `2 Re S ≥ −K` puts every zero on the line. Obstruction `stepanov_side_blind_to_real_zeros`: on the real pair `{¼, ¾}` the spline lag structure is `ĥ(−i/4)²(e^{u/4} + e^{−u/4})`, bounded below, unbounded above. An upper bound on point counts is blind to real zeros, as on a curve it is blind to a real eigenvalue `α > √q` (Bombieri–Stepanov need the twist for the other side); for `ζ` the absence of real zeros in the strip is the twist |
| C21 | The Stepanov count is needed only at the square degrees, as Bombieri's at the even extensions | proved (Lean) | `riemannHypothesis_iff_bddBelow_squareDegrees`: RH iff `c_B(log n²) ≥ −K` for all `n`; `riemannHypothesis_iff_bddBelow_of_sqrtGaps` for any degree set with gaps `O(√x)`. Degrees multiply, so the even powers of Frobenius are the graphs `Γ_{n²} = Γ_n ∘ Γ_n` |
| C22 | RH is invariant under base change: the degrees `nᵏ` decide it, from one side, for every `k` | proved (Lean) | `riemannHypothesis_iff_bddBelow_powerDegrees`: for each `k ≥ 1` and every box spline `U_1^{⋆(r+1)}` of order `r ≥ r₀(k)`, RH iff `2 Re S(k log n) ≥ −K` for all `n`. The gap method gives only width `≤ ½ − 1/k` (C16); the multiplicative structure gives everything: the trace Dirichlet series is `Σ_z e_z ζ(s − kz)` (`traceDirichlet_eq`), meromorphic on `1 < Re s < 2 + k/2` with poles `1 + kz` of residue `e_z` (`differentiableAt_traceZetaOf`), the analogue of the rationality of `Z(C/𝔽_{qᵏ})`; Landau for nonnegative Dirichlet series puts the abscissa at `1`, and the rightmost off-line pole on its line blows up along its ray against the convergent series. The order `r₀(k)` comes from the polynomial growth of `ζ` on `|Re| ≤ 3 + k` |

## Big picture

The two half-products exist and assemble the whole off-diagonal: `Γ_m·Γ_n` = one `𝔽₁`-cusp (toric,
integral) + the even jets of the dilation (archimedean, real, infinite rank) + torsion collisions over
the primes (`ℙ¹_ℤ`, discontinuous in `log n`). Each local index is nonnegative; Weil's defect is
`(m + n) − Γ_m·Γ_n` off the diagonal. The diagonal `Γ_n² = n(2 − 2g)` diverges only through the jet
tower at coincidence: the infinite genus is archimedean. This is Connes' local trace formula in
integer normalization, read from the `𝔽₁`-side; `Spec ℤ ×_{𝔽₁} Spec ℤ` behaves like the square of the
inverse limit of `𝔾_m` under the Frobenii (the adelic solenoid with radial scaling).

Signs: in Weil's kernel the primes enter as the Abel limit of the torsion log-energy of `ℙ¹_ℤ`, which
is positive before renormalization, and the archimedean channels (cusp and jets) enter negatively.
With atomic graphs the diagonal is `+∞` and carries everything. After smoothing, on probes orthogonal
to the pole plane the prime sum loses its main term together with the pole (the prime number theorem
pairs them), and what is left is the zero sum itself.

Smoothed by the cubic spline, the Frobenius graphs at integer degrees are a curve in every numerical
respect: genus `c_B(0)/2`, traces `c_B(log n)`, Hasse–Weil at every degree iff RH, the self-improvement
from a crude bound is free, one side of the crude bound suffices (Landau in place of Pringsheim), the
squares suffice, RH is invariant under base change (the degrees `nᵏ` decide it through the trace zeta
function `Σ_z e_z ζ(s − kz)`), and the count door holds plane by plane. Over `𝔽_q` the crude bound is Stepanov's
count, an upper bound on points; over `ℤ` it is `c_B(log n) ≥ −K`, which is RH. The object the corpus
is missing is therefore a natural binary count on the planes `⟨Γ_1, Γ_n⟩`, i.e. a reason for an upper
bound on the smoothed point counts at each integer degree.

The atomic surface of degree `N` is, unconditionally, a curve of genus `≍ N log N`. In the normalized
channels the jets have spectral radius `≍ N log N`, the pole (off the primitive part) `O(N log N)`,
and the primes, a Hecke operator, `≍ log N`. Resolution decides what is seen: at the atom spacing
`1/N` the archimedean self-energy dominates by a factor `N`; the arithmetic, and with it RH, appears
only after smoothing at a fixed scale, where all channels are `O(1)`.

## Open

1. A natural `ℕ`- or log-cardinality-valued count on each plane `⟨Γ_1, Γ_n⟩` with Tate limit `δ_n`,
   defined without `c_B` (C13); equivalently a one-sided crude bound `c_B(log n) ≥ −K`, an upper
   bound on the smoothed point counts (C11, C18).
2. The diagonal: a renormalized self-intersection of Frobenius graphs whose sign is Weil's; the
   off-diagonal is a nonnegative Lefschetz count. For atoms the renormalization is `Θ(N log N)` at
   degree `N` and unconditional (C15, C17); a diagonal of bounded genus exists only for smoothed graphs;
   the prime channel is `≍ log N` there (C19).
3. An arithmetic carrier of the jets `Σ_{k≥1} r^{−2k}` (trivial zeros): integral only at `k = 0`,
   carried by no metric on `ℙ¹_ℤ`; the even-sector trace of the dilation of `ℝ` at its fixed point.
4. Hasse–Weil on the one-sided planes `⟨Γ_1, Γ_p⟩` of prime degree: width `≤ 1/12` (C16); RH by this
   route needs prime gaps `x^{½+o(1)}`; the pairs `⟨Γ_p, Γ_q⟩` already decide RH (C14). The Dirichlet
   method of C22 would need the continuation of `Σ_z e_z P(s − z)`, `P` the prime zeta function,
   which has logarithmic singularities at `z + ρ'` for every zero `ρ'`, real ones among them (heuristic,
   not formalized).

## Log
- 2026-11-08 — created; C1–C22 formalized in `SurfaceOfSpecZ/` (twenty-two modules)
