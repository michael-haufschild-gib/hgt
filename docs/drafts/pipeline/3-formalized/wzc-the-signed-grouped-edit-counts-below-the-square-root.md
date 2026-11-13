# The signed grouped edit counts below the square root

- **ID:** A157
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `WorldsOfTheZeroConfiguration/TheSignedGroupedEditCountsBelowTheSquareRoot.lean`
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.1 "Models and laws of world I", A157
- **Statement:** with `Θ = zetaZeroAbscissa`, for every `½ < β < 2/3` with `Θ + 2β < 2` and every
  `γ` with `ζ(β + iγ) ≠ 0`, some signed grouped edit with zero pair `β ± iγ` is an integer-norm fake
  at a count exponent `c < ½`; its continuation `(s − 1)ζ_B` has, right of an abscissa `σ₁ < ½`,
  exactly the zeros of `(s − 1)ζ(s)` and `β ± iγ`.

## Goal
B183 below `√x`: a model over the rational primes (multiplicities `0, 1, 2`, integer norms) with a
non-real fake zero right of the line and a count rate below the square root. The range of `β` is
nonempty iff `Θ < 1`; with `Θ ≤ 7/8` [X] it is `(½, 9/16)`. No bound for `ζ` inside the strip is
used: only the zero-free half-plane `Re s > Θ` through `1/ζ(s + 1 − ρ)`.

## Lean
| Statement | Declaration (namespace `WorldsOfTheZeroConfiguration.SignedEdit`) |
|---|---|
| Lemma 1 (summation by parts, tail) | `sum_Ioc_div_eq`, `abs_sum_Ioc_div_le` |
| Lemma 2 (hyperbola count) | `exists_abs_sum_mul_zeta_sub_le` |
| Lemma 3 (twin coefficients) | `freeFn_compl_mul_le_one`, `abs_twinCoeff_le_one`, `twin`, `intCount_editSystem_eq`, `LSeries_twin_eq` |
| Lemma 4 (cofactor left of the line) | `exists_norm_posFiniteFactor_le_of_re`, `exists_norm_posCofactor_le_of_re`, `exists_norm_editExponent_le_of_re`, `exists_norm_editCofactor_le_of_re` |
| Lemma 5 (partial sums of `u`) | `exists_abs_sum_twin_le` |
| Theorem | `exists_isIntegerNormFakeAt_sEdit_lt_half` |

## Proof

*Lemma 1.* With `U(n) = Σ_{0<j≤n} f(j)`, by induction on `M ≥ D`:
`Σ_{D<m≤M} f(m)/m = U(M)/(M+1) − U(D)/(D+1) + Σ_{D<m≤M} U(m)(1/m − 1/(m+1))`.
If `|U(n)| ≤ C n^θ`, `θ < 1`: the end terms are `≤ C D^{θ−1}` and
`|U(m)|/(m(m+1)) ≤ C m^{θ−2}`, `Σ_{m>D} m^{θ−2} ≤ D^{θ−1}/(1−θ)`; so the sum is
`≤ C(2 + 1/(1−θ)) D^{θ−1}`.

*Lemma 2.* Let `|U(n)| ≤ C n^θ` (`0 ≤ θ < 1`), `Σ_{0<j≤n} |f(j)| ≤ Z n^a`, `θ ≤ a`, `a > 0`. By
Lemma 1, `V(D) = Σ_{0<m≤D} f(m)/m` is Cauchy with limit `A`, `|V(D) − A| ≤ K₁ D^{θ−1}`. For `N ≥ 1`
put `λ = 1/(1 + a − θ) ∈ (0, 1]`, `D = ⌊N^λ⌋`, so `N^λ/2 ≤ D ≤ N^λ ≤ N`.
`Σ_{n≤N} (f * 1)(n) = Σ_{d≤N} f(d)⌊N/d⌋` splits at `D`:
- `d ≤ D`: `Σ f(d)⌊N/d⌋ = N V(D) − Σ f(d)(N/d − ⌊N/d⌋)`; the first is `AN + O(N K₁ D^{θ−1})`,
  the second is at most `Σ_{d≤D} |f(d)| ≤ Z D^a`.
- `D < d ≤ N`: `Σ f(d)⌊N/d⌋ = Σ_{1≤k≤N} Σ_{D<d≤N/k} f(d)`; the inner sum vanishes unless
  `k ≤ N/D`, and then it is `U(⌊N/k⌋) − U(D)`, of size `≤ 2C N^θ k^{−θ}`; summing over
  `k ≤ N/D` gives `≤ 2C/(1−θ) · N D^{θ−1}`.
With `D^{θ−1} ≤ 2^{1−θ} N^{λ(θ−1)}`, `N · N^{λ(θ−1)} = N^{λa}` and `D^a ≤ N^{λa}`, the error is
`O(N^{a/(1+a−θ)})`.

*Lemma 3.* The norm count of the edit system is `1_S * 1_{Tᶜ} = 1 * u`, `u = μ_S * 1_{Tᶜ}`
(`S` deleted, `T` doubled; `normCount_eq_sum_divisors`). `|u(d)| ≤ (1_{S-numbers} * 1_{T-numbers})(d)`
(`abs_twinCoeff_le`), and since `S ∩ T = ∅` there is at most one pair: if `ab = a′b′ = d` with
`a, a′` `S`-numbers and `b, b′` `T`-numbers, then `gcd(a, b′) = 1`, so `a | a′`, symmetrically
`a′ | a`. Hence `|u| ≤ 1`. On `Re s > 1`, `ζ_B = L(1 * u) = ζ · L(u)` and `ζ_B = ζ M_B`
(`sub_one_mul_zetaSeriesC_eq`), so `L(u, s) = M_B(s)`.

*Lemma 4.* As `exists_norm_editCofactor_le` with `½` replaced by `σ₀ > max(α/2, β − ½, Θ + β − 1)`:
`1/ζ(w)` is subpolynomial on `Re w ≥ Θ + δ`, `δ = (σ₀ + 1 − β − Θ)/2`
(`exists_invZeta_shift_data_of_zeroFree`); the finite Euler factor is bounded on `Re s ≥ σ₀ > β − 1`;
`|H₁| ≤ C₁ √log(|t|+2) + C₂` on `Re s ≥ σ₀ > α/2`, `Q` bounded there, `R` bounded on
`Re s ≥ σ₀ > β − ½`, and `C₁√L ≤ ηL + C₁²/(4η)`.

*Lemma 5.* The smoothed Perron shift for coefficients `|u| ≤ 1`
(`HTGeometry.SmoothedPerron.exists_norm_sum_sub_le`) with `H(s) = (s − 1)M_B(s)` (so `H(1) = 0`),
strip and line bounds from Lemma 4 with exponent `ε`: `|U(n)| ≪ n^{(ε+σ₀)/(1+ε)+κ}`.

*Theorem.* Let `g = min(2 − Θ − 2β, 2/3 − β) > 0`, `α = β + g/10`, `a = β + g/5`, `ε = κ = g/10`,
`σ₀ = max(α/2, Θ + β − 1) + g/10`, `k₀ = ⌈10/g⌉`. Then `σ₀ > contAbscissa(α, β, Θ)` (as
`β − ½ ≤ Θ + β − 1`), and `a + max(α/2, Θ + β − 1) ≤ 1 − 4g/5` (from `β ≤ 2/3 − g` and
`Θ + 2β ≤ 2 − g`), so with `θ = (ε+σ₀)/(1+ε) + κ ≤ σ₀ + g/5`: `a + θ ≤ 1 − g/2 < 1` and `θ ≤ a`.
Rankin: the edited primes are summable at `a > α` (`summable_abs_sEdit_rpow`), so
`Σ_{0<j≤n} |u(j)| ≤ n^a Σ |u(j)| j^{−a} ≤ Z n^a` (`sum_abs_twinCoeff_mul_rpow_le`). Lemma 2 gives
`N_B(N) = AN + O(N^c)`, `c = a/(1 + a − θ) < ½ ⇔ a + θ < 1`; for real `x`, `N_B(x) = N_B(⌊x⌋)`.
`A > 0` because the system is an integer-norm fake (`isIntegerNormFakeAt_editSystem_sEdit`) with a
count exponent below `1` (`pos_density_of_integerNormFakeAt_lt_one`). The zeros of `editG` right of
`contAbscissa < ½` are `editG_eq_zero_iff`. ∎

Axioms of the headline theorem: `propext`, `Classical.choice`, `Quot.sound`.

## Remarks
- The earlier plan (Perron for `ζ_B` itself with the sub-Weyl exponent `33/200`) needed
  `Θ < 233/266`; it was dropped. Bounding the sawtooth of the twin coefficients trivially by their
  Rankin mass suffices because `u` is supported on the `(S ∪ T)`-numbers, a set of exponent `α`.
- The fake zero is non-real when `γ ≠ 0`, and the continuation has no real zero right of `σ₁`
  other than those of `ζ`: the balance law is met by a balanced two-sided edit, not by a real top.

## Log
- 2026-11-13 — created; Perron/sub-Weyl plan replaced by the twin-coefficient hyperbola route;
  proved on paper and formalized.
