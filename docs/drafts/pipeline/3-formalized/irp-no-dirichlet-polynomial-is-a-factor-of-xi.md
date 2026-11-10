# No Dirichlet polynomial is a factor of ξ (two-sided constant terms)

- **ID:** IRP-DP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** IRP README §6 Q2, §12 row "A factor with a Dirichlet series"
- **Statement:** every Dirichlet polynomial `D(s) = Σ_{n ∈ S} a_n n^{−s}` with at least two terms has
  a zero that is not a zero of `ξ` (`exists_zero_not_xi_zero`).

## Goal
Closes Q2 of IRP for Dirichlet polynomials with no hypothesis on the support (no constant term
needed, several bases allowed). The mechanism does not use the carrier rigidity
`RHTower.AtomDomination.eq_zero_of_herglotz_dirichlet_criticalCarrier`, which rests on Hamburger's
theorem for integer exponents and does not reach the rational frequencies `log(n/n₁)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean: `exists_zero_not_xi_zero`; four modules checked with `lake --old env lean`,
  empty output

## Lean
Folder `formal/GaloisForLFunctions/InfiniteRankPurityTheory/`.

| Module | Content |
|---|---|
| TheConstantTermsOnTheTwoSidesOfTheLineAgree | `fractSeries`; `mellin_fractSeries`, `tendsto_fractSeries_left`, `fractSeries_sub_leftLimit`, `fractSeries_eq`, `tsum_jump_eq`, `tsum_eq_of_tsum_dvd`, `constantTerms_agree`, `tsum_scale_eq_zero`, `tsum_left_eq_const`, `eq_const_mul_riemannZeta_div`; tools `exists_differentiableOn_deriv_mul_div`, `norm_le_of_good_heights` |
| TheInverseOfAnExponentialPolynomialExpandsWhereItIsBoundedBelow | `expPoly`, `Word`, `wordMass`, `freqMonoid`, `LogIndex`, `logWeight`, `logExp`; `hasSum_inv_expPoly_words`, `norm_wordMass_le`, `summable_exp_neg_freqMonoid`, `hasSum_inv_expPoly`, `hasSum_logWeight`, `tsum_logWeight_zero`, `sum_exp_eq_expPoly`, `sum_exp_eq_expPoly_neg`, `logDeriv_exp_mul`, `logDeriv_exp_mul_neg` |
| AZeroFreeExponentialPolynomialIsBoundedBelow | `exists_far_bound_expPoly`, `tendstoLocallyUniformly_expPoly`, `exists_le_norm_expPoly_of_zeroFree`, `hasSum_logWeight_of_zeroFree` |
| NoDirichletPolynomialIsAFactorOfXi | `norm_riemannZeta_div_le`, `exists_zero_not_xi_zero` |

`exists_good_heights` was split off `exists_bound_on_strip` in
`ADirichletPolynomialWithItsZerosOnTheLineHasAFunctionalEquation`.

## Paper proof

Notation: `m = min S`, `N = max S`, `Λ = D'/D`, `{u}` the fractional part,
`mellin f z = ∫_0^∞ u^{z−1} f(u) du`; `∫_0^∞ {u} u^{−s−1} du = −ζ(s)/s` for `0 < Re s < 1`
(`RHTower.integral_Ioi_zero_fract_cpow`).

### K. The constant terms agree (`constantTerms_agree`)
Countable families `(b_i, a_i)`, `0 < a_i ≤ 1`, with `Σ ‖b_i‖ a_i^σ < ∞` for `σ > ½`, and
`(c_j, q_j)`, `q_j ≥ 1`, with `Σ ‖c_j‖ q_j^σ < ∞` for `σ < ½`. `F` holomorphic on `0 < Re s < 1`,
bounded on `¼ ≤ Re s ≤ ¾`, with `F(s) = −(ζ(s)/s) Σ b_i a_i^s` on `½ < Re s < 1` and
`F(s) = −(ζ(s)/s) Σ c_j q_j^s` on `0 < Re s < ½`. Then `Σ_{q_j = 1} c_j = Σ_{a_i = 1} b_i`.

1. `g₊(u) = Σ b_i {a_i u}`, `g₋(u) = Σ c_j {q_j u}`. Since `{y} ≤ y^σ` for `0 ≤ σ ≤ 1`:
   `‖g₊(u)‖ ≤ A_σ u^σ` (`σ ∈ (½, 1]`), `‖g₋(u)‖ ≤ B_σ u^σ` (`σ ∈ [0, ½)`). By the scaling of the Mellin
   transform and summation under the integral, `mellin g₊ (−s) = F(s)` right of the line and
   `mellin g₋ (−s) = F(s)` left of it (`mellin_fractSeries`).
2. Split at `u = 1`: `T_±`, `B_±` the transforms of the parts of `g_±` on `u > 1` and `u ≤ 1`.
   `T₊` is holomorphic on `Re s > ½`, `T₋` on `Re s > 0`, `B₊` on `Re s < 1`, `B₋` on `Re s < ½`,
   each bounded by `C/dist` to the edge. `E₁ = F − B₊ − T₋` on the strip equals `T₊ − T₋` right of
   the line and `B₋ − B₊` left of it. The three glue to an entire function, bounded (near the line
   by the bound on `F`), and `T₊(x) − T₋(x) → 0` as `x → +∞`. By Liouville it vanishes.
3. Mellin inversion with transform `0` (`mellinInv_mellin_eq`): `g₊(u) = g₋(u)` at every point of
   continuity of `g₊ − g₋` other than `1`. The discontinuities form a countable set, so points of
   continuity accumulate from the right at every `u > 0`; both series are right continuous;
   hence `g₊ = g₋` on `(0, ∞)` (`fractSeries_eq`).
4. The left limit of `Σ b_i {a_i u}` at `u₀` is `Σ b_i (a_i u₀ − ⌈a_i u₀⌉ + 1)`; value minus left
   limit is `−Σ_{a_i u₀ ∈ ℤ} b_i`. So the weights of `a_i u₀ ∈ ℤ` and of `q_j u₀ ∈ ℤ` agree for
   every `u₀ > 0` (`tsum_jump_eq`).
5. At `u₀ = 1/k`: `a_i/k ∈ ℤ` only for `k = 1`, `a_i = 1`; `q_j/k ∈ ℤ` iff `q_j ∈ ℕ` and `k ∣ q_j`.
   So `S_k := Σ_{k ∣ q_j} c_j = [k = 1] β`, `β = Σ_{a_i = 1} b_i`. Then
   `Σ_{k ≤ N} μ(k) S_k = β` for every `N ≥ 1`, and the left side is `Σ_j c_j e_N(j)` with
   `e_N(j) = Σ_{k ≤ N, k ∣ q_j} μ(k)`, which equals `[q_j = 1]` for `N ≥ q_j` and is bounded by
   `d(q_j) ≤ C q_j^{1/4}`. Dominated convergence: `Σ_{q_j = 1} c_j = β`
   (`tsum_eq_of_tsum_dvd`).
6. *Rigidity.* At `u₀ = 1/(kt)`, `t > 1`, no `a_i u₀` is an integer, so `Σ_{q_j ∈ kt ℕ} c_j = 0`
   for every `k`; step 5 for the scales `q_j/t` gives `Σ_{q_j = t} c_j = 0` (`tsum_scale_eq_zero`).
   Regrouping by scales, `Σ c_j q_j^s = β` for `Re s < ½` (`tsum_left_eq_const`), so
   `F = −β ζ/s` left of the line and, by the identity theorem, on the strip
   (`eq_const_mul_riemannZeta_div`).

### A. Lower bounds (`exists_le_norm_expPoly_of_zeroFree`)
`P(w) = 1 + Σ_k c_k e^{−ℓ_k w}`, `ℓ_k > 0`, without zeros in `Re w > θ`. Then for `σ > θ` there is
`δ > 0` with `‖P‖ ≥ δ` on `Re w ≥ σ`: the vertical translates of `P` are twists by unimodular
numbers; far to the right all twists are `≥ ½`; a sequence with `P(w_j) → 0` has bounded real
parts, a subsequence of twists converges, the limit twist vanishes at a point of real part `≥ σ`
and is not identically zero, and by Hurwitz a translate of `P` vanishes right of `θ`.

### B. Expansion up to the zeros (`hasSum_inv_expPoly`, `hasSum_logWeight`)
1. *Words.* Where `Σ‖c_k‖e^{−ℓ_k Re w} < 1`: `1/P(w) = Σ_J β_J e^{−x_J w}` over words `J` in the index
   set, `β_J = Π(−c_{J_i})`, `x_J = Σ ℓ_{J_i}`, absolutely.
2. *Coefficient bound.* `μ(x) = Σ_{x_J = x} β_J`. On a far line `c₀`,
   `(2T)^{−1} ∫_{−T}^{T} e^{x(c₀+it)}/P(c₀+it) dt → μ(x)` (termwise, the mean of `e^{iθt}` tends to
   `[θ = 0]`). By Cauchy's theorem on `[σ, c₀] × [−T, T]` the integral over the line `c₀` differs
   from that over the line `σ` by two horizontal integrals bounded independently of `T`. On the
   line `σ`, `‖e^{xw}/P(w)‖ ≤ e^{σx}/δ`. So `‖μ(x)‖ ≤ e^{σx}/δ` (`norm_wordMass_le`).
3. *Sparsity.* The exponents lie in the additive monoid `M` generated by the `ℓ_k`, and
   `Σ_{x ∈ M} e^{−εx} ≤ Π_k (1 − e^{−εℓ_k})^{−1}`.
4. So `Σ_{x ∈ M} ‖μ(x)‖ e^{−σx} < ∞` for every `σ > θ`; `Σ_x μ(x) e^{−xw}` is holomorphic on
   `Re w > θ` and equals `1/P` far to the right, hence on `Re w > θ`.
5. `κ + P'/P = κ + (Σ_k (−c_k ℓ_k) e^{−ℓ_k w})(Σ_x μ(x) e^{−xw})`: one family with the constant `κ` at
   exponent `0` and all other exponents `ℓ_k + x > 0`.

### C. Conclusion (`exists_zero_not_xi_zero`)
Suppose every zero of `D` is a zero of `ξ`. The zeros lie on `Re s = ½` (P25 of the programme card)
and `ζ` vanishes at them.
1. `D(s) = a_m m^{−s} P(s)`, `P = 1 + Σ_{n ≠ m} (a_n/a_m) e^{−(log n − log m)s}`, without zeros in
   `Re s > ½`; `D(s) = a_N N^{−s} Q(−s)`, `Q = 1 + Σ_{n ≠ N} (a_n/a_N) e^{−(log N − log n)w}`, without
   zeros in `Re w > −½`. `Λ = −log m + P'/P = −log N − Q'(−s)/Q(−s)`.
2. By B: `Λ(s) = Σ b_i a_i^s` right of the line, constant term `−log m`, all other `a_i < 1`;
   `Λ(s) = Σ c_j q_j^s` left of it, constant term `−log N`, all other `q_j > 1`.
3. `F = −(ζ/s) Λ` is holomorphic on the strip: `Λ` has simple poles at the zeros of `D`, where `ζ`
   vanishes (`exists_differentiableOn_deriv_mul_div`, by orders:
   `ord(D') + ord(ζ) − ord(D) ≥ 0`).
4. `F` is bounded on `¼ ≤ Re s ≤ ¾`: `‖ζ(s)/s‖ ≤ 1/(1 − Re s) + 1/Re s ≤ 8`, `‖D'‖ ≤ Σ‖a_n‖ log n`,
   and `‖D‖` is bounded below on the two lines (A) and on horizontal segments at heights met in
   every interval of a fixed length (`exists_good_heights`); the maximum principle on the
   rectangles between such heights gives the bound (`norm_le_of_good_heights`).
5. K: `−log N = −log m`, so `N = m` and `D` has one term.

## Log
- 2026-11-10 — created in 1-in-progress
- 2026-11-10 — K, A, B, C formalized; card to 3-formalized
- 2026-11-10 — rigidity added to K: the left expansion is constant and `F = −β ζ/s` on the strip
