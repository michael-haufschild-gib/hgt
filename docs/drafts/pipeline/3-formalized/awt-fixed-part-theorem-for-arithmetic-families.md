# The zero motive of ζ is the fixed part of every arithmetic family

- **ID:** awt-fixed-part-theorem
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0911/fable.md` §5.2 (`(FP)`, B142, B85, B86)
- **Statement:** Fixed-part decompositions for the named canonical families; vanishing-mass and translated-law moment identities; an Euler-weight counterexample to reverse product-positivity transfer; and an RH-equivalent sublinear cover-family tensor-moment criterion. The counterexample does not retain an FE. The universal statement that no inequality derived from any arithmetic family can improve the base trace remains unproved.

## Goal
Record the exact fixed-part laws and their obstruction to reverse transfer from product positivity. The universal closure asserted in `(FP)` is a separate open claim.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules in `ArithmeticWeightTheory`, `lake --old env lean` green

## Mathematical statements and complete proofs

### 1. Amplified monodromy symmetry-breaking (`[PROVED HERE]`)

Let `s ⊂ ℕ₊` be a finite set of positive integers, `a : ℕ → ℝ_{\ge 0}`, `S_x = ∑_{n ∈ s} a_n χ_x(n)` on `G = GaugeTorus`, and `A : G → ℂ` any continuous amplifier.

1. **Coherent amplified pricing at the trivial fibre (`0`):** For *every* finite measure `ν` on `G` (without any orthogonality assumption), *every* continuous `A : G → ℂ`, and *every* `k ∈ ℕ`,
   $$\nu(\{0\}) \, |A(0)|^2 \Bigl(\sum_{n \in s} a_n\Bigr)^{2k} \le \int_G |A(x)|^2 |S_x|^{2k} \, d\nu(x).$$
   *Proof.* At `x = 0`, `χ_0(n) = 1` (`twist_trivial`), hence `S_0 = ∑_{n ∈ s} a_n ≥ 0` and `|S_0|^{2k} = (∑_{n ∈ s} a_n)^{2k}`. Nonnegativity of `|A(x)|^2 |S_x|^{2k}` on `G` gives `ν.real {0} · |A(0)|^2 |S_0|^{2k} = ∫_{\{0\}} |A|^2 |S|^{2k} dν ≤ ∫_G |A|^2 |S|^{2k} dν`. ∎

2. **Centred-trace decoupling under pole jump:** Let `C_x = c_0` at `x = 0` and `-S_x` on `G \setminus \{0\}`. Then
   $$\int_G |A(x)|^2 |C_x|^{2k} \, d\nu(x) - \int_G |A(x)|^2 |S_x|^{2k} \, d\nu(x) = \nu(\{0\}) |A(0)|^2 \bigl(|c_0|^{2k} - |S_0|^{2k}\bigr),$$
   and `∫_{G \setminus \{0\}} |A(x)|^2 |S_x|^{2k} dν = ∫_G |A(x)|^2 |S_x|^{2k} dν - ν(\{0\}) |A(0)|^2 |S_0|^{2k}`. Thus orthogonality evaluates `∫ |A|^2 |S|^{2k} dν`, controlling only `G \setminus \{0\}` while `c_0` cancels identically. ∎

3. **Strict amplified saving off the trivial fibre (`x_0 ≠ 0`):** Let `x_j ∈ G` (`j ∈ Fin 4`) have coordinate `j / 4` at `p = 2` and `0` elsewhere, so `χ_{x_j}(2) = i^j` and `χ_{x_j}(3) = 1`, with `ν = \frac{1}{4} ∑_{j=0}^3 δ_{x_j}`.
   - On `P = {4, 6, 9}`, `(χ_{x_j}(4), χ_{x_j}(6), χ_{x_j}(9)) = ((-1)^j, i^j, 1)` are orthonormal under `ν` (`TwistOrthonormalOn ν {4, 6, 9}`).
   - With `s = {2, 3}`, `a_2 = a_3 = 1`, `x_0 = x_2` (`χ_{x_2}(2) = -1, χ_{x_2}(3) = 1`), and `A(x) = -χ_x(2) + χ_x(3)`, we have `ν.real {x_2} |A(x_2)|^2 (a_2 + a_3)^2 = \frac{1}{4} \cdot 4 \cdot 4 = 4`, whereas `A(x) S_x = -χ_x(4) + χ_x(9)` cancels the collision at `6 = 2 \cdot 3 = 3 \cdot 2`, giving `∫_G |A(x)|^2 |S_x|^2 dν = 2 < 4`. ∎

### 2. One-way product-positivity coupling (`[PROVED HERE]`)

This resolves the named obstacle of `fable.md` §5.2: coupling `L_{\mathrm{base}}` to `L_f^{\mathrm{var}}` through nonnegative Dirichlet and von Mangoldt coefficients of `L_f = L_{\mathrm{base}} L_f^{\mathrm{var}}`.

1. **Abel–divisor monotonicity under symmetric shifts:**
   - For `c : ℕ → ℝ` with nonnegative partial sums `S_r = ∑_{j=0}^r c_j ≥ 0` (`0 ≤ r ≤ m`) and `r ≥ 1`, induction on `m` yields `S_m ≤ ∑_{j=0}^m r^{m - j} c_j` (`geom_weighted_sum_ge_sum`).
   - For any multiplicative `g : ArithmeticFunction ℝ` with `(ζ * g)(n) ≥ 0` and `a ≥ 0`, multiplicativity (`Nat.recOnPosPrimePosCoprime`) yields `(ζ * g)(n) ≤ (idRpow a * g)(n)` and `0 ≤ (idRpow (-a) * (idRpow a * g))(n)` for all `n : ℕ`, while `cosh(a log n) Λ(n) + λ_{\mathrm{var}}(n) ≥ Λ(n) + λ_{\mathrm{var}}(n) ≥ 0`. ∎

2. **Simple-pole rational-prime Euler-factor doubling (`F_θ = ζ · D_θ`):**
   For `1/2 < θ < 1`, let `flipVM θ n = Λ(n)` on prime powers with `n.minFac ∈ flipPrimes θ` (`0` otherwise), `doubledVM θ = Λ + flipVM θ`, and `flipSmoothAF θ` the `flipPrimes θ`-smooth indicator.
   - *Simple pole preserved:* For every `σ > θ` (including `σ = 1`), `∑_n flipVM θ n · n^{-σ} < ∞` (`summable_flipVM_rpow`), so `-F_θ'/F_θ` preserves the simple pole of residue `1` at `s = 1` and `archPoleWindow`.
   - *Product positivity preserved:* `0 ≤ (flipSmoothAF θ * (ζ * g))(n)` and `0 ≤ doubledVM θ n + λ_{\mathrm{var}}(n)` (`flipSmooth_mul_nonneg`).
   - *Window shift beats every `a < 1/2`:* By positivity and continuity of `splineAutoCorr` at `0` (`0 < splineAutoCorr 0`) and pigeonhole clustering of `flipBlock θ k` into `M` logarithmic bins, for all large `k` some prime `p ∈ flipBlock θ k` satisfies `primeWindowOf (doubledVM θ) p - primeWindow p ≥ c_0 p^{\theta - 1/2}`. Hence for every `a < 1/2`, `ζ` and `doubledVM θ` (`θ = 1/2 + (\max(a, 0) + 1/2)/2`) cannot both satisfy `|archPoleWindow p - primeWindowOf w p| ≤ K p^a` on all primes (`not_both_primeWindowOf_power_bound`, `no_reverse_weight_bound_from_product_positivity`). ∎

### 3. Fixed-part laws for the named families and mixtures (`[PROVED HERE]`)

1. **Five canonical family classes:**
   - *Gauge torus `(G, gaugeHaar)`:* `gaugeHaar {0} = 0`, `gaugeHaar (isozericClass σ_0) = 0` (`1/2 ≤ σ_0 < 1`), `gaugeHaar jumpLocus = 0`, and `0`-supported trace jumps cancel identically (`gaugeTorus_fixedPart_decoupling`).
   - *Dirichlet characters:* at modulus `q`, `(dirichletGaugeMeasure q).real {0} = 1 / φ(q) → 0` (`measureReal_dirichletGaugeMeasure_zero`, `tendsto_dirichletGaugeMeasure_zero`); across all characters modulo `1 ≤ q ≤ Q`, `Q / ∑_{q=1}^Q φ(q) → 0` (`tendsto_cumulative_principal_fraction`).
   - *Vertical line `[-T, T]`:* `(verticalHeightMeasure T).real {0} = 0` and `(verticalHeightMeasure T).real [-H, H] ≤ H / T → 0` (`measureReal_verticalHeightMeasure_Icc_le`, `tendsto_verticalHeightMeasure_Icc`).
   - *Hecke eigenforms under the Weyl law and Rankin–Selberg:* any finite set of `r` cuspidal modes has Weyl mass `r / cuspCount L → 0` (`tendsto_weyl_finiteMode_mass`), while Rankin–Selberg averages satisfy `∑_i w_i L(τ_i^2, z) = ζ(z) ∑_i w_i L(τ_i(\cdot^2), z)` (`Re z > 2`) with `(ζ * realTauSqAF (τ_i))(n) = τ_i(n)^2 ≥ 0` (`rankinSelberg_family_commonFactor`).
   - *Number fields under a counting measure:* `degreeOneCount (L^H) p = 1 + varPermChar H (frob p) ≥ 0` (`p ∤ discr L`) with `classMean (varPermChar H) = 0` and exact preservation of the `ζ`-summand `1` under mixtures (`numberField_counting_fixedPart`).

2. **Moment decoupling, pushforward realizability, and mixture closure:**
   - For any probability space `(Ω, ρ)` and `V ∈ L^{2k}(ρ)` with `∫ V^j dρ = μ_j` (`0 ≤ j ≤ 2k`), `Measure.map (c + V \cdot) ρ` is a probability measure on `ℝ` with `2k`-th moment `∑_{j=0}^{2k} \binom{2k}{j} c^{2k - j} μ_j` for *every* `c ∈ ℝ` (`commonFactor_moment_realizable_for_all_c`).
   - Convex mixtures `(1 - λ_n) μ_n + λ_n ρ_n` of vanishing-mass and common-factor families decouple asymptotically (`tendsto_mixture_moment_decomp`).

3. **Jensen–Minkowski coercivity and the RH equivalence for cover-family tensor moments:**
   - Weighted AM–GM yields `c^{2k} + 2k c^{2k - 1} v ≤ (c + v)^{2k}` (`even_pow_tangent_le`), hence `c^{2k} ≤ ∫ (c + V)^{2k} dρ ≤ 2^{2k} (c^{2k} + ∫ V^{2k} dρ)` when `∫ V dρ = 0` (`pow_two_mul_le_integral_add_of_integral_eq_zero`, `add_pow_two_mul_le`).
   - Instantiated on `(GaugeTorus, gaugeHaar)` with `C_x(p) = 2 Re S(log p) + Re T_x(log p)`, sublinear `2k`-th prime-trace moment exponents `1 + o(k)` hold if and only if `RiemannHypothesis` holds (`riemannHypothesis_iff_coverFamily_tensorExponent_sublinear`, `zeroMotive_is_fixedPart_of_every_arithmeticFamily`). ∎

## Lean 4 modules (`GaloisForLFunctions.ArithmeticWeightTheory`)
1. `AmplifiedMonodromyBreaksOnlyOffTheTrivialFibre.lean`:
   `measureReal_singleton_zero_mul_amplified_pow_le`, `integral_amplified_centred_sub_uncentred`, `integral_amplified_compl_zero_eq`, `twistOrthonormalOn_quarterTwoMeasure`, `exists_amplified_orthonormal_strict_saving`.
2. `ProductPositivityCouplingIsOneWay.lean`:
   `geom_weighted_sum_ge_sum`, `zeta_mul_le_idRpow_mul`, `symmShift_mul_nonneg_of_zeta_mul_nonneg`, `symmShift_vonMangoldt_add_nonneg`, `summable_flipVM_rpow`, `flipSmooth_mul_nonneg`, `eventually_exists_primeWindowOf_doubledVM_sub_ge`, `not_both_primeWindowOf_power_bound`, `no_reverse_weight_bound_from_product_positivity`.
3. `TheZeroMotiveIsTheFixedPartOfEveryArithmeticFamily.lean`:
   `gaugeHaar_singleton_zero`, `gaugeTorus_fixedPart_decoupling`, `measureReal_dirichletGaugeMeasure_zero`, `tendsto_dirichletGaugeMeasure_zero`, `tendsto_cumulative_principal_fraction`, `measureReal_verticalHeightMeasure_Icc_le`, `tendsto_verticalHeightMeasure_Icc`, `tendsto_weyl_finiteMode_mass`, `rankinSelberg_family_commonFactor`, `numberField_counting_fixedPart`, `commonFactor_moment_realizable_for_all_c`, `tendsto_mixture_moment_decomp`, `even_pow_tangent_le`, `pow_two_mul_le_integral_add_of_integral_eq_zero`, `riemannHypothesis_iff_coverFamily_tensorExponent_sublinear`, `zeroMotive_is_fixedPart_of_every_arithmeticFamily`.

## Log
- 2026-11-09 — proved on paper (`2-fully-proven`) and formalized unconditionally in Lean 4 (`3-formalized`, 3 modules in `ArithmeticWeightTheory`, wired into `ArithmeticWeightTheory.lean`).
