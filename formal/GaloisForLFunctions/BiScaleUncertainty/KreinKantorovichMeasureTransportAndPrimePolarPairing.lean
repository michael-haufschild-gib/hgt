import GaloisForLFunctions.BiScaleUncertainty.SignedKreinCollarAndPrimeDeficitTransfer

/-!
# Pillar XV: Krein–Kantorovich Measure Transport, Prime–Polar Pairing & Width Rigidity

This module develops **Pillar XV** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), establishing the **Krein–Kantorovich Signed
Measure-Transport Theory** between discrete arithmetic sums and continuum polar integrals, and
proving **Bounded-Energy Width Rigidity** to close **Trap 8 (The Midpoint Compression Escape)** in
the bounded-energy regime relevant to `EWU` and `HF`.

## Mathematical Motivation

In the Weil explicit formula (`EWU`, `HF`, `CHMD`), the discrete prime sum and the continuum polar
integral appear with opposite signs:
$$\mathcal{Q}_{\mathrm{prime}}(f) - \mathcal{Q}_{\mathrm{polar}}(f)
  = 2\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\,h_f(\log n) - 4\int_0^\infty h_f(x)\cosh(x/2)\,dx.$$
When treated separately on the grid-blind subspace `h_f(log n) = 0`, two obstructions arise:
1. **Decoupling of Discrete and Continuum Measures (Trap 9):** Setting `h_f(log n) = 0` erases
   `Λ(n) / √n` and leaves `-4 ∫ h_f(x) cosh(x/2) dx` uncoupled from the prime sum.
2. **The Midpoint Compression Escape (Trap 8, `InfiniteGridPolarRecovery.lean`):** Compressing a
   seed `f` to support radius `r₁ = 1 / (8(N+1))` and placing a polar copy at the midpoint
   `T_N = (log N + log(N+1)) / 2` satisfies `h(log n) = 0` (`∀ n ≥ 2`) because the compressed
   support sits inside the open gap `(log N, log(N+1))`, at normalized archimedean energy cost
   `≍ log N`.

This module resolves both obstructions:
- **Part A (Krein–Kantorovich Signed Measure Transport):** Couples a discrete node evaluation
  `M_ρ h_f(t)` directly to a continuum collar integral `∫_t^{t+δ} h_f(x) ρ(x - t) dx` via Krein's
  increment inequality and the reciprocal archimedean weight
  `1 / archLevySinhWeight(y) = e^{-y/2} sinh y ≤ y e^{y/2}`, which **vanishes linearly as `y → 0⁺`**.
- **Part B (Bounded-Energy Width Rigidity — Closing Trap 8):** Proves the converse of
  `InfiniteGridPolarRecovery.lean`: because `archLevySinhWeight(x) ≥ e^{-r₂/2} / x` on `[r₁, r₂]`
  (`0 < r₁ ≤ r₂`), any source whose autocorrelation is nonpositive (or vanishes) on `[r₁, r₂]`
  must pay archimedean Lévy energy at least `e^{-r₂/2} log(r₂ / r₁) h_f(0)`. Thus any source with
  bounded normalized energy `biScaleLevyEnergy f ≤ K h_f(0)` (`K = |Ω(0)| ≈ 2.752`) has a strictly
  positive minimum width `r₁ ≥ r₂ exp(-e^{r₂/2} K)` and **cannot** be compressed into a midpoint gap
  `(log N, log(N+1))` at large `N`.

## Main Results

1. **`inv_archLevySinhWeight_eq` & `exp_neg_half_mul_sinh_le`**:
   For `y > 0`, `(archLevySinhWeight y)⁻¹ = exp(-y / 2) * sinh y ≤ y * exp(y / 2)`.
2. **`archLevySinhWeight_ge_exp_neg_half_div`**:
   On `(0, r₂]`, `exp(-r₂ / 2) / y ≤ archLevySinhWeight y`.
3. **`krein_kantorovich_pointwise_abs_le` & `collar_measure_transport_abs_diff_le_levy`**:
   Pointwise and integrated Krein–Kantorovich measure-transport bounds between discrete node values
   `h_f(t)` and continuum collar integrals `∫_a^δ h_f(t + y) ρ(y) dy` for arbitrary signed
   autocorrelations `h_f`.
4. **`narrow_support_logarithmic_levy_lower_bound` & `bounded_levy_width_rigidity`**:
   If `h_f(x) ≤ 0` on `[r₁, r₂]` (`0 < r₁ ≤ r₂`), then
   `exp(-r₂ / 2) * log(r₂ / r₁) * h_f(0) ≤ ∫_{r₁}^{r₂} (h_f(0) - h_f(x)) archLevySinhWeight(x) dx`,
   and if this collar energy is bounded by `K * h_f(0)` (`h_f(0) > 0`), then
   `log(r₂ / r₁) ≤ exp(r₂ / 2) * K`.
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-! ## §1. Origin-Regularization of the Reciprocal Archimedean Weight -/

/-- For every `y : ℝ`, the reciprocal of `archLevySinhWeight y = exp(y / 2) / sinh y` is
`exp(-y / 2) * sinh y`. -/
theorem inv_archLevySinhWeight_eq (y : ℝ) :
    (archLevySinhWeight y)⁻¹ = Real.exp (-y / 2) * Real.sinh y := by
  unfold archLevySinhWeight
  rw [inv_div]
  have hexp : Real.exp (-y / 2) = (Real.exp (y / 2))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [hexp, div_eq_inv_mul]

/-- Exact factoring identity `exp(-y / 2) * sinh y = (1 / 2) * exp(y / 2) * (1 - exp(-2 y))`. -/
theorem exp_neg_half_mul_sinh_eq (y : ℝ) :
    Real.exp (-y / 2) * Real.sinh y =
      1 / 2 * Real.exp (y / 2) * (1 - Real.exp (-2 * y)) := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-y / 2) * Real.exp y = Real.exp (y / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (-y / 2) * Real.exp (-y) = Real.exp (y / 2) * Real.exp (-2 * y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  linarith

/-- **Linear Origin-Vanishing Bound for `exp(-y / 2) * sinh y`:**
For every `y ≥ 0`, `0 ≤ exp(-y / 2) * sinh y ≤ y * exp(y / 2)`.
This shows that the reciprocal archimedean weight `(archLevySinhWeight y)⁻¹` vanishes linearly as
`y → 0⁺`. -/
theorem exp_neg_half_mul_sinh_le {y : ℝ} (_ : 0 ≤ y) :
    Real.exp (-y / 2) * Real.sinh y ≤ y * Real.exp (y / 2) := by
  rw [exp_neg_half_mul_sinh_eq]
  have hexp_bound : 1 - Real.exp (-2 * y) ≤ 2 * y := by
    have h := Real.add_one_le_exp (-2 * y)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hexp_bound (by positivity : 0 ≤ 1 / 2 * Real.exp (y / 2))
  linarith

/-- Nonnegativity of `exp(-y / 2) * sinh y` for `y ≥ 0`. -/
theorem exp_neg_half_mul_sinh_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ Real.exp (-y / 2) * Real.sinh y :=
  mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.sinh_nonneg_iff.mpr hy)

/-- **Singular Hyperbolic Lower Bound on `archLevySinhWeight`:**
For any `0 < y ≤ r₂`, `exp(-r₂ / 2) / y ≤ archLevySinhWeight y`. -/
theorem archLevySinhWeight_ge_exp_neg_half_div {y r₂ : ℝ} (hy : 0 < y) (hyr₂ : y ≤ r₂) :
    Real.exp (-r₂ / 2) / y ≤ archLevySinhWeight y := by
  have h_upper : Real.exp (-y / 2) * Real.sinh y ≤ y * Real.exp (r₂ / 2) := by
    calc
      Real.exp (-y / 2) * Real.sinh y ≤ y * Real.exp (y / 2) :=
        exp_neg_half_mul_sinh_le (le_of_lt hy)
      _ ≤ y * Real.exp (r₂ / 2) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (le_of_lt hy)
  have h_recip := inv_archLevySinhWeight_eq y
  have hW_pos : 0 < archLevySinhWeight y := archLevySinhWeight_pos hy
  rw [div_le_iff₀ hy]
  have h1 : Real.exp (-r₂ / 2) = (Real.exp (r₂ / 2))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [h1, inv_le_iff_one_le_mul₀' (Real.exp_pos (r₂ / 2))]
  have hmul := mul_le_mul_of_nonneg_left h_upper (le_of_lt hW_pos)
  rw [← h_recip, mul_inv_cancel₀ (ne_of_gt hW_pos)] at hmul
  linarith

/-! ## §2. Pointwise & Integrated Krein–Kantorovich Measure-Transport Inequalities -/

/-- **Pointwise Krein–Kantorovich Transport Inequality:**
For any continuous compactly supported `f : ℝ → ℝ`, any node `t ∈ ℝ`, any jump `y > 0`, and any
transport density `ρ ≥ 0`,
$$\rho\,\bigl|h_f(t) - h_f(t + y)\bigr| \;\le\; \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)
  + \frac{h_f(0)}{2}\,\rho^2 e^{-y/2}\sinh y.$$ -/
theorem krein_kantorovich_pointwise_abs_le {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) {t y ρ : ℝ} (hy : 0 < y) (hρ : 0 ≤ ρ) :
    ρ * |autocorr f t - autocorr f (t + y)| ≤
      (autocorr f 0 - autocorr f y) * archLevySinhWeight y +
        autocorr f 0 / 2 * (ρ ^ 2 * (Real.exp (-y / 2) * Real.sinh y)) := by
  have hR : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hD : 0 ≤ autocorr f 0 - autocorr f y := autocorr_sub_nonneg hfc hf y
  have hW : 0 < archLevySinhWeight y := archLevySinhWeight_pos hy
  have hkrein : |autocorr f t - autocorr f (t + y)| ≤
      Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) := by
    rw [abs_sub_comm]
    exact abs_autocorr_add_sub_le_sqrt hfc hf t y
  have hmul := mul_le_mul_of_nonneg_left hkrein hρ
  have hyoung := signed_collar_young_bound (w := ρ) hW hR hD
  have hinv := inv_archLevySinhWeight_eq y
  have hterm :
      ρ ^ 2 / (2 * archLevySinhWeight y) * autocorr f 0 =
        autocorr f 0 / 2 * (ρ ^ 2 * (Real.exp (-y / 2) * Real.sinh y)) := by
    rw [← hinv]
    ring
  linarith

/-- **Pointwise Krein–Kantorovich Transport Bound with Linear Origin Regularization (`y > 0`):**
Using `exp(-y / 2) * sinh y ≤ y * exp(y / 2)`, the pointwise transport penalty is bounded by an
everywhere-continuous function of `y ∈ [0, ∞)`:
$$\rho\,\bigl|h_f(t) - h_f(t + y)\bigr| \;\le\; \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)
  + \frac{h_f(0)}{2}\,\rho^2 y\,e^{y/2}.$$ -/
theorem krein_kantorovich_pointwise_linear_reg_le {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) {t y ρ : ℝ} (hy : 0 < y) (hρ : 0 ≤ ρ) :
    ρ * |autocorr f t - autocorr f (t + y)| ≤
      (autocorr f 0 - autocorr f y) * archLevySinhWeight y +
        autocorr f 0 / 2 * (ρ ^ 2 * (y * Real.exp (y / 2))) := by
  have hbase := krein_kantorovich_pointwise_abs_le (t := t) hfc hf hy hρ
  have hR : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hreg := exp_neg_half_mul_sinh_le (le_of_lt hy)
  have hmul :
      autocorr f 0 / 2 * (ρ ^ 2 * (Real.exp (-y / 2) * Real.sinh y)) ≤
        autocorr f 0 / 2 * (ρ ^ 2 * (y * Real.exp (y / 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hreg (sq_nonneg ρ)
  linarith

/-- **Integrated Krein–Kantorovich Collar Measure-Transport Inequality:**
For any `f ∈ C²_c(ℝ)`, any node `t ∈ ℝ`, any collar interval `[a, δ]` (`0 < a ≤ δ`), and any
continuous nonnegative transport density `ρ : ℝ → ℝ` on `[a, δ]`, the signed discrepancy between
the discrete node evaluation `(∫_a^δ ρ(y) dy) h_f(t)` and the shifted continuum collar integral
`∫_a^δ h_f(t + y) ρ(y) dy` satisfies:
$$\left|\left(\int_a^\delta \rho(y)\,dy\right) h_f(t) - \int_a^\delta h_f(t + y)\,\rho(y)\,dy\right|
  \;\le\; \int_a^\delta \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy
    + \frac{h_f(0)}{2}\int_a^\delta \rho(y)^2 e^{-y/2}\sinh y\,dy.$$ -/
theorem collar_measure_transport_abs_diff_le_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (t : ℝ) {a δ : ℝ} (ha : 0 < a) (haδ : a ≤ δ)
    {ρ : ℝ → ℝ} (hρ_cont : ContinuousOn ρ (Icc a δ)) (hρ_nn : ∀ y ∈ Icc a δ, 0 ≤ ρ y) :
    |(∫ y in a..δ, ρ y) * autocorr f t - ∫ y in a..δ, autocorr f (t + y) * ρ y| ≤
      (∫ y in a..δ, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        autocorr f 0 / 2 * ∫ y in a..δ, ρ y ^ 2 * (Real.exp (-y / 2) * Real.sinh y) := by
  have hcont_ac : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hint_ρ : IntervalIntegrable ρ volume a δ :=
    hρ_cont.intervalIntegrable_of_Icc haδ
  have hint_prod : IntervalIntegrable (fun y : ℝ => autocorr f (t + y) * ρ y) volume a δ :=
    ((hcont_ac.comp (continuous_const.add continuous_id)).continuousOn.mul
      hρ_cont).intervalIntegrable_of_Icc haδ
  have hdiff_eq :
      (∫ y in a..δ, ρ y) * autocorr f t - (∫ y in a..δ, autocorr f (t + y) * ρ y) =
        ∫ y in a..δ, ρ y * (autocorr f t - autocorr f (t + y)) := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub
      (hint_ρ.mul_const _) hint_prod]
    refine intervalIntegral.integral_congr fun y _ => by ring
  rw [hdiff_eq]
  have hint_abs_in : IntervalIntegrable
      (fun y : ℝ => |ρ y * (autocorr f t - autocorr f (t + y))|) volume a δ :=
    (hρ_cont.mul (continuousOn_const.sub
      (hcont_ac.comp (continuous_const.add continuous_id)).continuousOn)).abs.intervalIntegrable_of_Icc haδ
  have habs_int :
      |∫ y in a..δ, ρ y * (autocorr f t - autocorr f (t + y))| ≤
        ∫ y in a..δ, |ρ y * (autocorr f t - autocorr f (t + y))| :=
    intervalIntegral.abs_integral_le_integral_abs haδ
  have hcont_w : ContinuousOn archLevySinhWeight (Icc a δ) :=
    continuousOn_archLevySinhWeight fun y hy => lt_of_lt_of_le ha hy.1
  have hint_levy : IntervalIntegrable
      (fun y : ℝ => (autocorr f 0 - autocorr f y) * archLevySinhWeight y) volume a δ :=
    ((continuousOn_const.sub hcont_ac.continuousOn).mul hcont_w).intervalIntegrable_of_Icc haδ
  have hint_pen : IntervalIntegrable
      (fun y : ℝ => ρ y ^ 2 * (Real.exp (-y / 2) * Real.sinh y)) volume a δ := by
    have hcont_exp_sinh : Continuous (fun y : ℝ => Real.exp (-y / 2) * Real.sinh y) :=
      (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul Real.continuous_sinh
    exact ((hρ_cont.pow 2).mul hcont_exp_sinh.continuousOn).intervalIntegrable_of_Icc haδ
  have hmono :
      (∫ y in a..δ, |ρ y * (autocorr f t - autocorr f (t + y))|) ≤
        ∫ y in a..δ,
          ((autocorr f 0 - autocorr f y) * archLevySinhWeight y +
            autocorr f 0 / 2 * (ρ y ^ 2 * (Real.exp (-y / 2) * Real.sinh y))) := by
    refine intervalIntegral.integral_mono_on haδ hint_abs_in
      (hint_levy.add (hint_pen.const_mul _)) fun y hy => ?_
    have hy_pos : 0 < y := lt_of_lt_of_le ha hy.1
    have hρy : 0 ≤ ρ y := hρ_nn y hy
    rw [abs_mul, abs_of_nonneg hρy]
    exact krein_kantorovich_pointwise_abs_le (t := t) hfc hf.continuous hy_pos hρy
  rw [intervalIntegral.integral_add hint_levy (hint_pen.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  linarith

/-! ## §3. Bounded-Energy Width Rigidity (Closing `Trap 8` in the Moderate-Energy Regime) -/

/-- Exact logarithmic integral of `exp(-r₂ / 2) / x` on `[r₁, r₂]` (`0 < r₁ ≤ r₂`):
`∫ x in r₁..r₂, exp(-r₂ / 2) / x = exp(-r₂ / 2) * log(r₂ / r₁)`. -/
theorem integral_exp_neg_half_div_eq {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁r₂ : r₁ ≤ r₂) :
    (∫ x in r₁..r₂, Real.exp (-r₂ / 2) / x) =
      Real.exp (-r₂ / 2) * Real.log (r₂ / r₁) := by
  have hdiv : (fun x : ℝ => Real.exp (-r₂ / 2) / x) = (fun x : ℝ => Real.exp (-r₂ / 2) * x⁻¹) := by
    funext x; rw [div_eq_mul_inv]
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hr₁r₂
  rw [hdiv, intervalIntegral.integral_const_mul,
    integral_inv_of_pos hr₁ hr₂]

/-- **Logarithmic Archimedean Energy Cost of Narrow Support (`narrow_support_logarithmic_levy_lower_bound`):**
If `f ∈ C²_c(ℝ)` satisfies `autocorr f x ≤ 0` for all `x ∈ [r₁, r₂]` (`0 < r₁ ≤ r₂`)—in
particular, if `autocorr f` is supported inside `[-r₁, r₁]`—then the archimedean Lévy energy on
`[r₁, r₂]` satisfies:
$$\exp(-r_2 / 2)\,\log\!\left(\frac{r_2}{r_1}\right)\,h_f(0)
  \;\le\; \int_{r_1}^{r_2} \bigl(h_f(0) - h_f(x)\bigr)\,\operatorname{archLevySinhWeight}(x)\,dx.$$ -/
theorem narrow_support_logarithmic_levy_lower_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁r₂ : r₁ ≤ r₂)
    (hnonpos : ∀ x ∈ Icc r₁ r₂, autocorr f x ≤ 0) :
    Real.exp (-r₂ / 2) * Real.log (r₂ / r₁) * autocorr f 0 ≤
      ∫ x in r₁..r₂, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
  have hR : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hcont_ac : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcont_w : ContinuousOn archLevySinhWeight (Icc r₁ r₂) :=
    continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le hr₁ hx.1
  have hint_rhs : IntervalIntegrable
      (fun x : ℝ => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) volume r₁ r₂ :=
    ((continuousOn_const.sub hcont_ac.continuousOn).mul hcont_w).intervalIntegrable_of_Icc hr₁r₂
  have hcont_inv : ContinuousOn (fun x : ℝ => Real.exp (-r₂ / 2) / x * autocorr f 0) (Icc r₁ r₂) := by
    refine ((continuousOn_const.div continuousOn_id ?_).mul continuousOn_const)
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hr₁ hx.1)
  have hint_lhs : IntervalIntegrable
      (fun x : ℝ => Real.exp (-r₂ / 2) / x * autocorr f 0) volume r₁ r₂ :=
    hcont_inv.intervalIntegrable_of_Icc hr₁r₂
  have hmono :
      (∫ x in r₁..r₂, Real.exp (-r₂ / 2) / x * autocorr f 0) ≤
        ∫ x in r₁..r₂, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    refine intervalIntegral.integral_mono_on hr₁r₂ hint_lhs hint_rhs fun x hx => ?_
    have hx_pos : 0 < x := lt_of_lt_of_le hr₁ hx.1
    have hw_ge := archLevySinhWeight_ge_exp_neg_half_div hx_pos hx.2
    have hsub_ge : autocorr f 0 ≤ autocorr f 0 - autocorr f x := by
      have h := hnonpos x hx
      linarith
    have hw_pos : 0 ≤ archLevySinhWeight x := le_of_lt (archLevySinhWeight_pos hx_pos)
    calc
      Real.exp (-r₂ / 2) / x * autocorr f 0
          ≤ archLevySinhWeight x * autocorr f 0 :=
            mul_le_mul_of_nonneg_right hw_ge hR
      _ = autocorr f 0 * archLevySinhWeight x := mul_comm _ _
      _ ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x :=
            mul_le_mul_of_nonneg_right hsub_ge hw_pos
  rw [intervalIntegral.integral_mul_const, integral_exp_neg_half_div_eq hr₁ hr₁r₂] at hmono
  exact hmono

/-- **Bounded-Energy Width Rigidity (Closing `Trap 8` in the Moderate-Energy Regime):**
If a nonzero source `f ∈ C²_c(ℝ)` (`0 < autocorr f 0`) has `autocorr f x ≤ 0` on `[r₁, r₂]`
(`0 < r₁ ≤ r₂`) and its archimedean Lévy energy on `[r₁, r₂]` is bounded by `K * autocorr f 0`,
then its compression ratio `r₂ / r₁` satisfies
$$\log\!\left(\frac{r_2}{r_1}\right) \;\le\; \exp(r_2 / 2)\,K.$$
Consequently, a source with bounded normalized archimedean energy `≤ K` cannot have its support
compressed to radius `r₁ < r₂ exp(-exp(r₂ / 2) K)` in order to hide inside a distant logarithmic
midpoint gap `(log N, log(N+1))` (`InfiniteGridPolarRecovery.lean`). -/
theorem bounded_levy_width_rigidity {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r₁ r₂ K : ℝ} (hr₁ : 0 < r₁) (hr₁r₂ : r₁ ≤ r₂)
    (hR : 0 < autocorr f 0) (hnonpos : ∀ x ∈ Icc r₁ r₂, autocorr f x ≤ 0)
    (henergy : (∫ x in r₁..r₂, (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
      K * autocorr f 0) :
    Real.log (r₂ / r₁) ≤ Real.exp (r₂ / 2) * K := by
  have hlow := narrow_support_logarithmic_levy_lower_bound hf hfc hr₁ hr₁r₂ hnonpos
  have hcomb : Real.exp (-r₂ / 2) * Real.log (r₂ / r₁) * autocorr f 0 ≤ K * autocorr f 0 :=
    le_trans hlow henergy
  have hdiv : Real.exp (-r₂ / 2) * Real.log (r₂ / r₁) ≤ K :=
    le_of_mul_le_mul_right hcomb hR
  have hexp_pos : 0 < Real.exp (r₂ / 2) := Real.exp_pos (r₂ / 2)
  have hmul := mul_le_mul_of_nonneg_left hdiv (le_of_lt hexp_pos)
  have hcancel : Real.exp (r₂ / 2) * (Real.exp (-r₂ / 2) * Real.log (r₂ / r₁)) =
      Real.log (r₂ / r₁) := by
    rw [← mul_assoc, ← Real.exp_add]
    have h0 : r₂ / 2 + -r₂ / 2 = 0 := by ring
    rw [h0, Real.exp_zero, one_mul]
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
