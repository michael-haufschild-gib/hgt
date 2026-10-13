import GaloisForLFunctions.RHTower.CosDilationLogPrimCoreDualRigidity
import GaloisForLFunctions.RHTower.CosDilationPeriodicMultiplierUnfolding

/-!
# Differential Law of the Logarithmic Primitive Core and Cumulative Autocorrelation Rigidity

Let `f : ℝ → ℝ` be a continuous core supported in `[α, β] ⊂ (0, ∞)` (`0 < α ≤ β`) with zero
mean `∫_{y > 0} f(y) dy = 0`, let `C_f(s) := ∫ r in 0..s, A_f(r) dr` be its cumulative dilation
autocorrelation, and let `g := logPrimCore f` (`g(y) = (∫_0^y f(t) dt) / y`) be its logarithmic
primitive core from `CosDilationLogPrimCoreDualRigidity`.

In `CosDilationLogPrimCoreDualRigidity` we established the inversion-dual cumulative identity
`C_f(s) + s * C_f(s⁻¹) = s * A_g(s)` for all `s > 0`, together with `A_g(1) = 2 * C_f(1)`.
Differentiating this identity with respect to `s` and cancelling `A_f(s) - s⁻¹ A_f(s⁻¹) = 0`
via the inversion symmetry `A_f(s⁻¹) = s * A_f(s)` reveals that `A_g` is continuously
differentiable on `(0, ∞)`—even though `f` is merely continuous—with exact derivatives

* `d/ds (s * A_g(s)) = C_f(s⁻¹)` (`hasDerivAt_mul_dilationAutocorr_logPrimCore`),
* `d/ds A_g(s) = -C_f(s) / s²` (`hasDerivAt_dilationAutocorr_logPrimCore`).

Integrating `d/ds A_g(s) = -C_f(s) / s²` over `[a, b] ⊂ (0, ∞)` and using the compact support
of `A_g` in `[α/β, β/α]` together with `A_g(1) = 2 * C_f(1)` yields the weighted cumulative
autocorrelation laws:

* `∫ u in α/β..1, C_f(u) / u² du = -2 * C_f(1) ≤ 0`
  (`intervalIntegral_alpha_div_beta_one_div_sq_dilationAutocorr`),
* `∫ u in 1..β/α, C_f(u) / u² du = 2 * C_f(1) ≥ 0`
  (`intervalIntegral_one_beta_div_alpha_div_sq_dilationAutocorr`),
* `∫ u in α/β..β/α, C_f(u) / u² du = 0`
  (`intervalIntegral_alpha_div_beta_beta_div_alpha_div_sq_dilationAutocorr`).

Consequently, although `C_f(α/β) = 0` and `C_f(1) > 0` for every non-zero zero-mean core `f`,
`C_f(u)` cannot be nonnegative on `[α/β, 1]` (`eq_zero_of_intervalIntegral_dilationAutocorr_nonneg_on_Icc`),
nor can `C_f(u)` be nonpositive on `[1, β/α]` (`eq_zero_of_intervalIntegral_dilationAutocorr_nonpos_on_Icc`).
Finally, unfolding the quarter-period integral `∫ x in 0..(1/4), Σ_k A_f(|x+k|) dx = Ψ_f(1) / π`
for blind cores with `β ≤ (11/4) α` expresses `Ψ_f(1) / π` directly as the two-window cumulative
autocorrelation sum `(∫ r in 3/4..5/4, A_f(r) dr) + (∫ r in 7/4..9/4, A_f(r) dr)`
(`cosDilationKernel_one_div_pi_eq_intervalIntegral_of_le_eleven_fourths`).
-/

open MeasureTheory Set Real Filter Topology

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Compact support of the cumulative autocorrelation `s ↦ ∫ r in 0..s, A_f(r) dr` -/

/-- **Cumulative autocorrelation vanishes below `α / β`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) and any `s ≤ α / β`,
`∫ r in 0..s, A_f(r) dr = 0`. -/
theorem intervalIntegral_dilationAutocorr_eq_zero_of_le (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    {s : ℝ} (hs : s ≤ α / β) :
    ∫ r in (0 : ℝ)..s, dilationAutocorr f r = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hαβ_pos : 0 < α / β := div_pos hα hβ0
  have h_zero : ∀ r ∈ uIcc (0 : ℝ) s, dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun hmem => ?_
    have hr_le : r ≤ max (0 : ℝ) s := (mem_uIcc.mp hr).elim
      (fun h => h.2.trans (le_max_right _ _)) (fun h => h.2.trans (le_max_left _ _))
    have hmax_le : max (0 : ℝ) s ≤ α / β := max_le hαβ_pos.le hs
    linarith [hmem.1]
  rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]

/-- **Cumulative autocorrelation vanishes above `β / α` for zero-mean cores.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `s ≥ β / α`, `∫ r in 0..s, A_f(r) dr = 0`. -/
theorem intervalIntegral_dilationAutocorr_eq_zero_of_ge (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : β / α ≤ s) :
    ∫ r in (0 : ℝ)..s, dilationAutocorr f r = 0 := by
  have h1_le_ratio : 1 ≤ β / α := ( one_le_div hα ).mpr hαβ
  have hs0 : 0 ≤ s := by linarith
  rw [intervalIntegral_zero_dilationAutocorr_eq_integral_mul_primCore hf hα hαβ hsupp hs0]
  have h_zero : ∀ y ∈ uIcc α β, f y * (primCore f (s * y) / y) = 0 := by
    intro y hy
    rw [uIcc_of_le hαβ] at hy
    have hβ_le_sy : β ≤ s * y := by
      calc β = (β / α) * α := (div_mul_cancel₀ β hα.ne').symm
        _ ≤ s * y := mul_le_mul hs hy.1 hα.le hs0
    rw [primCore_eq_zero_of_ge hf hα hαβ hsupp hmean hβ_le_sy, zero_div, mul_zero]
  rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]

/-! ### Exact differential laws for `dilationAutocorr (logPrimCore f)` -/

/-- **Derivative of `u ↦ u * A_{logPrimCore f}(u)` on `(0, ∞)`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `s > 0`,
`d/du (u * A_{logPrimCore f}(u))|_{u = s} = ∫ r in 0..s⁻¹, A_f(r) dr`. -/
theorem hasDerivAt_mul_dilationAutocorr_logPrimCore (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u => u * dilationAutocorr (logPrimCore f) u)
      (∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r) s := by
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  set C : ℝ → ℝ := fun u => ∫ r in (0 : ℝ)..u, dilationAutocorr f r with hC
  have hdC : ∀ u : ℝ, HasDerivAt C (dilationAutocorr f u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hA_cont.intervalIntegrable 0 u)
      (hA_cont.stronglyMeasurableAtFilter volume (𝓝 u)) hA_cont.continuousAt
  have hd_inv : HasDerivAt (fun u : ℝ => u⁻¹) (-(s ^ 2)⁻¹) s := hasDerivAt_inv hs.ne'
  have hdC_inv : HasDerivAt (fun u : ℝ => C u⁻¹) (dilationAutocorr f s⁻¹ * (-(s ^ 2)⁻¹)) s :=
    (hdC s⁻¹).comp s hd_inv
  have hd_prod : HasDerivAt (fun u : ℝ => u * C u⁻¹)
      (1 * C s⁻¹ + s * (dilationAutocorr f s⁻¹ * (-(s ^ 2)⁻¹))) s :=
    (hasDerivAt_id s).mul hdC_inv
  have hd_sum : HasDerivAt (fun u : ℝ => C u + u * C u⁻¹)
      (dilationAutocorr f s + (1 * C s⁻¹ + s * (dilationAutocorr f s⁻¹ * (-(s ^ 2)⁻¹)))) s :=
    (hdC s).add hd_prod
  have h_cancel : dilationAutocorr f s + (1 * C s⁻¹ + s * (dilationAutocorr f s⁻¹ * (-(s ^ 2)⁻¹))) =
      C s⁻¹ := by
    rw [dilationAutocorr_inv f hs]
    have : s ≠ 0 := hs.ne'
    field_simp
    ring
  rw [h_cancel] at hd_sum
  refine hd_sum.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with u hu
  exact (intervalIntegral_dilationAutocorr_add_inv_eq hf hα hαβ hsupp hmean hu).symm

/-- **Derivative of `A_{logPrimCore f}` on `(0, ∞)`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `s > 0`,
`d/du (A_{logPrimCore f}(u))|_{u = s} = -(∫ r in 0..s, A_f(r) dr) / s²`. -/
theorem hasDerivAt_dilationAutocorr_logPrimCore (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (dilationAutocorr (logPrimCore f))
      (-(∫ r in (0 : ℝ)..s, dilationAutocorr f r) / s ^ 2) s := by
  have hd_mul := hasDerivAt_mul_dilationAutocorr_logPrimCore hf hα hαβ hsupp hmean hs
  have hd_div := hd_mul.div (hasDerivAt_id' s) hs.ne'
  have h_eq_deriv : ((∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r) * s -
      s * dilationAutocorr (logPrimCore f) s * 1) / s ^ 2 =
      -(∫ r in (0 : ℝ)..s, dilationAutocorr f r) / s ^ 2 := by
    rw [← intervalIntegral_dilationAutocorr_add_inv_eq hf hα hαβ hsupp hmean hs]
    ring
  rw [h_eq_deriv] at hd_div
  refine hd_div.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with u (hu : 0 < u)
  exact (mul_div_cancel_left₀ _ hu.ne').symm

/-! ### Exact weighted integrals of the cumulative autocorrelation -/

/-- **Fundamental Theorem of Calculus for the `u⁻²`-weighted cumulative autocorrelation.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `0 < a` and `0 < b`,
`∫ u in a..b, (∫ r in 0..u, A_f(r) dr) / u² du = A_{logPrimCore f}(a) - A_{logPrimCore f}(b)`. -/
theorem intervalIntegral_div_sq_intervalIntegral_dilationAutocorr_eq (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in a..b, (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 =
      dilationAutocorr (logPrimCore f) a - dilationAutocorr (logPrimCore f) b := by
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hC_cont : Continuous fun u : ℝ => ∫ r in (0 : ℝ)..u, dilationAutocorr f r :=
    intervalIntegral.continuous_primitive hA_cont.intervalIntegrable 0
  have hu_pos : ∀ u ∈ uIcc a b, 0 < u := fun u hu =>
    lt_of_lt_of_le (lt_min ha hb) hu.1
  have h_cont_on : ContinuousOn
      (fun u : ℝ => -(∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) (uIcc a b) :=
    (hC_cont.neg.continuousOn).div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (hu_pos u hu).ne'
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt (dilationAutocorr (logPrimCore f))
      (-(∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) u := fun u hu =>
    hasDerivAt_dilationAutocorr_logPrimCore hf hα hαβ hsupp hmean (hu_pos u hu)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_cont_on.intervalIntegrable
  have h_neg : (fun u : ℝ => -(∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) =
      fun u : ℝ => -((∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) := by
    funext u; ring
  rw [h_neg, intervalIntegral.integral_neg] at hFTC
  linarith

/-- **Fundamental Theorem of Calculus for the inverted cumulative autocorrelation.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `0 < a` and `0 < b`,
`∫ u in a..b, (∫ r in 0..u⁻¹, A_f(r) dr) du = b * A_{logPrimCore f}(b) - a * A_{logPrimCore f}(a)`. -/
theorem intervalIntegral_inv_intervalIntegral_dilationAutocorr_eq (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in a..b, (∫ r in (0 : ℝ)..u⁻¹, dilationAutocorr f r) =
      b * dilationAutocorr (logPrimCore f) b - a * dilationAutocorr (logPrimCore f) a := by
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hC_cont : Continuous fun u : ℝ => ∫ r in (0 : ℝ)..u, dilationAutocorr f r :=
    intervalIntegral.continuous_primitive hA_cont.intervalIntegrable 0
  have hu_pos : ∀ u ∈ uIcc a b, 0 < u := fun u hu =>
    lt_of_lt_of_le (lt_min ha hb) hu.1
  have h_cont_on : ContinuousOn (fun u : ℝ => ∫ r in (0 : ℝ)..u⁻¹, dilationAutocorr f r)
      (uIcc a b) :=
    hC_cont.continuousOn.comp (continuousOn_id.inv₀ fun u hu => (hu_pos u hu).ne')
      (fun u _ => mem_univ _)
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt (fun s => s * dilationAutocorr (logPrimCore f) s)
      (∫ r in (0 : ℝ)..u⁻¹, dilationAutocorr f r) u := fun u hu =>
    hasDerivAt_mul_dilationAutocorr_logPrimCore hf hα hαβ hsupp hmean (hu_pos u hu)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_cont_on.intervalIntegrable

/-- **Exact negative weighted cumulative autocorrelation integral on `[α/β, 1]`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
`∫ u in (α / β)..1, (∫ r in 0..u, A_f(r) dr) / u² du = -2 * ∫ r in 0..1, A_f(r) dr`. -/
theorem intervalIntegral_alpha_div_beta_one_div_sq_dilationAutocorr (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) :
    ∫ u in (α / β)..1, (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 =
      -2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have h_pos : 0 < α / β := div_pos hα hβ0
  rw [intervalIntegral_div_sq_intervalIntegral_dilationAutocorr_eq hf hα hαβ hsupp hmean
    h_pos zero_lt_one]
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  have hg_zero : dilationAutocorr (logPrimCore f) (α / β) = 0 :=
    dilationAutocorr_eq_zero_of_not_mem_Ioo hg_cont hα hαβ hg_supp fun h =>
      lt_irrefl _ h.1
  rw [hg_zero, dilationAutocorr_logPrimCore_one_eq hf hα hαβ hsupp hmean]
  ring

/-- **Exact positive weighted cumulative autocorrelation integral on `[1, β/α]`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
`∫ u in 1..(β / α), (∫ r in 0..u, A_f(r) dr) / u² du = 2 * ∫ r in 0..1, A_f(r) dr`. -/
theorem intervalIntegral_one_beta_div_alpha_div_sq_dilationAutocorr (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) :
    ∫ u in (1 : ℝ)..(β / α), (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 =
      2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have h_pos : 0 < β / α := div_pos hβ0 hα
  rw [intervalIntegral_div_sq_intervalIntegral_dilationAutocorr_eq hf hα hαβ hsupp hmean
    zero_lt_one h_pos]
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  have hg_zero : dilationAutocorr (logPrimCore f) (β / α) = 0 :=
    dilationAutocorr_eq_zero_of_not_mem_Ioo hg_cont hα hαβ hg_supp fun h =>
      lt_irrefl _ h.2
  rw [hg_zero, dilationAutocorr_logPrimCore_one_eq hf hα hαβ hsupp hmean]
  ring

/-- **Total `u⁻²`-weighted cumulative autocorrelation integral on `[α/β, β/α]` vanishes.** -/
theorem intervalIntegral_alpha_div_beta_beta_div_alpha_div_sq_dilationAutocorr
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) :
    ∫ u in (α / β)..(β / α), (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  rw [intervalIntegral_div_sq_intervalIntegral_dilationAutocorr_eq hf hα hαβ hsupp hmean
    (div_pos hα hβ0) (div_pos hβ0 hα)]
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  have hg_lo : dilationAutocorr (logPrimCore f) (α / β) = 0 :=
    dilationAutocorr_eq_zero_of_not_mem_Ioo hg_cont hα hαβ hg_supp fun h => lt_irrefl _ h.1
  have hg_hi : dilationAutocorr (logPrimCore f) (β / α) = 0 :=
    dilationAutocorr_eq_zero_of_not_mem_Ioo hg_cont hα hαβ hg_supp fun h => lt_irrefl _ h.2
  rw [hg_lo, hg_hi, sub_self]

/-! ### Cumulative autocorrelation sign-change rigidity -/

/-- **Cumulative autocorrelation sign-change rigidity on `[α/β, 1]`.**
Although `C_f(α/β) = 0` and `C_f(1) ≥ 0`, if `f` is continuous and supported in `[α, β]`
(`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`, and `∫ r in 0..u, A_f(r) dr ≥ 0` for all
`u ∈ [α/β, 1]`, then `f = 0` everywhere. -/
theorem eq_zero_of_intervalIntegral_dilationAutocorr_nonneg_on_Icc (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hnonneg : ∀ u ∈ Icc (α / β) 1, 0 ≤ ∫ r in (0 : ℝ)..u, dilationAutocorr f r)
    (y : ℝ) : f y = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hle1 : α / β ≤ 1 := (div_le_one hβ0).mpr hαβ
  have h_int_nonneg :
      0 ≤ ∫ u in (α / β)..1, (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 := by
    refine intervalIntegral.integral_nonneg hle1 fun u hu => ?_
    exact div_nonneg (hnonneg u hu) (sq_nonneg u)
  rw [intervalIntegral_alpha_div_beta_one_div_sq_dilationAutocorr hf hα hαβ hsupp hmean]
    at h_int_nonneg
  exact eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos hf hα hαβ hsupp
    (by linarith) y

/-- **Dual cumulative autocorrelation sign-change rigidity on `[1, β/α]`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
and `∫ r in 0..u, A_f(r) dr ≤ 0` for all `u ∈ [1, β/α]`, then `f = 0` everywhere. -/
theorem eq_zero_of_intervalIntegral_dilationAutocorr_nonpos_on_Icc (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hnonpos : ∀ u ∈ Icc 1 (β / α), ∫ r in (0 : ℝ)..u, dilationAutocorr f r ≤ 0)
    (y : ℝ) : f y = 0 := by
  have hle1 : 1 ≤ β / α := (one_le_div hα).mpr hαβ
  have h_int_nonneg :
      0 ≤ ∫ u in (1 : ℝ)..(β / α), -((∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) := by
    refine intervalIntegral.integral_nonneg hle1 fun u hu => ?_
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (hnonpos u hu) (sq_nonneg u))
  rw [intervalIntegral.integral_neg,
    intervalIntegral_one_beta_div_alpha_div_sq_dilationAutocorr hf hα hαβ hsupp hmean]
    at h_int_nonneg
  exact eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos hf hα hαβ hsupp
    (by linarith) y

/-! ### Quarter-period cumulative unfolding for blind cores with `β ≤ (11/4) α` -/

/-- **Pointwise four-term collapse of the periodization on `[0, 1/4]` for `β ≤ (11/4) α`.**
If `f` is continuous and supported in `[α, β]` with `0 < α ≤ β ≤ (11/4) α`, then for every
`x ∈ [0, 1/4]`, the `k = 0` term and all `|k| ≥ 3` terms vanish, so
`Σ_{k ∈ ℤ} A_f(|x + k|) = A_f(1 - x) + A_f(1 + x) + A_f(2 - x) + A_f(2 + x)`. -/
theorem tsum_dilationAutocorr_abs_eq_four_terms_on_zero_quarter (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 11 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    (∑' k : ℤ, dilationAutocorr f |x + (k : ℝ)|) =
      dilationAutocorr f (1 - x) + dilationAutocorr f (1 + x) +
        dilationAutocorr f (2 - x) + dilationAutocorr f (2 + x) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 11 / 4 := by rw [div_le_iff₀ hα]; linarith
  have hlo : 4 / 11 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hZ : ∀ r : ℝ, (r ≤ 1 / 4 ∨ 11 / 4 ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  rw [tsum_eq_sum (s := ({-2, -1, 1, 2} : Finset ℤ)) fun k hk => ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have h_m2 : |x + ((-2 : ℤ) : ℝ)| = 2 - x := by
      push_cast; rw [abs_of_neg (by linarith)]; ring
    have h_m1 : |x + ((-1 : ℤ) : ℝ)| = 1 - x := by
      push_cast; rw [abs_of_neg (by linarith)]; ring
    have h_p1 : |x + ((1 : ℤ) : ℝ)| = 1 + x := by
      push_cast; rw [abs_of_pos (by linarith)]; ring
    have h_p2 : |x + ((2 : ℤ) : ℝ)| = 2 + x := by
      push_cast; rw [abs_of_pos (by linarith)]; ring
    rw [h_m2, h_m1, h_p1, h_p2]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    refine hZ |x + (k : ℝ)| ?_
    by_cases hk0 : k = 0
    · left
      subst hk0
      simp only [Int.cast_zero, add_zero, abs_of_nonneg hx0]
      exact hx1
    · right
      rcases le_or_gt 3 k with hk3 | hk3
      · have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
        rw [abs_of_pos (by linarith)]
        linarith
      · have hk_le : k ≤ -3 := by omega
        have : (k : ℝ) ≤ -3 := by exact_mod_cast hk_le
        rw [abs_of_neg (by linarith)]
        linarith

/-- **Two-window cumulative unfolding of `Ψ_f(1) / π` for blind cores with `β ≤ (11/4) α`.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β ≤ (11/4) α`) with
`Ψ_f(0) = 0`, then
`Ψ_f(1) / π = (∫ r in 3/4..5/4, A_f(r) dr) + (∫ r in 7/4..9/4, A_f(r) dr)`. -/
theorem cosDilationKernel_one_div_pi_eq_intervalIntegral_of_le_eleven_fourths
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 11 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    cosDilationKernel f 1 / π =
      (∫ r in (3 / 4 : ℝ)..(5 / 4), dilationAutocorr f r) +
        (∫ r in (7 / 4 : ℝ)..(9 / 4), dilationAutocorr f r) := by
  have hQ := (intervalIntegral_zero_quarter_tsum_dilationAutocorr_abs hf hα hαβ hsupp h0 hblind).symm
  rw [hQ]
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have h_congr : ∫ x in (0 : ℝ)..(1 / 4), (∑' k : ℤ, dilationAutocorr f |x + (k : ℝ)|) =
      ∫ x in (0 : ℝ)..(1 / 4),
        ((dilationAutocorr f (1 - x) + dilationAutocorr f (1 + x)) +
          (dilationAutocorr f (2 - x) + dilationAutocorr f (2 + x))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hx
    rw [tsum_dilationAutocorr_abs_eq_four_terms_on_zero_quarter hf hα hαβ hβ hsupp hx.1 hx.2]
    ring
  rw [h_congr]
  have hi1m : IntervalIntegrable (fun x => dilationAutocorr f (1 - x)) volume 0 (1 / 4) :=
    (hA_cont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hi1p : IntervalIntegrable (fun x => dilationAutocorr f (1 + x)) volume 0 (1 / 4) :=
    (hA_cont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hi2m : IntervalIntegrable (fun x => dilationAutocorr f (2 - x)) volume 0 (1 / 4) :=
    (hA_cont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hi2p : IntervalIntegrable (fun x => dilationAutocorr f (2 + x)) volume 0 (1 / 4) :=
    (hA_cont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi1m.add hi1p) (hi2m.add hi2p),
    intervalIntegral.integral_add hi1m hi1p,
    intervalIntegral.integral_add hi2m hi2p]
  have h1m : ∫ x in (0 : ℝ)..(1 / 4), dilationAutocorr f (1 - x) =
      ∫ r in (3 / 4 : ℝ)..1, dilationAutocorr f r := by
    rw [intervalIntegral.integral_comp_sub_left (dilationAutocorr f) 1]
    norm_num
  have h1p : ∫ x in (0 : ℝ)..(1 / 4), dilationAutocorr f (1 + x) =
      ∫ r in (1 : ℝ)..(5 / 4), dilationAutocorr f r := by
    have h_eq : (fun x : ℝ => dilationAutocorr f (1 + x)) =
        fun x : ℝ => dilationAutocorr f (x + 1) := by funext x; ring_nf
    rw [h_eq, intervalIntegral.integral_comp_add_right (dilationAutocorr f) 1]
    norm_num
  have h2m : ∫ x in (0 : ℝ)..(1 / 4), dilationAutocorr f (2 - x) =
      ∫ r in (7 / 4 : ℝ)..2, dilationAutocorr f r := by
    rw [intervalIntegral.integral_comp_sub_left (dilationAutocorr f) 2]
    norm_num
  have h2p : ∫ x in (0 : ℝ)..(1 / 4), dilationAutocorr f (2 + x) =
      ∫ r in (2 : ℝ)..(9 / 4), dilationAutocorr f r := by
    have h_eq : (fun x : ℝ => dilationAutocorr f (2 + x)) =
        fun x : ℝ => dilationAutocorr f (x + 2) := by funext x; ring_nf
    rw [h_eq, intervalIntegral.integral_comp_add_right (dilationAutocorr f) 2]
    norm_num
  rw [h1m, h1p, h2m, h2p,
    intervalIntegral.integral_add_adjacent_intervals (hA_cont.intervalIntegrable _ _)
      (hA_cont.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hA_cont.intervalIntegrable _ _)
      (hA_cont.intervalIntegrable _ _)]

end

end RHTower
