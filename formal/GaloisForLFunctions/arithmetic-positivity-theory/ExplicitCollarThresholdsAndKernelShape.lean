import GaloisForLFunctions.«arithmetic-positivity-theory».ExplicitBlockThresholdsOfTheCriticalFamily
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeToeplitzSymbolRange
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare

/-!
# Explicit collar thresholds and the exact shape of the critical prime kernel

This module resolves two structural questions of the critical factorial theory:

1. **Explicit collar integrals, channel constants and block thresholds.**
   We compute and bound the first and second derivatives of the smooth transition
   `σ = Real.smoothTransition` on `ℝ` (`0 ≤ σ' ≤ 4`, `|σ''| ≤ 95`), establish the exact mass
   conservation laws `criticalCollarMass + ∫_{v>1} |φ_e| = 1` and
   `criticalCollarMass + criticalEndpointMass = 2`, prove `|φ_e'(1)| = 2`, and derive explicit
   numerical bounds on the collar and endpoint integrals `∫ |ψ'|`, `∫ |ρ'|`, `∫ |ψ''|`, `∫_1^2 |φ_e''|`,
   the prime majorant `∑_r Λ(r) r^{-3/2}`, all channel constants (`criticalCollaredPrimeConstant`,
   `criticalPrimeChannelConstant`, `criticalCompleteChannelConstant`,
   `criticalCollaredChannelConstant`, `criticalWindowPrimeSlope`), the polynomial window exponent
   `criticalWindowExponent`, and the block thresholds (`criticalBlockThreshold`,
   `criticalCollaredBlockThreshold`, `criticalWindowThreshold`).

2. **Exact shape, monotonicity, extrema and first scale couplings of the critical kernel `R`.**
   We evaluate the band sine moments `μ_m = ∫₀^{π/6} (π/6 - ξ) ξ sin(mξ) dξ` in closed form,
   bound the spectral curvature constant `I₀ = ∑_m (A(m)/m³) μ_m > 0`, prove two-sided `1/k²`
   asymptotics and explicit numerical bounds for the scale couplings `κ(k)` (`k ≥ 1`, in
   particular `κ(1)` and `κ(2)`), establish quadratic difference bounds for `R(t₁) - R(t₂)` on
   `[0, 1/2]`, deduce that `R` is strictly decreasing on `[0, 1/2]` and strictly increasing on
   `[1/2, 1]`, and identify the exact global maximum `max_{[0,1]} R = R(0) = R(1)`, the exact
   global minimum `min_{[0,1]} R = R(1/2)`, their unique locations, their distances from the
   singleton mean `κ(0)`, and the exact Rayleigh spectral range `[(4/π⁴) R(1/2), (4/π⁴) R(0)]`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositivityTheory

set_option autoImplicit false

/-! ## Section 1: Explicit derivative and curvature bounds of `Real.smoothTransition` -/

private theorem expNegInvGlue_eq_of_pos {x : ℝ} (hx : 0 < x) :
    expNegInvGlue x = Real.exp (-x⁻¹) := by
  unfold expNegInvGlue
  exact if_neg (not_le.mpr hx)

private theorem hasDerivAt_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y⁻¹))
      (Real.exp (-x⁻¹) * - -(x ^ 2)⁻¹) x :=
    ((hasDerivAt_inv hx.ne').neg).exp
  have h2 : expNegInvGlue =ᶠ[𝓝 x] fun y : ℝ => Real.exp (-y⁻¹) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact expNegInvGlue_eq_of_pos hy
  refine (h1.congr_of_eventuallyEq h2).congr_deriv ?_
  rw [expNegInvGlue_eq_of_pos hx, inv_pow]
  ring

private theorem deriv_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x :=
  (hasDerivAt_expNegInvGlue_of_pos hx).deriv

private theorem deriv_expNegInvGlue_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv expNegInvGlue x = 0 := by
  have hcont : Continuous (deriv expNegInvGlue) :=
    (contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).2.continuous
  have hclosed : IsClosed {y : ℝ | deriv expNegInvGlue y = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : Iio (0 : ℝ) ⊆ {y : ℝ | deriv expNegInvGlue y = 0} := fun y hy => by
    have heq : expNegInvGlue =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact expNegInvGlue.zero_of_nonpos (le_of_lt hz)
    simp only [mem_setOf_eq, heq.deriv_eq, deriv_const]
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Iio' nonempty_Iio] at hcl
  exact hcl hx

private theorem hasDerivAt_deriv_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv expNegInvGlue) ((x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x) x := by
  have h1' : HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x := by
    refine ((hasDerivAt_inv hx.ne').pow 2).congr_deriv ?_
    simp only [inv_pow]
    ring
  have h2 := hasDerivAt_expNegInvGlue_of_pos hx
  have h3 : deriv expNegInvGlue =ᶠ[𝓝 x]
      (fun y : ℝ => y⁻¹ ^ 2) * expNegInvGlue := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_expNegInvGlue_of_pos hy
  refine ((h1'.mul h2).congr_of_eventuallyEq h3).congr_deriv ?_
  ring

private theorem deriv_deriv_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    deriv (deriv expNegInvGlue) x = (x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x :=
  (hasDerivAt_deriv_expNegInvGlue_of_pos hx).deriv

private theorem deriv_deriv_expNegInvGlue_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv (deriv expNegInvGlue) x = 0 := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (deriv expNegInvGlue) :=
    (contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).2
  have hcont : Continuous (deriv (deriv expNegInvGlue)) :=
    (contDiff_infty_iff_deriv.mp hcd).2.continuous
  have hclosed : IsClosed {y : ℝ | deriv (deriv expNegInvGlue) y = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : Iio (0 : ℝ) ⊆ {y : ℝ | deriv (deriv expNegInvGlue) y = 0} := fun y hy => by
    have heq : deriv expNegInvGlue =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact deriv_expNegInvGlue_of_nonpos (le_of_lt hz)
    simp only [mem_setOf_eq, heq.deriv_eq, deriv_const]
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Iio' nonempty_Iio] at hcl
  exact hcl hx

private theorem pow_mul_exp_neg_le (k : ℕ) (hk : 0 < k) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-u) ≤ (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : u / k ≤ Real.exp (u / k - 1) := by
    have := Real.add_one_le_exp (u / k - 1)
    linarith
  have h2 : (u / k) ^ k ≤ Real.exp (u / k - 1) ^ k :=
    pow_le_pow_left₀ (by positivity) h1 k
  rw [div_pow, ← Real.exp_nat_mul] at h2
  have h3 : (k : ℝ) * (u / k - 1) = u - k := by field_simp
  rw [h3, div_le_iff₀ (by positivity)] at h2
  have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-u)).le
  rwa [mul_comm (Real.exp (u - k)), mul_assoc, ← Real.exp_add,
    show u - (k : ℝ) + -u = -(k : ℝ) by ring] at h4

private theorem deriv_expNegInvGlue_bounds (x : ℝ) :
    0 ≤ deriv expNegInvGlue x ∧ deriv expNegInvGlue x ≤ 4 * Real.exp (-2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv_expNegInvGlue_of_nonpos hx]
    exact ⟨le_rfl, by positivity⟩
  · rw [deriv_expNegInvGlue_of_pos hx, expNegInvGlue_eq_of_pos hx]
    refine ⟨by positivity, ?_⟩
    have h := pow_mul_exp_neg_le 2 (by norm_num) (inv_nonneg.mpr hx.le)
    have h4 : ((2 : ℕ) : ℝ) ^ 2 * Real.exp (-((2 : ℕ) : ℝ)) = 4 * Real.exp (-2) := by norm_num
    rwa [h4] at h

private theorem abs_deriv_deriv_expNegInvGlue_le (x : ℝ) :
    |deriv (deriv expNegInvGlue) x| ≤ 63 * Real.exp (-2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv_deriv_expNegInvGlue_of_nonpos hx, abs_zero]
    positivity
  · rw [deriv_deriv_expNegInvGlue_of_pos hx, expNegInvGlue_eq_of_pos hx]
    set u := x⁻¹
    have hu : 0 ≤ u := inv_nonneg.mpr hx.le
    have h3 := pow_mul_exp_neg_le 3 (by norm_num) hu
    have h4 := pow_mul_exp_neg_le 4 (by norm_num) hu
    norm_num at h3 h4
    have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hinv : (Real.exp 1)⁻¹ ≤ 1 / 2.71 := by
      rw [one_div]
      exact inv_anti₀ (by positivity) he1
    have he3 : (27 : ℝ) * Real.exp (-3) ≤ 14 * Real.exp (-2) := by
      have : Real.exp (-3 : ℝ) = Real.exp (-2) * (Real.exp 1)⁻¹ := by
        rw [← Real.exp_neg, ← Real.exp_add]; norm_num
      rw [this]
      nlinarith [Real.exp_pos (-2)]
    have he4 : (256 : ℝ) * Real.exp (-4) ≤ 35 * Real.exp (-2) := by
      have : Real.exp (-4 : ℝ) = Real.exp (-2) * ((Real.exp 1)⁻¹) ^ 2 := by
        rw [← Real.exp_neg, sq, ← Real.exp_add, ← Real.exp_add]; norm_num
      rw [this]
      have hsq : ((Real.exp 1)⁻¹) ^ 2 ≤ 35 / 256 :=
        (pow_le_pow_left₀ (by positivity) hinv 2).trans (by norm_num)
      nlinarith [Real.exp_pos (-2)]
    rw [abs_mul, abs_of_pos (Real.exp_pos (-u))]
    have htri : |u ^ 4 - 2 * u ^ 3| ≤ u ^ 4 + 2 * u ^ 3 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    calc |u ^ 4 - 2 * u ^ 3| * Real.exp (-u)
        ≤ (u ^ 4 + 2 * u ^ 3) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right htri (Real.exp_pos (-u)).le
      _ = u ^ 4 * Real.exp (-u) + 2 * (u ^ 3 * Real.exp (-u)) := by ring
      _ ≤ 35 * Real.exp (-2) + 2 * (14 * Real.exp (-2)) := by linarith
      _ = 63 * Real.exp (-2) := by ring

private def smoothTransitionDenom (x : ℝ) : ℝ :=
  expNegInvGlue x + expNegInvGlue (1 - x)

private theorem smoothTransitionDenom_ge (x : ℝ) :
    Real.exp (-2) ≤ smoothTransitionDenom x := by
  unfold smoothTransitionDenom
  have hhalf : expNegInvGlue (1 / 2) = Real.exp (-2) := by
    rw [expNegInvGlue_eq_of_pos (by norm_num)]
    norm_num
  rcases le_total x (1 / 2) with hx | hx
  · have h1 : expNegInvGlue (1 / 2) ≤ expNegInvGlue (1 - x) :=
      expNegInvGlue.monotone (by linarith)
    have h0 : 0 ≤ expNegInvGlue x := expNegInvGlue.nonneg x
    linarith
  · have h1 : expNegInvGlue (1 / 2) ≤ expNegInvGlue x :=
      expNegInvGlue.monotone hx
    have h0 : 0 ≤ expNegInvGlue (1 - x) := expNegInvGlue.nonneg (1 - x)
    linarith

private theorem smoothTransitionDenom_pos (x : ℝ) :
    0 < smoothTransitionDenom x :=
  (Real.exp_pos (-2)).trans_le (smoothTransitionDenom_ge x)

private theorem smoothTransition_mul_denom (x : ℝ) :
    Real.smoothTransition x * smoothTransitionDenom x = expNegInvGlue x := by
  change (expNegInvGlue x / smoothTransitionDenom x) * smoothTransitionDenom x = expNegInvGlue x
  exact div_mul_cancel₀ _ (smoothTransitionDenom_pos x).ne'

private theorem hasDerivAt_expNegInvGlue (x : ℝ) :
    HasDerivAt expNegInvGlue (deriv expNegInvGlue x) x :=
  ((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) x).hasDerivAt

private theorem hasDerivAt_deriv_expNegInvGlue (x : ℝ) :
    HasDerivAt (deriv expNegInvGlue) (deriv (deriv expNegInvGlue) x) x :=
  (((contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).2).differentiable (by simp) x).hasDerivAt

private theorem hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) x).hasDerivAt

private theorem hasDerivAt_deriv_smoothTransition (x : ℝ) :
    HasDerivAt (deriv Real.smoothTransition) (deriv (deriv Real.smoothTransition) x) x :=
  (((contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2).differentiable
    (by simp) x).hasDerivAt

private theorem hasDerivAt_smoothTransitionDenom (x : ℝ) :
    HasDerivAt smoothTransitionDenom
      (deriv expNegInvGlue x - deriv expNegInvGlue (1 - x)) x := by
  unfold smoothTransitionDenom
  have h1 := hasDerivAt_expNegInvGlue x
  have h2 := (hasDerivAt_expNegInvGlue (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  exact (h1.add h2).congr_deriv (by ring)

private theorem deriv_smoothTransition_mul_denom (x : ℝ) :
    deriv Real.smoothTransition x * smoothTransitionDenom x =
      (1 - Real.smoothTransition x) * deriv expNegInvGlue x +
        Real.smoothTransition x * deriv expNegInvGlue (1 - x) := by
  have hlhs := (hasDerivAt_smoothTransition x).mul (hasDerivAt_smoothTransitionDenom x)
  have hrhs : HasDerivAt (Real.smoothTransition * smoothTransitionDenom)
      (deriv expNegInvGlue x) x :=
    (hasDerivAt_expNegInvGlue x).congr_of_eventuallyEq
      (Eventually.of_forall fun y => smoothTransition_mul_denom y)
  have heq := hlhs.unique hrhs
  linarith

/-- **Explicit first-derivative bounds of the smooth transition.** For every `x ∈ ℝ`,
`0 ≤ σ'(x) ≤ 4`. -/
theorem deriv_smoothTransition_bounds (x : ℝ) :
    0 ≤ deriv Real.smoothTransition x ∧ deriv Real.smoothTransition x ≤ 4 := by
  have hD := smoothTransitionDenom_ge x
  have hD0 := smoothTransitionDenom_pos x
  have hσ0 := Real.smoothTransition.nonneg x
  have hσ1 : 0 ≤ 1 - Real.smoothTransition x := sub_nonneg.mpr (Real.smoothTransition.le_one x)
  have hf1 := deriv_expNegInvGlue_bounds x
  have hf2 := deriv_expNegInvGlue_bounds (1 - x)
  have hid := deriv_smoothTransition_mul_denom x
  constructor
  · have hprod : 0 ≤ deriv Real.smoothTransition x * smoothTransitionDenom x := by
      rw [hid]
      exact add_nonneg (mul_nonneg hσ1 hf1.1) (mul_nonneg hσ0 hf2.1)
    exact nonneg_of_mul_nonneg_left hprod hD0
  · have hprod : deriv Real.smoothTransition x * smoothTransitionDenom x ≤
        4 * smoothTransitionDenom x := by
      calc deriv Real.smoothTransition x * smoothTransitionDenom x
          = (1 - Real.smoothTransition x) * deriv expNegInvGlue x +
              Real.smoothTransition x * deriv expNegInvGlue (1 - x) := hid
        _ ≤ (1 - Real.smoothTransition x) * (4 * Real.exp (-2)) +
              Real.smoothTransition x * (4 * Real.exp (-2)) := by
            gcongr
            · exact hf1.2
            · exact hf2.2
        _ = 4 * Real.exp (-2) := by ring
        _ ≤ 4 * smoothTransitionDenom x := by linarith
    exact le_of_mul_le_mul_right hprod hD0

theorem abs_deriv_smoothTransition_le_four (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ 4 := by
  obtain ⟨h0, h4⟩ := deriv_smoothTransition_bounds x
  rw [abs_of_nonneg h0]
  exact h4

private theorem deriv_deriv_smoothTransition_mul_denom (x : ℝ) :
    deriv (deriv Real.smoothTransition) x * smoothTransitionDenom x =
      (1 - Real.smoothTransition x) * deriv (deriv expNegInvGlue) x -
        Real.smoothTransition x * deriv (deriv expNegInvGlue) (1 - x) -
        2 * deriv Real.smoothTransition x *
          (deriv expNegInvGlue x - deriv expNegInvGlue (1 - x)) := by
  have h1 := (hasDerivAt_deriv_smoothTransition x).mul (hasDerivAt_smoothTransitionDenom x)
  have h2a := ((hasDerivAt_smoothTransition x).const_sub 1).mul (hasDerivAt_deriv_expNegInvGlue x)
  have h2b := (hasDerivAt_smoothTransition x).mul
    ((hasDerivAt_deriv_expNegInvGlue (1 - x)).comp x ((hasDerivAt_id x).const_sub 1))
  have h2 : HasDerivAt (deriv Real.smoothTransition * smoothTransitionDenom)
      (-(deriv Real.smoothTransition x) * deriv expNegInvGlue x +
        (1 - Real.smoothTransition x) * deriv (deriv expNegInvGlue) x +
        (deriv Real.smoothTransition x * deriv expNegInvGlue (1 - x) +
          Real.smoothTransition x * (deriv (deriv expNegInvGlue) (1 - x) * -1))) x :=
    (h2a.add h2b).congr_of_eventuallyEq (Eventually.of_forall fun y => by
      simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply]
      exact deriv_smoothTransition_mul_denom y)
  have heq := h1.unique h2
  linarith

/-- **Explicit second-derivative bound of the smooth transition.** For every `x ∈ ℝ`,
`|σ''(x)| ≤ 95`. -/
theorem abs_deriv_deriv_smoothTransition_le_ninetyFive (x : ℝ) :
    |deriv (deriv Real.smoothTransition) x| ≤ 95 := by
  have hD := smoothTransitionDenom_ge x
  have hD0 := smoothTransitionDenom_pos x
  have hσ0 := Real.smoothTransition.nonneg x
  have hσ1 : 0 ≤ 1 - Real.smoothTransition x := sub_nonneg.mpr (Real.smoothTransition.le_one x)
  obtain ⟨hd0, hd4⟩ := deriv_smoothTransition_bounds x
  obtain ⟨hf10, hf14⟩ := deriv_expNegInvGlue_bounds x
  obtain ⟨hf20, hf24⟩ := deriv_expNegInvGlue_bounds (1 - x)
  have hff1 := abs_deriv_deriv_expNegInvGlue_le x
  have hff2 := abs_deriv_deriv_expNegInvGlue_le (1 - x)
  have hid := deriv_deriv_smoothTransition_mul_denom x
  have hdiff : |deriv expNegInvGlue x - deriv expNegInvGlue (1 - x)| ≤ 4 * Real.exp (-2) := by
    rw [abs_le]
    constructor <;> linarith
  have hprod : |deriv (deriv Real.smoothTransition) x| * smoothTransitionDenom x ≤
      95 * smoothTransitionDenom x := by
    have habs_lhs : |deriv (deriv Real.smoothTransition) x| * smoothTransitionDenom x =
        |deriv (deriv Real.smoothTransition) x * smoothTransitionDenom x| := by
      rw [abs_mul, abs_of_pos hD0]
    rw [habs_lhs, hid]
    have htri1 := abs_sub
      ((1 - Real.smoothTransition x) * deriv (deriv expNegInvGlue) x -
        Real.smoothTransition x * deriv (deriv expNegInvGlue) (1 - x))
      (2 * deriv Real.smoothTransition x *
        (deriv expNegInvGlue x - deriv expNegInvGlue (1 - x)))
    have htri2 := abs_sub
      ((1 - Real.smoothTransition x) * deriv (deriv expNegInvGlue) x)
      (Real.smoothTransition x * deriv (deriv expNegInvGlue) (1 - x))
    rw [abs_mul, abs_of_nonneg hσ1, abs_mul, abs_of_nonneg hσ0] at htri2
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hd0] at htri1
    have hpart1 : (1 - Real.smoothTransition x) * |deriv (deriv expNegInvGlue) x| +
        Real.smoothTransition x * |deriv (deriv expNegInvGlue) (1 - x)| ≤
        63 * Real.exp (-2) := by
      calc (1 - Real.smoothTransition x) * |deriv (deriv expNegInvGlue) x| +
            Real.smoothTransition x * |deriv (deriv expNegInvGlue) (1 - x)|
          ≤ (1 - Real.smoothTransition x) * (63 * Real.exp (-2)) +
            Real.smoothTransition x * (63 * Real.exp (-2)) := by gcongr
        _ = 63 * Real.exp (-2) := by ring
    have hpart2 : 2 * deriv Real.smoothTransition x *
        |deriv expNegInvGlue x - deriv expNegInvGlue (1 - x)| ≤ 32 * Real.exp (-2) := by
      nlinarith [abs_nonneg (deriv expNegInvGlue x - deriv expNegInvGlue (1 - x))]
    linarith
  exact le_of_mul_le_mul_right hprod hD0

/-! ## Section 2: Collar and endpoint weight integrals and conservation laws -/

theorem criticalCollarWeight_nonneg (v : ℝ) : 0 ≤ criticalCollarWeight v :=
  div_nonneg (Real.smoothTransition.nonneg _) (sq_nonneg _)

theorem criticalEndpointWeight_nonneg (v : ℝ) : 0 ≤ criticalEndpointWeight v :=
  div_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _)) (sq_nonneg _)

theorem criticalCollarWeight_le_one {v : ℝ} (hv : 1 ≤ v) : criticalCollarWeight v ≤ 1 := by
  unfold criticalCollarWeight
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  exact (div_le_one (by positivity)).mpr ((Real.smoothTransition.le_one _).trans hv2)

private theorem integral_Ioi_rpow_neg_two {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi a, v ^ (-2 : ℝ) = a⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
  have : (-2 : ℝ) + 1 = -1 := by ring
  rw [this, Real.rpow_neg_one]
  ring

/-- **Exact collar–endpoint mass conservation.** The `L¹` norms of the collar weight `ψ` and the
endpoint weight `φ_e` on `(1, ∞)` sum to `∫_1^∞ v⁻² dv = 1`. -/
theorem criticalCollarMass_add_integral_criticalEndpointWeight :
    criticalCollarMass + ∫ v in Ioi 1, |criticalEndpointWeight v| = 1 := by
  unfold criticalCollarMass
  rw [← integral_add integrableOn_criticalCollarWeight.abs integrableOn_criticalEndpointWeight.abs]
  have hcongr : ∀ v ∈ Ioi (1 : ℝ),
      |criticalCollarWeight v| + |criticalEndpointWeight v| = v ^ (-2 : ℝ) := fun v hv => by
    rw [abs_of_nonneg (criticalCollarWeight_nonneg v),
      abs_of_nonneg (criticalEndpointWeight_nonneg v),
      criticalCollarWeight_add_criticalEndpointWeight (lt_trans zero_lt_one hv)]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_rpow_neg_two one_pos, inv_one]

/-- **Total mass conservation.** `criticalCollarMass + criticalEndpointMass = 2`. -/
theorem criticalCollarMass_add_criticalEndpointMass :
    criticalCollarMass + criticalEndpointMass = 2 := by
  unfold criticalEndpointMass
  linarith [criticalCollarMass_add_integral_criticalEndpointWeight]

/-- **Explicit collar mass bounds.** `1/2 ≤ criticalCollarMass ≤ 1`. -/
theorem criticalCollarMass_bounds :
    1 / 2 ≤ criticalCollarMass ∧ criticalCollarMass ≤ 1 := by
  constructor
  · unfold criticalCollarMass
    have hsub : ∫ v in Ioi (2 : ℝ), |criticalCollarWeight v| ≤
        ∫ v in Ioi (1 : ℝ), |criticalCollarWeight v| :=
      setIntegral_mono_set integrableOn_criticalCollarWeight.abs
        (Eventually.of_forall fun _ => abs_nonneg _)
        (LE.le.eventuallyLE (Ioi_subset_Ioi one_le_two))
    have heq : ∫ v in Ioi (2 : ℝ), |criticalCollarWeight v| = 1 / 2 := by
      have hc : ∀ v ∈ Ioi (2 : ℝ), |criticalCollarWeight v| = v ^ (-2 : ℝ) := fun v hv => by
        rw [abs_of_nonneg (criticalCollarWeight_nonneg v),
          criticalCollarWeight_eq_of_two_le (le_of_lt hv), one_mul,
          ← Real.rpow_intCast v (-2)]
        norm_num
      rw [setIntegral_congr_fun measurableSet_Ioi hc, integral_Ioi_rpow_neg_two two_pos]
      norm_num
    linarith
  · have h0 : 0 ≤ ∫ v in Ioi 1, |criticalEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    linarith [criticalCollarMass_add_integral_criticalEndpointWeight]

/-- **Explicit endpoint mass bounds.** `1 ≤ criticalEndpointMass ≤ 3/2`. -/
theorem criticalEndpointMass_bounds :
    1 ≤ criticalEndpointMass ∧ criticalEndpointMass ≤ 3 / 2 := by
  obtain ⟨h1, h2⟩ := criticalCollarMass_bounds
  have hsum := criticalCollarMass_add_criticalEndpointMass
  have h0 : 0 ≤ ∫ v in Ioi 1, |criticalEndpointWeight v| :=
    integral_nonneg fun _ => abs_nonneg _
  unfold criticalEndpointMass at hsum ⊢
  constructor <;> linarith

private theorem criticalCollarWeight_mul_sq {v : ℝ} (hv : v ≠ 0) :
    criticalCollarWeight v * v ^ 2 = Real.smoothTransition (v - 1) :=
  div_mul_cancel₀ _ (pow_ne_zero 2 hv)

private theorem deriv_criticalCollarWeight_mul_sq {v : ℝ} (hv : 0 < v) :
    deriv criticalCollarWeight v * v ^ 2 + criticalCollarWeight v * (2 * v) =
      deriv Real.smoothTransition (v - 1) := by
  have h1 := (hasDerivAt_criticalCollarWeight v).mul (hasDerivAt_pow 2 v)
  have h2 := ((hasDerivAt_smoothTransition (v - 1)).comp v
    ((hasDerivAt_id v).sub_const 1)).congr_deriv (by ring)
  have h3 : (Real.smoothTransition ∘ fun x => x - 1) =ᶠ[𝓝 v]
      criticalCollarWeight * fun x => x ^ 2 := by
    filter_upwards [Ioi_mem_nhds hv] with y hy
    simp only [Function.comp_apply, Pi.mul_apply]
    exact (criticalCollarWeight_mul_sq hy.ne').symm
  have heq := (h1.congr_of_eventuallyEq h3).unique h2
  norm_num at heq
  linarith

private theorem deriv_deriv_criticalCollarWeight_mul_sq {v : ℝ} (hv : 0 < v) :
    deriv (deriv criticalCollarWeight) v * v ^ 2 +
      4 * v * deriv criticalCollarWeight v + 2 * criticalCollarWeight v =
      deriv (deriv Real.smoothTransition) (v - 1) := by
  have h1a := (hasDerivAt_deriv_criticalCollarWeight v).mul (hasDerivAt_pow 2 v)
  have h1b := (hasDerivAt_criticalCollarWeight v).mul ((hasDerivAt_id v).const_mul 2)
  have h1 := h1a.add h1b
  have h2 := ((hasDerivAt_deriv_smoothTransition (v - 1)).comp v
    ((hasDerivAt_id v).sub_const 1)).congr_deriv (by ring)
  have h3 : (deriv Real.smoothTransition ∘ fun x => x - 1) =ᶠ[𝓝 v]
      (deriv criticalCollarWeight * fun x => x ^ 2) +
        criticalCollarWeight * fun y => 2 * id y := by
    filter_upwards [Ioi_mem_nhds hv] with y hy
    simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, id_eq]
    exact (deriv_criticalCollarWeight_mul_sq hy).symm
  have heq := (h1.congr_of_eventuallyEq h3).unique h2
  simp only [id_eq] at heq
  norm_num at heq
  linarith

theorem abs_deriv_criticalCollarWeight_le {v : ℝ} (hv : 1 ≤ v) :
    |deriv criticalCollarWeight v| ≤ 4 ∧ |v * deriv criticalCollarWeight v| ≤ 4 := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hid := deriv_criticalCollarWeight_mul_sq hv0
  obtain ⟨hσ0, hσ4⟩ := deriv_smoothTransition_bounds (v - 1)
  have hψ0 : 0 ≤ criticalCollarWeight v * (2 * v) :=
    mul_nonneg (criticalCollarWeight_nonneg v) (by positivity)
  have hψ2 : criticalCollarWeight v * (2 * v) ≤ 2 := by
    rw [criticalCollarWeight]
    have : Real.smoothTransition (v - 1) / v ^ 2 * (2 * v) =
        2 * Real.smoothTransition (v - 1) / v := by field_simp
    rw [this, div_le_iff₀ hv0]
    have := Real.smoothTransition.le_one (v - 1)
    linarith
  have hsq : |deriv criticalCollarWeight v| * v ^ 2 ≤ 4 := by
    have habs : |deriv criticalCollarWeight v| * v ^ 2 =
        |deriv criticalCollarWeight v * v ^ 2| := by
      rw [abs_mul, abs_of_pos (pow_pos hv0 2)]
    rw [habs, abs_le]
    constructor <;> linarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  constructor
  · nlinarith [abs_nonneg (deriv criticalCollarWeight v)]
  · rw [abs_mul, abs_of_pos hv0]
    have : v ≤ v ^ 2 := by nlinarith
    nlinarith [abs_nonneg (deriv criticalCollarWeight v)]

theorem abs_deriv_deriv_criticalCollarWeight_le {v : ℝ} (hv : 1 ≤ v) :
    |deriv (deriv criticalCollarWeight) v| ≤ 113 := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hid := deriv_deriv_criticalCollarWeight_mul_sq hv0
  have hσ := abs_deriv_deriv_smoothTransition_le_ninetyFive (v - 1)
  have hd := (abs_deriv_criticalCollarWeight_le hv).2
  have hψ := criticalCollarWeight_le_one hv
  have hψ0 := criticalCollarWeight_nonneg v
  have hsq : |deriv (deriv criticalCollarWeight) v| * v ^ 2 ≤ 113 := by
    have habs : |deriv (deriv criticalCollarWeight) v| * v ^ 2 =
        |deriv (deriv criticalCollarWeight) v * v ^ 2| := by
      rw [abs_mul, abs_of_pos (pow_pos hv0 2)]
    rw [habs]
    have heq : deriv (deriv criticalCollarWeight) v * v ^ 2 =
        deriv (deriv Real.smoothTransition) (v - 1) -
          4 * (v * deriv criticalCollarWeight v) - 2 * criticalCollarWeight v := by linarith
    rw [heq]
    have h1 := abs_sub
      (deriv (deriv Real.smoothTransition) (v - 1) - 4 * (v * deriv criticalCollarWeight v))
      (2 * criticalCollarWeight v)
    have h2 := abs_sub
      (deriv (deriv Real.smoothTransition) (v - 1))
      (4 * (v * deriv criticalCollarWeight v))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h2
    rw [abs_mul, abs_two, abs_of_nonneg hψ0] at h1
    linarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  nlinarith [abs_nonneg (deriv (deriv criticalCollarWeight) v)]

private theorem deriv_criticalCollarEndpointWeight_mul {v : ℝ} (hv : 0 < v) :
    deriv criticalCollarEndpointWeight v * v + criticalCollarEndpointWeight v =
      deriv Real.smoothTransition (v - 1) := by
  have h1 := (hasDerivAt_criticalCollarEndpointWeight v).mul (hasDerivAt_id v)
  have h2 := ((hasDerivAt_smoothTransition (v - 1)).comp v
    ((hasDerivAt_id v).sub_const 1)).congr_deriv (by ring)
  have h3 : (Real.smoothTransition ∘ fun x => x - 1) =ᶠ[𝓝 v]
      criticalCollarEndpointWeight * id := by
    filter_upwards [Ioi_mem_nhds hv] with y hy
    simp only [Function.comp_apply, Pi.mul_apply, id_eq]
    exact (div_mul_cancel₀ _ hy.ne').symm
  have heq := (h1.congr_of_eventuallyEq h3).unique h2
  simp only [id_eq] at heq
  linarith

theorem abs_deriv_criticalCollarEndpointWeight_le {v : ℝ} (hv : 1 ≤ v) :
    |deriv criticalCollarEndpointWeight v| ≤ 4 := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hid := deriv_criticalCollarEndpointWeight_mul hv0
  obtain ⟨hσ0, hσ4⟩ := deriv_smoothTransition_bounds (v - 1)
  have hρ0 : 0 ≤ criticalCollarEndpointWeight v :=
    div_nonneg (Real.smoothTransition.nonneg _) hv0.le
  have hρ1 : criticalCollarEndpointWeight v ≤ 1 :=
    (div_le_one hv0).mpr ((Real.smoothTransition.le_one _).trans hv)
  have hv_le : |deriv criticalCollarEndpointWeight v| * v ≤ 4 := by
    have habs : |deriv criticalCollarEndpointWeight v| * v =
        |deriv criticalCollarEndpointWeight v * v| := by
      rw [abs_mul, abs_of_pos hv0]
    rw [habs, abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg (deriv criticalCollarEndpointWeight v)]

private theorem deriv_criticalCollarWeight_two :
    deriv criticalCollarWeight 2 = -1 / 4 := by
  have hc : ContinuousAt (deriv criticalCollarWeight) 2 :=
    contDiff_deriv_criticalCollarWeight.continuous.continuousAt
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (2 : ℝ)))
  have h2 : Tendsto (deriv criticalCollarWeight) (𝓝[>] 2) (𝓝 (-1 / 4)) := by
    have hcont : ContinuousAt (fun x : ℝ => -2 * (x ^ 3)⁻¹) 2 :=
      continuousAt_const.mul ((continuous_pow 3).continuousAt.inv₀ (by norm_num))
    have hval : (-2 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ = -1 / 4 := by norm_num
    rw [← hval]
    refine (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (2 : ℝ)))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [deriv_criticalCollarWeight_of_two_lt hx, zpow_neg, show (3 : ℤ) = (3 : ℕ) by rfl,
      zpow_natCast]
  exact tendsto_nhds_unique h1 h2

private theorem setIntegral_Ioc_one_two_le_of_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 1 2))
    {C : ℝ} (hC : ∀ v ∈ Ioc (1 : ℝ) 2, f v ≤ C) :
    ∫ v in Ioc (1 : ℝ) 2, f v ≤ C := by
  calc ∫ v in Ioc (1 : ℝ) 2, f v
      ≤ ∫ _ in Ioc (1 : ℝ) 2, C :=
        setIntegral_mono_on hf (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc hC
    _ = C := by simp; ring

/-- **Explicit collar slope integral bound.** `∫_{v>1} |ψ'(v)| dv ≤ 17/4`. -/
theorem integral_abs_deriv_criticalCollarWeight_le :
    ∫ v in Ioi 1, |deriv criticalCollarWeight v| ≤ 17 / 4 := by
  have hint : IntegrableOn (fun v => |deriv criticalCollarWeight v|) (Ioi 1) :=
    integrableOn_deriv_criticalCollarWeight.abs
  have hi1 : IntegrableOn (fun v => |deriv criticalCollarWeight v|) (Ioc 1 2) :=
    IntegrableOn.mono_set hint Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (fun v => |deriv criticalCollarWeight v|) (Ioi 2) :=
    IntegrableOn.mono_set hint (Ioi_subset_Ioi one_le_two)
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2]
  have h1 : ∫ v in Ioc (1 : ℝ) 2, |deriv criticalCollarWeight v| ≤ 4 :=
    setIntegral_Ioc_one_two_le_of_le hi1
      fun v hv => (abs_deriv_criticalCollarWeight_le hv.1.le).1
  have h2 : ∫ v in Ioi (2 : ℝ), |deriv criticalCollarWeight v| = 1 / 4 := by
    have hcongr : ∀ v ∈ Ioi (2 : ℝ),
        |deriv criticalCollarWeight v| = -deriv criticalCollarWeight v := fun v hv => by
      have hd := deriv_criticalCollarWeight_of_two_lt hv
      have hneg : deriv criticalCollarWeight v ≤ 0 := by
        rw [hd]
        have : 0 ≤ (v : ℝ) ^ (-3 : ℤ) := zpow_nonneg (le_trans two_pos.le hv.le) (-3)
        linarith
      exact abs_of_nonpos hneg
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_neg,
      integral_Ioi_of_hasDerivAt_of_tendsto contDiff_criticalCollarWeight.continuous.continuousWithinAt
        (fun x _ => hasDerivAt_criticalCollarWeight x)
        (IntegrableOn.mono_set integrableOn_deriv_criticalCollarWeight (Ioi_subset_Ioi one_le_two))
        tendsto_criticalCollarWeight_atTop,
      criticalCollarWeight_eq_of_two_le le_rfl]
    norm_num
  linarith

/-- **Explicit endpoint-collar slope integral bound.** `∫_{v>1} |ρ'(v)| dv ≤ 9/2`. -/
theorem integral_abs_deriv_criticalCollarEndpointWeight_le :
    ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| ≤ 9 / 2 := by
  have hint : IntegrableOn (fun v => |deriv criticalCollarEndpointWeight v|) (Ioi 1) :=
    integrableOn_deriv_criticalCollarEndpointWeight.abs
  have hi1 : IntegrableOn (fun v => |deriv criticalCollarEndpointWeight v|) (Ioc 1 2) :=
    IntegrableOn.mono_set hint Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (fun v => |deriv criticalCollarEndpointWeight v|) (Ioi 2) :=
    IntegrableOn.mono_set hint (Ioi_subset_Ioi one_le_two)
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2]
  have h1 : ∫ v in Ioc (1 : ℝ) 2, |deriv criticalCollarEndpointWeight v| ≤ 4 :=
    setIntegral_Ioc_one_two_le_of_le hi1
      fun v hv => abs_deriv_criticalCollarEndpointWeight_le hv.1.le
  have h2 : ∫ v in Ioi (2 : ℝ), |deriv criticalCollarEndpointWeight v| = 1 / 2 := by
    have hcongr : ∀ v ∈ Ioi (2 : ℝ),
        |deriv criticalCollarEndpointWeight v| = -deriv criticalCollarEndpointWeight v := fun v hv => by
      have hd := deriv_criticalCollarEndpointWeight_of_two_lt hv
      have hneg : deriv criticalCollarEndpointWeight v ≤ 0 := by
        rw [hd]
        have : 0 ≤ (v : ℝ) ^ (-2 : ℤ) := zpow_nonneg (le_trans two_pos.le hv.le) (-2)
        linarith
      exact abs_of_nonpos hneg
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_neg,
      integral_Ioi_of_hasDerivAt_of_tendsto
        contDiff_criticalCollarEndpointWeight.continuous.continuousWithinAt
        (fun x _ => hasDerivAt_criticalCollarEndpointWeight x)
        (IntegrableOn.mono_set integrableOn_deriv_criticalCollarEndpointWeight
          (Ioi_subset_Ioi one_le_two))
        tendsto_criticalCollarEndpointWeight_atTop,
      criticalCollarEndpointWeight_eq_of_two_le le_rfl]
    norm_num
  linarith

/-- **Explicit collar curvature integral bound.** `∫_{v>1} |ψ''(v)| dv ≤ 453/4`. -/
theorem integral_abs_deriv_deriv_criticalCollarWeight_le :
    ∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v| ≤ 453 / 4 := by
  have hint : IntegrableOn (fun v => |deriv (deriv criticalCollarWeight) v|) (Ioi 1) :=
    integrableOn_deriv_deriv_criticalCollarWeight.abs
  have hi1 : IntegrableOn (fun v => |deriv (deriv criticalCollarWeight) v|) (Ioc 1 2) :=
    IntegrableOn.mono_set hint Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (fun v => |deriv (deriv criticalCollarWeight) v|) (Ioi 2) :=
    IntegrableOn.mono_set hint (Ioi_subset_Ioi one_le_two)
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2]
  have h1 : ∫ v in Ioc (1 : ℝ) 2, |deriv (deriv criticalCollarWeight) v| ≤ 113 :=
    setIntegral_Ioc_one_two_le_of_le hi1
      fun v hv => abs_deriv_deriv_criticalCollarWeight_le hv.1.le
  have h2 : ∫ v in Ioi (2 : ℝ), |deriv (deriv criticalCollarWeight) v| = 1 / 4 := by
    have hcongr : ∀ v ∈ Ioi (2 : ℝ),
        |deriv (deriv criticalCollarWeight) v| = deriv (deriv criticalCollarWeight) v := fun v hv => by
      have hd := deriv_deriv_criticalCollarWeight_of_two_lt hv
      have hpos : 0 ≤ deriv (deriv criticalCollarWeight) v := by
        rw [hd]
        have : 0 ≤ (v : ℝ) ^ (-4 : ℤ) := zpow_nonneg (le_trans two_pos.le hv.le) (-4)
        linarith
      exact abs_of_nonneg hpos
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_Ioi_of_hasDerivAt_of_tendsto
        contDiff_deriv_criticalCollarWeight.continuous.continuousWithinAt
        (fun x _ => hasDerivAt_deriv_criticalCollarWeight x)
        (IntegrableOn.mono_set integrableOn_deriv_deriv_criticalCollarWeight
          (Ioi_subset_Ioi one_le_two))
        tendsto_deriv_criticalCollarWeight_atTop,
      deriv_criticalCollarWeight_two]
    norm_num
  linarith

/-- **Explicit collar curvature bound.** `criticalCollarCurvature ≤ 4`. -/
theorem criticalCollarCurvature_le_four : criticalCollarCurvature ≤ 4 := by
  unfold criticalCollarCurvature
  have h1 := integral_abs_deriv_deriv_criticalCollarWeight_le
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (36 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

private theorem deriv_criticalCollarWeight_add_criticalEndpointWeight {v : ℝ} (hv : 0 < v) :
    deriv criticalCollarWeight v + deriv criticalEndpointWeight v = -2 * v ^ (-3 : ℤ) := by
  have h1 := (hasDerivAt_criticalCollarWeight v).add (hasDerivAt_criticalEndpointWeight hv)
  have h2 : HasDerivAt (fun y : ℝ => y ^ (-2 : ℤ)) (-2 * v ^ (-3 : ℤ)) v :=
    (hasDerivAt_zpow (-2) v (Or.inl hv.ne')).congr_deriv (by norm_num)
  have h3 : (fun y : ℝ => y ^ (-2 : ℤ)) =ᶠ[𝓝 v]
      criticalCollarWeight + criticalEndpointWeight := by
    filter_upwards [Ioi_mem_nhds hv] with y hy
    simp only [Pi.add_apply]
    rw [criticalCollarWeight_add_criticalEndpointWeight hy, ← Real.rpow_intCast y (-2)]
    norm_num
  exact (h1.congr_of_eventuallyEq h3).unique h2

private theorem deriv_deriv_criticalCollarWeight_add_criticalEndpointWeight {v : ℝ} (hv : 0 < v) :
    deriv (deriv criticalCollarWeight) v + deriv (deriv criticalEndpointWeight) v =
      6 * v ^ (-4 : ℤ) := by
  have h1 := (hasDerivAt_deriv_criticalCollarWeight v).add
    (hasDerivAt_deriv_criticalEndpointWeight hv)
  have h2 : HasDerivAt (fun y : ℝ => -2 * y ^ (-3 : ℤ)) (6 * v ^ (-4 : ℤ)) v :=
    ((hasDerivAt_zpow (-3) v (Or.inl hv.ne')).const_mul (-2)).congr_deriv (by norm_num; ring)
  have h3 : (fun y : ℝ => -2 * y ^ (-3 : ℤ)) =ᶠ[𝓝 v]
      deriv criticalCollarWeight + deriv criticalEndpointWeight := by
    filter_upwards [Ioi_mem_nhds hv] with y hy
    simp only [Pi.add_apply]
    exact (deriv_criticalCollarWeight_add_criticalEndpointWeight hy).symm
  exact (h1.congr_of_eventuallyEq h3).unique h2

/-- **Exact endpoint slope at `v = 1`.** `φ_e'(1) = -2`, hence `|φ_e'(1)| = 2`. -/
theorem deriv_criticalEndpointWeight_one : deriv criticalEndpointWeight 1 = -2 := by
  have h := deriv_criticalCollarWeight_add_criticalEndpointWeight one_pos
  rw [deriv_criticalCollarWeight_eq_zero le_rfl] at h
  norm_num at h
  exact h

theorem abs_deriv_criticalEndpointWeight_one : |deriv criticalEndpointWeight 1| = 2 := by
  rw [deriv_criticalEndpointWeight_one]
  norm_num

theorem abs_deriv_deriv_criticalEndpointWeight_le {v : ℝ} (hv : 1 ≤ v) :
    |deriv (deriv criticalEndpointWeight) v| ≤ 119 := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hid := deriv_deriv_criticalCollarWeight_add_criticalEndpointWeight hv0
  have hψ := abs_deriv_deriv_criticalCollarWeight_le hv
  have hv4 : 6 * v ^ (-4 : ℤ) ≤ 6 := by
    rw [zpow_neg, show (4 : ℤ) = (4 : ℕ) by rfl, zpow_natCast]
    have : 1 ≤ v ^ 4 := one_le_pow₀ hv
    have : (v ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
    linarith
  have hv4_0 : 0 ≤ 6 * v ^ (-4 : ℤ) := by
    have : 0 ≤ v ^ (-4 : ℤ) := zpow_nonneg hv0.le (-4)
    linarith
  have heq : deriv (deriv criticalEndpointWeight) v =
      6 * v ^ (-4 : ℤ) - deriv (deriv criticalCollarWeight) v := by linarith
  rw [heq]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hv4_0]
  linarith

/-- **Explicit endpoint curvature integral bound.** `∫_1^2 |φ_e''(v)| dv ≤ 119`. -/
theorem integral_abs_deriv_deriv_criticalEndpointWeight_le :
    ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v| ≤ 119 := by
  have hcont : ContinuousOn (fun v => |deriv (deriv criticalEndpointWeight) v|) (uIcc 1 2) := by
    rw [uIcc_of_le one_le_two]
    exact continuous_abs.comp_continuousOn
      (continuousOn_deriv_deriv_criticalEndpointWeight.mono fun x hx =>
        lt_of_lt_of_le one_pos hx.1)
  calc ∫ v in (1 : ℝ)..2, |deriv (deriv criticalEndpointWeight) v|
      ≤ ∫ _ in (1 : ℝ)..2, (119 : ℝ) :=
        intervalIntegral.integral_mono_on one_le_two hcont.intervalIntegrable
          intervalIntegrable_const fun v hv => abs_deriv_deriv_criticalEndpointWeight_le hv.1
    _ = 119 := by norm_num

/-- **Explicit endpoint curvature bound.** `criticalEndpointCurvature ≤ 4`. -/
theorem criticalEndpointCurvature_le_four : criticalEndpointCurvature ≤ 4 := by
  unfold criticalEndpointCurvature
  rw [abs_deriv_criticalEndpointWeight_one]
  have h1 := integral_abs_deriv_deriv_criticalEndpointWeight_le
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (36 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ## Section 3: Prime majorants, zeta sums, channel constants and block thresholds -/

/-- The critical prime majorant `envelopePrimeMajorant 1` coincides pointwise with
`r ↦ Λ(r) / r^{3/2}`. -/
theorem envelopePrimeMajorant_one_eq (r : ℕ) :
    envelopePrimeMajorant 1 r =
      (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (3 / 2 : ℝ) := by
  unfold envelopePrimeMajorant
  split_ifs with hr
  · norm_num
  · have hr01 : r = 0 ∨ r = 1 := by omega
    rcases hr01 with rfl | rfl <;> simp

/-- **Explicit critical prime majorant bound.** `∑_r Λ(r) r^{-3/2} ≤ 18`. -/
theorem tsum_envelopePrimeMajorant_one_le :
    (∑' r : ℕ, envelopePrimeMajorant 1 r) ≤ 18 := by
  simp_rw [envelopePrimeMajorant_one_eq]
  have h := RHTower.tsum_vonMangoldt_div_rpow_le_six (s := 3 / 2) (by norm_num)
  norm_num at h
  exact h

/-- **Explicit subcritical prime majorant bound.** `canonicalPrimeMajorantConstant ≤ 12`. -/
theorem canonicalPrimeMajorantConstant_le_twelve :
    canonicalPrimeMajorantConstant ≤ 12 := by
  unfold canonicalPrimeMajorantConstant
  have hcongr : (fun r : ℕ => envelopePrimeMajorant (3 / 2) r) =
      fun r : ℕ => (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (2 : ℝ) := by
    funext r
    unfold envelopePrimeMajorant
    split_ifs with hr
    · norm_num
    · have hr01 : r = 0 ∨ r = 1 := by omega
      rcases hr01 with rfl | rfl <;> simp
  rw [hcongr]
  exact (RHTower.tsum_vonMangoldt_div_rpow_le_six (s := 2) (by norm_num)).trans (by norm_num)

theorem tsum_one_div_nat_sq_le_two :
    (∑' k : ℕ, 1 / (k : ℝ) ^ 2) ≤ 2 := by
  rw [hasSum_zeta_two.tsum_eq]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem tsum_one_div_nat_mul_sqrt_le_three :
    (∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) ≤ 3 := by
  set f : ℕ → ℝ := fun k => 1 / ((k : ℝ) * Real.sqrt k)
  have hf_sum : Summable f := by
    refine ((Real.summable_nat_rpow.mpr (show (-3 / 2 : ℝ) < -1 by norm_num)).congr fun k => ?_)
    simp only [f]
    rcases eq_or_ne k 0 with rfl | hk
    · norm_num
    · have hk0 : (0 : ℝ) < k := by positivity
      rw [one_div, Real.sqrt_eq_rpow,
        show (k : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) = (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) by
          rw [Real.rpow_one],
        ← Real.rpow_add hk0, ← Real.rpow_neg hk0.le]
      norm_num
  have htele (j : ℕ) : f (j + 2) ≤ 2 / Real.sqrt (j + 1 : ℝ) - 2 / Real.sqrt (j + 2 : ℝ) := by
    simp only [f]
    push_cast
    set a := Real.sqrt ((j : ℝ) + 1)
    set b := Real.sqrt ((j : ℝ) + 2)
    have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have ha2 : a ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (j : ℝ) + 2 := Real.sq_sqrt (by positivity)
    have hdiff : 2 / a - 2 / b = 2 / (a * b * (b + a)) := by
      have hba : (b - a) * (b + a) = 1 := by nlinarith
      rw [div_sub_div _ _ ha0.ne' hb0.ne', div_eq_div_iff (by positivity) (by positivity)]
      calc (2 * b - a * 2) * (a * b * (b + a))
          = 2 * (a * b) * ((b - a) * (b + a)) := by ring
        _ = 2 * (a * b) := by rw [hba, mul_one]
    rw [hdiff, ← hb2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : a * b * (b + a) ≤ b * b * (b + b) := by gcongr
    have h2 : b * b * (b + b) = 2 * (b ^ 2 * b) := by ring
    linarith
  have htail : (∑' j : ℕ, f (j + 2)) ≤ 2 := by
    refine Real.tsum_le_of_sum_range_le (fun j => by simp only [f]; positivity) fun N => ?_
    let g : ℕ → ℝ := fun j => 2 / Real.sqrt ((j : ℝ) + 1)
    calc ∑ j ∈ Finset.range N, f (j + 2)
        ≤ ∑ j ∈ Finset.range N, (g j - g (j + 1)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          dsimp [g]
          have h := htele j
          rwa [show ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 by push_cast; ring]
      _ = g 0 - g N := Finset.sum_range_sub' g N
      _ ≤ 2 := by
          dsimp [g]
          norm_num
          positivity
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f]
  rw [← hf_sum.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hf0, hf1]
  linarith

/-- **Explicit dyadic dilation constant bound.** For `0 ≤ A` and `0 ≤ B`,
`dyadicDilationConstant A B ≤ 24 * A + 8000 * B`. -/
theorem dyadicDilationConstant_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    dyadicDilationConstant A B ≤ 24 * A + 8000 * B := by
  unfold dyadicDilationConstant
  have hk1 := tsum_one_div_nat_mul_sqrt_le_three
  have hk2 := tsum_one_div_nat_sq_le_two
  have hk1_0 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have hk2_0 : 0 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  have hprod1 : (∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * (∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤ 6 := by
    nlinarith
  have hprod2 : (∑' k : ℕ, 1 / (k : ℝ) ^ 2) * (∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤ 4 := by
    nlinarith
  have hpi : Real.pi ^ 2 / 3 ≤ 4 := by
    have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
  have hlin1 : 4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) ≤ 4 * (A + 322 * B) := by nlinarith
  have hlin1_0 : 0 ≤ 4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) := by positivity
  have hterm1 : 4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤
      4 * (A + 322 * B) * 6 :=
    mul_le_mul hlin1 hprod1 (by positivity) (by positivity)
  have hterm2 : 68 * B * ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤
      68 * B * 4 := by nlinarith
  linarith

theorem dyadicDilationConstant_collar_le :
    dyadicDilationConstant criticalCollarMass criticalCollarCurvature ≤ 33000 := by
  have h := dyadicDilationConstant_le
    (by linarith [criticalCollarMass_bounds.1]) criticalCollarCurvature_nonneg
  have hA := criticalCollarMass_bounds.2
  have hB := criticalCollarCurvature_le_four
  linarith

theorem criticalEndpointDilationConstant_le :
    criticalEndpointDilationConstant ≤ 34000 := by
  unfold criticalEndpointDilationConstant
  have h1 := dyadicDilationConstant_le
    (by linarith [criticalEndpointMass_bounds.1]) criticalEndpointCurvature_nonneg
  have hA := criticalEndpointMass_bounds.2
  have hB := criticalEndpointCurvature_le_four
  have hk1 := tsum_one_div_nat_mul_sqrt_le_three
  have hk2 := tsum_one_div_nat_sq_le_two
  have hk1_0 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have hk2_0 : 0 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  have hprod1 : (∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * (∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤ 6 := by
    nlinarith
  have hprod2 : (∑' k : ℕ, 1 / (k : ℝ) ^ 2) * (∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤ 4 := by
    nlinarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hfrac1 : 1 + 13 / (Real.pi * (11 / 12)) ≤ 6 := by
    have : 13 / (Real.pi * (11 / 12)) ≤ 5 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hfrac2 : 16 / Real.pi ≤ 6 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  change dyadicDilationConstant criticalEndpointMass criticalEndpointCurvature +
    (8 * (1 + 13 / (Real.pi * (11 / 12))) *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
      16 / Real.pi * ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2)) ≤ 34000
  have hextra1 : 8 * (1 + 13 / (Real.pi * (11 / 12))) *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤
      8 * 6 * 6 :=
    mul_le_mul (by linarith) hprod1 (by positivity) (by positivity)
  have hextra2 : 16 / Real.pi * ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤
      6 * 4 :=
    mul_le_mul hfrac2 hprod2 (by positivity) (by positivity)
  linarith

private theorem dyadicDilationConstant_nonneg' {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ dyadicDilationConstant A B := by
  unfold dyadicDilationConstant
  have hk1_0 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have hk2_0 : 0 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  positivity

private theorem criticalEndpointDilationConstant_nonneg' :
    0 ≤ criticalEndpointDilationConstant := by
  unfold criticalEndpointDilationConstant
  have h1 := dyadicDilationConstant_nonneg'
    (by linarith [criticalEndpointMass_bounds.1]) criticalEndpointCurvature_nonneg
  have hk1_0 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have hk2_0 : 0 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  change 0 ≤ dyadicDilationConstant criticalEndpointMass criticalEndpointCurvature +
    (8 * (1 + 13 / (Real.pi * (11 / 12))) *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
      16 / Real.pi * ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2))
  positivity

/-- **Explicit collared prime channel constant bound.** `criticalCollaredPrimeConstant ≤ 30000`. -/
theorem criticalCollaredPrimeConstant_le :
    criticalCollaredPrimeConstant ≤ 30000 := by
  unfold criticalCollaredPrimeConstant
  have h1 := dyadicDilationConstant_collar_le
  have h2 := tsum_envelopePrimeMajorant_one_le
  have h1_0 : 0 ≤ dyadicDilationConstant criticalCollarMass criticalCollarCurvature :=
    dyadicDilationConstant_nonneg' (by linarith [criticalCollarMass_bounds.1])
      criticalCollarCurvature_nonneg
  have h2_0 : 0 ≤ ∑' r : ℕ, envelopePrimeMajorant 1 r :=
    tsum_nonneg (envelopePrimeMajorant_nonneg 1)
  have hpi4 : 4 / Real.pi ^ 4 ≤ 1 / 20 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have : (81 : ℝ) ≤ Real.pi ^ 4 := by
      have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h12 : 4 / Real.pi ^ 4 *
      dyadicDilationConstant criticalCollarMass criticalCollarCurvature ≤
      (1 / 20) * 33000 :=
    mul_le_mul hpi4 h1 h1_0 (by positivity)
  have h123 : 4 / Real.pi ^ 4 *
      dyadicDilationConstant criticalCollarMass criticalCollarCurvature *
      (∑' r : ℕ, envelopePrimeMajorant 1 r) ≤ (1 / 20) * 33000 * 18 :=
    mul_le_mul h12 h2 h2_0 (by positivity)
  linarith

/-- **Explicit uncollared prime channel constant bound.** `criticalPrimeChannelConstant ≤ 61000`. -/
theorem criticalPrimeChannelConstant_le :
    criticalPrimeChannelConstant ≤ 61000 := by
  unfold criticalPrimeChannelConstant
  have h1 := dyadicDilationConstant_collar_le
  have h1' := criticalEndpointDilationConstant_le
  have h2 := tsum_envelopePrimeMajorant_one_le
  have h1_0 : 0 ≤ dyadicDilationConstant criticalCollarMass criticalCollarCurvature +
      criticalEndpointDilationConstant :=
    add_nonneg (dyadicDilationConstant_nonneg' (by linarith [criticalCollarMass_bounds.1])
      criticalCollarCurvature_nonneg) criticalEndpointDilationConstant_nonneg'
  have h2_0 : 0 ≤ ∑' r : ℕ, envelopePrimeMajorant 1 r :=
    tsum_nonneg (envelopePrimeMajorant_nonneg 1)
  have hpi4 : 4 / Real.pi ^ 4 ≤ 1 / 20 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have : (81 : ℝ) ≤ Real.pi ^ 4 := by
      have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h12 : 4 / Real.pi ^ 4 *
      (dyadicDilationConstant criticalCollarMass criticalCollarCurvature +
        criticalEndpointDilationConstant) ≤ (1 / 20) * 67000 :=
    mul_le_mul hpi4 (by linarith) h1_0 (by positivity)
  have h123 : 4 / Real.pi ^ 4 *
      (dyadicDilationConstant criticalCollarMass criticalCollarCurvature +
        criticalEndpointDilationConstant) *
      (∑' r : ℕ, envelopePrimeMajorant 1 r) ≤ (1 / 20) * 67000 * 18 :=
    mul_le_mul h12 h2 h2_0 (by positivity)
  linarith

theorem abs_gammaBracket_zero_le_seven :
    |_root_.Zeta23.EF.gammaBracket 0| ≤ 7 := by
  rw [RHTower.ArchimedeanAnomaly.abs_gammaBracket_zero]
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hlog : Real.log (8 * Real.pi) ≤ 4 := by
    have h8pi : 8 * Real.pi ≤ Real.exp 4 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he4 : (2.7 : ℝ) ^ 4 ≤ Real.exp 4 := by
        have : Real.exp 4 = Real.exp 1 ^ 4 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        exact pow_le_pow_left₀ (by norm_num) he 4
      linarith
    exact (Real.log_le_iff_le_exp (by positivity)).mpr h8pi
  linarith

theorem criticalCollarMassUpper_le_forty :
    criticalCollarMassUpper ≤ 40 := by
  unfold criticalCollarMassUpper factorialUnitIntervalUpper factorialWindowGapConstant
  have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hgap : 390 / Real.pi ≤ 130 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hpi4 : (81 : ℝ) ≤ Real.pi ^ 4 := by
    have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
    nlinarith
  have h1 : 49 * (1 + 390 / Real.pi) / (4 * Real.pi ^ 4) ≤ 20 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h2 : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
  have h3 : 0 ≤ 49 * (1 + 390 / Real.pi) / (4 * Real.pi ^ 4) := by positivity
  nlinarith

theorem criticalWindowBaseConstant_le :
    criticalWindowBaseConstant ≤ 1500 := by
  unfold criticalWindowBaseConstant
  have h1 := abs_gammaBracket_zero_le_seven
  have h2 := criticalCollarMassUpper_le_forty
  have h2_0 : 0 ≤ criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    exact mul_nonneg (by positivity) factorialUnitIntervalUpper_pos.le
  nlinarith [abs_nonneg (_root_.Zeta23.EF.gammaBracket 0)]

/-- **Explicit complete critical channel constant bound.**
`criticalCompleteChannelConstant ≤ 125000`. -/
theorem criticalCompleteChannelConstant_le :
    criticalCompleteChannelConstant ≤ 125000 := by
  have h1 := criticalWindowBaseConstant_le
  have h2 := criticalPrimeChannelConstant_le
  unfold criticalCompleteChannelConstant
  unfold criticalWindowBaseConstant at h1
  linarith

/-- **Explicit collared complete channel constant bound.**
`criticalCollaredChannelConstant ≤ 66000`. -/
theorem criticalCollaredChannelConstant_le :
    criticalCollaredChannelConstant ≤ 66000 := by
  unfold criticalCollaredChannelConstant
  have h1 := abs_gammaBracket_zero_le_seven
  have h2 := criticalCollarMassUpper_le_forty
  have h2_0 : 0 ≤ criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    exact mul_nonneg (by positivity) factorialUnitIntervalUpper_pos.le
  have h3 := integral_abs_deriv_criticalCollarWeight_le
  have h4 := integral_abs_deriv_criticalCollarEndpointWeight_le
  have h3_0 : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| :=
    integral_nonneg fun _ => abs_nonneg _
  have h4_0 : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
    integral_nonneg fun _ => abs_nonneg _
  have h5 := criticalCollaredPrimeConstant_le
  nlinarith [abs_nonneg (_root_.Zeta23.EF.gammaBracket 0)]

theorem criticalWindowPrimeSlope_le :
    criticalWindowPrimeSlope ≤ 30000 := by
  have hcol : windowCollarUniform ≤ 516 := by
    unfold windowCollarUniform crossSpacedBound
    have hA1 := criticalCollarMass_bounds.2
    have hB1 := criticalCollarCurvature_le_four
    have hB1_0 := criticalCollarCurvature_nonneg
    have hpi_sq : Real.pi ^ 2 / 3 ≤ 4 := by
      have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
    nlinarith
  have hend : windowEndpointUniform ≤ 542 := by
    unfold windowEndpointUniform crossSpacedBound
    have hA2 := criticalEndpointMass_bounds.2
    have hB2 := criticalEndpointCurvature_le_four
    have hB2_0 := criticalEndpointCurvature_nonneg
    have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpi_sq : Real.pi ^ 2 / 3 ≤ 4 := by
      have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
    have hfrac1 : 13 / (Real.pi * (11 / 12)) ≤ 5 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  have hfar : windowFarConstant ≤ 130 := by
    unfold windowFarConstant
    have hB1 := criticalCollarCurvature_le_four
    have hB2 := criticalEndpointCurvature_le_four
    have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hfrac2 : 4 / Real.pi ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hcol_0 : 0 ≤ windowCollarUniform := by
    unfold windowCollarUniform crossSpacedBound
    have := criticalCollarMass_bounds.1; have := criticalCollarCurvature_nonneg; positivity
  have hend_0 : 0 ≤ windowEndpointUniform := by
    unfold windowEndpointUniform crossSpacedBound
    have := criticalEndpointMass_bounds.1; have := criticalEndpointCurvature_nonneg; positivity
  have hfar_0 : 0 ≤ windowFarConstant := by
    unfold windowFarConstant
    have := criticalCollarCurvature_nonneg; have := criticalEndpointCurvature_nonneg; positivity
  have hpi_sq6 : (Real.pi ^ 2 / 6) ^ 2 ≤ 4 := by
    have : Real.pi ^ 2 / 6 ≤ 2 := by
      have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
    nlinarith [Real.pi_pos]
  have hk1 := tsum_one_div_nat_mul_sqrt_le_three
  have hk2 := tsum_one_div_nat_sq_le_two
  have hk1_0 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have hk2_0 : 0 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  have hprod1 : (∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * (∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤ 6 := by
    nlinarith
  have hsqrt8 : Real.sqrt 8 ≤ 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hwin : criticalWindowConstant ≤ 25000 := by
    unfold criticalWindowConstant
    have hp1 : (windowCollarUniform + windowEndpointUniform) * (Real.pi ^ 2 / 6) ^ 2 ≤
        1058 * 4 :=
      mul_le_mul (by linarith) hpi_sq6 (by positivity) (by positivity)
    have hp2a : Real.sqrt 8 * (windowCollarUniform + windowEndpointUniform) ≤ 3 * 1058 :=
      mul_le_mul hsqrt8 (by linarith) (by positivity) (by positivity)
    have hp2 : Real.sqrt 8 * (windowCollarUniform + windowEndpointUniform) *
        ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) ≤
        3 * 1058 * 6 :=
      mul_le_mul hp2a hprod1 (by positivity) (by positivity)
    have hp3 : windowFarConstant * (Real.pi ^ 2 / 6) ^ 2 ≤ 130 * 4 :=
      mul_le_mul hfar hpi_sq6 (by positivity) (by positivity)
    linarith
  unfold criticalWindowPrimeSlope
  have hpi4 : 4 / Real.pi ^ 4 ≤ 1 / 20 := by
    have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have : (81 : ℝ) ≤ Real.pi ^ 4 := by
      have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]; linarith
  have he1 : 6 * Real.exp 1 ≤ 18 := by linarith [Real.exp_one_lt_three.le]
  have hwin_0 := criticalWindowConstant_nonneg
  have hm1 : 4 / Real.pi ^ 4 * criticalWindowConstant ≤ (1 / 20) * 25000 :=
    mul_le_mul hpi4 hwin hwin_0 (by positivity)
  have hm2 : 4 / Real.pi ^ 4 * criticalWindowConstant * (6 * Real.exp 1) ≤
      (1 / 20) * 25000 * 18 :=
    mul_le_mul hm1 he1 (by positivity) (by positivity)
  linarith

private theorem half_le_exp_neg_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have h1 : Real.exp (1 / 2) ≤ 2 := by
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_one_lt_three.le, Real.exp_pos (1 / 2)]
  have h2 : 1 / 2 * Real.exp (1 / 2) ≤ 1 := by linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(1 / 2 : ℝ))).le
  rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, one_mul] at h3

/-- **Explicit lower bound on the archimedean logarithmic slope.**
`1 / 10 ^ 15 ≤ criticalArchLogSlope`. -/
theorem criticalArchLogSlope_ge :
    (1 / 10 ^ 15 : ℝ) ≤ criticalArchLogSlope := by
  unfold criticalArchLogSlope factorialWeightedPhaseLower
    factorialWindowLength factorialWindowGapConstant
  have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : Real.pi < 4 := Real.pi_lt_four
  set L := 16 * (390 / Real.pi)
  have hLeq : L = 6240 / Real.pi := by dsimp [L]; ring
  have hL_lo : 1560 ≤ L := by
    rw [hLeq, le_div_iff₀ (by positivity)]; linarith
  have hL_hi : L ≤ 2080 := by
    rw [hLeq, div_le_iff₀ (by positivity)]; linarith
  have hpi4 : Real.pi ^ 4 ≤ 256 := by
    have : Real.pi ^ 2 ≤ 16 := by nlinarith
    nlinarith [Real.pi_pos]
  have h1L : (1 + L) ^ 4 ≤ 2081 ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hexp := half_le_exp_neg_half
  have hphase : (4 / 10 ^ 15 : ℝ) ≤ L / (16 * Real.pi ^ 4 * (1 + L) ^ 4) := by
    rw [le_div_iff₀ (by positivity)]
    have hden : 16 * Real.pi ^ 4 * (1 + L) ^ 4 ≤ 16 * 256 * 2081 ^ 4 := by
      have : 16 * Real.pi ^ 4 ≤ 16 * 256 := by linarith
      exact mul_le_mul this h1L (by positivity) (by positivity)
    linarith
  have hm := mul_le_mul hexp (div_le_div_of_nonneg_right hphase zero_le_two)
    (by positivity) (by positivity)
  linarith

/-- **Explicit lower bound on the collared archimedean logarithmic slope.**
`1 / 10 ^ 8 ≤ criticalCollarArchLogSlope`. -/
theorem criticalCollarArchLogSlope_ge :
    (1 / 10 ^ 8 : ℝ) ≤ criticalCollarArchLogSlope := by
  unfold criticalCollarArchLogSlope criticalCollarMassLower
    factorialWindowLength factorialWindowGapConstant
  have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : Real.pi < 4 := Real.pi_lt_four
  set L := 16 * (390 / Real.pi)
  have hLeq : L = 6240 / Real.pi := by dsimp [L]; ring
  have hL_lo : 1560 ≤ L := by
    rw [hLeq, le_div_iff₀ (by positivity)]; linarith
  have hL_hi : L ≤ 2080 := by
    rw [hLeq, div_le_iff₀ (by positivity)]; linarith
  have hpi4 : Real.pi ^ 4 ≤ 256 := by
    have : Real.pi ^ 2 ≤ 16 := by nlinarith
    nlinarith [Real.pi_pos]
  have h2L : (2 + L) ^ 2 ≤ 2082 ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hexp := half_le_exp_neg_half
  have hmass : (4 / 10 ^ 8 : ℝ) ≤ L / (16 * Real.pi ^ 4) / (2 + L) ^ 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have hden : 16 * Real.pi ^ 4 * (2 + L) ^ 2 ≤ 16 * 256 * 2082 ^ 2 := by
      have : 16 * Real.pi ^ 4 ≤ 16 * 256 := by linarith
      exact mul_le_mul this h2L (by positivity) (by positivity)
    linarith
  have hm := mul_le_mul hexp (div_le_div_of_nonneg_right hmass zero_le_two)
    (by positivity) (by positivity)
  linarith

/-- **Explicit two-sided bounds on the polynomial window exponent `δ`.** -/
theorem criticalWindowExponent_bounds :
    (1 / 10 ^ 21 : ℝ) ≤ criticalWindowExponent ∧ criticalWindowExponent ≤ 1 := by
  unfold criticalWindowExponent
  have hs := criticalArchLogSlope_ge
  have hW := criticalWindowPrimeSlope_le
  have hW0 : 0 ≤ criticalWindowPrimeSlope := by
    unfold criticalWindowPrimeSlope
    have := criticalWindowConstant_nonneg
    positivity
  constructor
  · rw [le_div_iff₀ (by positivity)]
    norm_num at hs ⊢
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have hs_hi : criticalArchLogSlope ≤ 1 := by
      unfold criticalArchLogSlope factorialWeightedPhaseLower
        factorialWindowLength factorialWindowGapConstant
      have hpi1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      set L := 16 * (390 / Real.pi)
      have hL0 : 0 < L := by positivity
      have hexp : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have h1 : L / (16 * Real.pi ^ 4 * (1 + L) ^ 4) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]
        have hpow : 1 ≤ (1 + L) ^ 3 := one_le_pow₀ (by linarith)
        have hL4 : L ≤ (1 + L) ^ 4 := by
          have : (1 + L) ^ 4 = (1 + L) * (1 + L) ^ 3 := by ring
          nlinarith
        have hpi4 : 1 ≤ 16 * Real.pi ^ 4 := by
          have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
          nlinarith
        nlinarith
      nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]
    linarith

/-! ## Section 4: Closed form of band sine moments and the spectral curvature constant `I₀` -/

/-- Band sine moment `μ_m = ∫₀^{π/6} (π/6 - ξ) ξ sin(mξ) dξ`. -/
def criticalBandSineMoment (m : ℕ) : ℝ :=
  ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m)

/-- Absolute band sine moment `∫₀^{π/6} (π/6 - ξ) ξ |sin(mξ)| dξ`. -/
def criticalBandAbsSineMoment (m : ℕ) : ℝ :=
  ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|

theorem criticalBandSineMoment_zero : criticalBandSineMoment 0 = 0 := by
  simp [criticalBandSineMoment]

theorem criticalBandAbsSineMoment_nonneg (m : ℕ) : 0 ≤ criticalBandAbsSineMoment m := by
  refine intervalIntegral.integral_nonneg (by positivity) fun ξ hξ => ?_
  exact mul_nonneg (mul_nonneg (by linarith [hξ.2]) hξ.1) (abs_nonneg _)

/-- **Closed form of the band sine moment.** For `m ≥ 1`,
`μ_m = (2(1 - cos(mπ/6)) - (mπ/6) sin(mπ/6)) / m³`. -/
theorem criticalBandSineMoment_eq {m : ℕ} (hm : 0 < m) :
    criticalBandSineMoment m =
      (2 * (1 - Real.cos (Real.pi / 6 * m)) -
        (Real.pi / 6 * m) * Real.sin (Real.pi / 6 * m)) / (m : ℝ) ^ 3 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let F : ℝ → ℝ := fun ξ =>
    -((Real.pi / 6 - ξ) * ξ * Real.cos (ξ * m)) / (m : ℝ) +
      (Real.pi / 6 - 2 * ξ) * Real.sin (ξ * m) / (m : ℝ) ^ 2 -
      2 * Real.cos (ξ * m) / (m : ℝ) ^ 3
  have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6),
      HasDerivAt F ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m)) ξ := by
    intro ξ _
    have hlin : HasDerivAt (fun x : ℝ => x * m) (m : ℝ) ξ :=
      ((hasDerivAt_id ξ).mul_const (m : ℝ)).congr_deriv (by ring)
    have hsin : HasDerivAt (fun x : ℝ => Real.sin (x * m)) (Real.cos (ξ * m) * m) ξ :=
      hlin.sin
    have hcos : HasDerivAt (fun x : ℝ => Real.cos (x * m)) (-Real.sin (ξ * m) * m) ξ :=
      hlin.cos
    have hp1 : HasDerivAt (fun x : ℝ => (Real.pi / 6 - x) * x) (Real.pi / 6 - 2 * ξ) ξ :=
      (((hasDerivAt_id ξ).const_sub (Real.pi / 6)).mul (hasDerivAt_id ξ)).congr_deriv
        (by simp only [id_eq]; ring)
    have hp2 : HasDerivAt (fun x : ℝ => Real.pi / 6 - 2 * x) (-2) ξ :=
      (((hasDerivAt_id ξ).const_mul 2).const_sub (Real.pi / 6)).congr_deriv (by ring)
    have ht1 := ((hp1.mul hcos).neg).div_const (m : ℝ)
    have ht2 := (hp2.mul hsin).div_const ((m : ℝ) ^ 2)
    have ht3 := (hcos.const_mul 2).div_const ((m : ℝ) ^ 3)
    exact ((ht1.add ht2).sub ht3).congr_deriv (by field_simp; ring)
  unfold criticalBandSineMoment
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  dsimp [F]
  simp only [sub_self, zero_mul, mul_zero, Real.cos_zero, Real.sin_zero, neg_zero, zero_div,
    zero_add]
  field_simp
  ring

theorem criticalBandSineMoment_nonneg_of_le_twelve {m : ℕ} (hm : m ≤ 12) :
    0 ≤ criticalBandSineMoment m := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [criticalBandSineMoment_zero]
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    rcases le_or_gt m 6 with hm6 | hm6
    · unfold criticalBandSineMoment
      refine intervalIntegral.integral_nonneg (by positivity) fun ξ hξ => ?_
      have hmR : (m : ℝ) ≤ 6 := by exact_mod_cast hm6
      have hle : ξ * (m : ℝ) ≤ Real.pi := by
        calc ξ * (m : ℝ) ≤ (Real.pi / 6) * 6 :=
              mul_le_mul hξ.2 hmR (Nat.cast_nonneg m) (by positivity)
          _ = Real.pi := by ring
      have hsin : 0 ≤ Real.sin (ξ * m) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hξ.1 (Nat.cast_nonneg m)) hle
      exact mul_nonneg (mul_nonneg (by linarith [hξ.2]) hξ.1) hsin
    · rw [criticalBandSineMoment_eq hm_pos]
      have hm7 : 7 ≤ (m : ℝ) := by exact_mod_cast hm6
      have hm12 : (m : ℝ) ≤ 12 := by exact_mod_cast hm
      have hcos : Real.cos (Real.pi / 6 * m) ≤ 1 := Real.cos_le_one _
      have h1 : Real.pi ≤ Real.pi / 6 * (m : ℝ) := by
        have := mul_le_mul_of_nonneg_left hm7 (by positivity : 0 ≤ Real.pi / 6)
        linarith [Real.pi_pos]
      have h2 : Real.pi / 6 * (m : ℝ) ≤ 2 * Real.pi := by
        have := mul_le_mul_of_nonneg_left hm12 (by positivity : 0 ≤ Real.pi / 6)
        linarith [Real.pi_pos]
      have hsin : Real.sin (Real.pi / 6 * m) ≤ 0 := by
        rw [show Real.pi / 6 * (m : ℝ) = (Real.pi / 6 * m - Real.pi) + Real.pi by ring,
          Real.sin_add_pi, neg_nonpos]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hnum : 0 ≤ 2 * (1 - Real.cos (Real.pi / 6 * m)) -
          (Real.pi / 6 * m) * Real.sin (Real.pi / 6 * m) := by
        have hprod : (Real.pi / 6 * (m : ℝ)) * Real.sin (Real.pi / 6 * m) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hsin
        linarith
      exact div_nonneg hnum (by positivity)

theorem abs_criticalBandSineMoment_le {m : ℕ} (hm : 0 < m) :
    |criticalBandSineMoment m| ≤ (4 + Real.pi / 6 * m) / (m : ℝ) ^ 3 := by
  rw [criticalBandSineMoment_eq hm, abs_div, abs_of_pos (by positivity : 0 < (m : ℝ) ^ 3)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : |2 * (1 - Real.cos (Real.pi / 6 * m))| ≤ 4 := by
    rw [abs_mul, abs_two, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (Real.pi / 6 * m)]
  have h2 : |(Real.pi / 6 * m) * Real.sin (Real.pi / 6 * m)| ≤ Real.pi / 6 * m := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  exact (abs_sub _ _).trans (by linarith)

/-- Spectral curvature constant `I₀ = ∑_m (A(m)/m³) μ_m` of the critical kernel. -/
def criticalKernelCurvatureConstant : ℝ :=
  ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandSineMoment m

/-- Absolute band sine moment budget `M_abs = ∑_m (|A(m)|/m³) ∫₀^{π/6} (π/6 - ξ) ξ |sin(mξ)| dξ`. -/
def criticalKernelAbsMoment : ℝ :=
  ∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 * criticalBandAbsSineMoment m

theorem criticalBandAbsSineMoment_le_cube (m : ℕ) :
    criticalBandAbsSineMoment m ≤ (Real.pi / 6) ^ 3 / 6 := by
  have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
      (fun ξ : ℝ => Real.pi / 6 * ξ ^ 2 / 2 - ξ ^ 3 / 3) ((Real.pi / 6 - ξ) * ξ) ξ := by
    intro ξ _
    exact ((((hasDerivAt_pow 2 ξ).const_mul (Real.pi / 6)).div_const 2).sub
      ((hasDerivAt_pow 3 ξ).div_const 3)).congr_deriv (by ring)
  have hmom : ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * ξ = (Real.pi / 6) ^ 3 / 6 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  rw [← hmom]
  unfold criticalBandAbsSineMoment
  refine intervalIntegral.integral_mono_on (by positivity)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop) fun ξ hξ => ?_
  exact mul_le_of_le_one_right (mul_nonneg (by linarith [hξ.2]) hξ.1) (Real.abs_sin_le_one _)

theorem criticalBandAbsSineMoment_le_quartic (m : ℕ) :
    criticalBandAbsSineMoment m ≤ (m : ℝ) * (Real.pi / 6) ^ 4 / 12 := by
  have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
      (fun ξ : ℝ => (m : ℝ) * (Real.pi / 6 * ξ ^ 3 / 3 - ξ ^ 4 / 4))
      ((Real.pi / 6 - ξ) * ξ * (ξ * m)) ξ := by
    intro ξ _
    exact ((((hasDerivAt_pow 3 ξ).const_mul (Real.pi / 6)).div_const 3).sub
      ((hasDerivAt_pow 4 ξ).div_const 4) |>.const_mul (m : ℝ)).congr_deriv (by ring)
  have hmom : ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * ξ * (ξ * m) =
      (m : ℝ) * (Real.pi / 6) ^ 4 / 12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  rw [← hmom]
  unfold criticalBandAbsSineMoment
  refine intervalIntegral.integral_mono_on (by positivity)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop) fun ξ hξ => ?_
  have hs : |Real.sin (ξ * m)| ≤ ξ * m := by
    have := Real.abs_sin_le_abs (x := ξ * m)
    rwa [abs_of_nonneg (mul_nonneg hξ.1 (Nat.cast_nonneg m))] at this
  exact mul_le_mul_of_nonneg_left hs (mul_nonneg (by linarith [hξ.2]) hξ.1)

theorem abs_criticalBandSineMoment_le_absSineMoment (m : ℕ) :
    |criticalBandSineMoment m| ≤ criticalBandAbsSineMoment m := by
  unfold criticalBandSineMoment criticalBandAbsSineMoment
  refine (intervalIntegral.abs_integral_le_integral_abs (by positivity)).trans ?_
  refine intervalIntegral.integral_mono_on (by positivity)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop) fun ξ hξ => ?_
  rw [abs_mul, abs_of_nonneg (mul_nonneg (by linarith [hξ.2]) hξ.1)]

theorem summable_criticalKernelAbsMoment :
    Summable fun m : ℕ =>
      |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 * criticalBandAbsSineMoment m := by
  refine (summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.mul_right
    ((Real.pi / 6) ^ 3 / 6)).of_nonneg_of_le
    (fun m => mul_nonneg (div_nonneg (abs_nonneg _) (by positivity))
      (criticalBandAbsSineMoment_nonneg m))
    fun m => mul_le_mul_of_nonneg_left (criticalBandAbsSineMoment_le_cube m)
      (div_nonneg (abs_nonneg _) (by positivity))

theorem summable_abs_criticalKernelCurvatureTerm :
    Summable fun m : ℕ =>
      |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandSineMoment m| := by
  refine summable_criticalKernelAbsMoment.of_nonneg_of_le (fun _ => abs_nonneg _) fun m => ?_
  rw [abs_mul, abs_div, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (abs_criticalBandSineMoment_le_absSineMoment m)
    (div_nonneg (abs_nonneg _) (by positivity))

/-- **Explicit upper bound on the absolute band sine moment series.**
`criticalKernelAbsMoment ≤ 19 / 1000`. -/
theorem criticalKernelAbsMoment_le :
    criticalKernelAbsMoment ≤ 19 / 1000 := by
  unfold criticalKernelAbsMoment
  set x : ℕ → ℝ := fun m =>
    |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 * criticalBandAbsSineMoment m
  have hs : Summable x := summable_criticalKernelAbsMoment
  have hzero {m : ℕ} (hm : m = 1 ∨ m % 4 = 0) : x m = 0 := by
    simp [x, (factorialCriticalPrimeHarmonicCharge_sign m).2.1.mpr hm]
  have hx0 : x 0 = 0 := by simp [x]
  have hx1 : x 1 = 0 := hzero (Or.inl rfl)
  have hx4 : x 4 = 0 := hzero (Or.inr (by norm_num))
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hx2 : x 2 ≤ Real.log 2 / 4 * (2 * (Real.pi / 6) ^ 4 / 12) := by
    have hd := criticalBandAbsSineMoment_le_quartic 2
    simp only [x, factorialCriticalPrimeHarmonicCharge_two]
    have : |-2 * Real.log 2| / ((2 : ℕ) : ℝ) ^ 3 = Real.log 2 / 4 := by
      rw [abs_mul]; norm_num [abs_of_pos hl2]; ring
    rw [this]; push_cast at hd; nlinarith
  have hx3 : x 3 ≤ Real.log 3 / 9 * (3 * (Real.pi / 6) ^ 4 / 12) := by
    have hd := criticalBandAbsSineMoment_le_quartic 3
    simp only [x, factorialCriticalPrimeHarmonicCharge_odd_prime Nat.prime_three (by norm_num)]
    have : |((3 : ℕ) : ℝ) * Real.log ((3 : ℕ) : ℝ)| / ((3 : ℕ) : ℝ) ^ 3 = Real.log 3 / 9 := by
      push_cast; rw [abs_mul]; norm_num [abs_of_pos hl3]; ring
    rw [this]; push_cast at hd; nlinarith
  have htail (j : ℕ) : x (j + 5) ≤ (Real.pi / 6) ^ 3 / 6 *
      (Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2) := by
    have hd := criticalBandAbsSineMoment_le_cube (j + 5)
    have hA := abs_factorialCriticalPrimeHarmonicCharge_le (j + 5)
    simp only [x]
    have hc : |factorialCriticalPrimeHarmonicCharge (j + 5)| / ((j + 5 : ℕ) : ℝ) ^ 3 ≤
        Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e : (4 + ((j : ℝ) + 1)) = ((j + 5 : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      calc |factorialCriticalPrimeHarmonicCharge (j + 5)| * ((j + 5 : ℕ) : ℝ) ^ 2
          ≤ ((j + 5 : ℕ) : ℝ) * Real.log ((j + 5 : ℕ) : ℝ) * ((j + 5 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = _ := by ring
    calc |factorialCriticalPrimeHarmonicCharge (j + 5)| / ((j + 5 : ℕ) : ℝ) ^ 3 *
          criticalBandAbsSineMoment (j + 5)
        ≤ Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 * ((Real.pi / 6) ^ 3 / 6) :=
          mul_le_mul hc hd (criticalBandAbsSineMoment_nonneg _) (by
            have : (1 : ℝ) ≤ 4 + ((j : ℝ) + 1) := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
            exact div_nonneg (Real.log_nonneg this) (by positivity))
      _ = _ := by ring
  have hlogsum := GaloisForLFunctions.HTGeometry.tsum_logLin_div_sq_le (N := 4)
    (by have := Real.exp_one_lt_d9; linarith)
  have hlsum : Summable fun j : ℕ => Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 := by
    refine ((summable_nat_add_iff 5).mpr GaloisForLFunctions.HTGeometry.summable_logLin_div_sq).congr
      fun j => by push_cast; congr 2 <;> ring
  have htsum : ∑' j : ℕ, x (j + 5) ≤ (Real.pi / 6) ^ 3 / 6 * ((2 * Real.log 2 + 1) / 4) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← hlog4]
    calc ∑' j : ℕ, x (j + 5)
        ≤ ∑' j : ℕ, (Real.pi / 6) ^ 3 / 6 *
            (Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2) :=
          Summable.tsum_le_tsum htail ((summable_nat_add_iff 5).mpr hs) (hlsum.mul_left _)
      _ = (Real.pi / 6) ^ 3 / 6 * ∑' j : ℕ,
            Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogsum (by positivity)
  rw [← hs.sum_add_tsum_nat_add 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hx0, hx1, hx4]
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  set P := Real.pi / 6
  have hP0 : 0 ≤ P := by positivity
  have hP1 : P ≤ 0.5236 := by dsimp [P]; linarith
  have hP3 : P ^ 3 ≤ 0.5236 ^ 3 := pow_le_pow_left₀ hP0 hP1 3
  have hP4 : P ^ 4 ≤ 0.5236 ^ 4 := pow_le_pow_left₀ hP0 hP1 4
  have hL2 := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ (8 / 5) * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : 0 < (3 : ℝ) ^ 5) (by norm_num : (3 : ℝ) ^ 5 ≤ 2 ^ 8)
    simp only [Real.log_pow] at h; push_cast at h; linarith
  have a1 : Real.log 2 * P ^ 4 ≤ 0.6931471808 * 0.5236 ^ 4 :=
    mul_le_mul hL2.le hP4 (by positivity) (by norm_num)
  have a2 : Real.log 3 * P ^ 4 ≤ (8 / 5 * 0.6931471808) * 0.5236 ^ 4 :=
    mul_le_mul (by linarith) hP4 (by positivity) (by norm_num)
  have a3 : P ^ 3 * Real.log 2 ≤ 0.5236 ^ 3 * 0.6931471808 :=
    mul_le_mul hP3 hL2.le (by positivity) (by norm_num)
  have hx2' : x 2 ≤ (1 / 24) * (Real.log 2 * P ^ 4) := hx2.trans_eq (by dsimp [P]; ring)
  have hx3' : x 3 ≤ (1 / 36) * (Real.log 3 * P ^ 4) := hx3.trans_eq (by dsimp [P]; ring)
  have htsum' : (∑' j : ℕ, x (j + 5)) ≤
      (1 / 12) * (P ^ 3 * Real.log 2) + (1 / 24) * P ^ 3 :=
    htsum.trans_eq (by dsimp [P]; ring)
  norm_num at hP3 a1 a2 a3
  linarith

private theorem log_le_div_four_of_thirteen_le {x : ℝ} (hx : 13 ≤ x) :
    Real.log x ≤ x / 4 := by
  have hx0 : 0 < x := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 5 by positivity)
  rw [Real.log_div hx0.ne' (by norm_num)] at h1
  have h5 : Real.log 5 ≤ 1.62 := by
    have h := Real.log_le_log (by norm_num : 0 < (5 : ℝ) ^ 3) (by norm_num : (5 : ℝ) ^ 3 ≤ 2 ^ 7)
    simp only [Real.log_pow] at h; push_cast at h
    linarith [Real.log_two_lt_d9]
  linarith

private theorem log_le_three_tenths_of_nine_le {x : ℝ} (hx : 9 ≤ x) :
    Real.log x ≤ (3 / 10) * x := by
  have hx0 : 0 < x := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 4 by positivity)
  rw [Real.log_div hx0.ne' (by norm_num)] at h1
  have h4 : Real.log 4 ≤ 1.387 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  linarith

private theorem tsum_inv_cube_shift_le {N : ℕ} (hN : 2 ≤ N) :
    (∑' j : ℕ, 1 / ((j + N : ℕ) : ℝ) ^ 3) ≤ 1 / (2 * ((N : ℝ) - 1) * (N : ℝ)) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let g : ℕ → ℝ := fun j => 1 / (2 * ((j : ℝ) + N - 1) * ((j : ℝ) + N))
  have htele (j : ℕ) : 1 / ((j + N : ℕ) : ℝ) ^ 3 ≤ g j - g (j + 1) := by
    dsimp [g]
    push_cast
    set m := (j : ℝ) + N
    have hm2 : 2 ≤ m := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hm_sub : 0 < m - 1 := by linarith
    have hm_pos : 0 < m := by linarith
    have hm_add : 0 < m + 1 := by linarith
    have hdiff : 1 / (2 * (m - 1) * m) - 1 / (2 * (m + 1 - 1) * (m + 1)) =
        1 / ((m - 1) * m * (m + 1)) := by
      have hd1 : 2 * (m - 1) * m ≠ 0 := by positivity
      have hd2 : 2 * (m + 1 - 1) * (m + 1) ≠ 0 := by
        rw [add_sub_cancel_right]; positivity
      have hd3 : (m - 1) * m * (m + 1) ≠ 0 := by positivity
      rw [div_sub_div _ _ hd1 hd2, div_eq_div_iff (mul_ne_zero hd1 hd2) hd3]
      ring
    have heq : 1 / (2 * ((j : ℝ) + N - 1) * ((j : ℝ) + N)) -
        1 / (2 * ((j : ℝ) + 1 + N - 1) * ((j : ℝ) + 1 + N)) =
        1 / (2 * (m - 1) * m) - 1 / (2 * (m + 1 - 1) * (m + 1)) := by
      dsimp [m]; congr 3 <;> ring
    rw [heq, hdiff]
    refine div_le_div₀ zero_le_one le_rfl (by positivity) ?_
    have : m ^ 3 - (m - 1) * m * (m + 1) = m := by ring
    linarith
  refine Real.tsum_le_of_sum_range_le (fun j => by positivity) fun M => ?_
  calc ∑ j ∈ Finset.range M, 1 / ((j + N : ℕ) : ℝ) ^ 3
      ≤ ∑ j ∈ Finset.range M, (g j - g (j + 1)) := Finset.sum_le_sum fun j _ => htele j
    _ = g 0 - g M := Finset.sum_range_sub' g M
    _ ≤ g 0 := by
        have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
        have : 0 ≤ g M := by
          dsimp [g]
          have : 0 < (M : ℝ) + N - 1 := by linarith
          have : 0 < (M : ℝ) + N := by linarith
          positivity
        linarith
    _ = 1 / (2 * ((N : ℝ) - 1) * (N : ℝ)) := by dsimp [g]; ring

private theorem sqrt_three_bounds :
    (1.732 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 1.7321 := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.732)]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.7321)]
    exact Real.sqrt_le_sqrt (by norm_num)

private theorem log_three_five_seven_lower :
    (1.098 : ℝ) ≤ Real.log 3 ∧ (1.609 : ℝ) ≤ Real.log 5 ∧ (1.945 : ℝ) ≤ Real.log 7 := by
  have h2 := Real.log_two_gt_d9
  have h3 : 84 * Real.log 2 ≤ 53 * Real.log 3 := by
    have h := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 84)
      (by norm_num : (2 : ℝ) ^ 84 ≤ 3 ^ 53)
    simp only [Real.log_pow] at h; push_cast at h; linarith
  have h5 : 65 * Real.log 2 ≤ 28 * Real.log 5 := by
    have h := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 65)
      (by norm_num : (2 : ℝ) ^ 65 ≤ 5 ^ 28)
    simp only [Real.log_pow] at h; push_cast at h; linarith
  have h7 : 87 * Real.log 2 ≤ 31 * Real.log 7 := by
    have h := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 87)
      (by norm_num : (2 : ℝ) ^ 87 ≤ 7 ^ 31)
    simp only [Real.log_pow] at h; push_cast at h; linarith
  refine ⟨by linarith, by linarith, by linarith⟩

private theorem curvature_term_two_bounds :
    (-202 / 100000 : ℝ) ≤ factorialCriticalPrimeHarmonicCharge 2 / (2 : ℝ) ^ 3 *
        criticalBandSineMoment 2 ∧
      factorialCriticalPrimeHarmonicCharge 2 / (2 : ℝ) ^ 3 *
        criticalBandSineMoment 2 ≤ -201 / 100000 := by
  rw [factorialCriticalPrimeHarmonicCharge_two, criticalBandSineMoment_eq (by norm_num)]
  push_cast
  have hcos : Real.cos (Real.pi / 6 * 2) = 1 / 2 := by
    rw [show Real.pi / 6 * 2 = Real.pi / 3 by ring, Real.cos_pi_div_three]
  have hsin : Real.sin (Real.pi / 6 * 2) = Real.sqrt 3 / 2 := by
    rw [show Real.pi / 6 * 2 = Real.pi / 3 by ring, Real.sin_pi_div_three]
  rw [hcos, hsin]
  obtain ⟨hs1, hs2⟩ := sqrt_three_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hps1 : 3.1415 * 1.732 ≤ Real.pi * Real.sqrt 3 :=
    mul_le_mul hp1.le hs1 (by norm_num) (by positivity)
  have hps2 : Real.pi * Real.sqrt 3 ≤ 3.1416 * 1.7321 :=
    mul_le_mul hp2.le hs2 (by positivity) (by norm_num)
  constructor <;> nlinarith

private theorem curvature_term_three_bounds :
    (193 / 100000 : ℝ) ≤ factorialCriticalPrimeHarmonicCharge 3 / (3 : ℝ) ^ 3 *
        criticalBandSineMoment 3 ∧
      factorialCriticalPrimeHarmonicCharge 3 / (3 : ℝ) ^ 3 *
        criticalBandSineMoment 3 ≤ 195 / 100000 := by
  rw [factorialCriticalPrimeHarmonicCharge_odd_prime Nat.prime_three (by norm_num),
    criticalBandSineMoment_eq (by norm_num)]
  push_cast
  have hcos : Real.cos (Real.pi / 6 * 3) = 0 := by
    rw [show Real.pi / 6 * 3 = Real.pi / 2 by ring, Real.cos_pi_div_two]
  have hsin : Real.sin (Real.pi / 6 * 3) = 1 := by
    rw [show Real.pi / 6 * 3 = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [hcos, hsin]
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hl1 := log_three_five_seven_lower.1
  have hl2 : Real.log 3 ≤ 1.10 := by
    have h := Real.log_le_log (by norm_num : 0 < (3 : ℝ) ^ 41)
      (by norm_num : (3 : ℝ) ^ 41 ≤ 2 ^ 65)
    simp only [Real.log_pow] at h; push_cast at h
    linarith [Real.log_two_lt_d9]
  constructor <;> nlinarith

private theorem curvature_term_five_bounds :
    (124 / 100000 : ℝ) ≤ factorialCriticalPrimeHarmonicCharge 5 / (5 : ℝ) ^ 3 *
        criticalBandSineMoment 5 ∧
      factorialCriticalPrimeHarmonicCharge 5 / (5 : ℝ) ^ 3 *
        criticalBandSineMoment 5 ≤ 126 / 100000 := by
  rw [factorialCriticalPrimeHarmonicCharge_odd_prime Nat.prime_five (by norm_num),
    criticalBandSineMoment_eq (by norm_num)]
  push_cast
  have hcos : Real.cos (Real.pi / 6 * 5) = -Real.sqrt 3 / 2 := by
    rw [show Real.pi / 6 * 5 = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_six]
    ring
  have hsin : Real.sin (Real.pi / 6 * 5) = 1 / 2 := by
    rw [show Real.pi / 6 * 5 = Real.pi - Real.pi / 6 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_six]
  rw [hcos, hsin]
  obtain ⟨hs1, hs2⟩ := sqrt_three_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hl1 := log_three_five_seven_lower.2.1
  have hl2 : Real.log 5 ≤ 1.62 := by
    have h := Real.log_le_log (by norm_num : 0 < (5 : ℝ) ^ 3) (by norm_num : (5 : ℝ) ^ 3 ≤ 2 ^ 7)
    simp only [Real.log_pow] at h; push_cast at h
    linarith [Real.log_two_lt_d9]
  constructor <;> nlinarith

private theorem curvature_term_seven_bounds :
    (64 / 100000 : ℝ) ≤ factorialCriticalPrimeHarmonicCharge 7 / (7 : ℝ) ^ 3 *
        criticalBandSineMoment 7 ∧
      factorialCriticalPrimeHarmonicCharge 7 / (7 : ℝ) ^ 3 *
        criticalBandSineMoment 7 ≤ 66 / 100000 := by
  have hp7 : Nat.Prime 7 := by decide
  rw [factorialCriticalPrimeHarmonicCharge_odd_prime hp7 (by norm_num),
    criticalBandSineMoment_eq (by norm_num)]
  push_cast
  have hcos : Real.cos (Real.pi / 6 * 7) = -Real.sqrt 3 / 2 := by
    rw [show Real.pi / 6 * 7 = Real.pi / 6 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_six]
    ring
  have hsin : Real.sin (Real.pi / 6 * 7) = -1 / 2 := by
    rw [show Real.pi / 6 * 7 = Real.pi / 6 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_six]
    ring
  rw [hcos, hsin]
  obtain ⟨hs1, hs2⟩ := sqrt_three_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hl1 := log_three_five_seven_lower.2.2
  have hl2 : Real.log 7 ≤ 1.97 := by
    have h := Real.log_le_log (by norm_num : 0 < (7 : ℝ) ^ 6) (by norm_num : (7 : ℝ) ^ 6 ≤ 2 ^ 17)
    simp only [Real.log_pow] at h; push_cast at h
    linarith [Real.log_two_lt_d9]
  constructor <;> nlinarith

private def criticalKernelCurvatureTerm (m : ℕ) : ℝ :=
  factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandSineMoment m

private theorem summable_criticalKernelCurvatureTerm :
    Summable criticalKernelCurvatureTerm :=
  summable_abs_criticalKernelCurvatureTerm.of_abs

private theorem criticalKernelCurvatureTerm_zero_of_one_or_mod_four {m : ℕ}
    (hm : m = 1 ∨ m % 4 = 0) : criticalKernelCurvatureTerm m = 0 := by
  simp [criticalKernelCurvatureTerm, (factorialCriticalPrimeHarmonicCharge_sign m).2.1.mpr hm]

private theorem criticalKernelCurvatureTerm_nonneg {m : ℕ} (hm2 : m ≠ 2) (hm12 : m ≤ 12) :
    0 ≤ criticalKernelCurvatureTerm m := by
  have hA : 0 ≤ factorialCriticalPrimeHarmonicCharge m :=
    le_of_not_gt fun h => hm2 ((factorialCriticalPrimeHarmonicCharge_sign m).1.mp h)
  exact mul_nonneg (div_nonneg hA (by positivity))
    (criticalBandSineMoment_nonneg_of_le_twelve hm12)

private theorem abs_criticalKernelCurvatureTerm_le_of_thirteen_le {m : ℕ} (hm : 13 ≤ m) :
    |criticalKernelCurvatureTerm m| ≤ (5 / 24) * (1 / (m : ℝ) ^ 3) := by
  have hm0 : 0 < m := by omega
  have hmR : (13 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hA := abs_factorialCriticalPrimeHarmonicCharge_le m
  have hlog := log_le_div_four_of_thirteen_le hmR
  have hμ := abs_criticalBandSineMoment_le hm0
  have hpi : Real.pi / 6 ≤ 0.5236 := by linarith [Real.pi_lt_d4]
  have hlin : 4 + Real.pi / 6 * (m : ℝ) ≤ (5 / 6) * m := by
    have := mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ (m : ℝ))
    linarith
  have hμ' : |criticalBandSineMoment m| ≤ (5 / 6) / (m : ℝ) ^ 2 := by
    refine hμ.trans ?_
    calc (4 + Real.pi / 6 * (m : ℝ)) / (m : ℝ) ^ 3
        ≤ ((5 / 6) * (m : ℝ)) / (m : ℝ) ^ 3 := div_le_div_of_nonneg_right hlin (by positivity)
      _ = (5 / 6) / (m : ℝ) ^ 2 := by field_simp
  have hA' : |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 ≤ (1 / 4) / (m : ℝ) := by
    have h1 : |factorialCriticalPrimeHarmonicCharge m| ≤ (m : ℝ) * ((m : ℝ) / 4) :=
      hA.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    calc |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3
        ≤ ((m : ℝ) * ((m : ℝ) / 4)) / (m : ℝ) ^ 3 := div_le_div_of_nonneg_right h1 (by positivity)
      _ = (1 / 4) / (m : ℝ) := by field_simp
  unfold criticalKernelCurvatureTerm
  rw [abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 * |criticalBandSineMoment m|
      ≤ (1 / 4) / (m : ℝ) * ((5 / 6) / (m : ℝ) ^ 2) :=
        mul_le_mul hA' hμ' (abs_nonneg _) (by positivity)
    _ = (5 / 24) * (1 / (m : ℝ) ^ 3) := by ring

private theorem abs_criticalKernelCurvatureTerm_le_of_nine_le {m : ℕ} (hm : 9 ≤ m) :
    |criticalKernelCurvatureTerm m| ≤ (3 / 10) * (1 / (m : ℝ) ^ 3) := by
  have hm0 : 0 < m := by omega
  have hmR : (9 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hA := abs_factorialCriticalPrimeHarmonicCharge_le m
  have hlog := log_le_three_tenths_of_nine_le hmR
  have hμ := abs_criticalBandSineMoment_le hm0
  have hpi : Real.pi / 6 ≤ 0.5236 := by linarith [Real.pi_lt_d4]
  have hlin : 4 + Real.pi / 6 * (m : ℝ) ≤ 1 * m := by
    have := mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ (m : ℝ))
    linarith
  have hμ' : |criticalBandSineMoment m| ≤ 1 / (m : ℝ) ^ 2 := by
    refine hμ.trans ?_
    calc (4 + Real.pi / 6 * (m : ℝ)) / (m : ℝ) ^ 3
        ≤ (1 * (m : ℝ)) / (m : ℝ) ^ 3 := div_le_div_of_nonneg_right hlin (by positivity)
      _ = 1 / (m : ℝ) ^ 2 := by field_simp
  have hA' : |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 ≤ (3 / 10) / (m : ℝ) := by
    have h1 : |factorialCriticalPrimeHarmonicCharge m| ≤ (m : ℝ) * ((3 / 10) * (m : ℝ)) :=
      hA.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    calc |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3
        ≤ ((m : ℝ) * ((3 / 10) * (m : ℝ))) / (m : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = (3 / 10) / (m : ℝ) := by field_simp
  unfold criticalKernelCurvatureTerm
  rw [abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 * |criticalBandSineMoment m|
      ≤ (3 / 10) / (m : ℝ) * (1 / (m : ℝ) ^ 2) :=
        mul_le_mul hA' hμ' (abs_nonneg _) (by positivity)
    _ = (3 / 10) * (1 / (m : ℝ) ^ 3) := by ring

private theorem criticalKernelCurvatureTerm_six_le :
    criticalKernelCurvatureTerm 6 ≤ 11 / 10000 := by
  unfold criticalKernelCurvatureTerm
  have hμ6 : criticalBandSineMoment 6 = 1 / 54 := by
    rw [criticalBandSineMoment_eq (by norm_num)]
    push_cast
    rw [show Real.pi / 6 * 6 = Real.pi by ring, Real.cos_pi, Real.sin_pi]
    norm_num
  have hA6 := abs_factorialCriticalPrimeHarmonicCharge_le 6
  have hl6 : Real.log 6 ≤ 2 := by
    have : (6 : ℝ) ≤ Real.exp 2 := by
      have : (2.7 : ℝ) ^ 2 ≤ Real.exp 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 2
      linarith
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
  have hle6 : factorialCriticalPrimeHarmonicCharge 6 ≤ 12 := by
    have := (le_abs_self _).trans hA6
    push_cast at this; linarith
  rw [hμ6]; push_cast; linarith

/-- **Explicit two-sided bounds on the spectral curvature constant `I₀`.**
`11 / 10000 ≤ criticalKernelCurvatureConstant ≤ 52 / 10000`. -/
theorem criticalKernelCurvatureConstant_bounds :
    11 / 10000 ≤ criticalKernelCurvatureConstant ∧
      criticalKernelCurvatureConstant ≤ 52 / 10000 := by
  have heq : criticalKernelCurvatureConstant = ∑' m : ℕ, criticalKernelCurvatureTerm m := rfl
  rw [heq]
  have hsf := summable_criticalKernelCurvatureTerm
  have hf0 : criticalKernelCurvatureTerm 0 = 0 := by simp [criticalKernelCurvatureTerm]
  have hf1 : criticalKernelCurvatureTerm 1 = 0 :=
    criticalKernelCurvatureTerm_zero_of_one_or_mod_four (Or.inl rfl)
  have hf4 : criticalKernelCurvatureTerm 4 = 0 :=
    criticalKernelCurvatureTerm_zero_of_one_or_mod_four (Or.inr (by norm_num))
  have hf8 : criticalKernelCurvatureTerm 8 = 0 :=
    criticalKernelCurvatureTerm_zero_of_one_or_mod_four (Or.inr (by norm_num))
  have hf12 : criticalKernelCurvatureTerm 12 = 0 :=
    criticalKernelCurvatureTerm_zero_of_one_or_mod_four (Or.inr (by norm_num))
  have h2 : (-202 / 100000 : ℝ) ≤ criticalKernelCurvatureTerm 2 ∧
      criticalKernelCurvatureTerm 2 ≤ -201 / 100000 := curvature_term_two_bounds
  have h3 : (193 / 100000 : ℝ) ≤ criticalKernelCurvatureTerm 3 ∧
      criticalKernelCurvatureTerm 3 ≤ 195 / 100000 := curvature_term_three_bounds
  have h5 : (124 / 100000 : ℝ) ≤ criticalKernelCurvatureTerm 5 ∧
      criticalKernelCurvatureTerm 5 ≤ 126 / 100000 := curvature_term_five_bounds
  have h7 : (64 / 100000 : ℝ) ≤ criticalKernelCurvatureTerm 7 ∧
      criticalKernelCurvatureTerm 7 ≤ 66 / 100000 := curvature_term_seven_bounds
  constructor
  · rw [← hsf.sum_add_tsum_nat_add 13]
    have htail13 : -(67 / 100000 : ℝ) ≤ ∑' j : ℕ, criticalKernelCurvatureTerm (j + 13) := by
      have hs13 : Summable fun j : ℕ => |criticalKernelCurvatureTerm (j + 13)| :=
        (summable_nat_add_iff 13).mpr summable_abs_criticalKernelCurvatureTerm
      have hc13 : Summable fun j : ℕ => (5 / 24) * (1 / ((j + 13 : ℕ) : ℝ) ^ 3) :=
        ((summable_nat_add_iff 13).mpr
          (Real.summable_one_div_nat_pow.mpr (by norm_num))).mul_left _
      have h1 : -(∑' j : ℕ, |criticalKernelCurvatureTerm (j + 13)|) ≤
          ∑' j : ℕ, criticalKernelCurvatureTerm (j + 13) := by
        rw [← tsum_neg]
        exact Summable.tsum_le_tsum (fun j => neg_le_of_abs_le le_rfl)
          hs13.neg ((summable_nat_add_iff 13).mpr hsf)
      have h2 : (∑' j : ℕ, |criticalKernelCurvatureTerm (j + 13)|) ≤
          (5 / 24) * ∑' j : ℕ, 1 / ((j + 13 : ℕ) : ℝ) ^ 3 := by
        rw [← tsum_mul_left]
        exact Summable.tsum_le_tsum
          (fun j => abs_criticalKernelCurvatureTerm_le_of_thirteen_le (by omega)) hs13 hc13
      have h3 : (∑' j : ℕ, 1 / ((j + 13 : ℕ) : ℝ) ^ 3) ≤ 1 / 312 :=
        (tsum_inv_cube_shift_le (N := 13) (by norm_num)).trans (by norm_num)
      linarith
    have hf6 := criticalKernelCurvatureTerm_nonneg (m := 6) (by norm_num) (by norm_num)
    have hf9 := criticalKernelCurvatureTerm_nonneg (m := 9) (by norm_num) (by norm_num)
    have hf10 := criticalKernelCurvatureTerm_nonneg (m := 10) (by norm_num) (by norm_num)
    have hf11 := criticalKernelCurvatureTerm_nonneg (m := 11) (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      hf0, hf1, hf4, hf8, hf12]
    linarith [h2.1, h3.1, h5.1, h7.1]
  · rw [← hsf.sum_add_tsum_nat_add 9]
    have htail9 : ∑' j : ℕ, criticalKernelCurvatureTerm (j + 9) ≤ 21 / 10000 := by
      have hs9 : Summable fun j : ℕ => |criticalKernelCurvatureTerm (j + 9)| :=
        (summable_nat_add_iff 9).mpr summable_abs_criticalKernelCurvatureTerm
      have hc9 : Summable fun j : ℕ => (3 / 10) * (1 / ((j + 9 : ℕ) : ℝ) ^ 3) :=
        ((summable_nat_add_iff 9).mpr
          (Real.summable_one_div_nat_pow.mpr (by norm_num))).mul_left _
      have h1 : ∑' j : ℕ, criticalKernelCurvatureTerm (j + 9) ≤
          ∑' j : ℕ, |criticalKernelCurvatureTerm (j + 9)| :=
        Summable.tsum_le_tsum (fun j => le_abs_self _) ((summable_nat_add_iff 9).mpr hsf) hs9
      have h2 : (∑' j : ℕ, |criticalKernelCurvatureTerm (j + 9)|) ≤
          (3 / 10) * ∑' j : ℕ, 1 / ((j + 9 : ℕ) : ℝ) ^ 3 := by
        rw [← tsum_mul_left]
        exact Summable.tsum_le_tsum
          (fun j => abs_criticalKernelCurvatureTerm_le_of_nine_le (by omega)) hs9 hc9
      have h3 : (∑' j : ℕ, 1 / ((j + 9 : ℕ) : ℝ) ^ 3) ≤ 1 / 144 :=
        (tsum_inv_cube_shift_le (N := 9) (by norm_num)).trans (by norm_num)
      linarith
    have hf6 := criticalKernelCurvatureTerm_six_le
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      hf0, hf1, hf4, hf8]
    linarith [h2.2, h3.2, h5.2, h7.2]

/-! ## Section 5: Spectral perturbation master theorem and the scale couplings `κ(k)` -/

/-- **Spectral perturbation master theorem.** If a band-integrable weight `g m ξ` approximates
`C₀ (π/6 - ξ) ξ sin(mξ)` with error at most `ε₀ (π/6 - ξ) ξ |sin(mξ)|` on `(0, π/6]`, then its
harmonic charge series approximates `C₀ I₀` within `ε₀ M_abs`. -/
theorem abs_tsum_charge_band_integral_sub_le (g : ℕ → ℝ → ℝ)
    (hg : ∀ m, IntervalIntegrable (g m) volume 0 (Real.pi / 6)) {C₀ ε₀ : ℝ}
    (hpt : ∀ m, ∀ ξ ∈ Ioc (0 : ℝ) (Real.pi / 6),
      |g m ξ - C₀ * ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m))| ≤
        ε₀ * ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|)) :
    (Summable fun m : ℕ =>
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) ∧
    |(∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) - C₀ * criticalKernelCurvatureConstant| ≤
      ε₀ * criticalKernelAbsMoment := by
  have hint_diff (m : ℕ) :
      |(∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) - C₀ * criticalBandSineMoment m| ≤
        ε₀ * criticalBandAbsSineMoment m := by
    unfold criticalBandSineMoment criticalBandAbsSineMoment
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hg m) (by apply Continuous.intervalIntegrable; fun_prop),
      ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le (by positivity) ?_
      (by apply Continuous.intervalIntegrable; fun_prop)
    exact Eventually.of_forall fun ξ hξ => by
      rw [Real.norm_eq_abs]
      exact hpt m ξ hξ
  have hterm_diff (m : ℕ) :
      |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
          (∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) -
        C₀ * (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
          criticalBandSineMoment m)| ≤
        ε₀ * (|factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 *
          criticalBandAbsSineMoment m) := by
    have heq : factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        (∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) -
      C₀ * (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        criticalBandSineMoment m) =
      (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3) *
        ((∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) - C₀ * criticalBandSineMoment m) := by ring
    rw [heq, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    calc |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 *
          |(∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) - C₀ * criticalBandSineMoment m|
        ≤ |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 *
            (ε₀ * criticalBandAbsSineMoment m) :=
          mul_le_mul_of_nonneg_left (hint_diff m) (div_nonneg (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hs_curv := summable_abs_criticalKernelCurvatureTerm.of_abs
  have hs_diff : Summable fun m : ℕ =>
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        (∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) -
      C₀ * (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        criticalBandSineMoment m) := by
    refine (summable_criticalKernelAbsMoment.mul_left ε₀).of_norm_bounded fun m => ?_
    rw [Real.norm_eq_abs]
    exact hterm_diff m
  have hs_g : Summable fun m : ℕ =>
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ := by
    refine (hs_diff.add (hs_curv.mul_left C₀)).congr fun m => by ring
  refine ⟨hs_g, ?_⟩
  unfold criticalKernelCurvatureConstant criticalKernelAbsMoment
  rw [← tsum_mul_left, ← hs_g.tsum_sub (hs_curv.mul_left C₀), ← Real.norm_eq_abs, ← tsum_mul_left]
  exact tsum_of_norm_bounded (summable_criticalKernelAbsMoment.mul_left ε₀).hasSum fun m => by
    rw [Real.norm_eq_abs]
    exact hterm_diff m

/-- **Two-sided asymptotic and error bound for the scale couplings `κ(k)` (`k ≥ 1`).**
`|κ(k) - I₀ / (4π²k²)| ≤ (14 / 100000) / (4π²k⁴)`. -/
theorem abs_factorialCriticalPrimeCoupling_sub_le {k : ℕ} (hk : 1 ≤ k) :
    |factorialCriticalPrimeCoupling k -
        criticalKernelCurvatureConstant / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)| ≤
      (14 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 4) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
  have hpi := Real.pi_pos
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  have hD : 0 < 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - (Real.pi / 6) ^ 2 := by nlinarith
  let g : ℕ → ℝ → ℝ := fun m ξ =>
    (Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2)
  have hg (m : ℕ) : IntervalIntegrable (g m) volume 0 (Real.pi / 6) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by positivity)]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ξ hξ => ?_
    have : ξ ^ 2 ≤ (Real.pi / 6) ^ 2 := pow_le_pow_left₀ hξ.1 hξ.2 2
    linarith
  have hpt (m : ℕ) (ξ : ℝ) (hξ : ξ ∈ Ioc (0 : ℝ) (Real.pi / 6)) :
      |g m ξ - (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) *
          ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m))| ≤
        (1 / (143 * (4 * Real.pi ^ 2 * (k : ℝ) ^ 4))) *
          ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|) := by
    dsimp [g]
    have hξ2 : ξ ^ 2 ≤ (Real.pi / 6) ^ 2 := pow_le_pow_left₀ hξ.1.le hξ.2 2
    have hden : 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - (Real.pi / 6) ^ 2 ≤
        4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2 := by linarith
    have hden_pos : 0 < 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2 := hD.trans_le hden
    have hk0 : 0 < 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
    have hd_ne : 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2 ≠ 0 := hden_pos.ne'
    have hk_ne : 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 ≠ 0 := hk0.ne'
    have hfac : (Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m) /
          (4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2) -
        (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) *
          ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m)) =
        ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m)) *
          (ξ ^ 2 / ((4 * Real.pi ^ 2 * (k : ℝ) ^ 2) *
            (4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2))) := by
      set A := (Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m)
      set B := 4 * Real.pi ^ 2 * (k : ℝ) ^ 2
      set D := 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2
      have hBD : B - D = ξ ^ 2 := by dsimp [B, D]; ring
      rw [one_div_mul_eq_div, div_sub_div _ _ hd_ne hk_ne, mul_comm D B, ← hBD]
      ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (by linarith [hξ.2]) hξ.1.le),
      abs_div, abs_of_nonneg (sq_nonneg ξ), abs_of_pos (mul_pos hk0 hden_pos),
      mul_comm ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|)]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (mul_nonneg (by linarith [hξ.2]) hξ.1.le) (abs_nonneg _))
    rw [div_le_div_iff₀ (mul_pos hk0 hden_pos) (by positivity)]
    have h143 : 143 * (Real.pi / 6) ^ 2 * (k : ℝ) ^ 2 ≤
        4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - (Real.pi / 6) ^ 2 := by
      have : 144 * (Real.pi / 6) ^ 2 * (k : ℝ) ^ 2 = 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by ring
      nlinarith
    have hmul : ξ ^ 2 * (143 * (4 * Real.pi ^ 2 * (k : ℝ) ^ 4)) ≤
        (Real.pi / 6) ^ 2 * (143 * (4 * Real.pi ^ 2 * (k : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_right hξ2 (by positivity)
    have hmul2 : (Real.pi / 6) ^ 2 * (143 * (4 * Real.pi ^ 2 * (k : ℝ) ^ 4)) =
        (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) * (143 * (Real.pi / 6) ^ 2 * (k : ℝ) ^ 2) := by ring
    have hmul3 : (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) * (143 * (Real.pi / 6) ^ 2 * (k : ℝ) ^ 2) ≤
        (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) * (4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2) :=
      mul_le_mul_of_nonneg_left (h143.trans hden) hk0.le
    linarith
  have hmaster := (abs_tsum_charge_band_integral_sub_le g hg hpt).2
  rw [factorialCriticalPrimeCoupling_eq_tsum hk]
  change |(∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
      ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ) -
    criticalKernelCurvatureConstant / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)| ≤ _
  rw [show criticalKernelCurvatureConstant / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) =
    (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * criticalKernelCurvatureConstant by ring]
  refine hmaster.trans ?_
  have hM := criticalKernelAbsMoment_le
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : criticalKernelAbsMoment * (4 * Real.pi ^ 2 * (k : ℝ) ^ 4) ≤
      (19 / 1000) * (4 * Real.pi ^ 2 * (k : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_right hM (by positivity)
  nlinarith

/-- **Explicit two-sided bounds on the scale couplings `κ(k)` (`k ≥ 1`).**
Every off-diagonal scale coupling is strictly positive and decays as `≍ 1 / k²`. -/
theorem factorialCriticalPrimeCoupling_bounds {k : ℕ} (hk : 1 ≤ k) :
    (96 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) ≤ factorialCriticalPrimeCoupling k ∧
      factorialCriticalPrimeCoupling k ≤ (534 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk24 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
    nlinarith
  have herr : (14 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 4) ≤
      (14 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hk24 (by positivity)
  have hsub := (abs_factorialCriticalPrimeCoupling_sub_le hk).trans herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp hsub
  obtain ⟨hI1, hI2⟩ := criticalKernelCurvatureConstant_bounds
  have hmain1 : (110 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) ≤
      criticalKernelCurvatureConstant / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hmain2 : criticalKernelCurvatureConstant / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) ≤
      (520 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hadd1 : (110 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) -
      (14 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) =
      (96 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by ring
  have hadd2 : (520 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) +
      (14 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) =
      (534 / 100000) / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by ring
  constructor <;> linarith

theorem factorialCriticalPrimeCoupling_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < factorialCriticalPrimeCoupling k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact lt_of_lt_of_le (by positivity) (factorialCriticalPrimeCoupling_bounds hk).1

/-- **Explicit numerical bounds on the first scale coupling `κ(1)`.** -/
theorem factorialCriticalPrimeCoupling_one_bounds :
    1 / 50000 ≤ factorialCriticalPrimeCoupling 1 ∧
      factorialCriticalPrimeCoupling 1 ≤ 1 / 6000 := by
  obtain ⟨h1, h2⟩ := factorialCriticalPrimeCoupling_bounds (k := 1) le_rfl
  push_cast at h1 h2
  have hp1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hp2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hlo : (1 / 50000 : ℝ) ≤ (96 / 100000) / (4 * Real.pi ^ 2 * 1 ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.pi ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hp2.le 2
    linarith
  have hhi : (534 / 100000) / (4 * Real.pi ^ 2 * 1 ^ 2) ≤ 1 / 6000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 3.14 ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) hp1.le 2
    linarith
  exact ⟨hlo.trans h1, h2.trans hhi⟩

/-- **Explicit numerical bounds on the second scale coupling `κ(2)`.** -/
theorem factorialCriticalPrimeCoupling_two_bounds :
    1 / 200000 ≤ factorialCriticalPrimeCoupling 2 ∧
      factorialCriticalPrimeCoupling 2 ≤ 1 / 24000 := by
  obtain ⟨h1, h2⟩ := factorialCriticalPrimeCoupling_bounds (k := 2) (by norm_num)
  push_cast at h1 h2
  have hp1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hp2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hlo : (1 / 200000 : ℝ) ≤ (96 / 100000) / (4 * Real.pi ^ 2 * 2 ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.pi ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hp2.le 2
    linarith
  have hhi : (534 / 100000) / (4 * Real.pi ^ 2 * 2 ^ 2) ≤ 1 / 24000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 3.14 ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) hp1.le 2
    linarith
  exact ⟨hlo.trans h1, h2.trans hhi⟩

/-! ## Section 6: Quadratic difference bounds, strict monotonicity and exact extrema of `R` -/

private theorem cos_sub_cos_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b ^ 2 - a ^ 2) / 2 - (b ^ 4 - a ^ 4) / 24 ≤ Real.cos a - Real.cos b ∧
      Real.cos a - Real.cos b ≤ (b ^ 2 - a ^ 2) / 2 := by
  have hd_cos : ∀ u ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -Real.cos u) (Real.sin u) u :=
    fun u _ => (Real.hasDerivAt_cos u).neg.congr_deriv (by ring)
  have hd_u : ∀ u ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u :=
    fun u _ => ((hasDerivAt_pow 2 u).div_const 2).congr_deriv (by ring)
  have hd_u3 : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => u ^ 2 / 2 - u ^ 4 / 24) (u - u ^ 3 / 6) u :=
    fun u _ => (((hasDerivAt_pow 2 u).div_const 2).sub
      ((hasDerivAt_pow 4 u).div_const 24)).congr_deriv (by ring)
  have hi_cos : ∫ u in a..b, Real.sin u = Real.cos a - Real.cos b := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_cos
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  have hi_u : ∫ u in a..b, u = (b ^ 2 - a ^ 2) / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_u
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  have hi_u3 : ∫ u in a..b, (u - u ^ 3 / 6) = (b ^ 2 - a ^ 2) / 2 - (b ^ 4 - a ^ 4) / 24 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_u3
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  rw [← hi_cos, ← hi_u3, ← hi_u]
  constructor
  · refine intervalIntegral.integral_mono_on hab
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) fun u hu => ?_
    have hu0 : 0 ≤ u := ha.trans hu.1
    rcases hu0.eq_or_lt with rfl | hu_pos
    · simp
    · exact (Real.sin_gt_sub_cube hu_pos).le
  · refine intervalIntegral.integral_mono_on hab
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) fun u hu =>
      Real.sin_le (ha.trans hu.1)

private theorem abs_cos_sub_cos_div_sin_half_sub_le {ξ s₁ s₂ : ℝ}
    (hξ0 : 0 < ξ) (hξc : ξ ≤ Real.pi / 6) (hs2 : 0 ≤ s₂) (hs12 : s₂ ≤ s₁) (hs1 : s₁ ≤ 1 / 2) :
    |(Real.cos (ξ * s₂) - Real.cos (ξ * s₁)) / Real.sin (ξ / 2) - (s₁ ^ 2 - s₂ ^ 2) * ξ| ≤
      (1 / 50) * ((s₁ ^ 2 - s₂ ^ 2) * ξ) := by
  set x := ξ / 2
  set S := Real.sin x
  have hξx : ξ = 2 * x := by dsimp [x]; ring
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 3 / 10 := by dsimp [x]; linarith [Real.pi_lt_d2]
  have hx2 : x ^ 2 ≤ 9 / 100 := by nlinarith
  have hx3 : x ^ 3 ≤ (9 / 100) * x := by
    have : x ^ 3 = x * x ^ 2 := by ring
    nlinarith
  have hS_lo : x - x ^ 3 / 6 < S := Real.sin_gt_sub_cube hx0
  have hS_hi : S ≤ x := Real.sin_le hx0.le
  have hS_pos : 0 < S := by linarith
  have hs_diff : 0 ≤ s₁ ^ 2 - s₂ ^ 2 := by
    have : s₂ ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ hs2 hs12 2
    linarith
  obtain ⟨hc_lo, hc_hi⟩ := cos_sub_cos_bounds (a := ξ * s₂) (b := ξ * s₁)
    (by positivity) (mul_le_mul_of_nonneg_left hs12 hξ0.le)
  have hba2 : ((ξ * s₁) ^ 2 - (ξ * s₂) ^ 2) / 2 = 2 * (s₁ ^ 2 - s₂ ^ 2) * x ^ 2 := by
    rw [hξx]; ring
  have hba4 : ((ξ * s₁) ^ 4 - (ξ * s₂) ^ 4) / 24 ≤ (1 / 3) * (s₁ ^ 2 - s₂ ^ 2) * x ^ 4 := by
    have hfac : ((ξ * s₁) ^ 4 - (ξ * s₂) ^ 4) / 24 =
        (1 / 6) * (s₁ ^ 2 - s₂ ^ 2) * x ^ 2 * ((ξ * s₁) ^ 2 + (ξ * s₂) ^ 2) := by
      rw [hξx]; ring
    have hsum : (ξ * s₁) ^ 2 + (ξ * s₂) ^ 2 ≤ 2 * x ^ 2 := by
      have h1 : s₁ ^ 2 ≤ 1 / 4 := by nlinarith
      have h2 : s₂ ^ 2 ≤ 1 / 4 := by nlinarith
      rw [hξx]
      have : (2 * x * s₁) ^ 2 + (2 * x * s₂) ^ 2 = 4 * x ^ 2 * (s₁ ^ 2 + s₂ ^ 2) := by ring
      nlinarith
    rw [hfac]
    have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (1 / 6) * (s₁ ^ 2 - s₂ ^ 2) * x ^ 2)
    linarith
  have hS_mul_lo : 2 * (s₁ ^ 2 - s₂ ^ 2) * x ^ 2 - (1 / 3) * (s₁ ^ 2 - s₂ ^ 2) * x ^ 4 ≤
      2 * (s₁ ^ 2 - s₂ ^ 2) * x * S := by
    have := mul_le_mul_of_nonneg_left hS_lo.le (by positivity : 0 ≤ 2 * (s₁ ^ 2 - s₂ ^ 2) * x)
    linarith
  have hS_mul_hi : 2 * (s₁ ^ 2 - s₂ ^ 2) * x * S ≤ 2 * (s₁ ^ 2 - s₂ ^ 2) * x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hS_hi (by positivity : 0 ≤ 2 * (s₁ ^ 2 - s₂ ^ 2) * x)
    linarith
  have hnum : |(Real.cos (ξ * s₂) - Real.cos (ξ * s₁)) - (s₁ ^ 2 - s₂ ^ 2) * ξ * S| ≤
      (1 / 50) * ((s₁ ^ 2 - s₂ ^ 2) * ξ) * S := by
    have hx4_le : (1 / 3) * x ^ 3 ≤ (1 / 50) * 2 * S := by linarith
    have hx4_mul := mul_le_mul_of_nonneg_left hx4_le (mul_nonneg hs_diff hx0.le)
    have hξS1 : (s₁ ^ 2 - s₂ ^ 2) * ξ * S = 2 * (s₁ ^ 2 - s₂ ^ 2) * x * S := by
      rw [hξx]; ring
    have hξS2 : (1 / 50) * ((s₁ ^ 2 - s₂ ^ 2) * ξ) * S =
        (s₁ ^ 2 - s₂ ^ 2) * x * (1 / 50 * 2 * S) := by
      rw [hξx]; ring
    have hx4_eq : (s₁ ^ 2 - s₂ ^ 2) * x * (1 / 3 * x ^ 3) =
        (1 / 3) * (s₁ ^ 2 - s₂ ^ 2) * x ^ 4 := by ring
    rw [hξS1, hξS2, abs_le]
    constructor <;> linarith
  have hrw : (Real.cos (ξ * s₂) - Real.cos (ξ * s₁)) / S - (s₁ ^ 2 - s₂ ^ 2) * ξ =
      ((Real.cos (ξ * s₂) - Real.cos (ξ * s₁)) - (s₁ ^ 2 - s₂ ^ 2) * ξ * S) / S := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hS_pos, div_le_iff₀ hS_pos]
  exact hnum

/-- **Quadratic difference bounds of the critical kernel on `[0, 1/2]`.**
For `0 ≤ t₁ ≤ t₂ ≤ 1/2`,
`(7 / 20000) ((1/2 - t₁)² - (1/2 - t₂)²) ≤ R(t₁) - R(t₂) ≤ (56 / 20000) ((1/2 - t₁)² - (1/2 - t₂)²)`. -/
theorem factorialCriticalPrimeContinuousRealKernel_sub_bounds {t₁ t₂ : ℝ}
    (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂) (ht2 : t₂ ≤ 1 / 2) :
    (7 / 20000) * ((1 / 2 - t₁) ^ 2 - (1 / 2 - t₂) ^ 2) ≤
        factorialCriticalPrimeContinuousRealKernel t₁ -
          factorialCriticalPrimeContinuousRealKernel t₂ ∧
      factorialCriticalPrimeContinuousRealKernel t₁ -
          factorialCriticalPrimeContinuousRealKernel t₂ ≤
        (56 / 20000) * ((1 / 2 - t₁) ^ 2 - (1 / 2 - t₂) ^ 2) := by
  have ht1_mem : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht1, by linarith⟩
  have ht2_mem : t₂ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set s₁ := 1 / 2 - t₁
  set s₂ := 1 / 2 - t₂
  have hs2 : 0 ≤ s₂ := by dsimp [s₂]; linarith
  have hs12 : s₂ ≤ s₁ := by dsimp [s₁, s₂]; linarith
  have hs1 : s₁ ≤ 1 / 2 := by dsimp [s₁]; linarith
  have hs_diff : 0 ≤ s₁ ^ 2 - s₂ ^ 2 := by
    have : s₂ ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ hs2 hs12 2
    linarith
  let g : ℕ → ℝ → ℝ := fun m ξ =>
    (Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t₂ - criticalBandWindowCos m ξ t₁)
  have hg (m : ℕ) : IntervalIntegrable (g m) volume 0 (Real.pi / 6) := by
    apply Continuous.intervalIntegrable
    dsimp [g]; unfold criticalBandWindowCos; fun_prop
  have hpt (m : ℕ) (ξ : ℝ) (hξ : ξ ∈ Ioc (0 : ℝ) (Real.pi / 6)) :
      |g m ξ - (s₁ ^ 2 - s₂ ^ 2) * ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m))| ≤
        ((1 / 50) * (s₁ ^ 2 - s₂ ^ 2)) * ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|) := by
    obtain ⟨hξ0, hξc⟩ := hξ
    have hpi := Real.pi_gt_three
    have hs_sin : 0 < Real.sin (ξ / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
    have hD1 : criticalBandWindowCos m ξ t₁ =
        Real.cos (ξ * s₁) * Real.sin (ξ * m) / Real.sin (ξ / 2) := by
      unfold criticalBandWindowCos
      rw [eq_div_iff hs_sin.ne', mul_comm, sin_half_mul_bandWindowCos ξ t₁ m]
      have : Real.cos (ξ * (t₁ - 1 / 2)) = Real.cos (ξ * s₁) := by
        rw [← Real.cos_neg, show -(ξ * (t₁ - 1 / 2)) = ξ * s₁ by dsimp [s₁]; ring]
      rw [this]
    have hD2 : criticalBandWindowCos m ξ t₂ =
        Real.cos (ξ * s₂) * Real.sin (ξ * m) / Real.sin (ξ / 2) := by
      unfold criticalBandWindowCos
      rw [eq_div_iff hs_sin.ne', mul_comm, sin_half_mul_bandWindowCos ξ t₂ m]
      have : Real.cos (ξ * (t₂ - 1 / 2)) = Real.cos (ξ * s₂) := by
        rw [← Real.cos_neg, show -(ξ * (t₂ - 1 / 2)) = ξ * s₂ by dsimp [s₂]; ring]
      rw [this]
    dsimp [g]
    rw [hD1, hD2]
    have hfac : (Real.pi / 6 - ξ) *
          (Real.cos (ξ * s₂) * Real.sin (ξ * m) / Real.sin (ξ / 2) -
            Real.cos (ξ * s₁) * Real.sin (ξ * m) / Real.sin (ξ / 2)) -
        (s₁ ^ 2 - s₂ ^ 2) * ((Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m)) =
        (Real.pi / 6 - ξ) * Real.sin (ξ * m) *
          ((Real.cos (ξ * s₂) - Real.cos (ξ * s₁)) / Real.sin (ξ / 2) -
            (s₁ ^ 2 - s₂ ^ 2) * ξ) := by ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.pi / 6 - ξ)]
    have hdiff := abs_cos_sub_cos_div_sin_half_sub_le hξ0 hξc hs2 hs12 hs1
    calc (Real.pi / 6 - ξ) * |Real.sin (ξ * m)| *
          |(Real.cos (ξ * s₂) - Real.cos (ξ * s₁)) / Real.sin (ξ / 2) - (s₁ ^ 2 - s₂ ^ 2) * ξ|
        ≤ (Real.pi / 6 - ξ) * |Real.sin (ξ * m)| *
            ((1 / 50) * ((s₁ ^ 2 - s₂ ^ 2) * ξ)) :=
          mul_le_mul_of_nonneg_left hdiff (mul_nonneg (by linarith) (abs_nonneg _))
      _ = ((1 / 50) * (s₁ ^ 2 - s₂ ^ 2)) * ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|) := by
          ring
  have hmaster := (abs_tsum_charge_band_integral_sub_le g hg hpt).2
  have hdev_eq (m : ℕ) : ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ =
      criticalBandWindowDeviation m t₂ - criticalBandWindowDeviation m t₁ := by
    dsimp [g]
    unfold criticalBandWindowDeviation
    rw [criticalBandWindow_eq_integral m t₂, criticalBandWindow_eq_integral m t₁,
      sub_sub_sub_cancel_right, ← intervalIntegral.integral_sub
        (by apply Continuous.intervalIntegrable; unfold criticalBandWindowCos; fun_prop)
        (by apply Continuous.intervalIntegrable; unfold criticalBandWindowCos; fun_prop)]
    congr 1; funext ξ; ring
  have hR_diff : factorialCriticalPrimeContinuousRealKernel t₁ -
      factorialCriticalPrimeContinuousRealKernel t₂ =
      (1 / 2) * ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ := by
    rw [factorialCriticalPrimeContinuousRealKernel_eq ht1_mem,
      factorialCriticalPrimeContinuousRealKernel_eq ht2_mem]
    have hs1_dev := (summable_charge_mul_criticalBandWindowDeviation ht1_mem).of_abs
    have hs2_dev := (summable_charge_mul_criticalBandWindowDeviation ht2_mem).of_abs
    have htsum : (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
          criticalBandWindowDeviation m t₂) -
        (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
          criticalBandWindowDeviation m t₁) =
        ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
          ∫ ξ in (0 : ℝ)..Real.pi / 6, g m ξ := by
      rw [← hs2_dev.tsum_sub hs1_dev]
      refine tsum_congr fun m => ?_
      rw [hdev_eq m]; ring
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hmaster
  obtain ⟨hI1, hI2⟩ := criticalKernelCurvatureConstant_bounds
  have hM := criticalKernelAbsMoment_le
  have hI_lo : (11 / 10000) * (s₁ ^ 2 - s₂ ^ 2) ≤
      (s₁ ^ 2 - s₂ ^ 2) * criticalKernelCurvatureConstant := by
    have := mul_le_mul_of_nonneg_left hI1 hs_diff
    linarith
  have hI_hi : (s₁ ^ 2 - s₂ ^ 2) * criticalKernelCurvatureConstant ≤
      (52 / 10000) * (s₁ ^ 2 - s₂ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hI2 hs_diff
    linarith
  have hM_hi : (1 / 50) * (s₁ ^ 2 - s₂ ^ 2) * criticalKernelAbsMoment ≤
      (4 / 10000) * (s₁ ^ 2 - s₂ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ (1 / 50) * (s₁ ^ 2 - s₂ ^ 2))
    linarith
  rw [hR_diff]
  constructor <;> linarith

/-- **Strict antitonicity of the critical prime kernel on `[0, 1/2]`.** -/
theorem strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half :
    StrictAntiOn factorialCriticalPrimeContinuousRealKernel (Icc 0 (1 / 2)) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have hb := (factorialCriticalPrimeContinuousRealKernel_sub_bounds ht₁.1 hlt.le ht₂.2).1
  have hsq : 0 < (1 / 2 - t₁) ^ 2 - (1 / 2 - t₂) ^ 2 := by
    have : (1 / 2 - t₁) ^ 2 - (1 / 2 - t₂) ^ 2 = (t₂ - t₁) * (1 - t₁ - t₂) := by ring
    rw [this]
    exact mul_pos (by linarith) (by linarith [ht₁.2, ht₂.2])
  linarith

/-- **Strict monotonicity of the critical prime kernel on `[1/2, 1]`.** -/
theorem strictMonoOn_factorialCriticalPrimeContinuousRealKernel_Icc_half_one :
    StrictMonoOn factorialCriticalPrimeContinuousRealKernel (Icc (1 / 2) 1) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have h1 : 1 - t₂ ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [ht₂.2], by linarith [ht₁.1]⟩
  have h2 : 1 - t₁ ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [ht₁.2], by linarith [ht₁.1]⟩
  have hanti := strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half h1 h2 (by linarith)
  rwa [factorialCriticalPrimeContinuousRealKernel_reflect,
    factorialCriticalPrimeContinuousRealKernel_reflect] at hanti

/-- **Global extrema of the critical kernel on the unit cell.**
For every `t ∈ [0, 1]`, `R(1/2) ≤ R(t) ≤ R(0) = R(1)`. -/
theorem factorialCriticalPrimeContinuousRealKernel_mem_Icc_extrema {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    factorialCriticalPrimeContinuousRealKernel (1 / 2) ≤
        factorialCriticalPrimeContinuousRealKernel t ∧
      factorialCriticalPrimeContinuousRealKernel t ≤
        factorialCriticalPrimeContinuousRealKernel 0 := by
  rcases le_total t (1 / 2) with ht2 | ht2
  · have hanti := strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half.antitoneOn
    exact ⟨hanti ⟨ht.1, ht2⟩ ⟨by norm_num, le_rfl⟩ ht2,
      hanti ⟨le_rfl, by norm_num⟩ ⟨ht.1, ht2⟩ ht.1⟩
  · have h1t : 1 - t ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [ht.2], by linarith⟩
    have hanti := strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half.antitoneOn
    rw [← factorialCriticalPrimeContinuousRealKernel_reflect t]
    exact ⟨hanti h1t ⟨by norm_num, le_rfl⟩ h1t.2,
      hanti ⟨le_rfl, by norm_num⟩ h1t h1t.1⟩

/-- **Unique global minimum of `R` on `[0, 1]`.** `R(t) = R(1/2)` on `[0, 1]` if and only if
`t = 1/2`. -/
theorem factorialCriticalPrimeContinuousRealKernel_eq_min_iff {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    factorialCriticalPrimeContinuousRealKernel t =
      factorialCriticalPrimeContinuousRealKernel (1 / 2) ↔ t = 1 / 2 := by
  constructor
  · intro heq
    rcases lt_trichotomy t (1 / 2) with hlt | rfl | hgt
    · have := strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half
        ⟨ht.1, hlt.le⟩ ⟨by norm_num, le_rfl⟩ hlt
      linarith
    · rfl
    · have := strictMonoOn_factorialCriticalPrimeContinuousRealKernel_Icc_half_one
        ⟨le_rfl, by norm_num⟩ ⟨hgt.le, ht.2⟩ hgt
      linarith
  · rintro rfl; rfl

/-- **Unique global maxima of `R` on `[0, 1]`.** `R(t) = R(0)` on `[0, 1]` if and only if
`t = 0` or `t = 1`. -/
theorem factorialCriticalPrimeContinuousRealKernel_eq_max_iff {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    factorialCriticalPrimeContinuousRealKernel t =
      factorialCriticalPrimeContinuousRealKernel 0 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro heq
    rcases le_total t (1 / 2) with ht2 | ht2
    · rcases ht.1.eq_or_lt with h0 | h0
      · exact Or.inl h0.symm
      · have := strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half
          ⟨le_rfl, by norm_num⟩ ⟨ht.1, ht2⟩ h0
        linarith
    · rcases ht.2.eq_or_lt with h1 | h1
      · exact Or.inr h1
      · have h1t : 1 - t ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith, by linarith⟩
        have := strictAntiOn_factorialCriticalPrimeContinuousRealKernel_Icc_zero_half
          ⟨le_rfl, by norm_num⟩ h1t (by linarith)
        rw [factorialCriticalPrimeContinuousRealKernel_reflect] at this
        linarith
  · rintro (rfl | rfl)
    · rfl
    · have := factorialCriticalPrimeContinuousRealKernel_reflect 0
      simpa using this

/-- **Exact supremum of `R` on the unit cell.** `sup_{[0,1]} R = R(0)`. -/
theorem sSup_factorialCriticalPrimeContinuousRealKernel_eq :
    sSup (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1) =
      factorialCriticalPrimeContinuousRealKernel 0 := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ((nonempty_Icc.mpr zero_le_one).image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (factorialCriticalPrimeContinuousRealKernel_mem_Icc_extrema ht).2
  · exact le_csSup
      (isCompact_Icc.image_of_continuousOn
        continuousOn_factorialCriticalPrimeContinuousRealKernel).bddAbove
      (mem_image_of_mem _ ⟨le_rfl, zero_le_one⟩)

/-- **Exact infimum of `R` on the unit cell.** `inf_{[0,1]} R = R(1/2)`. -/
theorem sInf_factorialCriticalPrimeContinuousRealKernel_eq :
    sInf (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1) =
      factorialCriticalPrimeContinuousRealKernel (1 / 2) := by
  refine le_antisymm ?_ ?_
  · exact csInf_le
      (isCompact_Icc.image_of_continuousOn
        continuousOn_factorialCriticalPrimeContinuousRealKernel).bddBelow
      (mem_image_of_mem _ ⟨by norm_num, by norm_num⟩)
  · refine le_csInf ((nonempty_Icc.mpr zero_le_one).image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (factorialCriticalPrimeContinuousRealKernel_mem_Icc_extrema ht).1

/-- **Exact top of the Rayleigh spectral range of the limiting critical prime form.**
The least upper bound of `factorialCriticalPrimeRayleighSet` is `(4/π⁴) R(0)`. -/
theorem isLUB_factorialCriticalPrimeRayleighSet_exact :
    IsLUB factorialCriticalPrimeRayleighSet
      (4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel 0) := by
  rw [← sSup_factorialCriticalPrimeContinuousRealKernel_eq]
  exact isLUB_factorialCriticalPrimeRayleighSet

/-- **Exact bottom of the Rayleigh spectral range of the limiting critical prime form.**
The greatest lower bound of `factorialCriticalPrimeRayleighSet` is `(4/π⁴) R(1/2)`. -/
theorem isGLB_factorialCriticalPrimeRayleighSet_exact :
    IsGLB factorialCriticalPrimeRayleighSet
      (4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel (1 / 2)) := by
  rw [← sInf_factorialCriticalPrimeContinuousRealKernel_eq]
  exact isGLB_factorialCriticalPrimeRayleighSet

/-- **Exact oscillation bounds of the critical kernel `R(0) - R(1/2)` on the unit cell.** -/
theorem factorialCriticalPrimeContinuousRealKernel_oscillation_bounds :
    7 / 80000 ≤
        factorialCriticalPrimeContinuousRealKernel 0 -
          factorialCriticalPrimeContinuousRealKernel (1 / 2) ∧
      factorialCriticalPrimeContinuousRealKernel 0 -
          factorialCriticalPrimeContinuousRealKernel (1 / 2) ≤
        56 / 80000 := by
  have h := factorialCriticalPrimeContinuousRealKernel_sub_bounds
    (t₁ := 0) (t₂ := 1 / 2) le_rfl (by norm_num) le_rfl
  constructor <;> linarith

private theorem intervalIntegrable_kernel_zero_half :
    IntervalIntegrable factorialCriticalPrimeContinuousRealKernel volume 0 (1 / 2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num)]
  exact continuousOn_factorialCriticalPrimeContinuousRealKernel.mono
    (Icc_subset_Icc_right (by norm_num))

private theorem intervalIntegrable_kernel_half_one :
    IntervalIntegrable factorialCriticalPrimeContinuousRealKernel volume (1 / 2) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num)]
  exact continuousOn_factorialCriticalPrimeContinuousRealKernel.mono
    (Icc_subset_Icc_left (by norm_num))

private theorem factorialCriticalPrimeCoupling_zero_eq_two_mul_integral_half :
    factorialCriticalPrimeCoupling 0 =
      2 * ∫ t in (0 : ℝ)..(1 / 2), factorialCriticalPrimeContinuousRealKernel t := by
  unfold factorialCriticalPrimeCoupling
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  set R := factorialCriticalPrimeContinuousRealKernel
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    intervalIntegrable_kernel_zero_half intervalIntegrable_kernel_half_one
  have href : ∫ t in (1 / 2 : ℝ)..1, R t = ∫ t in (0 : ℝ)..(1 / 2), R t := by
    calc ∫ t in (1 / 2 : ℝ)..1, R t
        = ∫ t in (1 / 2 : ℝ)..1, R (1 - t) :=
          intervalIntegral.integral_congr fun t _ =>
            (factorialCriticalPrimeContinuousRealKernel_reflect t).symm
      _ = ∫ t in (1 - 1 : ℝ)..(1 - 1 / 2), R t :=
          intervalIntegral.integral_comp_sub_left R 1
      _ = ∫ t in (0 : ℝ)..(1 / 2), R t := by
          rw [show (1 - 1 : ℝ) = 0 by norm_num, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← hsplit, href]
  ring

/-- **Distance of the global maximum `R(0)` from the singleton mean `κ(0)`.**
`7 / 120000 ≤ R(0) - κ(0) ≤ 56 / 120000`. -/
theorem factorialCriticalPrimeContinuousRealKernel_zero_sub_coupling_zero_bounds :
    7 / 120000 ≤
        factorialCriticalPrimeContinuousRealKernel 0 - factorialCriticalPrimeCoupling 0 ∧
      factorialCriticalPrimeContinuousRealKernel 0 - factorialCriticalPrimeCoupling 0 ≤
        56 / 120000 := by
  set R := factorialCriticalPrimeContinuousRealKernel
  have hR_int : IntervalIntegrable (fun t => R 0 - R t) volume 0 (1 / 2) :=
    intervalIntegrable_const.sub intervalIntegrable_kernel_zero_half
  have hid : R 0 - factorialCriticalPrimeCoupling 0 =
      2 * ∫ t in (0 : ℝ)..(1 / 2), (R 0 - R t) := by
    rw [factorialCriticalPrimeCoupling_zero_eq_two_mul_integral_half,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_kernel_zero_half]
    simp; ring
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt (fun t : ℝ => t / 4 - (t - 1 / 2) ^ 3 / 3) ((1 / 2) ^ 2 - (1 / 2 - t) ^ 2) t := by
    intro t _
    exact (((hasDerivAt_id t).div_const 4).sub
      ((((hasDerivAt_id t).sub_const (1 / 2)).pow 3).div_const 3)).congr_deriv
      (by simp only [id_eq]; ring)
  have hmom : ∫ t in (0 : ℝ)..(1 / 2), ((1 / 2 : ℝ) ^ 2 - (1 / 2 - t) ^ 2) = 1 / 12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num
  rw [hid]
  have hlo : (7 / 20000) * (1 / 12) ≤ ∫ t in (0 : ℝ)..(1 / 2), (R 0 - R t) := by
    rw [← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop) hR_int fun t ht => ?_
    simpa [sub_zero] using
      (factorialCriticalPrimeContinuousRealKernel_sub_bounds le_rfl ht.1 ht.2).1
  have hhi : ∫ t in (0 : ℝ)..(1 / 2), (R 0 - R t) ≤ (56 / 20000) * (1 / 12) := by
    rw [← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num) hR_int
      (by apply Continuous.intervalIntegrable; fun_prop) fun t ht => ?_
    simpa [sub_zero] using
      (factorialCriticalPrimeContinuousRealKernel_sub_bounds le_rfl ht.1 ht.2).2
  constructor <;> linarith

/-- **Distance of the singleton mean `κ(0)` from the global minimum `R(1/2)`.**
`7 / 240000 ≤ κ(0) - R(1/2) ≤ 56 / 240000`. -/
theorem factorialCriticalPrimeCoupling_zero_sub_kernel_half_bounds :
    7 / 240000 ≤
        factorialCriticalPrimeCoupling 0 -
          factorialCriticalPrimeContinuousRealKernel (1 / 2) ∧
      factorialCriticalPrimeCoupling 0 -
          factorialCriticalPrimeContinuousRealKernel (1 / 2) ≤
        56 / 240000 := by
  set R := factorialCriticalPrimeContinuousRealKernel
  have hR_int : IntervalIntegrable (fun t => R t - R (1 / 2)) volume 0 (1 / 2) :=
    intervalIntegrable_kernel_zero_half.sub intervalIntegrable_const
  have hid : factorialCriticalPrimeCoupling 0 - R (1 / 2) =
      2 * ∫ t in (0 : ℝ)..(1 / 2), (R t - R (1 / 2)) := by
    rw [factorialCriticalPrimeCoupling_zero_eq_two_mul_integral_half,
      intervalIntegral.integral_sub intervalIntegrable_kernel_zero_half intervalIntegrable_const]
    simp; ring
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt (fun t : ℝ => (t - 1 / 2) ^ 3 / 3) ((1 / 2 - t) ^ 2) t := by
    intro t _
    exact ((((hasDerivAt_id t).sub_const (1 / 2)).pow 3).div_const 3).congr_deriv
      (by simp only [id_eq]; ring)
  have hmom : ∫ t in (0 : ℝ)..(1 / 2), (1 / 2 - t) ^ 2 = 1 / 24 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num
  rw [hid]
  have hlo : (7 / 20000) * (1 / 24) ≤ ∫ t in (0 : ℝ)..(1 / 2), (R t - R (1 / 2)) := by
    rw [← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop) hR_int fun t ht => ?_
    simpa [sub_self] using
      (factorialCriticalPrimeContinuousRealKernel_sub_bounds ht.1 ht.2 le_rfl).1
  have hhi : ∫ t in (0 : ℝ)..(1 / 2), (R t - R (1 / 2)) ≤ (56 / 20000) * (1 / 24) := by
    rw [← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num) hR_int
      (by apply Continuous.intervalIntegrable; fun_prop) fun t ht => ?_
    simpa [sub_self] using
      (factorialCriticalPrimeContinuousRealKernel_sub_bounds ht.1 ht.2 le_rfl).2
  constructor <;> linarith

end GaloisForLFunctions.ArithmeticPositivityTheory

