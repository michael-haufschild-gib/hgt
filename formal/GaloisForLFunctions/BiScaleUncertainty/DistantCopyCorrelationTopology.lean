import GaloisForLFunctions.BiScaleUncertainty.SignedGridEnergySources

/-!
# Exact correlation error of a separated copy

The scalar coefficient `a / (1 + a²)` is the exact global correlation error.
The bound is attained at the copy center, so uniform convergence is equivalent
to decay of that coefficient even when the centers vary.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def copyMixingCoefficient (a : ℝ) : ℝ := a / (1 + a ^ 2)

theorem abs_copyMixingCoefficient_le_half (a : ℝ) : |copyMixingCoefficient a| ≤ 1 / 2 := by
  have hd : 0 < 1 + a ^ 2 := by positivity
  rw [copyMixingCoefficient, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [sq_nonneg (|a| - 1), sq_abs a]

def normalizedSourceCorrelation (f : ℝ → ℝ) (x : ℝ) : ℝ := autocorr f x / autocorr f 0

theorem normalizedSourceCorrelation_zero {f : ℝ → ℝ} (hR : 0 < autocorr f 0) :
    normalizedSourceCorrelation f 0 = 1 := div_self hR.ne'

theorem normalizedSourceCorrelation_abs_le_one {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) (x : ℝ) :
    |normalizedSourceCorrelation f x| ≤ 1 := by
  rw [normalizedSourceCorrelation, abs_div, abs_of_pos hR]
  exact (div_le_one hR).mpr (abs_autocorr_le_zero hfc hf x)

theorem autocorr_subtractCopy_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D T : ℝ}
    (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D < T) (a : ℝ) :
    autocorr (subtractCopy f a T) 0 = (1 + a ^ 2) * autocorr f 0 := by
  exact autocorr_subtractCopy_local hf hfc (A := 0) hs (by simpa using hT) (by simp) a

theorem autocorr_subtractCopy_zero_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T : ℝ}
    (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D < T) (a : ℝ) :
    0 < autocorr (subtractCopy f a T) 0 := by
  rw [autocorr_subtractCopy_zero hf hfc hs hT a]
  positivity

/-- Exact normalized two-packet error, retaining the actual sign of the coefficient. -/
theorem normalizedSourceCorrelation_subtractCopy_sub {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D < T) (a x : ℝ) :
    normalizedSourceCorrelation (subtractCopy f a T) x - normalizedSourceCorrelation f x =
      -copyMixingCoefficient a *
        (normalizedSourceCorrelation f (x - T) + normalizedSourceCorrelation f (x + T)) := by
  unfold normalizedSourceCorrelation copyMixingCoefficient
  rw [autocorr_subtractCopy_zero hf hfc hs hT, autocorr_subtractCopy hf hfc]
  have hd : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hR.ne', hd]
  ring

/-- Disjoint translated correlation packets give the sharp global error upper bound. -/
theorem normalizedSourceCorrelation_subtractCopy_error_le {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D < T) (a x : ℝ) :
    |normalizedSourceCorrelation (subtractCopy f a T) x - normalizedSourceCorrelation f x| ≤
      |copyMixingCoefficient a| := by
  have hp : |normalizedSourceCorrelation f (x - T) + normalizedSourceCorrelation f (x + T)| ≤ 1 := by
    by_cases hz : normalizedSourceCorrelation f (x - T) = 0
    · rw [hz, zero_add]
      exact normalizedSourceCorrelation_abs_le_one hf hfc hR _
    · have hx : |x - T| ≤ D := le_of_not_gt fun h => hz (by
        simp only [normalizedSourceCorrelation, hs _ h, zero_div])
      have hright : D < |x + T| := lt_of_lt_of_le
        (by linarith only [(abs_le.mp hx).1, hT] : D < x + T) (le_abs_self _)
      have hz' : normalizedSourceCorrelation f (x + T) = 0 := by
        simp only [normalizedSourceCorrelation, hs _ hright, zero_div]
      rw [hz', add_zero]
      exact normalizedSourceCorrelation_abs_le_one hf hfc hR _
  rw [normalizedSourceCorrelation_subtractCopy_sub hf hfc hR hs hT, abs_mul, abs_neg]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (abs_nonneg (copyMixingCoefficient a))

/-- The copy center records the full signed mixing coefficient. -/
theorem normalizedSourceCorrelation_subtractCopy_center {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hD : 0 < D) (hs : ∀ x, D < |x| → autocorr f x = 0)
    (hT : D < T) (a : ℝ) :
    normalizedSourceCorrelation (subtractCopy f a T) T = -copyMixingCoefficient a := by
  have hz : normalizedSourceCorrelation f T = 0 := by
    simp only [normalizedSourceCorrelation, hs T (hT.trans_le (le_abs_self T)), zero_div]
  have hz2 : normalizedSourceCorrelation f (T + T) = 0 := by
    simp only [normalizedSourceCorrelation,
      hs (T + T) (lt_of_lt_of_le (by linarith : D < T + T) (le_abs_self _)), zero_div]
  have he := normalizedSourceCorrelation_subtractCopy_sub hf hfc hR hs hT a T
  simpa only [hz, sub_zero, sub_self, normalizedSourceCorrelation_zero hR, hz2,
    add_zero, mul_one] using he

/-- The global upper bound is attained at the moving copy center. -/
theorem normalizedSourceCorrelation_subtractCopy_error_at_center {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hD : 0 < D) (hs : ∀ x, D < |x| → autocorr f x = 0)
    (hT : D < T) (a : ℝ) :
    |normalizedSourceCorrelation (subtractCopy f a T) T - normalizedSourceCorrelation f T| =
      |copyMixingCoefficient a| := by
  rw [normalizedSourceCorrelation_subtractCopy_center hf hfc hR hD hs hT]
  have hz : normalizedSourceCorrelation f T = 0 := by
    simp only [normalizedSourceCorrelation, hs T (hT.trans_le (le_abs_self T)), zero_div]
  rw [hz, sub_zero, abs_neg]

/-- Global uniform convergence to the seed is exactly decay of the scalar mixing coefficient. -/
theorem tendstoUniformly_subtractCopy_iff_mixing {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D : ℝ} (hD : 0 < D) (hs : ∀ x, D < |x| → autocorr f x = 0)
    (a T : ℕ → ℝ) (hT : ∀ n, D < T n) :
    TendstoUniformly (fun n => normalizedSourceCorrelation (subtractCopy f (a n) (T n)))
      (normalizedSourceCorrelation f) atTop ↔
      Tendsto (fun n => copyMixingCoefficient (a n)) atTop (𝓝 0) := by
  constructor
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp h ε hε] with n hn
    have ht := hn (T n)
    rw [Real.dist_eq, abs_sub_comm,
      normalizedSourceCorrelation_subtractCopy_error_at_center hf hfc hR hD hs (hT n)] at ht
    simpa only [Real.dist_eq, sub_zero] using ht
  · intro h
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp h ε hε] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    apply (normalizedSourceCorrelation_subtractCopy_error_le hf hfc hR hs (hT n) (a n) x).trans_lt
    simpa only [Real.dist_eq, sub_zero] using hn

end

end GaloisForLFunctions.BiScaleUncertainty
