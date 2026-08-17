import GaloisForLFunctions.HTGeometry.BoundedPowerSeriesUnique
import GaloisForLFunctions.HTGeometry.HausdorffCDDMeasureSource

/-!
# The Stieltjes transform determines a finite source on the unit interval

In the compactified coordinate the Stieltjes kernel is `y/(1 + t y)`, and for `|t| < 1` it is the
geometric series

`y/(1 + t y) = ∑ (-t)^n y^{n+1}`,

uniformly on the unit interval.  Integrating term by term turns the Stieltjes transform into a
power series in `t` whose coefficients are exactly the moments.  Two finite sources with the same
transform near zero therefore have the same moments, and Hausdorff uniqueness identifies them.

This is what upgrades "the Stieltjes values agree" to "the measures agree" without any weak
compactness or Stone–Weierstrass argument: the geometric expansion and the uniqueness of bounded
power-series coefficients suffice.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Stieltjes kernel in the compactified coordinate. -/
def stieltjesKernel (t : ℝ) (y : HausdorffSourceSpace) : ℝ := (y : ℝ) / (1 + t * (y : ℝ))

theorem hasSum_stieltjesKernel {t : ℝ} (ht : |t| < 1) (y : HausdorffSourceSpace) :
    HasSum (fun n : ℕ => (-t) ^ n * (y : ℝ) ^ (n + 1)) (stieltjesKernel t y) := by
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := y.property.1
  have hy1 : (y : ℝ) ≤ 1 := y.property.2
  have hnorm : ‖-t * (y : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hy0]
    calc |t| * (y : ℝ) ≤ |t| * 1 := by
          exact mul_le_mul_of_nonneg_left hy1 (abs_nonneg t)
      _ = |t| := mul_one _
      _ < 1 := ht
  have hgeom := hasSum_geometric_of_norm_lt_one hnorm
  have hmul := hgeom.mul_left (y : ℝ)
  have hden : (1 : ℝ) - -t * (y : ℝ) = 1 + t * (y : ℝ) := by ring
  have hval : (y : ℝ) * (1 - -t * (y : ℝ))⁻¹ = stieltjesKernel t y := by
    rw [hden, stieltjesKernel, div_eq_mul_inv]
  rw [hval] at hmul
  refine hmul.congr_fun fun n => ?_
  rw [mul_pow]
  ring

/-- The moments are bounded by the total mass. -/
theorem abs_hausdorffMoment_le (ν : Measure HausdorffSourceSpace) [IsFiniteMeasure ν] (m : ℕ) :
    |hausdorffMoment ν m| ≤ (ν Set.univ).toReal := by
  have hbound : ∀ y : HausdorffSourceSpace, ‖(y : ℝ) ^ m‖ ≤ 1 := by
    intro y
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg y.property.1]
    exact pow_le_one₀ y.property.1 y.property.2
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun y : HausdorffSourceSpace => (y : ℝ) ^ m) (C := 1)
    (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at h
  simpa [hausdorffMoment, measureReal_def] using h

/-- **The Stieltjes transform is the moment generating series.** -/
theorem integral_stieltjesKernel_eq_tsum (ν : Measure HausdorffSourceSpace) [IsFiniteMeasure ν]
    {t : ℝ} (ht : |t| < 1) :
    ∫ y, stieltjesKernel t y ∂ν = ∑' n : ℕ, (-t) ^ n * hausdorffMoment ν (n + 1) := by
  have hcont : ∀ n : ℕ, Continuous
      (fun y : HausdorffSourceSpace => (-t) ^ n * (y : ℝ) ^ (n + 1)) := fun n =>
    continuous_const.mul (continuous_subtype_val.pow (n + 1))
  have hint : ∀ n : ℕ, Integrable
      (fun y : HausdorffSourceSpace => (-t) ^ n * (y : ℝ) ^ (n + 1)) ν := fun n =>
    (hcont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnormle : ∀ (n : ℕ) (y : HausdorffSourceSpace),
      ‖(-t) ^ n * (y : ℝ) ^ (n + 1)‖ ≤ |t| ^ n := by
    intro n y
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_pow, abs_of_nonneg y.property.1]
    have hy : (y : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ y.property.1 y.property.2
    calc |t| ^ n * (y : ℝ) ^ (n + 1) ≤ |t| ^ n * 1 :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = |t| ^ n := mul_one _
  have hnormint : ∀ n : ℕ,
      ∫ y, ‖(-t) ^ n * (y : ℝ) ^ (n + 1)‖ ∂ν ≤ |t| ^ n * (ν Set.univ).toReal := by
    intro n
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun y : HausdorffSourceSpace => (-t) ^ n * (y : ℝ) ^ (n + 1)) (C := |t| ^ n)
      (Filter.Eventually.of_forall (hnormle n))
    have hnn : 0 ≤ ∫ y, ‖(-t) ^ n * (y : ℝ) ^ (n + 1)‖ ∂ν :=
      integral_nonneg fun y => norm_nonneg _
    have hbd : ∫ y, ‖(-t) ^ n * (y : ℝ) ^ (n + 1)‖ ∂ν ≤ |t| ^ n * (ν Set.univ).toReal := by
      have hle := integral_mono ((hint n).norm) (integrable_const (|t| ^ n))
        (fun y => hnormle n y)
      simpa [measureReal_def, mul_comm] using hle
    exact hbd
  have hsummable : Summable fun n : ℕ => ∫ y, ‖(-t) ^ n * (y : ℝ) ^ (n + 1)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
      hnormint ?_
    exact (summable_geometric_of_lt_one (abs_nonneg t) ht).mul_right _
  have hsum := hasSum_integral_of_summable_integral_norm hint hsummable
  have hpoint : ∀ y : HausdorffSourceSpace,
      (∑' n : ℕ, (-t) ^ n * (y : ℝ) ^ (n + 1)) = stieltjesKernel t y := fun y =>
    (hasSum_stieltjesKernel ht y).tsum_eq
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)] at hsum
  have hmom : ∀ n : ℕ, (∫ y, (-t) ^ n * (y : ℝ) ^ (n + 1) ∂ν)
      = (-t) ^ n * hausdorffMoment ν (n + 1) := by
    intro n
    rw [hausdorffMoment, integral_const_mul]
  rw [← hsum.tsum_eq]
  exact tsum_congr hmom

/-- **The Stieltjes transform determines the source.**  Two finite sources with the same total mass
and the same Stieltjes transform on a neighbourhood of zero coincide. -/
theorem hausdorffSource_eq_of_stieltjes_eq {μ ν : Measure HausdorffSourceSpace}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : hausdorffMoment μ 0 = hausdorffMoment ν 0)
    (h : ∀ t : ℝ, 0 < |t| → |t| < r → ∫ y, stieltjesKernel t y ∂μ = ∫ y, stieltjesKernel t y ∂ν) :
    μ = ν := by
  set c : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * (hausdorffMoment μ (n + 1) - hausdorffMoment ν (n + 1))
    with hc
  set C : ℝ := (μ Set.univ).toReal + (ν Set.univ).toReal with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have := ENNReal.toReal_nonneg (a := μ Set.univ)
    have := ENNReal.toReal_nonneg (a := ν Set.univ)
    linarith
  have hbound : ∀ n, |c n| ≤ C := by
    intro n
    rw [hc]
    simp only
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    calc |hausdorffMoment μ (n + 1) - hausdorffMoment ν (n + 1)|
        ≤ |hausdorffMoment μ (n + 1)| + |hausdorffMoment ν (n + 1)| := by
            have hstep := abs_add_le (hausdorffMoment μ (n + 1)) (-hausdorffMoment ν (n + 1))
            simpa [sub_eq_add_neg] using hstep
      _ ≤ C := by
          have h1 := abs_hausdorffMoment_le μ (n + 1)
          have h2 := abs_hausdorffMoment_le ν (n + 1)
          rw [hC]
          linarith
  have hzero : ∀ t : ℝ, 0 < |t| → |t| < r → ∑' n : ℕ, c n * t ^ n = 0 := by
    intro t ht0 htr
    have ht1 : |t| < 1 := lt_of_lt_of_le htr hr1
    have hμ := integral_stieltjesKernel_eq_tsum μ ht1
    have hν := integral_stieltjesKernel_eq_tsum ν ht1
    have heq : (∑' n : ℕ, (-t) ^ n * hausdorffMoment μ (n + 1))
        = ∑' n : ℕ, (-t) ^ n * hausdorffMoment ν (n + 1) := by
      rw [← hμ, ← hν]
      exact h t ht0 htr
    have hsμ : Summable fun n : ℕ => (-t) ^ n * hausdorffMoment μ (n + 1) := by
      refine Summable.of_norm_bounded (g := fun n : ℕ => |t| ^ n * (μ Set.univ).toReal)
        ((summable_geometric_of_lt_one (abs_nonneg t) ht1).mul_right _) ?_
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_hausdorffMoment_le μ (n + 1)) (by positivity)
    have hsν : Summable fun n : ℕ => (-t) ^ n * hausdorffMoment ν (n + 1) := by
      refine Summable.of_norm_bounded (g := fun n : ℕ => |t| ^ n * (ν Set.univ).toReal)
        ((summable_geometric_of_lt_one (abs_nonneg t) ht1).mul_right _) ?_
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_hausdorffMoment_le ν (n + 1)) (by positivity)
    have hcongr : ∀ n : ℕ, c n * t ^ n
        = (-t) ^ n * hausdorffMoment μ (n + 1) - (-t) ^ n * hausdorffMoment ν (n + 1) := by
      intro n
      rw [hc]
      simp only
      rw [neg_pow]
      ring
    rw [tsum_congr hcongr, hsμ.tsum_sub hsν, heq, sub_self]
  have hmomzero := coeff_eq_zero_of_tsum_eq_zero hC0 hr hr1 hbound hzero
  refine hausdorffSource_eq_of_moments_eq ?_
  intro m
  cases m with
  | zero => exact h0
  | succ n =>
      have := hmomzero n
      rw [hc] at this
      simp only at this
      have hne : ((-1 : ℝ) ^ n) ≠ 0 := by
        exact pow_ne_zero n (by norm_num)
      have hsub := (mul_eq_zero.mp this).resolve_left hne
      linarith [hsub]

end GaloisForLFunctions.HTGeometry
