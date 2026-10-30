import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor

/-!
# The conductor scale of the completed energy

The first coprime Fourier-tail term retains both the factor `m/φ(m)` and the
tail threshold `c/m`. The tilted spline therefore has a seventh-power floor
below the overlap scale and a constant floor at every conductor above it.
-/

noncomputable section
open MeasureTheory Set Filter
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The first coprime term keeps the conductor-dependent Fourier-tail threshold. -/
theorem tiltedUnitSpline_completedConductorEnergy_ge_scaled_tail
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    (2 / (∫ u, tiltedUnitSpline u ^ 2)) * ((m : ℝ) / m.totient) *
        (∫ t in Ioi (c / m), shellSpectrum tiltedUnitSpline t) ≤
      completedConductorEnergy tiltedUnitSpline c m := by
  have hsum := hasSum_completedConductorEnergy contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm
  have hnonneg : ∀ n : ℕ, 0 ≤ (if Nat.Coprime m (n + 1) then
      2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
        ∫ t in Ioi (((n : ℝ) + 1) * c / m), shellSpectrum tiltedUnitSpline t else 0) := by
    intro n
    split_ifs
    · exact mul_nonneg (mul_nonneg (div_nonneg zero_le_two
        (mul_nonneg integral_tiltedUnitSpline_sq_pos.le (Nat.cast_nonneg _)))
        (div_nonneg (Nat.cast_nonneg _) (by positivity)))
        (setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t)
    · exact le_rfl
  have hfirst := le_hasSum hsum 0 fun n _ => hnonneg n
  simp only [Nat.coprime_one_right_eq_true, if_true, Nat.cast_zero, zero_add,
    one_mul, div_one] at hfirst
  refine (le_of_eq ?_).trans hfirst
  ring

private theorem tilted_tail_ge_at_one {z : ℝ} (hz : z ≤ 1) :
    tiltedSplineTailConstant ≤ ∫ t in Ioi z, shellSpectrum tiltedUnitSpline t := by
  have hfloor := tiltedSplineTailConstant_div_pow_le_shellTail (c := 1) le_rfl
  simp only [one_pow, div_one] at hfloor
  exact hfloor.trans (setIntegral_mono_set
    (integrableOn_shellSpectrum_Ioi contDiff_tiltedUnitSpline hasCompactSupport_tiltedUnitSpline z)
    (ae_of_all _ fun t => shellSpectrum_nonneg t)
    (Eventually.of_forall (Ioi_subset_Ioi hz)))

/-- Below the overlap scale the floor grows as `m⁸/φ(m)`; above it the floor
is a fixed positive multiple of `m/φ(m)`. -/
theorem tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    (2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) *
        ((m : ℝ) / m.totient) * min 1 (((m : ℝ) / c) ^ 7) ≤
      completedConductorEnergy tiltedUnitSpline c m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hM := integral_tiltedUnitSpline_sq_pos
  have hfirst := tiltedUnitSpline_completedConductorEnergy_ge_scaled_tail hc hm
  have hcoef : 0 ≤ (2 / (∫ u, tiltedUnitSpline u ^ 2)) * ((m : ℝ) / m.totient) := by
    positivity
  by_cases hmc : (m : ℝ) ≤ c
  · have hcm : 1 ≤ c / m := (one_le_div hm0).mpr hmc
    have hratio : ((m : ℝ) / c) ^ 7 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hm0.le hc.le)
        ((div_le_one hc).mpr hmc) 7
    rw [min_eq_right hratio]
    have htail := tiltedSplineTailConstant_div_pow_le_shellTail hcm
    calc
      _ = (2 / (∫ u, tiltedUnitSpline u ^ 2)) * ((m : ℝ) / m.totient) *
          (tiltedSplineTailConstant / (c / m) ^ 7) := by
        field_simp
      _ ≤ _ := (mul_le_mul_of_nonneg_left htail hcoef).trans hfirst
  · have hcm : c ≤ (m : ℝ) := (lt_of_not_ge hmc).le
    have hratio : 1 ≤ ((m : ℝ) / c) ^ 7 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        ((one_le_div hc).mpr hcm) 7
    rw [min_eq_left hratio]
    have htail := tilted_tail_ge_at_one ((div_le_one hm0).mpr hcm)
    calc
      _ = (2 / (∫ u, tiltedUnitSpline u ^ 2)) * ((m : ℝ) / m.totient) *
          tiltedSplineTailConstant := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left htail hcoef).trans hfirst

/-- Every conductor beyond the overlap scale has a common positive energy floor. -/
theorem tiltedUnitSpline_completedConductorEnergy_ge_above_overlap
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) (hcm : c ≤ (m : ℝ)) :
    2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2) ≤
      completedConductorEnergy tiltedUnitSpline c m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hratio : 1 ≤ ((m : ℝ) / c) ^ 7 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      ((one_le_div hc).mpr hcm) 7
  have hfloor := tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale hc hm
  rw [min_eq_left hratio, mul_one] at hfloor
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hcoef : 0 ≤ 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2) :=
    div_nonneg (mul_nonneg zero_le_two tiltedSplineTailConstant_pos.le)
      integral_tiltedUnitSpline_sq_pos.le
  exact (le_mul_of_one_le_right hcoef ((one_le_div htot).mpr htot_le)).trans hfloor

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tiltedUnitSpline_completedConductorEnergy_ge_scaled_tail
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tiltedUnitSpline_completedConductorEnergy_ge_above_overlap
