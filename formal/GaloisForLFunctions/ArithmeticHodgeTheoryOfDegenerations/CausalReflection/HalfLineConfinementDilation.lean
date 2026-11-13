import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCompressionEnergy
import GaloisForLFunctions.BiScaleUncertainty.FiniteSourceEnergyScalarization

/-!
# Compressed unit profiles on the negative half-line

Dilating a reflected compact spline gives unit profiles with exponentially
weighted mass at most `exp(8/a)` and Lévy cost at most `log a` plus a constant.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri BiScaleUncertainty

/-- A concrete negative-support seed gives the coefficient-one compression bound. -/
theorem exists_unit_halfLine_logarithmic_dilates :
    ∃ A C : ℝ, 1 ≤ A ∧ ∀ a : ℝ, A ≤ a →
      ∃ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F ∧ (∫ u, F u ^ 2) = 1 ∧
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ Real.exp (8 / a) ∧
        biScaleLevyEnergy F ≤ Real.log a + C := by
  let G : ℝ → ℝ := fun u => SpacingScaleHarmonicAnalysis.tiltedUnitSpline (-u)
  have hwin : CohomologyOfWindowsOfSpecZ.IsWindowTest 1 G := by
    refine ⟨SpacingScaleHarmonicAnalysis.contDiff_tiltedUnitSpline.comp contDiff_id.neg, ?_⟩
    intro u hu
    apply SpacingScaleHarmonicAnalysis.tiltedUnitSpline_eq_zero
    intro hm
    exact hu ⟨by linarith only [hm.2], by linarith only [hm.1]⟩
  have hdG := criticalHalfLineEnergyDomain_of_window hwin
  let m : ℝ := ∫ u, G u ^ 2
  have hm : 0 < m := by
    dsimp only [m, G]
    rw [integral_neg_eq_self (fun u => SpacingScaleHarmonicAnalysis.tiltedUnitSpline u ^ 2)]
    exact SpacingScaleHarmonicAnalysis.integral_tiltedUnitSpline_sq_pos
  have hmassG : autocorr G 0 = m := by simp only [autocorr, add_zero, ← pow_two]; rfl
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius hwin.hasCompactSupport
  obtain ⟨C, hC⟩ := exists_sourceRescale_logarithmic_energy_bound_of_support
    hwin.contDiff hwin.hasCompactSupport (hmassG.symm ▸ hm) hD hsupp
  refine ⟨max D 1, C, le_max_right _ _, ?_⟩
  intro a hAa
  have ha1 : 1 ≤ a := (le_max_right D 1).trans hAa
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hDa : D ≤ a := (le_max_left D 1).trans hAa
  let H : ℝ → ℝ := sourceRescale G a
  have hdH : CriticalHalfLineEnergyDomain H :=
    criticalHalfLineEnergyDomain_of_compact_negative (contDiff_sourceRescale hwin.contDiff a)
      (hasCompactSupport_sourceRescale hwin.hasCompactSupport ha)
      (fun u hu => hdG.support (a * u) (mul_nonneg ha.le hu))
  let c : ℝ := Real.sqrt (a / m)
  let F : ℝ → ℝ := fun u => c * H u
  have hc : c ^ 2 = a / m := Real.sq_sqrt (div_pos ha hm).le
  have hdF : CriticalHalfLineEnergyDomain F := hdH.const_mul c
  have hmassH : autocorr H 0 = a⁻¹ * m := by
    change autocorr (sourceRescale G a) 0 = _
    rw [autocorr_sourceRescale G ha, mul_zero, hmassG]
  have hmassF : (∫ u, F u ^ 2) = 1 := by
    change (∫ u, (c * H u) ^ 2) = 1
    rw [HTGeometry.integral_sq_const_mul, hc]
    have hmassH' : (∫ u, H u ^ 2) = a⁻¹ * m := by
      simpa only [autocorr, add_zero, ← pow_two] using hmassH
    rw [hmassH']
    field_simp [ha.ne', hm.ne']
  have hweight : (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ Real.exp (8 / a) := by
    calc
      _ ≤ ∫ u, F u ^ 2 * Real.exp (8 / a) := by
        apply integral_mono hdF.exponential (hdF.sq.mul_const _)
        intro u
        by_cases hu : -(1 / a) ≤ u
        · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          apply Real.exp_le_exp.mpr
          simp only [div_eq_mul_inv, one_mul] at hu ⊢
          linarith only [hu]
        · have hau : a * u < -1 := by
            have h := mul_lt_mul_of_pos_left (lt_of_not_ge hu) ha
            have he : a * -(1 / a) = -1 := by field_simp
            rwa [he] at h
          have hz : G (a * u) = 0 := hwin.vanish (a * u) fun hv =>
            (not_le_of_gt hau) hv.1
          change (c * G (a * u)) ^ 2 * _ ≤ (c * G (a * u)) ^ 2 * _
          simp only [hz, mul_zero, zero_pow two_ne_zero, zero_mul, le_refl]
      _ = _ := by rw [integral_mul_const, hmassF, one_mul]
  have henergy : biScaleLevyEnergy F = normalizedArchEnergy H := by
    change biScaleLevyEnergy (fun u => c * H u) = _
    rw [biScaleLevyEnergy_source_const_mul, hc, normalizedArchEnergy, hmassH]
    field_simp [ha.ne', hm.ne']
  refine ⟨F, hdF, hmassF, hweight, ?_⟩
  rw [henergy]
  simpa only [add_comm] using hC a ha hDa

#print axioms exists_unit_halfLine_logarithmic_dilates

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
