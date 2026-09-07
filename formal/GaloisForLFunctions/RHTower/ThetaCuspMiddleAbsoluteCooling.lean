import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceMiddleAbsoluteBounds
import GaloisForLFunctions.RHTower.ThetaCuspMiddleMomentBounds
import GaloisForLFunctions.RHTower.ThetaCuspSharpFiniteCooling

/-! # Complete absolute cooling through order ten on the middle scale -/
open MeasureTheory Filter Topology
namespace RHTower
noncomputable section

/-- Absolute scalar-score control integrates against the complete higher measure. -/
theorem abs_thetaCuspCoolingJet_le_middle_leadingMoment {n : ℕ} (hn : n ≤ 10)
    {x : ℝ} (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspCoolingJet n 0 x| ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*
      thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) n := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hs := integrable_laplaceCoolingJet_mul_exp_higher n 0 hB
  rw [thetaCuspCoolingJet_eq_integral_score n 0 hB,
    thetaCuspHigherLikelihoodSpectralMoment_eq_integral, ← integral_const_mul]
  calc
    _ ≤ ∫ t : ℝ, |HTGeometry.laplaceCoolingJet n 0 (q*t)*
          Real.exp (-thetaCuspLikelihoodCoordinate x*t)| ∂thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t : ℝ => HTGeometry.laplaceCoolingJet n 0 (q*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    _ ≤ _ := by
      apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hs.norm)
        ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure n hB).const_mul _)
      filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
      have hqt : 111/10 ≤ q*t := by dsimp [q] at *; nlinarith
      have hb := HTGeometry.laplaceCoolingJet_abs_le_of_middle hn hqt
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (2*(q*t))^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = _ := by simp only [mul_pow]; ring

/-- Every required derivative of the complete likelihood remainder has a middle-scale bound. -/
theorem abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_middle
    {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| ≤
      (6*thetaCuspSingleAtomReflectionScale 1 x)^n/100+
        (16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  rw [iteratedDeriv_thetaCuspLikelihoodSourceRemainder n
    (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  have hqp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  apply (abs_thetaCuspCoolingJet_le_middle_leadingMoment hn hq).trans
  calc
    _ ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*
        ((3 : ℝ)^n/100+8^n*thetaCuspDeepTailErrorScale x) :=
      mul_le_mul_of_nonneg_left (thetaCuspHigherLikelihoodSpectralMoment_le_middle hn hq) (by positivity)
    _ = _ := by
      have h6 : (6*thetaCuspSingleAtomReflectionScale 1 x)^n =
          (2*thetaCuspSingleAtomReflectionScale 1 x)^n*3^n := by rw [← mul_pow]; congr 1; ring
      have h16 : (16*thetaCuspSingleAtomReflectionScale 1 x)^n =
          (2*thetaCuspSingleAtomReflectionScale 1 x)^n*8^n := by rw [← mul_pow]; congr 1; ring
      rw [h6, h16]
      ring

end
end RHTower
