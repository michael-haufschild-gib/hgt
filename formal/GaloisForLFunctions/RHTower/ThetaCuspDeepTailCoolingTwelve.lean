import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreTwelve
import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCooling
import GaloisForLFunctions.RHTower.ThetaCuspDeepTailExtendedSupport
import GaloisForLFunctions.RHTower.ThetaCuspDeepTailPeakTwelve

/-! # Complete deep-tail differentiation through order twelve on the original middle ray -/
open MeasureTheory Filter Topology Set
namespace RHTower
noncomputable section

/-- Signed finite cooling preserves positivity and is bounded by the leading spectral moment. -/
theorem thetaCuspDeepCoolingJet_signed_le_leadingMoment_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x ∧
    (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x ≤
      (2*thetaCuspSingleAtomReflectionScale 1 x)^n *
        thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hs := integrable_laplaceCoolingJet_mul_exp_deep n 0 hB
  rw [thetaCuspDeepCoolingJet_eq_integral_score n 0 hB, ← integral_const_mul]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    have hqt : 24 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds_twelve hn hqt).1
    have hm := mul_nonneg hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change 0 ≤ (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    nlinarith only [hm]
  · rw [thetaCuspDeepTailMoment, ← integral_const_mul]
    apply integral_mono_ae (hs.const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure n hB).const_mul _)
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    have hqt : 24 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds_twelve hn hqt).2
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t)) ≤
      (2*q)^n*(t^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    calc
      _ ≤ (2*(q*t))^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t) := by nlinarith only [hm]
      _ = _ := by simp only [mul_pow]; ring

/-- Sharp signed bounds for every required derivative of the complete deep likelihood. -/
theorem thetaCuspDeepLikelihoodRemainder_signed_bounds_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*iteratedDeriv n thetaCuspDeepLikelihoodRemainder x ∧
    (-1 : ℝ)^n*iteratedDeriv n thetaCuspDeepLikelihoodRemainder x ≤
      ((96/5)*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  rw [iteratedDeriv_thetaCuspDeepLikelihoodRemainder n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  have h := thetaCuspDeepCoolingJet_signed_le_leadingMoment_twelve hn hq
  refine ⟨h.1, h.2.trans ?_⟩
  have hb := thetaCuspDeepTailMoment_le_errorScale_twelve hn hq
  have hp := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n by
      apply pow_nonneg
      have : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
      positivity)
  calc
    _ ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*((48/5)^n*thetaCuspDeepTailErrorScale x) := hp
    _ = _ := by rw [← mul_assoc, ← mul_pow]; congr 2; ring

/-- Absolute errors retain the full calibrated n≥3 tail, uniformly through derivative twelve. -/
theorem abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      ((96/5)*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  have h := thetaCuspDeepLikelihoodRemainder_signed_bounds_twelve hn hq
  have he : |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| =
      (-1 : ℝ)^n*iteratedDeriv n thetaCuspDeepLikelihoodRemainder x := by
    rw [← abs_of_nonneg h.1, abs_mul, abs_pow]
    norm_num
  rw [he]
  exact h.2


/-- The two new derivatives lose at most one quarter of the original leading-scale bound. -/
theorem abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_peak
    {n : ℕ} (hn : n = 11 ∨ n = 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      (5/4 : ℝ)*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  rw [iteratedDeriv_thetaCuspDeepLikelihoodRemainder n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  have h := thetaCuspDeepCoolingJet_signed_le_leadingMoment_twelve (by omega : n ≤ 12) hq
  have he : |thetaCuspDeepCoolingJet n 0 x| = (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x := by
    rw [← abs_of_nonneg h.1, abs_mul, abs_pow]
    norm_num
  rw [he]
  have hb := thetaCuspDeepTailMoment_le_errorScale_peak hn hq
  have hq0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  calc
    _ ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*
        ((5/4 : ℝ)*8^n*thetaCuspDeepTailErrorScale x) :=
      h.2.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = _ := by
      have hp : (16 : ℝ)^n = (2 : ℝ)^n*8^n := by rw [← mul_pow]; norm_num
      simp only [mul_pow, hp]
      ring

/-- Preserve the sharper old constants at every order where they were already proved. -/
def thetaCuspDeepDerivativeBoundTwelve (n : ℕ) (x : ℝ) : ℝ :=
  (if n ≤ 10 then 1 else 5/4)*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*
    thetaCuspDeepTailErrorScale x

/-- The full deep-tail derivative is bounded through twelve without weakening lower orders. -/
theorem abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_hybrid
    {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      thetaCuspDeepDerivativeBoundTwelve n x := by
  by_cases h : n ≤ 10
  · simpa only [thetaCuspDeepDerivativeBoundTwelve, if_pos h, one_mul] using
      abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le h hq
  · simpa only [thetaCuspDeepDerivativeBoundTwelve, if_neg h] using
      abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_peak (by omega : n = 11 ∨ n = 12) hq

end
end RHTower
