import GaloisForLFunctions.RHTower.KapustinGaugeSmirnovCollision
import GaloisForLFunctions.HTGeometry.GammaMonomialAnalytic

/-!
# Holomorphic real-line extension of the Kapustin Toeplitz symbol

The fixed reciprocal-Gamma Toeplitz symbol is the real boundary restriction of an explicit
Gamma-ratio times a rational fourth Blaschke factor.  This module proves exact boundary equality,
holomorphy at every real point, and nonvanishing there.  These are the real-analytic symbol inputs
for Makarov--Poltoratski kernel regularization.
-/

open Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Explicit complex extension of the reciprocal-Gamma Toeplitz symbol. -/
def kapustinToeplitzAnalyticSymbol (z : ℂ) : ℂ :=
  (Complex.Gamma ((1 / 2 : ℂ) + z * I) /
      Complex.Gamma ((1 / 2 : ℂ) - z * I)) *
    Complex.exp (-2 * I * z * (Real.log (2 * Real.pi) : ℂ)) *
      ((z + I) / (z - I)) ^ 4

theorem gammaVertical_ratio_eq_exp_two_phase (x : ℝ) :
    Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I) /
        Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I) =
      Complex.exp (2 * I * (gammaVerticalPhase (1 / 2) x : ℂ)) := by
  let z := gammaVerticalValue (1 / 2) x
  have hz : z ≠ 0 := gammaVerticalValue_ne_zero (by norm_num) x
  have hpolar := gammaVerticalValue_eq_norm_mul_exp_phase
    (by norm_num : (0 : ℝ) < 1 / 2) x
  have hconj : Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I) =
      (starRingEnd ℂ) z := by
    rw [show (1 / 2 : ℂ) - (x : ℂ) * I =
        (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) * I) by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im],
      Complex.Gamma_conj]
    congr 2
    norm_num [z, gammaVerticalValue]
  rw [show Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I) = z by
      norm_num [z, gammaVerticalValue], hconj]
  change z / (starRingEnd ℂ) z = _
  change z = (‖z‖ : ℂ) *
    Complex.exp (I * (gammaVerticalPhase (1 / 2) x : ℂ)) at hpolar
  rw [hpolar]
  have hnorm : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [conj_I]
  field_simp
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The explicit holomorphic extension has exactly the original boundary symbol. -/
theorem kapustinToeplitzAnalyticSymbol_ofReal (x : ℝ) :
    kapustinToeplitzAnalyticSymbol (x : ℂ) = kapustinToeplitzSymbol x := by
  rw [kapustinToeplitzAnalyticSymbol, kapustinToeplitzSymbol,
    kapustinToeplitzPhase,
    gammaVertical_ratio_eq_exp_two_phase]
  simp only [kapustinReciprocalGammaPhase]
  have hcond : Complex.exp
      (-2 * I * (x : ℂ) * (Real.log (2 * Real.pi) : ℂ)) =
      Complex.exp (-2 * I * ((x * Real.log (2 * Real.pi) : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hcond]
  have hcayley : ((x : ℂ) + I) / ((x : ℂ) - I) =
      (starRingEnd ℂ) (realCayley x) := by
    rw [realCayley]
    simp only [map_div₀, map_sub, map_add, conj_ofReal, conj_I]
    rw [sub_neg_eq_add, ← sub_eq_add_neg]
  rw [hcayley, ← map_pow, conj_realCayley_pow_four_eq_exp_neg_eight_arctan]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The fixed symbol is holomorphic on a complex neighborhood of every real point. -/
theorem analyticAt_kapustinToeplitzAnalyticSymbol_ofReal (x : ℝ) :
    AnalyticAt ℂ kapustinToeplitzAnalyticSymbol (x : ℂ) := by
  have hplusArg : AnalyticAt ℂ (fun z : ℂ => (1 / 2 : ℂ) + z * I) (x : ℂ) :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hminusArg : AnalyticAt ℂ (fun z : ℂ => (1 / 2 : ℂ) - z * I) (x : ℂ) :=
    analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hplusGamma : AnalyticAt ℂ
      (fun z : ℂ => Complex.Gamma ((1 / 2 : ℂ) + z * I)) (x : ℂ) := by
    have hg : AnalyticAt ℂ Complex.Gamma
        ((1 / 2 : ℂ) + (x : ℂ) * I) :=
      analyticAt_Gamma_of_re_pos (by norm_num)
    have hc := AnalyticAt.comp (g := Complex.Gamma)
      (f := fun z : ℂ => (1 / 2 : ℂ) + z * I) (x := (x : ℂ)) hg hplusArg
    simpa [Function.comp_def] using hc
  have hminusGamma : AnalyticAt ℂ
      (fun z : ℂ => Complex.Gamma ((1 / 2 : ℂ) - z * I)) (x : ℂ) := by
    have hg : AnalyticAt ℂ Complex.Gamma
        ((1 / 2 : ℂ) - (x : ℂ) * I) :=
      analyticAt_Gamma_of_re_pos (by norm_num)
    have hc := AnalyticAt.comp (g := Complex.Gamma)
      (f := fun z : ℂ => (1 / 2 : ℂ) - z * I) (x := (x : ℂ)) hg hminusArg
    simpa [Function.comp_def] using hc
  have hminusNe : Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcayley : AnalyticAt ℂ (fun z : ℂ => (z + I) / (z - I)) (x : ℂ) := by
    apply (analyticAt_id.add analyticAt_const).div
      (analyticAt_id.sub analyticAt_const)
    intro hx
    have him := congrArg Complex.im hx
    norm_num at him
  change AnalyticAt ℂ
    (fun z => (Complex.Gamma ((1 / 2 : ℂ) + z * I) /
      Complex.Gamma ((1 / 2 : ℂ) - z * I)) *
      Complex.exp (-2 * I * z * (Real.log (2 * Real.pi) : ℂ)) *
      ((z + I) / (z - I)) ^ 4) (x : ℂ)
  exact ((hplusGamma.div hminusGamma hminusNe).mul
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).cexp)).mul
      (hcayley.pow 4)

/-- The extension has no real zero or pole. -/
theorem kapustinToeplitzAnalyticSymbol_ofReal_ne_zero (x : ℝ) :
    kapustinToeplitzAnalyticSymbol (x : ℂ) ≠ 0 := by
  rw [kapustinToeplitzAnalyticSymbol_ofReal]
  exact norm_ne_zero_iff.mp (by rw [norm_kapustinToeplitzSymbol]; norm_num)

end RHTower
