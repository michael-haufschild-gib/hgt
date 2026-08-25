import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedVariationBound
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary

/-!
# Logarithmic growth of chi on moving left lines

The individual logarithmic derivative of zeta's functional-equation factor
grows only logarithmically on displaced Levinson lines.  Uniformity follows
because both digamma arguments stay in `[1/8,3/8]`.
-/

noncomputable section

open Complex

namespace RHTower

/-- Uniform logarithmic bound for `chi'/chi` on moving displaced lines. -/
theorem norm_logDeriv_zetaChi_displacedLinePt_le_log
    {d tau : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (htau : 4 ≤ tau) :
    ‖logDeriv zetaChi (displacedLinePt d tau)‖ ≤
      Real.log tau +
        (GaloisForLFunctions.digammaVerticalLogConstant + |Real.log Real.pi|) := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hzre : 0 < (displacedLinePt d tau).re := by
    rw [displacedLinePt_re]
    linarith
  have h1zre : 0 < (1 - displacedLinePt d tau).re := by
    rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    linarith
  rw [logDeriv_zetaChi_off_poles
    (div_two_ne_neg_nat_of_re_pos hzre)
    (div_two_ne_neg_nat_of_re_pos h1zre)]
  let sigmaL : ℝ := 1 / 4 - d / 2
  let sigmaR : ℝ := 1 / 4 + d / 2
  let t : ℝ := tau / 2
  have hsigmaL0 : 0 < sigmaL := by dsimp only [sigmaL]; linarith
  have hsigmaR0 : 0 < sigmaR := by dsimp only [sigmaR]; linarith
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith
  have hsigmaLt : sigmaL ≤ t := by dsimp only [sigmaL, t]; linarith
  have hsigmaRt : sigmaR ≤ t := by dsimp only [sigmaR, t]; linarith
  have hLarg : displacedLinePt d tau / 2 =
      (sigmaL : ℂ) + (t : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, sigmaL, t]
      ring
    · norm_num [displacedLinePt, t]
  have hRarg : (1 - displacedLinePt d tau) / 2 =
      (sigmaR : ℂ) - (t : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, sigmaR, t]
      ring
    · norm_num [displacedLinePt, t]
      ring
  have hL := GaloisForLFunctions.norm_digamma_vertical_le_log
    hsigmaL0 ht1 hsigmaLt
  have hRpos := GaloisForLFunctions.norm_digamma_vertical_le_log
    hsigmaR0 ht1 hsigmaRt
  have hR : ‖Complex.digamma ((sigmaR : ℂ) - (t : ℂ) * I)‖ ≤
      Real.log t + GaloisForLFunctions.digammaVerticalLogConstant := by
    let z : ℂ := (sigmaR : ℂ) + (t : ℂ) * I
    have hz : (starRingEnd ℂ) z =
        (sigmaR : ℂ) - (t : ℂ) * I := by
      apply Complex.ext <;> simp [z]
    rw [← hz, ReflectedDigammaAnomaly.digamma_conj, norm_conj]
    exact hRpos
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have htLe : t ≤ tau := by dsimp only [t]; linarith
  have hlog : Real.log t ≤ Real.log tau :=
    Real.log_le_log ht0 htLe
  rw [hLarg, hRarg]
  calc
    ‖-(Complex.digamma ((sigmaL : ℂ) + (t : ℂ) * I) / 2) -
          Complex.digamma ((sigmaR : ℂ) - (t : ℂ) * I) / 2 +
          (Real.log Real.pi : ℂ)‖
        ≤ ‖Complex.digamma ((sigmaL : ℂ) + (t : ℂ) * I)‖ / 2 +
            ‖Complex.digamma ((sigmaR : ℂ) - (t : ℂ) * I)‖ / 2 +
            |Real.log Real.pi| := by
          calc
            _ ≤ ‖-(Complex.digamma ((sigmaL : ℂ) + (t : ℂ) * I) / 2) -
                  Complex.digamma ((sigmaR : ℂ) - (t : ℂ) * I) / 2‖ +
                ‖(Real.log Real.pi : ℂ)‖ := norm_add_le _ _
            _ ≤ (‖-(Complex.digamma ((sigmaL : ℂ) + (t : ℂ) * I) / 2)‖ +
                  ‖Complex.digamma ((sigmaR : ℂ) - (t : ℂ) * I) / 2‖) +
                ‖(Real.log Real.pi : ℂ)‖ := by gcongr; exact norm_sub_le _ _
            _ = _ := by
              rw [norm_div, norm_neg, norm_div, Complex.norm_real,
                Real.norm_eq_abs]
              norm_num
    _ ≤ (Real.log t + GaloisForLFunctions.digammaVerticalLogConstant) / 2 +
          (Real.log t + GaloisForLFunctions.digammaVerticalLogConstant) / 2 +
          |Real.log Real.pi| := by gcongr
    _ = Real.log t +
          (GaloisForLFunctions.digammaVerticalLogConstant + |Real.log Real.pi|) := by ring
    _ ≤ Real.log tau +
          (GaloisForLFunctions.digammaVerticalLogConstant + |Real.log Real.pi|) := by
          gcongr

end RHTower
