import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeTranslationCompletedRadialWorkEquivalence
import GaloisForLFunctions.RHTower.BurnolBilateralApertureRH
import GaloisForLFunctions.RHTower.XiHedenmalmBorelSoninApertureComparison
import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletionLanding

/-!
# Completed radial work is squared Sonin aperture escape

Every off-line Xi multiplicity copy has a canonical representative whose completed divisor point
lies in the strict right half of the critical strip.  Burnol's literal completed-Mellin evaluation
vector at that representative has geometric-aperture Lyapunov exponent equal to the absolute
centered spectral width of the original copy.

The completed Hedenmalm radial source work is exactly the square of this Lyapunov exponent times
the norm square of the completed first-divided Xi source vector.  Thus finite prime/Ward/Dirac
dissipation and cofinal Sonin escape are not independent obstructions: the former is the quadratic
local shadow of the latter.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

/-- Canonical multiplicity-preserving orientation toward the strict right half of the completed
critical strip.  On-line copies are left fixed only by convention; strict-right claims below are
made for off-line copies. -/
def xiSoninRightOrientedCopy (q : XiZeroCopy) : XiZeroCopy :=
  if (xiSpectralPoint q).im < 0 then q else xiZeroCopyLineConjEquiv q

/-- Sonin aperture Lyapunov rate attached to an Xi copy. -/
def thetaXiSoninApertureLyapunovRate (q : XiZeroCopy) : ℝ :=
  |(xiSpectralPoint q).im|

theorem xiSpectralPoint_im_xiSoninRightOrientedCopy_abs (q : XiZeroCopy) :
    |(xiSpectralPoint (xiSoninRightOrientedCopy q)).im| =
      thetaXiSoninApertureLyapunovRate q := by
  rw [thetaXiSoninApertureLyapunovRate, xiSoninRightOrientedCopy]
  split_ifs with h
  · rfl
  · rw [xiSpectralPoint_lineConj, Complex.conj_im, abs_neg]

theorem xiSpectralPoint_im_xiSoninRightOrientedCopy_neg
    (q : XiZeroCopy) (hoff : (xiSpectralPoint q).im ≠ 0) :
    (xiSpectralPoint (xiSoninRightOrientedCopy q)).im < 0 := by
  rw [xiSoninRightOrientedCopy]
  split_ifs with h
  · exact h
  · rw [xiSpectralPoint_lineConj, Complex.conj_im]
    exact neg_lt_zero.mpr (lt_of_le_of_ne (not_lt.mp h) hoff.symm)

/-- The canonical completed point is the literal Xi divisor support, not a proxy spectral sample. -/
theorem criticalAffine_xiSoninRightOrientedCopy (q : XiZeroCopy) :
    (1 / 2 : ℂ) + xiSpectralPoint (xiSoninRightOrientedCopy q) * Complex.I =
      ((xiSoninRightOrientedCopy q).1 : ℂ) := by
  rw [xiSpectralPoint_eq_support]
  exact criticalAffine_xiSpectralPointSupport (xiSoninRightOrientedCopy q).1

/-- **Actual-fibre Sonin Lyapunov law.**  Along every geometric aperture tower, the completed
Mellin evaluation vector at the canonically right-oriented off-line Xi divisor has logarithmic
norm-growth rate equal to the absolute centered spectral width of the original copy. -/
theorem tendsto_log_norm_burnolExtendedSoninEvaluationVector_xi
    (q : XiZeroCopy) (hoff : (xiSpectralPoint q).im ≠ 0)
    {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 1 < r) :
    let qR := xiSoninRightOrientedCopy q
    let alpha := xiSpectralPoint qR
    let hlo : 1 / 2 < (1 / 2 + alpha * Complex.I).re := by
      rw [re_centeredSpectralPoint]
      linarith [xiSpectralPoint_im_xiSoninRightOrientedCopy_neg q hoff]
    let hhi : (1 / 2 + alpha * Complex.I).re < 1 := by
      rw [re_centeredSpectralPoint]
      linarith [(xiSpectralPoint_im_mem_openHalf qR).1]
    Tendsto
      (fun N : ℕ =>
        Real.log
            ‖burnolExtendedSoninEvaluationVector (1 / 2 + alpha * Complex.I)
              ((r ^ N)⁻¹ * a) hlo hhi
              (mul_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans hr) N)) ha)‖ /
          ((N : ℝ) * Real.log r))
      atTop (nhds (thetaXiSoninApertureLyapunovRate q)) := by
  dsimp only
  have h := tendsto_log_norm_burnolExtendedSoninEvaluationVector_unconditional
    (w := 1 / 2 + xiSpectralPoint (xiSoninRightOrientedCopy q) * Complex.I)
    (a := a) (r := r)
    (by
      rw [re_centeredSpectralPoint]
      linarith [xiSpectralPoint_im_xiSoninRightOrientedCopy_neg q hoff])
    (by
      rw [re_centeredSpectralPoint]
      linarith [(xiSpectralPoint_im_mem_openHalf (xiSoninRightOrientedCopy q)).1])
    ha ha1 hr
  rw [abs_re_centeredSpectralPoint_sub_half,
    xiSpectralPoint_im_xiSoninRightOrientedCopy_abs] at h
  exact h

/-- **Local--cofinal work law.**  Completed radial source work is Lyapunov escape squared times
the literal completed first-divided Xi source energy. -/
theorem burnolCompletedRadialSourceWork_eq_soninLyapunovRate_sq_mul_norm_sq
    (q : XiZeroCopy) :
    burnolCompletedRadialSourceWork q.1 =
      thetaXiSoninApertureLyapunovRate q ^ 2 *
        ‖completedXiFirstDividedL2 q.1‖ ^ 2 := by
  rw [burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq,
    ← xiSpectralPoint_eq_support, thetaXiSoninApertureLyapunovRate]
  rw [sq_abs]

/-- Radial work is zero exactly when the cofinal Sonin Lyapunov exponent is zero, because actual
completed divided-source energy is strictly positive. -/
theorem burnolCompletedRadialSourceWork_eq_zero_iff_soninLyapunovRate_eq_zero
    (q : XiZeroCopy) :
    burnolCompletedRadialSourceWork q.1 = 0 ↔
      thetaXiSoninApertureLyapunovRate q = 0 := by
  rw [burnolCompletedRadialSourceWork_eq_soninLyapunovRate_sq_mul_norm_sq]
  have hnorm : ‖completedXiFirstDividedL2 q.1‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (completedXiFirstDividedL2_ne_zero q.1))
  constructor
  · intro h
    have hrateSq : thetaXiSoninApertureLyapunovRate q ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right hnorm
    exact (sq_eq_zero_iff.mp hrateSq)
  · intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

end RHTower
