import GaloisForLFunctions.RHTower.LevinsonShiftedLinearMollifier
import GaloisForLFunctions.RHTower.LevinsonMollifiedBudget
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGeneralPowerBound

/-!
# Shifted linear mollifier bridge to Levinson's literal detector

The Littlewood/counting gate is phrased using `levinsonMollifiedDetector`, whose mollifier is an
entire Dirichlet polynomial.  Mean-square calculations use the critical-line-normalized linear
mollifier.  The coefficient shift by `n^sigma` cancels evaluation at real part `sigma`, so these
are exactly the same function on the integration line.
-/

open Complex Finset

noncomputable section

namespace RHTower

/-- The gate's entire shifted mollifier is exactly the normalized linear mollifier on its defining
vertical line. -/
theorem levinsonMollifiedDetector_shiftedLinear_line
    (lam : ℂ) (M : ℕ) (sigma t : ℝ) :
    levinsonMollifiedDetector lam (levinsonShiftedLinearMollifierCoeff M sigma)
        (Finset.Icc 1 M) (((sigma : ℝ) : ℂ) + (t : ℂ) * I) =
      levinsonG lam (((sigma : ℝ) : ℂ) + (t : ℂ) * I) *
        Sieve.levinsonLinearMollifier M t := by
  rw [levinsonMollifiedDetector, edPoly_levinsonShiftedLinearMollifierCoeff_line]

/-- Displaced-line form used by the smooth approximate functional equation. -/
theorem levinsonMollifiedDetector_shiftedLinear_displaced
    (lam : ℂ) (M : ℕ) (d t : ℝ) :
    levinsonMollifiedDetector lam
        (levinsonShiftedLinearMollifierCoeff M (1 / 2 - d))
        (Finset.Icc 1 M) (displacedLinePt d t) =
      levinsonG lam (displacedLinePt d t) * Sieve.levinsonLinearMollifier M t := by
  simpa only [displacedLinePt] using
    levinsonMollifiedDetector_shiftedLinear_line lam M (1 / 2 - d) t

end RHTower

end
