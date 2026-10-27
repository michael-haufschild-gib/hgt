import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryXiZeroHasALocalQuadraticTerminal
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReflectedXiPairHasAHeightReserve
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# The ray beyond a quadratic terminal

The terminal cone excludes zeros on the outward horizontal ray and makes
every critical-line-reflected zero pair nonnegative there.
-/

open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Every zero pair contributes nonnegatively beyond a quadratic terminal. -/
theorem xiTerminal_pair_nonneg (p : XiZeroCopy)
    (hcone : ∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
      xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2)
    {x : ℝ} (hx : xiZeroDepth p < x) (q : XiZeroCopy) :
    0 ≤ xiLinePairRe x ((q.1 : ℂ).re - 1 / 2)
      (xiZeroHeight p - xiZeroHeight q) := by
  apply xiLinePairRe_nonneg_of_quadratic_cone (xiZeroDepth_bounds p).1 hx
  have hq : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤
      xiZeroDepth p ^ 2 + (xiZeroHeight q - xiZeroHeight p) ^ 2 := by
    simpa only [xiZeroDepth, sq_abs] using hcone q
  nlinarith only [hq]

/-- The horizontal ray to the right of a right-hand terminal contains no Xi zeros. -/
theorem xi_ne_zero_on_terminal_ray (p : XiZeroCopy) (hp : 1 / 2 < (p.1 : ℂ).re)
    (hcone : ∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
      xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2)
    {h : ℝ} (hh : 0 < h) : xi ((p.1 : ℂ) + (h : ℂ)) ≠ 0 := by
  intro hz
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
  have hqre : (q.1 : ℂ).re = (p.1 : ℂ).re + h := by rw [hq]; simp
  have hqim : (q.1 : ℂ).im = (p.1 : ℂ).im := by rw [hq]; simp
  have hp0 : 0 < (p.1 : ℂ).re - 1 / 2 := by linarith
  have hq0 : 0 < (p.1 : ℂ).re + h - 1 / 2 := by linarith
  have hc := hcone q
  dsimp only [xiZeroDepth, xiZeroHeight] at hc
  rw [hqre, hqim, abs_of_pos hp0, abs_of_pos hq0] at hc
  have hprod : 0 < h * (2 * ((p.1 : ℂ).re - 1 / 2) + h) :=
    mul_pos hh (by linarith)
  nlinarith only [hc, hprod]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
