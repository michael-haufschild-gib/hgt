import GaloisForLFunctions.HTGeometry.BoundedDiscExpansion
import GaloisForLFunctions.HTGeometry.MassCarrierShellPowers

/-!
# Disc bounds for the shell factors

Assembling a product of expansions needs, besides the expansions themselves, a bound for each factor
on the disc.  For a shell power it comes from the modulus of a principal power with a real exponent
being that power of the modulus, together with the base staying above one half on the disc of the
binomial radius.  For the root defect it is the order-one expansion, whose truncating polynomial
vanishes identically.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ShellBounds

/-- On the binomial disc the shell base stays above one half. -/
theorem half_le_norm_one_add_shell {x r : ℝ} (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ r) : (1 : ℝ) / 2 ≤ ‖1 + (x : ℂ) ^ 2 * w ^ 2‖ := by
  have hu := norm_shell_arg hxr hw
  have h := norm_sub_norm_le (1 : ℂ) (-((x : ℂ) ^ 2 * w ^ 2))
  have hn : ‖(-((x : ℂ) ^ 2 * w ^ 2) : ℂ)‖ = ‖(x : ℂ) ^ 2 * w ^ 2‖ := norm_neg _
  have h2 : (1 : ℂ) - -((x : ℂ) ^ 2 * w ^ 2) = 1 + (x : ℂ) ^ 2 * w ^ 2 := by ring
  rw [h2, norm_one, hn] at h
  linarith

/-- **The shell power is bounded on the binomial disc.** -/
theorem norm_shellPow_le {α : ℝ} (hα : α ≤ 0) {x r : ℝ} (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ r) :
    ‖(1 + (x : ℂ) ^ 2 * w ^ 2) ^ ((α : ℝ) : ℂ)‖ ≤ (2 : ℝ) ^ (-α) := by
  have hge := half_le_norm_one_add_shell hxr hw
  rw [Complex.norm_cpow_real]
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hge hα
  refine le_trans h (le_of_eq ?_)
  rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num,
    ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- The one-term shell expansion is constant. -/
theorem shellBinomPoly_one (α : ℝ) (x : ℝ) : shellBinomPoly α 1 x = 1 := by
  rw [shellBinomPoly, Finset.sum_range_one]
  simp

/-- Hence the order-zero root-defect expansion has vanishing truncating polynomial. -/
theorem shellDefectPoly_zero (x : ℝ) : shellDefectPoly 0 x = 0 := by
  rw [shellDefectPoly, shellBinomPoly_one, sub_self, Polynomial.divX_zero]

/-- The linear rate of the root defect at the origin. -/
def shellDefectRate (x : ℝ) : ℝ := cbinomAbsCoeff ((1 : ℝ) / 2) 1 * |x| ^ 2

theorem shellDefectRate_nonneg (x : ℝ) : 0 ≤ shellDefectRate x :=
  mul_nonneg (cbinomAbsCoeff_nonneg _ _) (pow_nonneg (abs_nonneg x) 2)

/-- **The root defect vanishes linearly in the reciprocal spectral parameter.** -/
theorem norm_shellDefect_le {x r : ℝ} (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖shellDefect x w‖ ≤ shellDefectRate x * ‖w‖ := by
  have h := hasPolyExpansion_shellDefect 0 x hxr w hw
  rw [shellDefectPoly_zero] at h
  simpa [shellDefectRate] using h

end ShellBounds

end

end GaloisForLFunctions.HTGeometry
