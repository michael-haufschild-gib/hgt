import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffTails
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffLowTail

/-!
# Hausdorff saddle estimates at the actual Xi zeros

Evenness transfers the analytic kernel bounds to the absolute ordinate of
every divisor copy. The strip displacement remains at most one half.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open _root_.RHTower

theorem atom_eq_kernel (R : ℝ) (k r : ℕ) (q : XiZeroCopy) :
    hausdorffAtomTerm R k r q = kernel R (k + 1) r (xiSpectralPoint q) := rfl

/-- Negating a centered zero puts its real coordinate on the positive axis. -/
theorem atom_eq_kernel_abs_ordinate (R : ℝ) (k r : ℕ) (q : XiZeroCopy) :
    ∃ y : ℝ, |y| ≤ 1 / 2 ∧ hausdorffAtomTerm R k r q =
      kernel R (k + 1) r ((|(q.1 : ℂ).im| : ℝ) + (y : ℂ) * Complex.I) := by
  have hy : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
    obtain ⟨h₁, h₂⟩ := xiSpectralPoint_im_mem_openHalf q
    exact abs_le.mpr ⟨by linarith only [h₁], h₂.le⟩
  rw [atom_eq_kernel, ← xiSpectralPoint_re_eq_ordinate']
  by_cases hx : 0 ≤ (xiSpectralPoint q).re
  · refine ⟨(xiSpectralPoint q).im, hy, ?_⟩
    rw [abs_of_nonneg hx, Complex.re_add_im]
  · refine ⟨-(xiSpectralPoint q).im, by simpa only [abs_neg] using hy, ?_⟩
    rw [abs_of_neg (lt_of_not_ge hx)]
    have heq : ((-(xiSpectralPoint q).re : ℝ) : ℂ) +
        ((-(xiSpectralPoint q).im : ℝ) : ℂ) * Complex.I = -xiSpectralPoint q := by
      apply Complex.ext <;> simp
    rw [heq, kernel_neg]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
