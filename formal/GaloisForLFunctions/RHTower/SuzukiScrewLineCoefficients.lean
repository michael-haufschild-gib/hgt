import GaloisForLFunctions.RHTower.SuzukiWeilFrakSZeroSeries

/-!
# Unconditional steps of Suzuki Theorem 4.2

Two ingredients of the screw-line theorem that need no hypothesis at all.

`S_0 = 0` is immediate from the zero-series form (every coefficient `e^{0} - 1` vanishes); in the
paper this is checked from eqs. (1.5)-(1.6) by a Lerch limit, which the zero-series form makes
unnecessary.

Square-summability of the screw coefficients `(e^{-i gamma t} - 1)/gamma` is the `L^2` convergence
step of the proof.  It is unconditional because every Xi zero lies in the critical strip, so
`|e^{-i gamma t} - 1| <= e^{|t|/2} + 1` uniformly in `gamma` (`norm_suzukiPtZeroExp_le`), and
`sum m_gamma/|gamma|^2` converges.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Two unconditional steps of Suzuki Theorem 4.2 -/

/-- `𝔖_0 = 0`. -/
theorem suzukiFrakSFull_zero (z : ℂ) : suzukiFrakSFull 0 z = 0 := by
  rw [suzukiFrakSFull, suzukiPtZeroSum_zero, mul_zero]

/-- The screw-line coefficient of the `q`-th zero copy. -/
def suzukiScrewCoeff (t : ℝ) (q : XiZeroCopy) : ℂ :=
  (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) / xiSpectralPoint q

/-- **The coefficient family of `𝔖_t` is square summable.**  This is the `L²`-convergence step in
the proof of Suzuki Theorem 4.2, and it is unconditional: every Xi zero lies in the critical strip,
so `|e^{-iγt} - 1| ≤ e^{|t|/2} + 1` uniformly in `γ`. -/
theorem summable_norm_sq_suzukiScrewCoeff (t : ℝ) :
    Summable (fun q : XiZeroCopy => ‖suzukiScrewCoeff t q‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left ((Real.exp (|t| / 2) + 1) ^ 2))
  have hnum : ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖
      ≤ Real.exp (|t| / 2) + 1 := by
    calc ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖
        ≤ ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp (|t| / 2) + 1 := by
          have := norm_suzukiPtZeroExp_le t q
          simp only [norm_one]
          linarith
  have hγ : (0 : ℝ) < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hnn : (0 : ℝ) ≤ Real.exp (|t| / 2) + 1 := by positivity
  rw [suzukiScrewCoeff, norm_div, div_pow]
  rw [div_le_iff₀ (by positivity)]
  have hsq : ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖ ^ 2
      ≤ (Real.exp (|t| / 2) + 1) ^ 2 := by
    nlinarith [norm_nonneg (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1), hnum, hnn]
  calc ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖ ^ 2
      ≤ (Real.exp (|t| / 2) + 1) ^ 2 := hsq
    _ = (Real.exp (|t| / 2) + 1) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) * ‖xiSpectralPoint q‖ ^ 2 := by
        field_simp

end
end RHTower

