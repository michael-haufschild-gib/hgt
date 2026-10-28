import GaloisForLFunctions.HTGeometry.HardyNumberSpectrum
import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity

/-!
# Explicit normalized Blaschke coefficients

The geometric ground normalization and the two tails of each excitation give
closed coefficient formulas for the complete number-operator basis.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem inv_norm_hardyKernel_real {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) :
    ‖hardyKernel hq‖⁻¹ = Real.sqrt (1 - q ^ 2) := by
  have hnorm := norm_sq_hardyKernel hq
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hnorm
  have hqabs : |q| < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hq
  have hpos : 0 < 1 - q ^ 2 := by
    nlinarith only [hqabs, abs_nonneg q, sq_abs q]
  have hsq : (‖hardyKernel hq‖⁻¹) ^ 2 = 1 - q ^ 2 := by
    rw [inv_pow, hnorm, inv_inv]
  nlinarith only [hsq, Real.sq_sqrt hpos.le,
    inv_nonneg.mpr (norm_nonneg (hardyKernel hq)), Real.sqrt_nonneg (1 - q ^ 2)]

/-- Ground and excitation coefficients, with positive labels shifted by one. -/
def hardyBlaschkeCoefficient (q : ℝ) : ℕ → ℕ → ℂ
  | 0, n => (Real.sqrt (1 - q ^ 2) : ℂ) * (q : ℂ) ^ n
  | j + 1, n => if j < n then (1 - (q : ℂ) ^ 2) * (q : ℂ) ^ (n - (j + 1))
      else if n = j then -(q : ℂ) else 0

/-- The complete Hilbert basis has the stated explicit normalized coefficients. -/
theorem hardyNumberBasis_coefficient {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) (k n : ℕ) :
    hardyNumberBasis hq k n = hardyBlaschkeCoefficient q k n := by
  rw [hardyNumberBasis_apply, hardyBlaschkeBasis_apply]
  cases k with
  | zero =>
    change (‖hardyKernel hq‖ : ℂ)⁻¹ * ((starRingEnd ℂ) (q : ℂ)) ^ n = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_inv, inv_norm_hardyKernel_real hq]
    rfl
  | succ j =>
    change blaschkeMul hq (HilbertSchmidt.lpBasis ℕ j) n = _
    rw [HilbertSchmidt.lpBasis_apply]
    exact blaschkeMul_single_apply hq j n

end GaloisForLFunctions.HTGeometry
