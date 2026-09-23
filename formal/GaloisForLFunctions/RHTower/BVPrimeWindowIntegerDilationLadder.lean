import GaloisForLFunctions.RHTower.BVPrimeWindowIntervalSource
import GaloisForLFunctions.RHTower.PrimeWoldBVAdjacentDecimation
import GaloisForLFunctions.RHTower.BVPrimeWindowSieveResidue

/-!
# Bilateral integer dilation ladder for BV prime windows

Every integer rung `W_j(x)=W(r^j x)` stays in the compact-BV source class.  Rungs two steps apart
are related by literal square-index coefficient decimation.  Their continued-source residues carry
the exact horizontal character, while the complementary off-multiple layer removes the constant
fraction `r⁻²` on every Laurent fibre.
-/

open Complex

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

open GaloisForLFunctions.HTGeometry

/-- Integer-indexed positive dilation ladder `W_j(x)=W(r^j x)`. -/
def integerDilation (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (j : ℤ) :
    CompactBVPrimeWindow :=
  W.argumentDilation (r ^ j) (zpow_pos hr j)

@[simp] theorem integerDilation_apply
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (j : ℤ) (x : ℝ) :
    W.integerDilation r hr j x = W (r ^ j * x) := rfl

@[simp] theorem integerDilation_lower
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (j : ℤ) :
    (W.integerDilation r hr j).lower = W.lower / r ^ j := rfl

@[simp] theorem integerDilation_upper
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (j : ℤ) :
    (W.integerDilation r hr j).upper = W.upper / r ^ j := rfl

/-- Exact Mellin character on every integer rung. -/
theorem mellinTransform_integerDilation
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (j : ℤ) (s : ℂ) :
    (W.integerDilation r hr j).mellinTransform s =
      ((r ^ j : ℝ) : ℂ) ^ (s - 1) * W.mellinTransform s := by
  exact mellinTransform_argumentDilation W (r ^ j) (zpow_pos hr j) s

private theorem integerDilation_scale_sub_two_mul_sq
    (r : ℕ) (hr : 0 < r) (j : ℤ) :
    ((r : ℝ) ^ (j - 2)) * ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ j := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Nat.cast_pow]
  change (r : ℝ) ^ (j - 2) * (r : ℝ) ^ (2 : ℤ) = (r : ℝ) ^ j
  rw [← zpow_add₀ hrR]
  congr 1
  omega

/-- Two adjacent ladder steps compose to dilation by the square index. -/
theorem integerDilation_eq_sub_two_argumentDilation_sq
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) :
    W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) j =
      (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).argumentDilation
        ((r ^ 2 : ℕ) : ℝ) (Nat.cast_pos.mpr (pow_pos hr 2)) := by
  apply ext
  · rw [integerDilation_lower, argumentDilation_lower, integerDilation_lower,
      div_div, integerDilation_scale_sub_two_mul_sq r hr j]
  · rw [integerDilation_upper, argumentDilation_upper, integerDilation_upper,
      div_div, integerDilation_scale_sub_two_mul_sq r hr j]
  · funext x
    rw [show (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) j).toFun x =
        W ((r : ℝ) ^ j * x) by rfl]
    rw [show ((W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).argumentDilation
        ((r ^ 2 : ℕ) : ℝ) (Nat.cast_pos.mpr (pow_pos hr 2))).toFun x =
        W ((r : ℝ) ^ (j - 2) * (((r ^ 2 : ℕ) : ℝ) * x)) by rfl]
    rw [← mul_assoc, integerDilation_scale_sub_two_mul_sq r hr j]

/-- Full bilateral finite-prime square-index decimation law. -/
theorem weightedPrimeWindow_integerDilation_eq_sub_two_sq_mul
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) (n : ℕ) :
    (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) j).weightedPrimeWindow n =
      (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).weightedPrimeWindow
        (r ^ 2 * n) := by
  rw [integerDilation_eq_sub_two_argumentDilation_sq W r hr j]
  exact weightedPrimeWindow_argumentDilation_eq_mul _ (r ^ 2) (pow_pos hr 2) n

/-- Full bilateral complete prime--polar square-index decimation law. -/
theorem polarCoefficient_integerDilation_eq_sub_two_sq_mul
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) (n : ℕ) :
    (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) j).polarCoefficient n =
      (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).polarCoefficient
        (r ^ 2 * n) := by
  rw [integerDilation_eq_sub_two_argumentDilation_sq W r hr j]
  exact polarCoefficient_argumentDilation_eq_mul _ (r ^ 2) (pow_pos hr 2) n

/-- Coefficient-operator form `D_(r^(2 : ℕ)) p_(j-2)=p_j`. -/
theorem decimate_polarCoefficient_integerDilation_sub_two
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) :
    decimate (r ^ 2)
        (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).polarCoefficient =
      (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) j).polarCoefficient := by
  funext n
  exact (polarCoefficient_integerDilation_eq_sub_two_sq_mul W r hr j n).symm

private theorem cpow_sq_character
    (r : ℕ) (hr : 0 < r) (rho : ℂ) :
    (((r ^ 2 : ℕ) : ℝ) : ℂ) ^ (rho - 1 / 2) =
      (r : ℂ) ^ (2 * rho - 1) := by
  have hr0 : (0 : ℝ) ≤ r := by positivity
  calc
    (((r ^ 2 : ℕ) : ℝ) : ℂ) ^ (rho - 1 / 2) =
        (((r : ℝ) : ℂ) * ((r : ℝ) : ℂ)) ^ (rho - 1 / 2) := by
      push_cast
      rw [pow_two]
    _ = (((r : ℝ) : ℂ) ^ (rho - 1 / 2)) *
        (((r : ℝ) : ℂ) ^ (rho - 1 / 2)) := by
      rw [Complex.mul_cpow_ofReal_nonneg hr0 hr0]
    _ = ((((r : ℝ) : ℂ) ^ (rho - 1 / 2))) ^ 2 := by ring
    _ = ((r : ℂ) ^ ((2 : ℂ) * (rho - 1 / 2))) := by
      symm
      exact Complex.cpow_nat_mul (r : ℂ) 2 (rho - 1 / 2)
    _ = (r : ℂ) ^ (2 * rho - 1) := by
      congr 1
      ring

/-- Exact horizontal Laurent character between every pair of rungs two steps apart. -/
theorem continuedSourceResidueValue_integerDilation_eq_sub_two_character
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) (rho : ℂ) :
    (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) j).continuedSourceResidueValue rho =
      (r : ℂ) ^ (2 * rho - 1) *
        (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).continuedSourceResidueValue rho := by
  rw [integerDilation_eq_sub_two_argumentDilation_sq W r hr j,
    continuedSourceResidueValue_argumentDilation, cpow_sq_character r hr rho]

/-- Laurent residue of the off-`r^(2 : ℕ)` coefficient layer at rung `j-2`. -/
def integerDilationOffMultipleResidueValue
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) (rho : ℂ) : ℂ :=
  adjacentOffMultipleResidueValue
    (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2))
    (r ^ 2) (pow_pos hr 2) rho

/-- The off-multiple layer removes the zero-independent fraction `r⁻²` on every rung. -/
theorem integerDilationOffMultipleResidueValue_eq
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) (rho : ℂ) :
    integerDilationOffMultipleResidueValue W r hr j rho =
      (1 - ((r : ℂ)⁻¹) ^ 2) *
        (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).continuedSourceResidueValue rho := by
  rw [integerDilationOffMultipleResidueValue, adjacentOffMultipleResidueValue_eq]
  congr 2
  push_cast
  rw [inv_pow]

/-- The complementary coefficient layer is literally supported away from multiples of `r²`. -/
theorem integerDilation_offMultiple_polarCoefficient_apply
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (j : ℤ) (n : ℕ) :
    offMultiple (r ^ 2)
        (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).polarCoefficient n =
      if r ^ 2 ∣ n then 0 else
        (W.integerDilation (r : ℝ) (Nat.cast_pos.mpr hr) (j - 2)).polarCoefficient n := by
  exact offMultiple_apply (pow_pos hr 2) _ n

end CompactBVPrimeWindow
end RHTower
