import GaloisForLFunctions.RHTower.BVPrimeWindowDilationOrientation
import GaloisForLFunctions.RHTower.PrimeStokesWoldCalderonSuspension

/-!
# Prime Wold--BV adjacent decimation

The reciprocal BV-window comparison uses two dilation steps and therefore square-index
decimation.  A single adjacent step already gives literal multiplication-index decimation.  Its
off-multiple Laurent residue has factor `1 - r⁻¹`, exactly the boundary mass of the unit
exponential Wold--Calderón cell.

This is a dependency-closed source identity.  It neither constructs the all-prime enhanced
completion nor proves conservativity on Xi conormal fibres.
-/

open Complex

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- One positive integer argument-dilation step is literal multiplication-index decimation on the
finite von-Mangoldt window. -/
theorem weightedPrimeWindow_argumentDilation_eq_mul
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    (W.argumentDilation (r : ℝ) (Nat.cast_pos.mpr hr)).weightedPrimeWindow n =
      W.weightedPrimeWindow (r * n) := by
  unfold weightedPrimeWindow
  apply tsum_congr
  intro k
  congr 1
  rw [argumentDilation_apply]
  congr 1
  push_cast
  ring

/-- The complete prime--polar coefficient obeys the same adjacent multiplication-index
decimation, including its archimedean counterterm. -/
theorem polarCoefficient_argumentDilation_eq_mul
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    (W.argumentDilation (r : ℝ) (Nat.cast_pos.mpr hr)).polarCoefficient n =
      W.polarCoefficient (r * n) := by
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hcpow :
      (((r : ℝ) : ℂ)) ^ ((3 / 2 : ℂ) - 1) =
        ((Real.sqrt r : ℝ) : ℂ) := by
    rw [show (3 / 2 : ℂ) - 1 = (((1 / 2 : ℝ) : ℂ)) by norm_num]
    rw [← Complex.ofReal_cpow hr0, ← Real.sqrt_eq_rpow]
  have hsqrt :
      ((Real.sqrt ((r * n : ℕ) : ℝ) : ℝ) : ℂ) =
        ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) := by
    push_cast
    rw [Real.sqrt_mul hr0]
    exact map_mul Complex.ofRealHom _ _
  rw [polarCoefficient, polarCoefficient,
    mellinTransform_argumentDilation,
    weightedPrimeWindow_argumentDilation_eq_mul]
  rw [hcpow, hsqrt]
  ring
  exact_mod_cast hr

/-- Laurent residue of the coefficient layer left after deleting indices divisible by `r`.
The factor `r^(-(rho+1/2))` is the Dirichlet-series effect of inflation. -/
def adjacentOffMultipleResidueValue
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (rho : ℂ) : ℂ :=
  W.continuedSourceResidueValue rho -
    (r : ℂ) ^ (-(rho + 1 / 2)) *
      (W.argumentDilation (r : ℝ) (Nat.cast_pos.mpr hr)).continuedSourceResidueValue rho

/-- The adjacent off-multiple Laurent layer removes the zero-independent fraction `r⁻¹` from
every continued residue. -/
theorem adjacentOffMultipleResidueValue_eq
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (rho : ℂ) :
    adjacentOffMultipleResidueValue W r hr rho =
      (1 - (r : ℂ)⁻¹) * W.continuedSourceResidueValue rho := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [adjacentOffMultipleResidueValue,
    continuedSourceResidueValue_argumentDilation]
  simp only [Complex.ofReal_natCast]
  have hpow :
      (r : ℂ) ^ (-(rho + 1 / 2)) * (r : ℂ) ^ (rho - 1 / 2) =
        (r : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hrC]
    rw [show -(rho + 1 / 2) + (rho - 1 / 2) = (-1 : ℂ) by ring,
      Complex.cpow_neg_one]
  rw [← mul_assoc, hpow]
  ring

/-- The complexified unit-exponential Wold boundary mass is the same adjacent defect factor. -/
theorem unitExponentialWoldBoundaryMass_log_nat_cast
    (r : ℕ) (hr : 0 < r) :
    ((unitExponentialWoldBoundaryMass (Real.log r) : ℝ) : ℂ) =
      1 - (r : ℂ)⁻¹ := by
  rw [unitExponentialWoldBoundaryMass_log (Nat.cast_pos.mpr hr)]
  norm_num [Complex.ofReal_inv]

/-- **Exact local Wold--BV weld.**  The adjacent off-multiple Laurent residue fraction is precisely
the unit-exponential Wold--Calderón fundamental-cell mass. -/
theorem adjacentOffMultipleResidueValue_eq_woldBoundaryMass
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (rho : ℂ) :
    adjacentOffMultipleResidueValue W r hr rho =
      (unitExponentialWoldBoundaryMass (Real.log r) : ℂ) *
        W.continuedSourceResidueValue rho := by
  rw [adjacentOffMultipleResidueValue_eq,
    unitExponentialWoldBoundaryMass_log_nat_cast]
  exact_mod_cast hr

end CompactBVPrimeWindow
end RHTower
