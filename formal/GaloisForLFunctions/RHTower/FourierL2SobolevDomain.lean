import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# Integer-order Fourier--Sobolev domains on `L²(ℝ)`

This module gives a reusable, non-circular definition of the integer-order Sobolev domains used
by closed Fourier-multiplier operators. A vector has order `n` precisely when multiplication of
its Fourier transform by `ξ ^ n` remains in `L²`. For `n = 1, 2`, these are the standard
Fourier realizations of `H¹(ℝ)` and `H²(ℝ)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RHTower

/-- Integer-order Fourier--Sobolev domain on scalar `L²(ℝ)`.

The harmless constant factors `(2π)^n` are omitted: multiplication by a fixed nonzero scalar does
not change maximal `L²` membership. -/
def fourierL2SobolevDomain (n : ℕ) : Submodule ℂ SoninL2 :=
  (GaloisForLFunctions.HTGeometry.maximalRealL2MulDomain volume
      (fun ξ : ℝ => ξ ^ n)).comap
    fourierUnitary.toLinearEquiv.toLinearMap

/-- Exact weighted-`L²` membership criterion for the Fourier--Sobolev domain. -/
theorem mem_fourierL2SobolevDomain_iff (n : ℕ) (f : SoninL2) :
    f ∈ fourierL2SobolevDomain n ↔
      MemLp (fun ξ : ℝ => ((ξ ^ n : ℝ) : ℂ) *
        (fourierUnitary f : ℝ → ℂ) ξ) 2 volume := by
  rfl

/-- Standard Fourier realization of `H¹(ℝ)`. -/
abbrev fourierL2H1 : Submodule ℂ SoninL2 := fourierL2SobolevDomain 1

/-- Standard Fourier realization of `H²(ℝ)`. -/
abbrev fourierL2H2 : Submodule ℂ SoninL2 := fourierL2SobolevDomain 2

end RHTower
