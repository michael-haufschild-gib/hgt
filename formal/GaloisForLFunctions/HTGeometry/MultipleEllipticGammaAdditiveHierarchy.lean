import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHierarchy
import GaloisForLFunctions.HTGeometry.EllipticThetaLogCoordinate

/-!
# Additive all-order multiple elliptic-gamma hierarchy

The convergent multiplicative kernel is pulled back by the standard uncentered exponential
coordinate.  Translation by any structural parameter gives exactly the lower-order coordinate-
deletion face.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The uncentered multiplicative coordinate for the standard multiple elliptic gamma product. -/
def multipleEllipticGammaCoordinate (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * I * z)

theorem multipleEllipticGammaCoordinate_ne_zero (z : ℂ) :
    multipleEllipticGammaCoordinate z ≠ 0 := by
  simp [multipleEllipticGammaCoordinate]

/-- Additive translation multiplies the standard coordinate by the corresponding nome. -/
theorem multipleEllipticGammaCoordinate_add (τ z : ℂ) :
    multipleEllipticGammaCoordinate (z + τ) =
      ellipticNome τ * multipleEllipticGammaCoordinate z := by
  rw [multipleEllipticGammaCoordinate, multipleEllipticGammaCoordinate, ellipticNome,
    mul_add, Complex.exp_add]
  ring

/-- Additive logarithmic derivative kernel of the all-order multiple elliptic gamma product. -/
def multipleEllipticGammaAdditiveLogKernel (τ : ι → ℂ) (z : ℂ) : ℂ :=
  2 * Real.pi * I * multipleEllipticGammaLogKernel
    (fun i => ellipticNome (τ i)) (multipleEllipticGammaCoordinate z)

/-- **Actual additive all-order hierarchy equation.** Every structural translation lowers the
kernel to the coordinate-deletion face. -/
theorem multipleEllipticGammaAdditiveLogKernel_add_sub
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) (q : ι) (z : ℂ) :
    multipleEllipticGammaAdditiveLogKernel τ (z + τ q) -
        multipleEllipticGammaAdditiveLogKernel τ z =
      multipleEllipticGammaAdditiveLogKernel
        (fun i : {i : ι // i ≠ q} => τ i) z := by
  rw [multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaCoordinate_add, ← mul_sub]
  rw [multipleEllipticGammaLogKernel_mul_coordinate_sub q
    (fun i => ellipticNome_ne_zero (τ i))
    (fun i => norm_ellipticNome_lt_one (hτ i))
    (multipleEllipticGammaCoordinate_ne_zero z)]

end

end GaloisForLFunctions
