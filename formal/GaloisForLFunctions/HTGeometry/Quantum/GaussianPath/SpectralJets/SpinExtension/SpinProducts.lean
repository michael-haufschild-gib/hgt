import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Module

/-! # Pauli products for transmitting a spectral response across one bond -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The ZX bond and the new onsite X insertion produce a signed old Z response. -/
theorem longitudinal_flip_product (Z : Mat I) (hZ : Z*Z=1) (g l : ℂ) :
    (g • Z+l • 1)*(g • Z+l • 1) = (g^2+l^2) • 1+(2*g*l) • Z := by
  simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hZ,one_mul,mul_one,smul_add]
  module

/-- The two orderings of XX and YY leave their old Pauli commutator. The new
spin sign in that commutator cancels the sign of the virtual energy denominator. -/
theorem transverse_flip_product (X Y Z : Mat I) (hX : X*X=1) (hY : Y*Y=1)
    (hXY : X*Y=Complex.I • Z) (hYX : Y*X=(-Complex.I) • Z) (g s : ℂ) :
    (g • X-s • Y)*(g • X+s • Y) =
      (g^2-s^2) • 1+(2*Complex.I*g*s) • Z := by
  simp only [sub_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hX,hY,hXY,hYX,smul_add]
  module

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
