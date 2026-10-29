import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Trace-dual fractional ideals have discriminant norms

The codifferent is the inverse different, whose norm is the absolute
field discriminant. The trace dual of a fractional ideal is its inverse
times the codifferent, giving the exact norm formula also at the zero ideal.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- The codifferent has norm equal to the reciprocal absolute discriminant. -/
theorem absNorm_numberField_codifferent :
    FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ (1 : FI)) =
      ((NumberField.discr K).natAbs : ℚ)⁻¹ := by
  have h : (_root_.differentIdeal ℤ (𝓞 K) : FI)⁻¹ =
      FractionalIdeal.dual ℤ ℚ (1 : FI) := by
    rw [_root_.coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  rw [← h, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K (𝓞 K)]

/-- The norm of a trace-dual fractional ideal includes the exact absolute discriminant factor. -/
theorem absNorm_numberField_traceDual (I : FI) :
    FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ I) =
      (((NumberField.discr K).natAbs : ℚ) * FractionalIdeal.absNorm I)⁻¹ := by
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ I, map_mul, map_inv₀,
    absNorm_numberField_codifferent, mul_inv_rev, mul_comm]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.absNorm_numberField_traceDual
