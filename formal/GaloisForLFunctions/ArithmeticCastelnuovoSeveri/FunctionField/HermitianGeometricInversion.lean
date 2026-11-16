import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianCoordinateHom
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldHomExt

/-!
# Inversion of the geometric Hermitian coordinates

The substitution `(z,u) ↦ (z/u,1/u)` preserves the Hermitian equation.
It defines an actual constant-field automorphism: its image contains both
original coordinates. This exchanges the origin chart with the chart at infinity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "η" => hermitianExtensionTraceConstant p s E
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "z" => hermitianExtensionRadicalCoordinate p s E

/-- The transcendental additive coordinate is nonzero. -/
theorem hermitianGeometricAdditive_ne_zero : u ≠ 0 := by
  intro h
  apply hermitianExtensionAdditiveCoordinate_transcendental p s E
  rw [h]
  simpa only [map_zero] using (isAlgebraic_algebraMap (R := E) (A := H) (0 : E))

/-- Inverting the additive coordinate and dividing the radical by it preserves the curve. -/
def hermitianGeometricInversionPoint : HermitianAffinePoint p s H :=
  ⟨(z / u, u⁻¹), by
    have hu := hermitianGeometricAdditive_ne_zero p s
    change (u⁻¹) ^ Q + u⁻¹ = (z / u) ^ (Q + 1)
    rw [div_pow, hermitianExtensionField_equation, add_div, pow_succ u Q, inv_pow]
    field_simp
    ring⟩

/-- The inverse additive coordinate remains transcendental over the geometric constants. -/
theorem hermitianGeometricInversionPoint_transcendental :
    Transcendental E (hermitianGeometricInversionPoint p s).val.2 := by
  intro h
  change IsAlgebraic E (u⁻¹) at h
  have hi := h.inv
  rw [inv_inv] at hi
  exact hermitianExtensionAdditiveCoordinate_transcendental p s E hi

/-- Coordinate inversion induces a homomorphism of the actual geometric function field. -/
def hermitianGeometricInversionHom : H →ₐ[E] H :=
  hermitianFieldHomOfCoordinates p s E H (hermitianGeometricInversionPoint p s)
    (hermitianGeometricInversionPoint_transcendental p s)

/-- The additive coordinate is inverted. -/
theorem hermitianGeometricInversionHom_additive :
    hermitianGeometricInversionHom p s u = u⁻¹ :=
  hermitianFieldHomOfCoordinates_additive _ _ _ _ _ _

/-- The radical coordinate is divided by the additive coordinate. -/
theorem hermitianGeometricInversionHom_radical :
    hermitianGeometricInversionHom p s z = z / u :=
  hermitianFieldHomOfCoordinates_radical _ _ _ _ _ _

/-- The image of inversion contains both original field generators. -/
theorem hermitianGeometricInversionHom_surjective :
    Function.Surjective (hermitianGeometricInversionHom p s) := by
  let f := hermitianGeometricInversionHom p s
  have hui : u⁻¹ ∈ f.fieldRange := ⟨u, hermitianGeometricInversionHom_additive p s⟩
  have hu : u ∈ f.fieldRange := by
    simpa only [inv_inv] using f.fieldRange.inv_mem hui
  have hzu : z / u ∈ f.fieldRange := ⟨z, hermitianGeometricInversionHom_radical p s⟩
  have hz : z ∈ f.fieldRange := by
    simpa only [div_mul_cancel₀ z (hermitianGeometricAdditive_ne_zero p s)] using
      f.fieldRange.mul_mem hzu hu
  have hy : algebraMap E[X] H X ∈ f.fieldRange := by
    rw [← hermitianExtensionAdditiveCoordinate_recover p s E]
    exact f.fieldRange.mul_mem (f.fieldRange.algebraMap_mem (η : E)) hu
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem η⁻¹ (Q - 2) 1 Q f.fieldRange hy hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- The inversion substitution is an automorphism of the actual geometric Hermitian field. -/
def hermitianGeometricInversion : H ≃ₐ[E] H :=
  AlgEquiv.ofBijective (hermitianGeometricInversionHom p s)
    ⟨(hermitianGeometricInversionHom p s).injective, hermitianGeometricInversionHom_surjective p s⟩

/-- Applying coordinate inversion twice fixes every rational function. -/
theorem hermitianGeometricInversion_involutive :
    Function.Involutive (hermitianGeometricInversion p s) := by
  let f := hermitianGeometricInversionHom p s
  have hu : f (f u) = u := by
    rw [hermitianGeometricInversionHom_additive, map_inv₀,
      hermitianGeometricInversionHom_additive, inv_inv]
  have hz : f (f z) = z := by
    rw [hermitianGeometricInversionHom_radical, map_div₀,
      hermitianGeometricInversionHom_radical, hermitianGeometricInversionHom_additive]
    field_simp [hermitianGeometricAdditive_ne_zero p s]
  have he : f.comp f = AlgHom.id E H := by
    apply kummerBranchField_algHom_ext η⁻¹ (Q - 2) 1 Q
    · change f (f (algebraMap E[X] H X)) = algebraMap E[X] H X
      rw [← hermitianExtensionAdditiveCoordinate_recover p s E, map_mul, AlgHom.commutes,
        map_mul, AlgHom.commutes, hu]
    · exact hz
  intro x
  exact congrArg (fun g : H →ₐ[E] H => g x) he

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
