import Mathlib.NumberTheory.RatFunc.Ostrowski

/-!
# Inversion of the rational-function coordinate

The substitution `t ↦ t⁻¹` is the algebraic change of coordinate relating the place at infinity
of `F(t)` to the `X`-adic coordinate used by Laurent series.  This file records that substitution
without yet making a topological assertion about the two completions.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IntermediateField
open scoped RatFunc

universe u

noncomputable section

/-- The inverse rational-function coordinate generates `F(t)` over `F`. -/
theorem rationalFunctionAdjoinInvX_eq_top (F : Type u) [Field F] :
    F⟮((RatFunc.X : RatFunc F)⁻¹)⟯ = ⊤ := by
  apply top_unique
  rw [← RatFunc.adjoin_X]
  rw [IntermediateField.adjoin_simple_le_iff]
  simpa using (F⟮((RatFunc.X : RatFunc F)⁻¹)⟯).inv_mem
    (IntermediateField.mem_adjoin_simple_self F ((RatFunc.X : RatFunc F)⁻¹))

/-- The inverse coordinate is transcendental over the coefficient field. -/
theorem rationalFunctionInvX_transcendental (F : Type u) [Field F] :
    Transcendental F ((RatFunc.X : RatFunc F)⁻¹) := by
  rw [Transcendental]
  intro h
  exact RatFunc.transcendental_X (K := F) ((IsAlgebraic.inv_iff).mp h)

/-- Algebra automorphism of `F(t)` induced by the substitution `t ↦ t⁻¹`. -/
noncomputable def rationalFunctionInversionAlgEquiv (F : Type u) [Field F] :
    RatFunc F ≃ₐ[F] RatFunc F :=
  (RatFunc.algEquivOfTranscendental ((RatFunc.X : RatFunc F)⁻¹)
    (rationalFunctionInvX_transcendental F)).trans
    ((IntermediateField.equivOfEq (rationalFunctionAdjoinInvX_eq_top F)).trans
      IntermediateField.topEquiv)

/-- Coordinate inversion sends the rational-function variable to its inverse. -/
theorem rationalFunctionInversionAlgEquiv_X (F : Type u) [Field F] :
    rationalFunctionInversionAlgEquiv F (RatFunc.X : RatFunc F) = (RatFunc.X : RatFunc F)⁻¹ := by
  simp [rationalFunctionInversionAlgEquiv]

/-- Coordinate inversion is involutive on the rational-function variable. -/
theorem rationalFunctionInversionAlgEquiv_inv_X (F : Type u) [Field F] :
    rationalFunctionInversionAlgEquiv F ((RatFunc.X : RatFunc F)⁻¹) = RatFunc.X := by
  rw [map_inv₀, rationalFunctionInversionAlgEquiv_X]
  exact inv_inv _

end

end GaloisForLFunctions.HTGeometry.ABHN
