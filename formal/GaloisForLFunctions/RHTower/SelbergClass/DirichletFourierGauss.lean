import GaloisForLFunctions.RHTower.SelbergClass.DirichletFourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Primitive Fourier coefficients and Gauss sums

This module proves the primitive-conductor case of the closed Fourier coefficient in
Kaczorowski--Perelli's Lemma 1.  The imprimitive conductor/Möbius factor is deliberately not hidden:
it remains a separate theorem.
-/

open AddChar

namespace RHTower

noncomputable section

/-- Negative standard additive phase `x ↦ e(-a x / D)`. -/
def negativeAdditivePhase {D : ℕ} [NeZero D] (a : ZMod D) : ZMod D → ℂ :=
  fun x ↦ ZMod.stdAddChar (-a * x)

/-- For a primitive character, the negative-phase Fourier coefficient is the character value
times the conjugate Gauss sum. -/
theorem primitive_dirichletCharacterFourierCoeff_negativeAdditivePhase {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (a : ZMod D) :
    dirichletCharacterFourierCoeff (negativeAdditivePhase a) χ =
      χ a * star (gaussSum χ ZMod.stdAddChar) := by
  have hχinv : χ⁻¹.IsPrimitive := by
    simpa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  change gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (-a)) = _
  have hphase : ZMod.stdAddChar.mulShift (-a) = (ZMod.stdAddChar)⁻¹.mulShift a := by
    ext x
    simp only [mulShift_apply, AddChar.inv_apply, neg_mul]
  rw [hphase]
  rw [gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar)⁻¹ hχinv a]
  rw [← star_gaussSum_eq χ ZMod.stdAddChar]
  simp

end


end RHTower
