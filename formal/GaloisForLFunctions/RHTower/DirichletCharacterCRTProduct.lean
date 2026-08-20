/-
# Pullbacks of products of bundled multiplicative characters through CRT

This small algebraic layer turns two already bundled complex multiplicative
characters into a bundled character on a ring that is concretely CRT-equivalent
to their product. The construction acts on units and extends by zero, and its
pointwise theorem proves that extension agrees with the literal product at all
residues.
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Complex.Norm
import Mathlib.NumberTheory.MulChar.Basic

noncomputable section

namespace RHTower

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-- Product of the two unit characters after transport through a CRT ring equivalence. -/
def crtProductUnitHom (e : T ≃+* (R × S)) (χ : MulChar R ℂ) (ψ : MulChar S ℂ) :
    Tˣ →* ℂˣ where
  toFun u :=
    χ.toUnitHom (Units.map (MonoidHom.fst R S) (Units.map e.toMonoidHom u)) *
    ψ.toUnitHom (Units.map (MonoidHom.snd R S) (Units.map e.toMonoidHom u))
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_mul_mul_comm]

/-- Bundled CRT pullback of the literal product of two multiplicative characters. -/
def crtProductCharacter (e : T ≃+* (R × S)) (χ : MulChar R ℂ) (ψ : MulChar S ℂ) :
    MulChar T ℂ :=
  MulChar.ofUnitHom (crtProductUnitHom e χ ψ)

/-- The bundled CRT pullback is the literal coordinatewise product, including at nonunits. -/
theorem crtProductCharacter_apply (e : T ≃+* (R × S)) (χ : MulChar R ℂ) (ψ : MulChar S ℂ)
    (x : T) :
    crtProductCharacter e χ ψ x = χ (e x).1 * ψ (e x).2 := by
  classical
  by_cases hx : IsUnit x
  · rcases hx with ⟨u, rfl⟩
    simp [crtProductCharacter, crtProductUnitHom]
  · rw [MulChar.map_nonunit _ hx]
    have hprod : ¬ IsUnit (e x) := by
      intro h
      exact hx (by simpa using (h.map e.symm.toMonoidHom))
    rw [Prod.isUnit_iff, not_and_or] at hprod
    rcases hprod with hfst | hsnd
    · rw [MulChar.map_nonunit χ hfst, zero_mul]
    · rw [MulChar.map_nonunit ψ hsnd, mul_zero]

/-- A CRT pullback of two quadratic characters is again quadratic. -/
theorem crtProductCharacter_isQuadratic (e : T ≃+* (R × S)) (χ : MulChar R ℂ)
    (ψ : MulChar S ℂ) (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) :
    (crtProductCharacter e χ ψ).IsQuadratic := by
  intro x
  rw [crtProductCharacter_apply]
  rcases hχ (e x).1 with hχ | hχ | hχ <;>
    rcases hψ (e x).2 with hψ | hψ | hψ <;> simp [hχ, hψ]

end RHTower
