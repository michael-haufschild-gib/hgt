import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Tactic.LinearCombination

/-!
# A derivation of a fraction field is determined by its restriction

Two derivations of a fraction field that agree on the image of the base ring are equal: the quotient
rule solves for the derivative of a fraction in terms of the derivatives of a numerator and a
denominator.

This is what identifies a derivation transported from a concrete differential field with the formal
jet derivation: both are derivations of the same fraction field, and they agree on the polynomial
ring because they agree on the variables.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A derivation of a fraction field is determined by its values on the base ring.** -/
theorem derivation_ext_of_fractionRing {C R K : Type*} [CommRing C] [CommRing R] [IsDomain R]
    [Field K] [Algebra C R] [Algebra R K] [Algebra C K] [IsScalarTower C R K]
    [IsFractionRing R K] {D₁ D₂ : Derivation C K K}
    (h : ∀ a : R, D₁ (algebraMap R K a) = D₂ (algebraMap R K a)) : D₁ = D₂ := by
  ext x
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K (b : R) ≠ 0 := by
    refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
    exact hb
  have hxb : x * algebraMap R K (b : R) = algebraMap R K a := by
    rw [← hx, div_mul_cancel₀ _ hb0]
  have hD : ∀ D : Derivation C K K,
      D x * algebraMap R K (b : R) = D (algebraMap R K a) - x * D (algebraMap R K (b : R)) := by
    intro D
    have hlei := congrArg D hxb
    rw [Derivation.leibniz] at hlei
    simp only [smul_eq_mul] at hlei
    linear_combination hlei
  have h₁ := hD D₁
  have h₂ := hD D₂
  rw [h a, h b] at h₁
  have hmul : D₁ x * algebraMap R K (b : R) = D₂ x * algebraMap R K (b : R) := by
    rw [h₁, h₂]
  exact mul_right_cancel₀ hb0 hmul

end

end GaloisForLFunctions.HTGeometry
