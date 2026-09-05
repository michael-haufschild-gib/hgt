import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Root geometry of Brizard's Weierstrass cubic

The Jacobi--Weierstrass identity in arXiv:2607.21750 defines the modulus by the root-gap ratio
`m = (e₂-e₃)/(e₁-e₃)`.  This module proves that reconstruction exactly, classifies every possible
root collision, identifies repeated roots with the paper's discriminant-zero locus, and verifies
the conventional strict root ordering throughout the classical interior parameter region.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Exact modulus reconstruction from the cubic roots displayed after equation (73). -/
theorem modulus_eq_root_gap_ratio (P : Parameters) :
    (e₂ P - e₃ P) / (e₁ P - e₃ P) = P.modulus := by
  rw [e₂_sub_e₃, e₁_sub_e₃]
  field_simp [P.q₀.ne_zero]

/-- The normalizing gap `e₁-e₃ = 1/q₀` never vanishes. -/
theorem e₁_ne_e₃ (P : Parameters) : e₁ P ≠ e₃ P := by
  intro h
  have hgap := e₁_sub_e₃ P
  rw [h, sub_self] at hgap
  exact (one_div_ne_zero P.q₀.ne_zero) hgap.symm

theorem e₁_eq_e₂_iff (P : Parameters) : e₁ P = e₂ P ↔ P.modulus = 1 := by
  rw [← sub_eq_zero, e₁_sub_e₂, div_eq_zero_iff]
  simp only [P.q₀.ne_zero, or_false]
  constructor <;> intro h <;> linarith

theorem e₂_eq_e₃_iff (P : Parameters) : e₂ P = e₃ P ↔ P.modulus = 0 := by
  rw [← sub_eq_zero, e₂_sub_e₃, div_eq_zero_iff]
  simp [P.q₀.ne_zero]

/-- The invariant discriminant vanishes exactly when the displayed cubic has a repeated root. -/
theorem repeated_root_iff_singular (P : Parameters) :
    e₁ P = e₂ P ∨ e₂ P = e₃ P ∨ e₁ P = e₃ P ↔ discriminant P = 0 := by
  rw [e₁_eq_e₂_iff, e₂_eq_e₃_iff, discriminant_eq_zero_iff]
  simp only [e₁_ne_e₃ P, or_false]
  tauto

/-- Strictly classical modulus and positive scale. -/
abbrev ClassicalInteriorParameters :=
  {P : Parameters // 0 < P.modulus ∧ P.modulus < 1 ∧ 0 < (P.q₀ : ℝ)}

/-- Standard real-root order underlying the classical Jacobi chart. -/
theorem classicalInterior_root_order (P : ClassicalInteriorParameters) :
    e₃ P < e₂ P ∧ e₂ P < e₁ P := by
  constructor
  · have h := e₂_sub_e₃ P.val
    have hdiv : 0 < P.val.modulus / (P.val.q₀ : ℝ) :=
      div_pos P.property.1 P.property.2.2
    linarith
  · have h := e₁_sub_e₂ P.val
    have hdiv : 0 < (1 - P.val.modulus) / (P.val.q₀ : ℝ) :=
      div_pos (by linarith [P.property.2.1]) P.property.2.2
    linarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
