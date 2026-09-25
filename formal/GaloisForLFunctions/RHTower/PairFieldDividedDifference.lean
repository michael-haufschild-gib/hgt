import Mathlib

/-!
# The pair field is a divided difference, hence a pointwise value of the regular field

The gap equation of the backward flow carries the pair field
`Δ = Σ_y [(x₁ - y)(x₂ - y)]⁻¹` over the zeros outside a consecutive pair. Attempting to evolve `Δ`
through the field equation mixes in the pair's own singular part, which is adverse. This module
avoids the evolution entirely.

Partial fractions give `[(x₁ - y)(x₂ - y)]⁻¹ = [(x₁ - y)⁻¹ - (x₂ - y)⁻¹]/(x₂ - x₁)`, so summing over
the surrounding zeros,

  `Δ = [ L(x₁) - L(x₂) ] / (x₂ - x₁)`,

the divided difference of the regular logarithmic derivative across the gap. Because the pair is
**consecutive**, no surrounding zero lies in the closed gap, so `L` is differentiable there and the
mean value theorem applies. Its derivative is minus the regular field, whence

  `Δ = V(ξ)`  for some `ξ` strictly inside the gap,

with `V(z) = Σ_y (z - y)⁻²` the regular field. So the pair quantity is an honest pointwise value of a
field that is smooth across the gap, carrying none of the pair's singularity. That is the separation
the collision analysis needs: any bound on the regular field on the gap interval bounds `Δ`, and the
adverse diffusion of the raw field near a close pair is irrelevant to it.
-/

namespace RHTower

noncomputable section

/-- Regular logarithmic derivative of the surrounding zeros. -/
def regLogDeriv (S : Finset ℝ) (z : ℝ) : ℝ := ∑ y ∈ S, (z - y)⁻¹

/-- Regular field of the surrounding zeros. -/
def regField (S : Finset ℝ) (z : ℝ) : ℝ := ∑ y ∈ S, ((z - y) ^ (2 : ℕ))⁻¹

/-- The pair field of a consecutive pair against the surrounding zeros. -/
def pairRegField (S : Finset ℝ) (x₁ x₂ : ℝ) : ℝ := ∑ y ∈ S, ((x₁ - y) * (x₂ - y))⁻¹

theorem regField_nonneg (S : Finset ℝ) (z : ℝ) : 0 ≤ regField S z :=
  Finset.sum_nonneg fun y _ => inv_nonneg.mpr (by positivity)

/-- **The pair field is a divided difference.** -/
theorem pairRegField_eq_slope {S : Finset ℝ} {x₁ x₂ : ℝ} (hne : x₁ ≠ x₂)
    (hS : ∀ y ∈ S, y ≠ x₁ ∧ y ≠ x₂) :
    pairRegField S x₁ x₂ = (regLogDeriv S x₁ - regLogDeriv S x₂) / (x₂ - x₁) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [pairRegField, regLogDeriv, regLogDeriv, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨h₁, h₂⟩ := hS y hy
  have hy1 : x₁ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁)
  have hy2 : x₂ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂)
  field_simp
  ring

/-- The regular logarithmic derivative differentiates to minus the regular field. -/
theorem hasDerivAt_regLogDeriv {S : Finset ℝ} {z : ℝ} (hz : ∀ y ∈ S, y ≠ z) :
    HasDerivAt (regLogDeriv S) (-regField S z) z := by
  have key : ∀ y ∈ S, HasDerivAt (fun w : ℝ => (w - y)⁻¹) (-1 / (z - y) ^ (2 : ℕ)) z := by
    intro y hy
    have hyz : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz y hy))
    exact ((hasDerivAt_id z).sub_const y).inv hyz
  have hsum := HasDerivAt.sum key
  have hfun : (∑ i ∈ S, fun w : ℝ => (w - i)⁻¹) = fun w : ℝ => ∑ y ∈ S, (w - y)⁻¹ := by
    funext w
    exact Finset.sum_apply w S _
  rw [hfun] at hsum
  have h : HasDerivAt (fun w : ℝ => ∑ y ∈ S, (w - y)⁻¹)
      (∑ y ∈ S, -1 / (z - y) ^ (2 : ℕ)) z := hsum
  have heq : (∑ y ∈ S, -1 / (z - y) ^ (2 : ℕ)) = -regField S z := by
    rw [regField, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [neg_div, one_div]
  rw [← heq]
  exact h

/-- **The pair field is a pointwise value of the regular field inside the gap.** For a consecutive
pair, no surrounding zero lies in the closed gap, and the mean value theorem places `Δ` at an
interior point. -/
theorem exists_pairRegField_eq_regField {S : Finset ℝ} {x₁ x₂ : ℝ} (hlt : x₁ < x₂)
    (hS : ∀ y ∈ S, y < x₁ ∨ x₂ < y) :
    ∃ ξ ∈ Set.Ioo x₁ x₂, pairRegField S x₁ x₂ = regField S ξ := by
  have hout : ∀ z ∈ Set.Icc x₁ x₂, ∀ y ∈ S, y ≠ z := by
    intro z hz y hy
    rcases hS y hy with h | h
    · exact fun hc => absurd (hc ▸ h) (not_lt.mpr hz.1)
    · exact fun hc => absurd (hc ▸ h) (not_lt.mpr hz.2)
  have hderiv : ∀ z ∈ Set.Icc x₁ x₂, HasDerivAt (regLogDeriv S) (-regField S z) z :=
    fun z hz => hasDerivAt_regLogDeriv (hout z hz)
  have hcont : ContinuousOn (regLogDeriv S) (Set.Icc x₁ x₂) :=
    fun z hz => ((hderiv z hz).continuousAt).continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (regLogDeriv S) (fun z => -regField S z) hlt hcont
      (fun z hz => hderiv z (Set.mem_Icc_of_Ioo hz))
  refine ⟨ξ, hξ, ?_⟩
  have hne : x₁ ≠ x₂ := ne_of_lt hlt
  have hS' : ∀ y ∈ S, y ≠ x₁ ∧ y ≠ x₂ := by
    intro y hy
    rcases hS y hy with h | h
    · exact ⟨ne_of_lt h, ne_of_lt (h.trans hlt)⟩
    · exact ⟨fun hc => absurd (hc ▸ h) (not_lt.mpr hlt.le), fun hc => absurd (hc ▸ h) (lt_irrefl _)⟩
  rw [pairRegField_eq_slope hne hS']
  linear_combination hslope

end

end RHTower
