import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The Kronecker phase field and the deck-invariant radius

A vector orthogonal to a family with dense span vanishes, so the phase functional attached to a
nonzero vector is not identically zero: the Kronecker field of a nonunitary point is nonzero.

The suspension radius `u‖h‖` is unchanged by the deck relation, which multiplies the vector by a
positive rational and divides the height by it.

* `deningerOrthogonal_denseSpan_eq_zero` : orthogonality to a dense-span family forces zero.
* `deningerKronecker_ne_zero` : the phase functional of a nonzero vector is not identically zero.
* `deningerRadius_deck_invariant` : the radius is deck invariant.
-/

namespace RHTower

open scoped InnerProductSpace

section DenseSpan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **A vector orthogonal to a family with dense span is zero.**  The vectors it annihilates form
a closed submodule, which therefore contains the closure of the span. -/
theorem deningerOrthogonal_denseSpan_eq_zero {s : Set H}
    (hdense : Dense ((Submodule.span ℝ s : Submodule ℝ H) : Set H)) {h : H}
    (hperp : ∀ a ∈ s, ⟪h, a⟫_ℝ = 0) : h = 0 := by
  have hker : Submodule.span ℝ s ≤ (innerSL ℝ h).ker :=
    Submodule.span_le.mpr fun a ha => by simpa using hperp a ha
  have hclosed : IsClosed ((((innerSL ℝ h).ker : Submodule ℝ H)) : Set H) :=
    (innerSL ℝ h).isClosed_ker
  have hsub := hclosed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr hker)
  have hmem : h ∈ (((innerSL ℝ h).ker : Submodule ℝ H) : Set H) := hsub (hdense h)
  have hzero : ⟪h, h⟫_ℝ = 0 := by simpa using hmem
  exact inner_self_eq_zero.mp hzero

/-- **The Kronecker phase functional of a nonzero vector is not identically zero.**  This is why
the phase field is nonvanishing off the unitary locus. -/
theorem deningerKronecker_ne_zero {s : Set H}
    (hdense : Dense ((Submodule.span ℝ s : Submodule ℝ H) : Set H)) {h : H} (hh : h ≠ 0) :
    ∃ a ∈ s, ⟪h, a⟫_ℝ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hh (deningerOrthogonal_denseSpan_eq_zero hdense hcon)

end DenseSpan

section Radius

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The suspension radius of a point of the nonunitary locus. -/
noncomputable def deningerRadius (u : ℝ) (h : H) : ℝ := u * ‖h‖

/-- **The radius is invariant under the deck relation** `(h, u) ↦ (q·h, u/q)`. -/
theorem deningerRadius_deck_invariant {q : ℝ} (hq : 0 < q) (u : ℝ) (h : H) :
    deningerRadius (u / q) (q • h) = deningerRadius u h := by
  rw [deningerRadius, deningerRadius, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
  field_simp

omit [NormedSpace ℝ H] in
/-- **The radius scales linearly along the suspension flow** `u ↦ c·u`. -/
theorem deningerRadius_flow (c u : ℝ) (h : H) :
    deningerRadius (c * u) h = c * deningerRadius u h := by
  rw [deningerRadius, deningerRadius]
  ring

end Radius

end RHTower
