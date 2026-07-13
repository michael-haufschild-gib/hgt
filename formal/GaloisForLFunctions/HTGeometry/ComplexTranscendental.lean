import Mathlib

/-!
# A transcendental complex number exists

The algebraic numbers over `ℚ` in `ℂ` form a countable set (`Algebraic.countable`), while `ℂ` has
cardinality the continuum; hence some complex number is transcendental over `ℚ`.
-/

namespace GaloisForLFunctions

/-- There is a complex number transcendental over `ℚ`. -/
theorem exists_transcendental_complex : ∃ τ : ℂ, Transcendental ℚ τ := by
  by_contra h
  push Not at h
  have halg : ∀ τ : ℂ, IsAlgebraic ℚ τ := fun τ => not_not.mp (h τ)
  have hset : {x : ℂ | IsAlgebraic ℚ x} = Set.univ := Set.eq_univ_of_forall halg
  have hcount : (Set.univ : Set ℂ).Countable := hset ▸ Algebraic.countable ℚ ℂ
  have _hc : Countable ℂ := Set.countable_univ_iff.mp hcount
  have hle : Cardinal.mk ℂ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  rw [Cardinal.mk_complex] at hle
  exact absurd hle (not_le.mpr Cardinal.aleph0_lt_continuum)

end GaloisForLFunctions
