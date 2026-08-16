import Mathlib

/-!
# The counting step of the oscillator ladder

Only `j` even rungs lie below `4j+1`: they are `1, 5, …, 4j−3`.  So `j+1` distinct even rungs cannot
all lie there.

This is the pigeonhole that closes the lower half of the differential ordering: `j+1` mutually
orthogonal even modes have `j+1` distinct limiting separation constants, each an even rung, and if
all were below `4j+1` there would be one too many.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

/-- **The counting contradiction.**  There is no injective family of `j+1` even rungs below
`4j+1`. -/
theorem not_injective_evenRung_below {j : ℕ} (m : Fin (j + 1) → ℝ)
    (hrung : ∀ k, ∃ n : ℕ, Even n ∧ m k = 2 * (n : ℝ) + 1)
    (hbelow : ∀ k, m k < 4 * (j : ℝ) + 1)
    (hinj : Function.Injective m) : False := by
  choose n hne hm using hrung
  have hlt : ∀ k, n k < 2 * j := by
    intro k
    have h := hbelow k
    rw [hm k] at h
    have hcast : (n k : ℝ) < 2 * (j : ℝ) := by linarith
    exact_mod_cast hcast
  have hhalf : ∀ k, n k / 2 < j := by
    intro k
    obtain ⟨t, ht⟩ := hne k
    have hk := hlt k
    omega
  set f : Fin (j + 1) → Fin j := fun k => ⟨n k / 2, hhalf k⟩ with hf
  have hfinj : Function.Injective f := by
    intro k₁ k₂ h
    apply hinj
    rw [hm k₁, hm k₂]
    have hv : n k₁ / 2 = n k₂ / 2 := congrArg Fin.val h
    obtain ⟨t₁, ht₁⟩ := hne k₁
    obtain ⟨t₂, ht₂⟩ := hne k₂
    have hn : n k₁ = n k₂ := by omega
    rw [hn]
  have hcard := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_fin] at hcard
  omega

end GaloisForLFunctions.HTGeometry
