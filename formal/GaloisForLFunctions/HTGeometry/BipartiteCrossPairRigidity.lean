import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Rigidity of the crown graph with one edge deleted

The residue step of a local spectral extension produces equalities `u α = v β` for every *ordered*
pair of distinct labels, with at most one pair missing because the affine multiplier may vanish at
one gap.  The underlying bipartite graph is the complete bipartite graph minus a perfect matching,
the crown graph; for at least three labels it stays connected after deleting one further edge, so
all the values coincide.

The proof exhibits the explicit two-step path, so no graph-connectivity API is used.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [Fintype A] [DecidableEq A] {M : Type*}

/-- With at least three labels, every pair of labels admits a third. -/
theorem exists_third_label (hcard : 3 ≤ Fintype.card A) (x y : A) :
    ∃ β : A, β ≠ x ∧ β ≠ y := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hsub : (Finset.univ : Finset A) ⊆ {x, y} := by
    intro a _
    rcases eq_or_ne a x with h | h
    · simp [h]
    · simp [hcon a h]
  have hle := Finset.card_le_card hsub
  have h2 : ({x, y} : Finset A).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  simp only [Finset.card_univ] at hle
  omega

omit [Fintype A] [DecidableEq A] in
/-- Two labels sharing an admissible third have equal first-layer values. -/
theorem crossPair_eq_of_common (u v : A → M) (exc : A × A)
    (h : ∀ x y : A, x ≠ y → (x, y) ≠ exc → u x = v y)
    {x y γ : A} (hxγ : x ≠ γ) (hyγ : y ≠ γ) (hx : (x, γ) ≠ exc) (hy : (y, γ) ≠ exc) :
    u x = u y := by
  rw [h x γ hxγ hx, h y γ hyγ hy]

/-- **Crown rigidity.**  Cross equalities on every ordered pair of distinct labels except at most
one force all values, on both layers, to coincide. -/
theorem crossPair_constant (hcard : 3 ≤ Fintype.card A) (u v : A → M) (exc : A × A)
    (h : ∀ x y : A, x ≠ y → (x, y) ≠ exc → u x = v y) :
    (∀ x y, u x = u y) ∧ (∀ x y, v x = v y) ∧ (∀ x y, u x = v y) := by
  have hu : ∀ x y : A, u x = u y := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · rfl
    obtain ⟨β, hβx, hβy⟩ := exists_third_label hcard x y
    by_cases hxβ : (x, β) = exc
    · -- the missing pair is `(x, β)`: go `x → y → β → x → y`
      have e1 : (x, y) ≠ exc := by rw [← hxβ]; simpa using Ne.symm hβy
      have e2 : (β, y) ≠ exc := by rw [← hxβ]; simp [hβx]
      have e3 : (β, x) ≠ exc := by rw [← hxβ]; simp [hβx]
      have e4 : (y, x) ≠ exc := by rw [← hxβ]; simp [Ne.symm hxy]
      have h1 : u x = u β := crossPair_eq_of_common u v exc h hxy hβy e1 e2
      have h2 : u β = u y := crossPair_eq_of_common u v exc h hβx (Ne.symm hxy) e3 e4
      rw [h1, h2]
    · by_cases hyβ : (y, β) = exc
      · have e1 : (y, x) ≠ exc := by rw [← hyβ]; simpa using Ne.symm hβx
        have e2 : (β, x) ≠ exc := by rw [← hyβ]; simp [hβy]
        have e3 : (β, y) ≠ exc := by rw [← hyβ]; simp [hβy]
        have e4 : (x, y) ≠ exc := by rw [← hyβ]; simp [hxy]
        have h1 : u y = u β := crossPair_eq_of_common u v exc h (Ne.symm hxy) hβx e1 e2
        have h2 : u β = u x := crossPair_eq_of_common u v exc h hβy hxy e3 e4
        rw [← h2, ← h1]
      · exact crossPair_eq_of_common u v exc h (Ne.symm hβx) (Ne.symm hβy) hxβ hyβ
  have hcross : ∀ x y : A, u x = v y := by
    intro x y
    obtain ⟨β, hβx, hβy⟩ := exists_third_label hcard x y
    by_cases hβ : (β, y) = exc
    · obtain ⟨γ, hγβ, hγy⟩ := exists_third_label hcard β y
      have hval : u γ = v y := h γ y hγy (by rw [← hβ]; simp [hγβ])
      rw [hu x γ, hval]
    · have hval : u β = v y := h β y hβy hβ
      rw [hu x β, hval]
  have hv : ∀ x y : A, v x = v y := by
    intro x y
    obtain ⟨z⟩ : Nonempty A := by
      rw [← Fintype.card_pos_iff]
      omega
    rw [← hcross z x, ← hcross z y]
  exact ⟨hu, hv, hcross⟩

end GaloisForLFunctions.HTGeometry
