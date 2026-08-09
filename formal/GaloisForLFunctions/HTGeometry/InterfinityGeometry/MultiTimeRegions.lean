import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralHorizonCocycle

/-!
# The multi-time observer polyhedron

With `d` independent future times the admissible observers and the face-stable observers are the
open polyhedra

`𝒪_β = {ρ : 2ρ_j + β_j > 0 for all j}`,  `D_β = {ρ ∈ 𝒪_β : ρ_j + β_j > 0 for all j}`,

each a product of the corresponding one-time regions.  Both are open and convex, `D_β ⊆ 𝒪_β`, and
in every coordinate the horizon width is `𝔡_{β_j} + β_j/2 = max(0, −β_j/2)`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open Set

variable {d : ℕ}

/-- The admissible multi-time observer region. -/
def multiObserverRegion (β : Fin d → ℝ) : Set (Fin d → ℝ) := {ρ | ∀ j, 0 < 2 * ρ j + β j}

/-- The face-stable multi-time death region. -/
def multiStableRegion (β : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {ρ | (∀ j, 0 < 2 * ρ j + β j) ∧ ∀ j, 0 < ρ j + β j}

theorem mem_multiObserverRegion_iff (β ρ : Fin d → ℝ) :
    ρ ∈ multiObserverRegion β ↔ ∀ j, ρ j ∈ observerLine (β j) := by
  simp only [multiObserverRegion, mem_setOf_eq, mem_observerLine_iff]

theorem mem_multiStableRegion_iff (β ρ : Fin d → ℝ) :
    ρ ∈ multiStableRegion β ↔ ∀ j, ρ j ∈ stableRegion (β j) := by
  simp only [multiStableRegion, mem_setOf_eq, mem_stableRegion_iff]
  constructor
  · rintro ⟨h1, h2⟩ j
    exact ⟨h1 j, h2 j⟩
  · intro h
    exact ⟨fun j => (h j).1, fun j => (h j).2⟩

/-- The admissible region is the product of the one-time observer lines. -/
theorem multiObserverRegion_eq_pi (β : Fin d → ℝ) :
    multiObserverRegion β = Set.pi univ fun j => observerLine (β j) := by
  ext ρ
  rw [mem_multiObserverRegion_iff, mem_pi]
  simp

/-- The face-stable region is the product of the one-time death regions. -/
theorem multiStableRegion_eq_pi (β : Fin d → ℝ) :
    multiStableRegion β = Set.pi univ fun j => stableRegion (β j) := by
  ext ρ
  rw [mem_multiStableRegion_iff, mem_pi]
  simp

theorem multiStableRegion_subset (β : Fin d → ℝ) :
    multiStableRegion β ⊆ multiObserverRegion β := by
  intro ρ hρ
  rw [mem_multiStableRegion_iff] at hρ
  rw [mem_multiObserverRegion_iff]
  exact fun j => stableRegion_subset_observerLine (β j) (hρ j)

/-- **The observer region is an open polyhedron.** -/
theorem isOpen_multiObserverRegion (β : Fin d → ℝ) : IsOpen (multiObserverRegion β) := by
  rw [multiObserverRegion_eq_pi]
  exact isOpen_set_pi finite_univ fun j _ => isOpen_Ioi

/-- **The face-stable region is an open polyhedron.** -/
theorem isOpen_multiStableRegion (β : Fin d → ℝ) : IsOpen (multiStableRegion β) := by
  rw [multiStableRegion_eq_pi]
  exact isOpen_set_pi finite_univ fun j _ => isOpen_Ioi

theorem convex_multiObserverRegion (β : Fin d → ℝ) : Convex ℝ (multiObserverRegion β) := by
  rw [multiObserverRegion_eq_pi]
  exact convex_pi fun j _ => convex_Ioi _

theorem convex_multiStableRegion (β : Fin d → ℝ) : Convex ℝ (multiStableRegion β) := by
  rw [multiStableRegion_eq_pi]
  exact convex_pi fun j _ => convex_Ioi _

/-- **The coordinatewise horizon widths.** -/
theorem multi_deathCut_add (β : Fin d → ℝ) (j : Fin d) :
    deathCut (β j) + β j / 2 = max 0 (-β j / 2) := deathCut_add (β j)

/-- The face-stable region exhausts the observer region exactly when no weight is singular. -/
theorem multiStableRegion_eq_iff (β : Fin d → ℝ) :
    (∀ j, deathCut (β j) = -β j / 2) ↔ ∀ j, 0 ≤ β j := by
  constructor
  · intro h j
    exact (deathCut_eq_iff (β j)).1 (h j)
  · intro h j
    exact (deathCut_eq_iff (β j)).2 (h j)

end GaloisForLFunctions.HTGeometry.Interfinity
