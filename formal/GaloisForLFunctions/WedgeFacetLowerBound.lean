import Mathlib

/-!
# Dimension-three impossibility for the nonpure two-thick wedge

The lower-bound half of the exact faithful facet-separation dimension of the connected nonpure
two-thick complex `S¹ ∨ S²`: no faithful facet separation of this complex exists in a complex
vector space of dimension at most three, hence `ffsDim(Δ_wedge) ≥ 4`.

The complex has vertices `{0,…,5}` and seven facets — the three circle edges `{0,1},{1,2},{0,2}`
and the four sphere triangles `{0,3,4},{0,3,5},{0,4,5},{3,4,5}`, glued at vertex `0`.  A faithful
separation supplies vectors `a v` and forms `ℓ i` with the exact zero pattern
`ℓ i (a v) = 0 ↔ v ∉ wedgeFacet i`.

The argument is pure complex linear algebra.  Set `L = span_ℂ{a₃,a₄,a₅}` (the sphere apex vectors).
Both forms `ℓ_{0,1}` and `ℓ_{1,2}` annihilate `a₃,a₄,a₅`, hence all of `L`.

* If `dim L ≤ 1`, then `a₅ ≠ 0` spans `L`, so `a₃ ∈ ℂ·a₅`; applying `ℓ_{0,3,4}` (which kills `a₅`,
  since `5 ∉ {0,3,4}`) forces `ℓ_{0,3,4}(a₃) = 0`, contradicting `3 ∈ {0,3,4}`.
* If `dim L ≥ 2`, then `a₀ ∈ L`: otherwise `L ⊔ ℂ·a₀` has dimension `≥ 3 ≥ dim E`, so equals the
  whole space, forcing `ℓ_{1,2}` (which kills `L` and `a₀`) to vanish identically, contradicting
  `1 ∈ {1,2}`.  But `a₀ ∈ L` makes `ℓ_{0,1}(a₀) = 0`, contradicting `0 ∈ {0,1}`.

Either way the ambient dimension exceeds three.
-/

open Finset

namespace GaloisForLFunctions

/-- The seven facets of the nonpure two-thick wedge `S¹ ∨ S²` on vertices `{0,…,5}`: the three
edges `{0,1},{1,2},{0,2}` of the circle and the four triangles `{0,3,4},{0,3,5},{0,4,5},{3,4,5}`
of the sphere, joined at vertex `0`. -/
def wedgeFacet : Fin 7 → Finset (Fin 6)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}
  | 3 => {0, 3, 4}
  | 4 => {0, 3, 5}
  | 5 => {0, 4, 5}
  | 6 => {3, 4, 5}

/-- **Dimension-three impossibility for the wedge.**  No faithful facet separation of the nonpure
two-thick wedge `S¹ ∨ S²` exists in a complex vector space of dimension at most three: given
vectors `a` and forms `ℓ` realizing the exact facet zero pattern `ℓ i (a v) = 0 ↔ v ∉ wedgeFacet i`
in an `E` with `dim_ℂ E ≤ 3`, a contradiction follows.  Hence `ffsDim(Δ_wedge) ≥ 4`. -/
theorem wedge_no_faithfulSeparation_of_finrank_le_three
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E ≤ 3)
    (a : Fin 6 → E) (ℓ : Fin 7 → (E →ₗ[ℂ] ℂ))
    (hzero : ∀ (i : Fin 7) (v : Fin 6), ℓ i (a v) = 0 ↔ v ∉ wedgeFacet i) :
    False := by
  -- zero / nonzero incidence facts used
  have z10 : ℓ 1 (a 0) = 0 := (hzero 1 0).mpr (by decide)
  have z13 : ℓ 1 (a 3) = 0 := (hzero 1 3).mpr (by decide)
  have z14 : ℓ 1 (a 4) = 0 := (hzero 1 4).mpr (by decide)
  have z15 : ℓ 1 (a 5) = 0 := (hzero 1 5).mpr (by decide)
  have n11 : ℓ 1 (a 1) ≠ 0 := fun h => (hzero 1 1).mp h (by decide)
  have z03 : ℓ 0 (a 3) = 0 := (hzero 0 3).mpr (by decide)
  have z04 : ℓ 0 (a 4) = 0 := (hzero 0 4).mpr (by decide)
  have z05 : ℓ 0 (a 5) = 0 := (hzero 0 5).mpr (by decide)
  have n00 : ℓ 0 (a 0) ≠ 0 := fun h => (hzero 0 0).mp h (by decide)
  have z35 : ℓ 3 (a 5) = 0 := (hzero 3 5).mpr (by decide)
  have n33 : ℓ 3 (a 3) ≠ 0 := fun h => (hzero 3 3).mp h (by decide)
  have n65 : ℓ 6 (a 5) ≠ 0 := fun h => (hzero 6 5).mp h (by decide)
  have a5ne : a 5 ≠ 0 := fun h => n65 (by rw [h, map_zero])
  -- L = span{a₃,a₄,a₅}
  set L : Submodule ℂ E := Submodule.span ℂ ({a 3, a 4, a 5} : Set E) with hL
  have a3L : a 3 ∈ L := Submodule.subset_span (by simp)
  have a5L : a 5 ∈ L := Submodule.subset_span (by simp)
  -- ℓ 0 and ℓ 1 annihilate L
  have hL0 : ∀ x ∈ L, ℓ 0 x = 0 := by
    intro x hx
    have hsub : L ≤ LinearMap.ker (ℓ 0) := by
      rw [hL, Submodule.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h | h <;> subst h <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker] <;> assumption
    exact LinearMap.mem_ker.mp (hsub hx)
  -- dichotomy on dim L
  rcases Nat.lt_or_ge (Module.finrank ℂ L) 2 with hle | hgt
  · -- dim L ≤ 1
    have hsl : (ℂ ∙ a 5) ≤ L := (Submodule.span_singleton_le_iff_mem (a 5) L).mpr a5L
    have hrank1 : Module.finrank ℂ (ℂ ∙ a 5) = 1 := finrank_span_singleton a5ne
    have heq : (ℂ ∙ a 5) = L :=
      Submodule.eq_of_le_of_finrank_le hsl (by rw [hrank1]; omega)
    have a3span : a 3 ∈ (ℂ ∙ a 5) := by rw [heq]; exact a3L
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a3span
    have : ℓ 3 (a 3) = 0 := by rw [← hc, map_smul, z35, smul_zero]
    exact n33 this
  · -- dim L ≥ 2
    have a0L : a 0 ∈ L := by
      by_contra ha0
      set M : Submodule ℂ E :=
        Submodule.span ℂ (insert (a 0) ({a 3, a 4, a 5} : Set E)) with hM
      have hLM : L < M := by
        rw [hL, hM]
        refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert _ _)) ?_
        intro he
        apply ha0
        rw [hL, he]
        exact Submodule.subset_span (Set.mem_insert _ _)
      have hlt : Module.finrank ℂ L < Module.finrank ℂ M :=
        Submodule.finrank_lt_finrank_of_lt hLM
      have h1 : Module.finrank ℂ M ≤ Module.finrank ℂ E := Submodule.finrank_le M
      have hMtop : M = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        omega
      have hM1 : ℓ 1 (a 1) = 0 := by
        have hsub : M ≤ LinearMap.ker (ℓ 1) := by
          rw [hM, Submodule.span_le]
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with h | h | h | h <;> subst h <;>
            simp only [SetLike.mem_coe, LinearMap.mem_ker]
          · exact z10
          · exact z13
          · exact z14
          · exact z15
        exact LinearMap.mem_ker.mp (hsub (hMtop ▸ Submodule.mem_top))
      exact n11 hM1
    exact n00 (hL0 (a 0) a0L)

end GaloisForLFunctions
