import GaloisForLFunctions.HTGeometry.S3ProductSign

/-!
# From individual sign flips to independent cubic permutation actions

Single-coordinate sign flips generate every sign pattern. Coordinate
surjectivity then gives the full product of three-letter permutation groups.
-/

namespace GaloisForLFunctions.HTGeometry
open Equiv.Perm

/-- Independent single-coordinate sign flips suffice for surjectivity onto a product of S3. -/
theorem s3_hom_surjective_of_coordinate_and_flips {ι G : Type*} [Finite ι] [Group G]
    (A : G →* (ι → Equiv.Perm (Fin 3)))
    (hcoord : ∀ i, Function.Surjective (fun σ : G => A σ i))
    (hflip : ∀ i, ∃ σ : G, sign (A σ i) = -1 ∧ ∀ j, j ≠ i → sign (A σ j) = 1) :
    Function.Surjective A := by
  classical
  let B : G →* (ι → ℤˣ) :=
    { toFun := fun σ i => sign (A σ i)
      map_one' := by funext i; simp
      map_mul' := by intro σ τ; funext i; simp }
  have hB : Function.Surjective B := by
    intro ε
    have hm : ε ∈ B.range := by
      apply Subgroup.pi_mem_of_mulSingle_mem
      intro i
      rcases Int.units_eq_one_or (ε i) with hi | hi
      · rw [hi, Pi.mulSingle_one]
        exact B.range.one_mem
      · obtain ⟨σ, hσi, hσj⟩ := hflip i
        refine ⟨σ, ?_⟩
        funext j
        by_cases hji : j = i
        · subst j
          simpa only [B, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_same, hi] using hσi
        · simpa only [B, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_of_ne hji] using hσj j hji
    exact hm
  apply MonoidHom.range_eq_top.mp
  apply s3_subgroup_eq_top_of_sign_surjective
  · intro i p
    obtain ⟨σ, hσ⟩ := hcoord i p
    exact ⟨⟨A σ, ⟨σ, rfl⟩⟩, hσ⟩
  · intro ε
    obtain ⟨σ, hσ⟩ := hB ε
    exact ⟨⟨A σ, ⟨σ, rfl⟩⟩, hσ⟩

end GaloisForLFunctions.HTGeometry
