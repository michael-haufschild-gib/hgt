import GaloisForLFunctions.HTGeometry.LinearFamilyGreatestMaximizer
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The simultaneous kernel of a self-adjoint family

For a family of self-adjoint operators the orthogonal complement of the simultaneous kernel is the
span of the ranges.  Both are therefore preserved by every invertible map conjugating the family
span into itself, and the orthogonal projection onto the simultaneous kernel commutes with such a
map.  This is what lets the kernel projector be adjoined to the family without destroying its
symmetries.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {X J : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]

/-- The simultaneous kernel of an operator family. -/
def familyCommonKernel (A : J → X →ₗ[ℂ] X) : Submodule ℂ X := ⨅ j, LinearMap.ker (A j)

theorem mem_familyCommonKernel {A : J → X →ₗ[ℂ] X} {x : X} :
    x ∈ familyCommonKernel A ↔ ∀ j, A j x = 0 := by
  rw [familyCommonKernel, Submodule.mem_iInf]
  exact forall_congr' fun _ => LinearMap.mem_ker

theorem linearFamilyShadow_eq_bot_of_mem_commonKernel (A : J → X →ₗ[ℂ] X) {x : X}
    (hx : x ∈ familyCommonKernel A) :
    linearFamilyShadow A (Submodule.span ℂ {x}) = ⊥ := by
  rw [linearFamilyShadow, eq_bot_iff]
  refine iSup_le fun j => ?_
  rw [Submodule.map_span, Set.image_singleton, mem_familyCommonKernel.mp hx j]
  simp

/-- **The orthogonal complement of the simultaneous kernel is the span of the ranges.** -/
theorem familyCommonKernel_orthogonal_eq (A : J → X →ₗ[ℂ] X)
    (hsa : ∀ j, LinearMap.adjoint (A j) = A j) :
    (familyCommonKernel A)ᗮ = ⨆ j, LinearMap.range (A j) := by
  have hle : (⨆ j, LinearMap.range (A j)) ≤ (familyCommonKernel A)ᗮ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro n hn
    have hnj : A j n = 0 := mem_familyCommonKernel.mp hn j
    have hmove : (inner ℂ n (A j z) : ℂ) = inner ℂ (A j n) z := by
      rw [← hsa j, LinearMap.adjoint_inner_right, hsa j]
    rw [hmove, hnj, inner_zero_left]
  have hkey : (⨆ j, LinearMap.range (A j))ᗮ ≤ familyCommonKernel A := by
    intro x hx
    rw [mem_familyCommonKernel]
    intro j
    have hzero : (inner ℂ (A j (A j x)) x : ℂ) = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx _ (le_iSup (fun k => LinearMap.range (A k)) j
        ⟨A j x, rfl⟩)
    have hmove : (inner ℂ (A j (A j x)) x : ℂ) = inner ℂ (A j x) (A j x) := by
      conv_lhs => rw [← hsa j]
      rw [LinearMap.adjoint_inner_left, hsa j]
    rw [hmove] at hzero
    exact inner_self_eq_zero.mp hzero
  refine le_antisymm ?_ hle
  calc (familyCommonKernel A)ᗮ ≤ ((⨆ j, LinearMap.range (A j))ᗮ)ᗮ :=
        Submodule.orthogonal_le hkey
    _ = ⨆ j, LinearMap.range (A j) := Submodule.orthogonal_orthogonal _

/-- A span-covariant automorphism preserves the simultaneous kernel. -/
theorem map_familyCommonKernel_le (A : J → X →ₗ[ℂ] X) (e : X ≃ₗ[ℂ] X)
    (hback : ∀ j, (((e.symm : X →ₗ[ℂ] X).comp (A j)).comp (e : X →ₗ[ℂ] X)) ∈
      linearFamilyOperatorSpan A) :
    (familyCommonKernel A).map (e : X →ₗ[ℂ] X) ≤ familyCommonKernel A := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_familyCommonKernel]
  intro j
  have hmem : (((e.symm : X →ₗ[ℂ] X).comp (A j)).comp (e : X →ₗ[ℂ] X)) x ∈
      linearFamilyShadow A (Submodule.span ℂ {x}) :=
    linearFamilyOperatorSpan_apply_mem_shadow A _ (hback j)
      (Submodule.mem_span_singleton_self x)
  rw [linearFamilyShadow_eq_bot_of_mem_commonKernel A hx, Submodule.mem_bot] at hmem
  have hval : e.symm (A j (e x)) = 0 := hmem
  have := congrArg (e : X →ₗ[ℂ] X) hval
  simpa using this

/-- A span-covariant automorphism preserves the orthogonal complement of the simultaneous
kernel. -/
theorem map_familyCommonKernel_orthogonal_le (A : J → X →ₗ[ℂ] X)
    (hsa : ∀ j, LinearMap.adjoint (A j) = A j) (e : X ≃ₗ[ℂ] X)
    (hforward : ∀ j, (((e : X →ₗ[ℂ] X).comp (A j)).comp (e.symm : X →ₗ[ℂ] X)) ∈
      linearFamilyOperatorSpan A) :
    (familyCommonKernel A)ᗮ.map (e : X →ₗ[ℂ] X) ≤ (familyCommonKernel A)ᗮ := by
  rw [familyCommonKernel_orthogonal_eq A hsa, Submodule.map_iSup]
  refine iSup_le fun j => ?_
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  have hmem : (((e : X →ₗ[ℂ] X).comp (A j)).comp (e.symm : X →ₗ[ℂ] X)) (e z) ∈
      linearFamilyShadow A (Submodule.span ℂ {e z}) :=
    linearFamilyOperatorSpan_apply_mem_shadow A _ (hforward j)
      (Submodule.mem_span_singleton_self _)
  have hval : (((e : X →ₗ[ℂ] X).comp (A j)).comp (e.symm : X →ₗ[ℂ] X)) (e z) = e (A j z) := by
    simp
  rw [hval] at hmem
  have hsub : linearFamilyShadow A (Submodule.span ℂ {e z}) ≤ ⨆ k, LinearMap.range (A k) := by
    refine iSup_le fun k => ?_
    rintro _ ⟨y, -, rfl⟩
    exact le_iSup (fun m => LinearMap.range (A m)) k ⟨y, rfl⟩
  exact hsub hmem

/-- A map preserving a subspace and its orthogonal complement commutes with the orthogonal
projection onto it. -/
theorem starProjection_map_comm (K : Submodule ℂ X) (e : X ≃ₗ[ℂ] X)
    (h1 : K.map (e : X →ₗ[ℂ] X) ≤ K) (h2 : Kᗮ.map (e : X →ₗ[ℂ] X) ≤ Kᗮ) (x : X) :
    K.starProjection (e x) = e (K.starProjection x) := by
  have hsplit : e x = e (K.starProjection x) + e (x - K.starProjection x) := by
    rw [← map_add]
    congr 1
    abel
  have hmem1 : e (K.starProjection x) ∈ K :=
    h1 ⟨K.starProjection x, K.starProjection_apply_mem x, rfl⟩
  have hmem2 : e (x - K.starProjection x) ∈ Kᗮ :=
    h2 ⟨x - K.starProjection x, Submodule.sub_starProjection_mem_orthogonal x, rfl⟩
  rw [hsplit, map_add, Submodule.starProjection_eq_self_iff.mpr hmem1,
    (Submodule.starProjection_apply_eq_zero_iff K).mpr hmem2, add_zero]

/-- Every image of a self-adjoint family member is orthogonal to the simultaneous kernel. -/
theorem apply_mem_orthogonal_commonKernel (A : J → X →ₗ[ℂ] X)
    (hsa : ∀ j, LinearMap.adjoint (A j) = A j) (k : J) (w : X) :
    A k w ∈ (familyCommonKernel A)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro n hn
  have h1 : A k n = 0 := mem_familyCommonKernel.mp hn k
  have hmove : (inner ℂ n (A k w) : ℂ) = inner ℂ (A k n) w := by
    rw [← hsa k, LinearMap.adjoint_inner_right, hsa k]
  rw [hmove, h1, inner_zero_left]

end GaloisForLFunctions.HTGeometry
