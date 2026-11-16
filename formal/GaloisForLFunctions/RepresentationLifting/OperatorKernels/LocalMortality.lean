import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Local annihilation and a common zero operator

In a finitely generated module, a multiplicative family of endomorphisms
contains zero exactly when it can kill each vector separately. Successively
killing the images of finitely many generators preserves earlier zeros.
This is the linear form of the pairwise-merging argument for reset words.
-/

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Pointwise annihilation can be synchronized on any finite set of vectors. -/
theorem exists_annihilator_finset (S : Submonoid (Module.End R M))
    (h : ∀ x : M, ∃ T ∈ S, T x = 0) (s : Finset M) :
    ∃ T ∈ S, ∀ x ∈ s, T x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨B, hB, hs⟩ := ih
      obtain ⟨A, hA, ha⟩ := h (B a)
      refine ⟨A * B, S.mul_mem hA hB, ?_⟩
      intro x hx
      rw [Module.End.mul_apply]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [hs x hx, map_zero]

/-- Finite generation turns local mortality into one globally annihilating product. -/
theorem zero_mem_submonoid_iff_pointwise_killable [Module.Finite R M]
    (S : Submonoid (Module.End R M)) :
    (0 : Module.End R M) ∈ S ↔ ∀ x : M, ∃ T ∈ S, T x = 0 := by
  constructor
  · intro h x
    exact ⟨0, h, rfl⟩
  · intro h
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
    obtain ⟨T, hT, hkill⟩ := exists_annihilator_finset S h s
    have hzero : T = 0 := LinearMap.ext_on hs (fun x hx => hkill x hx)
    rwa [hzero] at hT

/-- Pairwise merging and zero synchronization coincide for finite linear systems. -/
theorem zero_mem_submonoid_iff_pairwise_mergeable [Module.Finite R M]
    (S : Submonoid (Module.End R M)) :
    (0 : Module.End R M) ∈ S ↔ ∀ x y : M, ∃ T ∈ S, T x = T y := by
  rw [zero_mem_submonoid_iff_pointwise_killable]
  constructor
  · intro h x y
    obtain ⟨T, hT, hxy⟩ := h (x - y)
    exact ⟨T, hT, sub_eq_zero.mp (by rwa [map_sub] at hxy)⟩
  · intro h x
    obtain ⟨T, hT, hx⟩ := h x 0
    exact ⟨T, hT, by rwa [map_zero] at hx⟩

/-- If zero is absent, one vector survives every allowed product. -/
theorem exists_common_survivor_iff [Module.Finite R M]
    (S : Submonoid (Module.End R M)) :
    (∃ x : M, ∀ T ∈ S, T x ≠ 0) ↔ (0 : Module.End R M) ∉ S := by
  classical
  rw [zero_mem_submonoid_iff_pointwise_killable]
  push Not
  rfl

#print axioms exists_annihilator_finset
#print axioms zero_mem_submonoid_iff_pointwise_killable
#print axioms zero_mem_submonoid_iff_pairwise_mergeable
#print axioms exists_common_survivor_iff

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
