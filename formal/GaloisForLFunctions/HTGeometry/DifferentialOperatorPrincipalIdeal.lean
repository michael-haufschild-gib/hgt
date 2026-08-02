import GaloisForLFunctions.HTGeometry.DifferentialOperatorCyclicDimension
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# The operator ring is a left principal ideal domain

Division with remainder makes every left ideal of `K[∂;δ]` principal: an element of least order in
a nonzero left ideal generates it, since the remainder of any other element has smaller order and
still lies in the ideal.

Consequently the operator ring is left Noetherian, and so is every finite power of it, so lattices
inside `K[∂;δ]^r` are finitely generated.  This is what turns a lattice commensurability statement
into a finite-dimensionality statement.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- **Left ideals are principal.**  An element of least order generates. -/
theorem exists_generator (I : Submodule (DiffOp K) (DiffOp K)) :
    ∃ b : DiffOp K, I = Submodule.span (DiffOp K) {b} := by
  classical
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · obtain ⟨x₀, hx₀I, hx₀⟩ := hI
    have hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ degree x = n := ⟨degree x₀, x₀, hx₀I, hx₀, rfl⟩
    obtain ⟨b, hbI, hb0, hbdeg⟩ := Nat.find_spec hex
    refine ⟨b, le_antisymm (fun a haI => ?_) ?_⟩
    · obtain ⟨q, r, hqr, hr⟩ := exists_right_div hb0 a
      have hrI : r ∈ I := by
        have hqb : q * b ∈ I := I.smul_mem q hbI
        have : r = a - q * b := by
          rw [hqr]
          abel
        rw [this]
        exact I.sub_mem haI hqb
      have hr0 : r = 0 := by
        rcases hr with hzero | hlt
        · exact hzero
        · by_contra hrne
          refine Nat.find_min hex (m := degree r) ?_ ⟨r, hrI, hrne, rfl⟩
          rw [← hbdeg]
          exact hlt
      refine Submodule.mem_span_singleton.mpr ⟨q, ?_⟩
      rw [hqr, hr0, add_zero]
      rfl
    · exact (Submodule.span_le).mpr (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hbI)
  · refine ⟨0, le_antisymm (fun x hx => ?_) ?_⟩
    · have hx0 : x = 0 := by
        by_contra hne
        exact hI ⟨x, hx, hne⟩
      rw [hx0]
      exact Submodule.zero_mem _
    · rw [Submodule.span_zero_singleton]
      exact bot_le

instance isNoetherian_self : IsNoetherian (DiffOp K) (DiffOp K) := by
  refine isNoetherian_def.mpr fun I => ?_
  obtain ⟨b, rfl⟩ := exists_generator I
  exact ⟨{b}, by simp⟩

instance isNoetherian_pi_self {ι : Type*} [Finite ι] :
    IsNoetherian (DiffOp K) (ι → DiffOp K) := isNoetherian_pi

/-- Lattices inside a finite power of the operator ring are finitely generated. -/
theorem fg_submodule {ι : Type*} [Finite ι] (N : Submodule (DiffOp K) (ι → DiffOp K)) :
    N.FG := IsNoetherian.noetherian N

end

end DiffOp

end GaloisForLFunctions.HTGeometry
