import GaloisForLFunctions.HTGeometry.QuotientCharacterAnnihilator
import GaloisForLFunctions.HTGeometry.RankThreePeriodNonHausdorff

/-!
# The holographic visibility gap

For a nonclosed subgroup, continuity erases more information than algebra does.  Every continuous
additive observable that vanishes on the subgroup also vanishes on its closure, while an abstract
rational-circle character detects every point outside the subgroup itself.  Thus points in the
closure boundary are topologically invisible but algebraically visible.

The rank-three specialization is the exact topological/algebraic mismatch used by the proposed
elliptic-gamma holographic horizon.  The mismatch is formal infrastructure; scientific novelty in
that application comes from identifying the differential-Galois automorphisms with the algebraic
characters, not from this general topological fact alone.
-/

namespace GaloisForLFunctions

open scoped Topology

noncomputable section

/-- A continuous additive observable that vanishes on a subgroup vanishes on its closure. -/
theorem continuous_addMonoidHom_eq_zero_of_mem_closure
    {A B : Type*} [AddCommGroup A] [TopologicalSpace A]
    [AddCommGroup B] [TopologicalSpace B] [T1Space B]
    (H : AddSubgroup A) (f : A →+ B) (hf : Continuous f)
    (hzero : ∀ h : A, h ∈ H → f h = 0) {a : A}
    (ha : a ∈ closure (H : Set A)) :
    f a = 0 := by
  have hclosed : IsClosed (f ⁻¹' ({0} : Set B)) := isClosed_singleton.preimage hf
  have hsub : (H : Set A) ⊆ f ⁻¹' ({0} : Set B) := by
    intro h hh
    exact Set.mem_singleton_iff.mpr (hzero h hh)
  exact Set.mem_singleton_iff.mp (closure_minimal hsub hclosed ha)

/-- Every nonclosed subgroup has a point that no continuous additive observable can distinguish
from the subgroup, but an abstract rational-circle character of the quotient does distinguish. -/
theorem exists_topologicallyInvisible_algebraicallyVisible
    {A B : Type*} [AddCommGroup A] [TopologicalSpace A]
    [AddCommGroup B] [TopologicalSpace B] [T1Space B]
    (H : AddSubgroup A) (hH : ¬ IsClosed (H : Set A)) :
    ∃ a : A, a ∉ H ∧
      (∀ f : A →+ B, Continuous f →
        (∀ h : A, h ∈ H → f h = 0) → f a = 0) ∧
      ∃ c : CharacterModule (A ⧸ H),
        c (QuotientAddGroup.mk a) ≠ 0 := by
  have hnotSubset : ¬ closure (H : Set A) ⊆ (H : Set A) := by
    intro hsubset
    apply hH
    have heq : closure (H : Set A) = (H : Set A) :=
      Set.Subset.antisymm hsubset subset_closure
    rw [← heq]
    exact isClosed_closure
  obtain ⟨a, haclosure, haH⟩ := Set.not_subset.mp hnotSubset
  refine ⟨a, haH, ?_, exists_quotientCharacter_ne_zero_of_not_mem H haH⟩
  intro f hf hzero
  exact continuous_addMonoidHom_eq_zero_of_mem_closure H f hf hzero haclosure

/-- Three rationally independent complex periods produce an explicit visibility gap: some shift
is invisible to every continuous real additive observable annihilating the period subgroup, yet is
detected by an algebraic character of the triptic quotient. -/
theorem rankThreePeriod_exists_topologicallyInvisible_algebraicallyVisible
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ∃ a : ℂ, a ∉ Submodule.span ℤ (Set.range v) ∧
      (∀ f : ℂ →+ ℝ, Continuous f →
        (∀ h : ℂ, h ∈ Submodule.span ℤ (Set.range v) → f h = 0) → f a = 0) ∧
      ∃ c : CharacterModule (ℂ ⧸ Submodule.span ℤ (Set.range v)),
        c (QuotientAddGroup.mk a) ≠ 0 := by
  exact exists_topologicallyInvisible_algebraicallyVisible
    (B := ℝ) (Submodule.span ℤ (Set.range v)).toAddSubgroup
      (not_isClosed_intSpan_fin_three v hv)

end

end GaloisForLFunctions
