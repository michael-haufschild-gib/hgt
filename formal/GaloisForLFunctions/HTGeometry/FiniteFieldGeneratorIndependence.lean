import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Recovering independence from a generated field

A finite family is algebraically independent when its generated field contains an independent
family of the same cardinality.  This packages the transcendence-degree argument used to recover
raw jet independence from independent raw/reciprocal observations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

/-- A finite field-generating family is independent if its generated field contains an independent
family with the same cardinality. -/
theorem algebraicIndependent_of_independent_family_mem_adjoin
    {K : Type u} {E : Type v} {I J : Type w} [Field K] [Field E] [Algebra K E]
    [Finite I] [Finite J]
    (a : I → E) (y : J → E)
    (hy : AlgebraicIndependent K y)
    (hmem : ∀ j, y j ∈ IntermediateField.adjoin K (Set.range a))
    (hcard : Cardinal.mk I = Cardinal.mk J) :
    AlgebraicIndependent K a := by
  let A := IntermediateField.adjoin K (Set.range a)
  let aA : I → A := fun i ↦
    ⟨a i, IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  let yA : J → A := fun j ↦ ⟨y j, hmem j⟩
  have hyA : AlgebraicIndependent K yA := by
    apply AlgebraicIndependent.of_comp A.val
    simpa [A, yA, Function.comp_def] using hy
  have htop : IntermediateField.adjoin K (Set.range aA) = ⊤ := by
    simpa [A, aA] using adjoin_range_lift_eq_top a a rfl
  letI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range aA)) A :=
    isAlgebraic_adjoin_of_intermediate_adjoin_eq_top aA htop
  have hle : Cardinal.lift.{v} (Cardinal.mk I) ≤
      Cardinal.lift.{w} (Algebra.trdeg K A) := by
    rw [hcard]
    exact hyA.lift_cardinalMk_le_trdeg
  have haA : AlgebraicIndependent K aA :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K aA hle).1
  have hmap := haA.map' A.val.injective
  simpa [A, aA, Function.comp_def] using hmap

end

end GaloisForLFunctions.HTGeometry
