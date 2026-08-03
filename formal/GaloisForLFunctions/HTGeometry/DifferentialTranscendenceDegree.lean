import GaloisForLFunctions.HTGeometry.DifferentialMatroid
import GaloisForLFunctions.HTGeometry.TranslateFamilyIndependence
import Mathlib.Combinatorics.Matroid.Rank.Cardinal

/-!
# Differential transcendence degree

This module defines differential transcendence degree without a finiteness restriction, as the
cardinal rank of the characteristic-zero differential matroid.  It also proves the exact basis
formula used by differential-horizon dimension calculations.
-/

open scoped Classical Differential

namespace GaloisForLFunctions

open Set

noncomputable section

universe u

/-- Differential transcendence degree, as the cardinal rank of the differential matroid. -/
noncomputable def differentialTranscendenceDegree
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] : Cardinal :=
  (differentialMatroid F E).cRank

/-- A differentially independent family generating the extension as a differential field is a
differential transcendence basis, so its index cardinal is the differential transcendence degree. -/
theorem differentialTranscendenceDegree_eq_cardinalMk_of_differentialIndependent_of_adjoin_eq_top
    {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤) :
    differentialTranscendenceDegree F E = Cardinal.mk ι := by
  let M := differentialMatroid F E
  have hind : M.Indep (Set.range x) := by
    rw [differentialMatroid_indep_iff]
    exact diffIndepOn_range_of_differentialIndependent hx
  have hclosure : M.closure (Set.range x) = M.E := by
    rw [differentialMatroid_ground]
    apply Set.eq_univ_of_forall
    intro y
    rw [differentialMatroid_mem_closure_iff_of_indep
      (diffIndepOn_range_of_differentialIndependent hx)]
    change DifferentialAlgebraicOver (differentialAdjoin F (Set.range x)) y
    let B := differentialAdjoin F (Set.range x)
    have hy : y ∈ B := by
      change y ∈ differentialAdjoin F (Set.range x)
      rw [hgen]
      exact Set.mem_univ y
    let yB : B := ⟨y, hy⟩
    unfold DifferentialAlgebraicOver
    intro hdiff
    have htrans : Transcendental B y :=
      hdiff.algebraicIndependent.transcendental Unit.unit
    apply htrans
    simpa [yB] using (isAlgebraic_algebraMap (R := B) (A := E) yB)
  have hbase : M.IsBase (Set.range x) :=
    M.isBase_iff_indep_closure_eq.mpr ⟨hind, hclosure⟩
  change M.cRank = Cardinal.mk ι
  exact hbase.cardinalMk_eq_cRank.symm.trans
    (Cardinal.mk_range_eq x hx.injective)

end

end GaloisForLFunctions
