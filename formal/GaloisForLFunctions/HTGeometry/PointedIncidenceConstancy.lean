import GaloisForLFunctions.HTGeometry.DiscretePeriodGaugeClassification
import GaloisForLFunctions.HTGeometry.RankThreePeriods
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary

/-!
# Joint-fixed elements of a rank-three period source are constant

The exact gauge classification says a nonconstant global meromorphic element fixed by an integral
period source exists exactly when that source is discrete.  Three rationally independent periods
never span a discrete group, so in that case every fixed element is a constant.

This is the constancy step of the pointed incidence phase: two ambient primitives of the same
two-shift boundary differ by a jointly fixed element, hence by a constant, which the source pointing
then removes.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- **A meromorphic element fixed by a non-discrete period source is constant.** -/
theorem exists_const_of_fixed_of_not_discrete {L : Submodule ℤ ℂ} (hL : ¬ DiscreteTopology L)
    {z : meroField (Set.univ : Set ℂ)}
    (hfix : ∀ q ∈ L, addTranslationMeroEquiv q z = z) :
    ∃ c : ℂ, algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ c) = z := by
  by_contra hnc
  exact hL ((exists_nonconstant_fixed_iff_discretePeriodSource L).mp ⟨z, hfix, hnc⟩)

/-- Fixed periods of a meromorphic element form an integral submodule. -/
theorem fixed_span_of_fixed_generators {v : Fin 3 → ℂ} {z : meroField (Set.univ : Set ℂ)}
    (hgen : ∀ i, addTranslationMeroEquiv (v i) z = z) :
    ∀ q ∈ Submodule.span ℤ (Set.range v), addTranslationMeroEquiv q z = z := by
  intro q hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro x ⟨i, rfl⟩
    exact hgen i
  · exact addTranslationMeroEquiv_zero_apply z
  · intro a b _ _ ha hb
    rw [← addTranslationMeroEquiv_add, hb, ha]
  · intro n a _ ha
    induction n using Int.induction_on with
    | zero => simpa using addTranslationMeroEquiv_zero_apply z
    | succ k ih =>
        have hstep : ((k : ℤ) + 1) • a = a + (k : ℤ) • a := by
          rw [add_smul, one_smul]
          ring
        rw [hstep, ← addTranslationMeroEquiv_add, ih, ha]
    | pred k ih =>
        have hstep : (-(k : ℤ) - 1) • a = -a + (-(k : ℤ)) • a := by
          rw [sub_smul, neg_smul, one_smul]
          ring
        have hneg : addTranslationMeroEquiv (-a) z = z := by
          have hsum := addTranslationMeroEquiv_add (-a) a z
          rw [ha, neg_add_cancel] at hsum
          rw [hsum]
          exact addTranslationMeroEquiv_zero_apply z
        rw [hstep, ← addTranslationMeroEquiv_add, ih, hneg]

/-- **The joint-fixed field of a rationally independent period triple is constant.** -/
theorem exists_const_of_fixed_rankThree {v : Fin 3 → ℂ} (hv : LinearIndependent ℚ v)
    {z : meroField (Set.univ : Set ℂ)} (hgen : ∀ i, addTranslationMeroEquiv (v i) z = z) :
    ∃ c : ℂ, algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ c) = z :=
  exists_const_of_fixed_of_not_discrete (not_discrete_intSpan_fin_three v hv)
    (fixed_span_of_fixed_generators hgen)

/-- **The pointed constancy step.**  Two elements fixed by the same rationally independent period
triple that agree after a constant-separating evaluation are equal. -/
theorem eq_of_fixed_rankThree_of_sub_const {v : Fin 3 → ℂ} (hv : LinearIndependent ℚ v)
    {x y : meroField (Set.univ : Set ℂ)}
    (hgen : ∀ i, addTranslationMeroEquiv (v i) (x - y) = x - y)
    (hconst : ∀ c : ℂ, algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ c) = x - y → c = 0) : x = y := by
  obtain ⟨c, hc⟩ := exists_const_of_fixed_rankThree hv hgen
  have hc0 : c = 0 := hconst c hc
  rw [hc0] at hc
  have hzero : (0 : meroField (Set.univ : Set ℂ)) = x - y := by
    rw [← hc, map_zero, map_zero]
  exact sub_eq_zero.mp hzero.symm

end

end GaloisForLFunctions.HTGeometry
