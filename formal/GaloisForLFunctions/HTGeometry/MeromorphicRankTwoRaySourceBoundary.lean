import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel

/-!
# Two ray periods already cut the meromorphic field down to the constants

Three translation generators are needed when the periods may span a discrete subgroup of `ℂ`.  Two
periods lying on one ray with irrational radius ratio generate a dense subgroup of that line, so a
meromorphic function fixed by both is constant.  This is the rank-two source boundary the
multiple-sine face-lifting argument runs on.
-/

open Filter Set
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] HTGeometry.twoCylDomain HTGeometry.twoCylComplexAlgebraAnalytic
  HTGeometry.twoCylComplexAlgebra HTGeometry.twoCylDifferential

/-- The two source generators acting on the global meromorphic differential field. -/
def rankTwoGeneratorMeromorphicDifferenceDifferentialField (v : Fin 2 → ℂ) :
    CommutingDifferenceDifferentialField (Fin 2) ℂ (meroField Set.univ) where
  aut i := addTranslationMeroEquiv (v i)
  aut_comm i j x := by
    simpa only [addTranslationMeroEquiv_add] using
      congrArg (fun r : ℂ ↦ addTranslationMeroEquiv r x) (add_comm (v i) (v j))
  aut_deriv i x := addTranslationMeroEquiv_deriv (v i) x
  aut_algebraMap i c := by
    change addTranslationMeroEquiv (v i)
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ c)) = _
    exact addTranslationMeroEquiv_const (v i) c

/-- **The common fixed field of two ray generators is exactly the complex constants.** -/
theorem rankTwoRay_generator_jointFixed_iff_constant {c : ℂ} (hc : c ≠ 0) {a b : ℝ}
    (hirr : Irrational (a / b)) (z : meroField (Set.univ : Set ℂ)) :
    JointFixed (rankTwoGeneratorMeromorphicDifferenceDifferentialField
        ![c * (a : ℂ), c * (b : ℂ)]) z ↔
      ∃ w : ℂ, meromorphicConstantEmbedding w = z := by
  constructor
  · intro hfixed
    have h1 : addTranslationMeroEquiv (c * (a : ℂ)) z = z := hfixed 0
    have h2 : addTranslationMeroEquiv (c * (b : ℂ)) z = z := hfixed 1
    obtain ⟨w, hw⟩ := HTGeometry.exists_constant_of_two_rayPeriods_fixed hc hirr h1 h2
    exact ⟨w, by simpa [meromorphicConstantEmbedding] using hw⟩
  · rintro ⟨w, rfl⟩ i
    exact (rankTwoGeneratorMeromorphicDifferenceDifferentialField
      ![c * (a : ℂ), c * (b : ℂ)]).aut_algebraMap i w

end

end GaloisForLFunctions
