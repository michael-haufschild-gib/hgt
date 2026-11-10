import GaloisForLFunctions.RHTower.LindelofCosineFiniteDefectDepth
import GaloisForLFunctions.RHTower.XiCosineShiftDefectLimit
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment

/-!
# The cosine finite-stratum law closes the tail condition

Zeros approaching the line give finite nonreal defects at every positive
cosine level. Excluding finite nonempty defects then makes all those
levels real, and their limit forces RH. Unlike the heat family, finiteness
of cosine defects is supplied here by the explicit tail condition.
-/

open Complex Filter Topology RHTower
open RHTower.BacklundConverse RHTower.CosineDefectBudget

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws

/-- Under a finite-stratum law on cosine levels, RH is exactly ZAL. -/
theorem riemannHypothesis_iff_zerosApproachLine_of_cosine_finite_stratum_law
    (hlaw : ∀ h : ℝ, 0 < h →
      {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite →
      ∀ z : ℂ, cosShiftXi h z = 0 → z.im = 0) :
    RiemannHypothesis ↔ ZerosApproachLine := by
  refine ⟨zerosApproachLine_of_riemannHypothesis, fun hZ => ?_⟩
  apply CosineDefectLimit.riemannHypothesis_iff_eventually_cosShiftXi_real.mpr
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact hlaw h hh (cosShiftXi_finite_nonreal_of_zerosApproachLine hZ hh)

#print axioms riemannHypothesis_iff_zerosApproachLine_of_cosine_finite_stratum_law

end GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws
