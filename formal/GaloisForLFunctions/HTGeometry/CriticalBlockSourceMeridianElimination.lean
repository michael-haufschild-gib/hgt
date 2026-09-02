import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationEtaleCover
import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationPathConnected
import GaloisForLFunctions.HTGeometry.CriticalObservationConnectedCover
import GaloisForLFunctions.HTGeometry.CriticalSourceBlockComplexPoints
import GaloisForLFunctions.HTGeometry.CoveringClosedLiftMonodromy

/-!
# Eliminate a critical block cover from its two source meridians

Once formal purity makes a critical block normalization a covering, two closed source loops whose
observation classes are the marked torus meridians force its fibre to be a singleton.  This module
assembles that endgame without retaining any finite-group or cyclic-character premise.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Path

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet ℂ m n)}
variable [Algebra.FormallyEtale (criticalObservationChartRing ℂ m n)
  (CriticalBlockNormalization ℂ B)]

/-- Analytic torus-affine projection of a critical block normalization. -/
def criticalBlockAnalyticProjection :
    AlgSpec (CriticalBlockNormalization ℂ B) →
      ComplexTorusAffineChart (n + m - 2) :=
  criticalObservationAnalyticProjection m n
    (criticalBlockNormalizationProjection B)

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- Formal purity makes the analytic block projection a covering. -/
theorem criticalBlockAnalyticProjection_isCoveringMap :
    IsCoveringMap (criticalBlockAnalyticProjection (m := m) (n := n) (B := B)) :=
  criticalObservationAnalyticProjection_isCoveringMap m n
    (isCoveringMap_criticalBlockNormalizationProjection_of_formallyEtale
      (m := m) (n := n) (B := B))

/-- **Two source meridians eliminate a block cover.**  If closed loops in the actual source chart
project to the two coordinate generators of the torus-affine observation chart, then the formally
étale connected block cover has a singleton fibre. -/
theorem criticalBlockCover_fiber_subsingleton_of_source_meridians
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B)
    (x : AlgSpec (criticalSourceChartRing ℂ m n))
    (hx : criticalSourceBlockAnalyticProjectionContinuousMap hB hmem x = 1)
    (deltaFirst deltaSecond : Path.Homotopic.Quotient x x)
    (hfirst :
      (deltaFirst.map (criticalSourceBlockAnalyticProjectionContinuousMap hB hmem)).cast
        hx.symm hx.symm = torusChartFirstFundamentalGenerator (n + m - 2))
    (hsecond :
      (deltaSecond.map (criticalSourceBlockAnalyticProjectionContinuousMap hB hmem)).cast
        hx.symm hx.symm = torusChartSecondFundamentalGenerator (n + m - 2)) :
    Subsingleton
      ((criticalBlockAnalyticProjection (m := m) (n := n) (B := B)) ⁻¹'
        {(1 : ComplexTorusAffineChart (n + m - 2))}) := by
  let p := criticalBlockAnalyticProjection (m := m) (n := n) (B := B)
  have cov : IsCoveringMap p := criticalBlockAnalyticProjection_isCoveringMap
  let f := criticalSourceToBlockNormalization hB hmem
  have hf : Continuous f := continuous_criticalSourceToBlockNormalization hB hmem
  let q := criticalSourceBlockAnalyticProjectionContinuousMap hB hmem
  change q x = (1 : ComplexTorusAffineChart (n + m - 2)) at hx
  change (deltaFirst.map q).cast hx.symm hx.symm =
    torusChartFirstFundamentalGenerator (n + m - 2) at hfirst
  change (deltaSecond.map q).cast hx.symm hx.symm =
    torusChartSecondFundamentalGenerator (n + m - 2) at hsecond
  have hq : q = (⟨p, cov.continuous⟩ :
      C(AlgSpec (CriticalBlockNormalization ℂ B),
        ComplexTorusAffineChart (n + m - 2))).comp ⟨f, hf⟩ := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hxf : p (f x) = (1 : ComplexTorusAffineChart (n + m - 2)) := by
    change (((⟨p, cov.continuous⟩ :
      C(AlgSpec (CriticalBlockNormalization ℂ B),
        ComplexTorusAffineChart (n + m - 2))).comp ⟨f, hf⟩) x) = 1
    rw [← hq]
    exact hx
  let e : p ⁻¹' {(1 : ComplexTorusAffineChart (n + m - 2))} :=
    ⟨f x, by simpa using hxf⟩
  have hfixFirst := covering_monodromy_fixed_of_closed_lift_of_eq p cov f hf q hq x hx
    deltaFirst
  have hfixSecond := covering_monodromy_fixed_of_closed_lift_of_eq p cov f hf q hq x hx
    deltaSecond
  have hfixFirst' : cov.monodromy (torusChartFirstFundamentalGenerator (n + m - 2)) e = e := by
    rw [← hfirst]
    exact hfixFirst
  have hfixSecond' : cov.monodromy (torusChartSecondFundamentalGenerator (n + m - 2)) e = e := by
    rw [← hsecond]
    exact hfixSecond
  letI : PathConnectedSpace (AlgSpec (CriticalBlockNormalization ℂ B)) :=
    pathConnectedSpace_algSpec_criticalBlockNormalization hB hmem
  exact subsingleton_torusChartCover_fiber_of_generators_fixed p cov e hfixFirst' hfixSecond'

end

end GaloisForLFunctions.HTGeometry
