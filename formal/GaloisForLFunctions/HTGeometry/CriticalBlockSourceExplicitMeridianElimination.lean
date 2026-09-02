import GaloisForLFunctions.HTGeometry.CriticalBlockSourceMeridianElimination
import GaloisForLFunctions.HTGeometry.CriticalSourceExplicitMeridians

/-!
# Eliminate critical block covers with the explicit source meridians

The two required source loops are now constructed on the actual critical source chart.  This
module feeds them into block-cover rigidity.  Consequently formal purity of the block
normalization is the only premise left in the global block elimination.
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

/-- Two source meridians expressed through the direct source projection eliminate the block
cover.  This form avoids transporting dependent path endpoints through the propositionally equal
block-mediated projection. -/
theorem criticalBlockCover_fiber_subsingleton_of_direct_source_meridians_at
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B)
    (x : AlgSpec (criticalSourceChartRing ℂ m n))
    (alpha : Path (1 : ComplexTorusAffineChart (n + m - 2))
      (criticalSourceAnalyticProjectionContinuousMap x))
    (deltaFirst deltaSecond : Path.Homotopic.Quotient x x)
    (hfirst :
      (Path.Homotopic.Quotient.mk alpha).trans
        ((deltaFirst.map criticalSourceAnalyticProjectionContinuousMap).trans
          (Path.Homotopic.Quotient.mk alpha.symm)) =
        torusChartFirstFundamentalGenerator (n + m - 2))
    (hsecond :
      (Path.Homotopic.Quotient.mk alpha).trans
        ((deltaSecond.map criticalSourceAnalyticProjectionContinuousMap).trans
          (Path.Homotopic.Quotient.mk alpha.symm)) =
        torusChartSecondFundamentalGenerator (n + m - 2)) :
    Subsingleton
      ((criticalBlockAnalyticProjection (m := m) (n := n) (B := B)) ⁻¹'
        {(1 : ComplexTorusAffineChart (n + m - 2))}) := by
  let p := criticalBlockAnalyticProjection (m := m) (n := n) (B := B)
  have cov : IsCoveringMap p := criticalBlockAnalyticProjection_isCoveringMap
  let f := criticalSourceToBlockNormalization hB hmem
  have hf : Continuous f := continuous_criticalSourceToBlockNormalization hB hmem
  let q := criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
  have hq : q = (⟨p, cov.continuous⟩ :
      C(AlgSpec (CriticalBlockNormalization ℂ B),
        ComplexTorusAffineChart (n + m - 2))).comp ⟨f, hf⟩ := by
    apply ContinuousMap.ext
    intro z
    exact congrFun (criticalSourceBlockAnalyticProjection_eq_source hB hmem).symm z
  let y : ComplexTorusAffineChart (n + m - 2) := q x
  let eY : p ⁻¹' {y} := ⟨f x, by simpa [y, hq]⟩
  have hfixFirst : cov.monodromy (deltaFirst.map q) eY = eY := by
    exact covering_monodromy_fixed_of_closed_lift_at_of_eq p cov f hf q hq x deltaFirst
  have hfixSecond : cov.monodromy (deltaSecond.map q) eY = eY := by
    exact covering_monodromy_fixed_of_closed_lift_at_of_eq p cov f hf q hq x deltaSecond
  change Path (1 : ComplexTorusAffineChart (n + m - 2)) y at alpha
  change (Path.Homotopic.Quotient.mk alpha).trans
      ((deltaFirst.map q).trans (Path.Homotopic.Quotient.mk alpha.symm)) =
    torusChartFirstFundamentalGenerator (n + m - 2) at hfirst
  change (Path.Homotopic.Quotient.mk alpha).trans
      ((deltaSecond.map q).trans (Path.Homotopic.Quotient.mk alpha.symm)) =
    torusChartSecondFundamentalGenerator (n + m - 2) at hsecond
  have hfirst' :
      (Path.Homotopic.Quotient.mk alpha).trans
        ((deltaFirst.map q).trans (Path.Homotopic.Quotient.mk alpha).symm) =
      torusChartFirstFundamentalGenerator (n + m - 2) := by
    simpa using hfirst
  have hsecond' :
      (Path.Homotopic.Quotient.mk alpha).trans
        ((deltaSecond.map q).trans (Path.Homotopic.Quotient.mk alpha).symm) =
      torusChartSecondFundamentalGenerator (n + m - 2) := by
    simpa using hsecond
  obtain ⟨e, hgenFirst, hgenSecond⟩ :=
    covering_monodromy_two_conjugates_fixed_transport cov
      (Path.Homotopic.Quotient.mk alpha) eY
      (deltaFirst.map q) (deltaSecond.map q) hfixFirst hfixSecond
      (torusChartFirstFundamentalGenerator (n + m - 2))
      (torusChartSecondFundamentalGenerator (n + m - 2)) hfirst' hsecond'
  letI : PathConnectedSpace (AlgSpec (CriticalBlockNormalization ℂ B)) :=
    pathConnectedSpace_algSpec_criticalBlockNormalization hB hmem
  exact subsingleton_torusChartCover_fiber_of_generators_fixed p cov e hgenFirst hgenSecond

/-- The explicit closed loops on the actual critical source chart eliminate every connected block
cover.  There are no source-loop or homotopy-class premises left. -/
theorem criticalBlockCover_fiber_subsingleton_of_explicit_source_meridians
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    Subsingleton
      ((criticalBlockAnalyticProjection (m := m) (n := n) (B := B)) ⁻¹'
        {(1 : ComplexTorusAffineChart (n + m - 2))}) := by
  exact criticalBlockCover_fiber_subsingleton_of_direct_source_meridians_at
    hB hmem
    (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
      (criticalFirstMeridianAwayBase m n).2)
    (criticalChartMeridianConnector m n)
    (Path.Homotopic.Quotient.mk (criticalFirstSourceLocalMeridian m n))
    (Path.Homotopic.Quotient.mk (criticalSecondSourceMeridian m n))
    (criticalFirstSourceMeridian_conjugate_mk m n)
    (criticalSecondSourceMeridian_conjugate_mk m n)

end

end GaloisForLFunctions.HTGeometry
