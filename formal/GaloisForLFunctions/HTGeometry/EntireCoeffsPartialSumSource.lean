import GaloisForLFunctions.HTGeometry.GutzmerEntire
import GaloisForLFunctions.HTGeometry.PolydiscApproximation
import GaloisForLFunctions.HTGeometry.RandomEntireJetLawNondegeneracy

/-!
# Partial sums of an entire coefficient series converge in the compact-open source space

An entire coefficient sequence has infinite radius, so its partial sums converge locally uniformly
on the whole plane.  Transported to the one-coordinate model this is convergence in the compact-open
topology of entire sources, hence convergence of every finite jet packet.  This is the substitute
for continuity in coefficient families that are not uniformly bounded.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- The one-coordinate source of a partial sum. -/
def partialSumSource (a : ℕ → ℂ) (M : ℕ) : MultivariateEntire 1 :=
  oneDimMultivariateEntireOfDifferentiable
    ((FormalMultilinearSeries.ofScalars ℂ a).partialSum M)
    (differentiable_partialSum _ M)

/-- The one-coordinate source of an entire coefficient sequence. -/
def coeffFunSource (ha : EntireCoeffs a) : MultivariateEntire 1 :=
  oneDimMultivariateEntireOfDifferentiable (coeffFun a) (differentiable_coeffFun ha)

theorem tendstoLocallyUniformly_partialSum (ha : EntireCoeffs a) :
    TendstoLocallyUniformly
      (fun M : ℕ => (FormalMultilinearSeries.ofScalars ℂ a).partialSum M) (coeffFun a) atTop := by
  have hrad : (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := ofScalars_radius_eq_top ha
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    rw [hrad]
    exact ENNReal.zero_lt_top
  have hball : HasFPowerSeriesOnBall (coeffFun a) (FormalMultilinearSeries.ofScalars ℂ a) 0
      (FormalMultilinearSeries.ofScalars ℂ a).radius :=
    (FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall hpos
  have h := hball.tendstoLocallyUniformlyOn
  rw [hrad] at h
  have huniv : Metric.eball (0 : ℂ) ⊤ = Set.univ := by
    ext z
    simp
  rw [huniv, tendstoLocallyUniformlyOn_univ] at h
  refine h.congr_right fun z => ?_
  rw [zero_add]

theorem tendsto_partialSumSource (ha : EntireCoeffs a) :
    Tendsto (fun M : ℕ => partialSumSource a M) atTop (nhds (coeffFunSource ha)) := by
  refine tendsto_multivariateEntire_of_locallyUniform ?_
  have hcomp := (tendstoLocallyUniformly_partialSum ha).comp
    (fun z : Fin 1 → ℂ => z 0) (continuous_apply 0)
  exact hcomp

/-- **Jet packets of partial sums converge.** -/
theorem tendsto_packet_partialSumSource {H : Type*} (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (ha : EntireCoeffs a) :
    Tendsto (fun M : ℕ => finiteAffineJetPacketObservation
        (fun h => oneDimTranslationFrame (shift h)) p base (partialSumSource a M)) atTop
      (nhds (finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
        (coeffFunSource ha))) :=
  ((continuous_finiteAffineJetPacketObservation _ p base).continuousAt).tendsto.comp
    (tendsto_partialSumSource ha)

end

end GaloisForLFunctions.HTGeometry
