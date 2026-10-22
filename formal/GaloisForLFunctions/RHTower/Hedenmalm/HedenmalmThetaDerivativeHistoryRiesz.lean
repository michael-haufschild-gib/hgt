import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmEssentialInverseFlowTrace
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaDerivativeHistoryQuotient
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Literal Riesz projections on the actual derivative-history quotient

The existing compact theta Riesz projection around each nonzero spectral
point annihilates every actual derivative generator. Continuity extends
this to their closed history. The same bounded projection therefore lifts
from the literal history quotient and induces an idempotent there. Its
finite root range and complementary kernel retain the full nonzero block.
-/

open MeasureTheory Set Topology Complex Module

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmHilbertSchmidt

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev RH := thetaQuantileDerivativeHistory

/-- The actual isolating contour excludes the zero-history spectral point. -/
theorem zero_not_mem_thetaRiesz_closedBall (mu : ThetaNonzeroSpectrum) :
    (0 : ℂ) ∉ Metric.closedBall (mu : ℂ) (thetaRieszRadius mu) := by
  intro hzero
  have hdist : ‖(mu : ℂ)‖ ≤ thetaRieszRadius mu := by
    simpa using Metric.mem_closedBall.mp hzero
  exact (not_le_of_gt (thetaRieszRadius_spec mu).2.1) hdist

/-- The literal contour projection kills each vector of the actual zero-Jordan chain. -/
theorem thetaLocalRieszProjection_derivative (mu : ThetaNonzeroSpectrum) (n : ℕ) :
    thetaLocalRieszProjection mu (thetaQuantileDerivativeVector n) = 0 := by
  apply rieszProjection_apply_eq_zero_of_pow_eq_zero
    (thetaRieszRadius_spec mu).1.le (thetaRieszRadius_spec mu).2.2.1
    (zero_not_mem_thetaRiesz_closedBall mu) (mu := 0) (n := n + 1)
  simp only [zero_smul, sub_zero]
  rw [thetaKernelOperator_eq_thetaCompactSourceInverse]
  exact thetaCompactSourceInverse_pow_derivative_eq_zero n (n + 1) le_rfl

/-- Closed derivative history lies in the kernel of each nonzero literal Riesz projection. -/
theorem thetaQuantileDerivativeHistory_le_ker_thetaLocalRieszProjection
    (mu : ThetaNonzeroSpectrum) :
    thetaQuantileDerivativeHistory ≤ (thetaLocalRieszProjection mu).ker := by
  apply (Submodule.span ℂ (range thetaQuantileDerivativeVector)).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (thetaLocalRieszProjection mu).isClosed_ker
  rintro _ ⟨n, rfl⟩
  exact thetaLocalRieszProjection_derivative mu n

theorem thetaLocalRieszProjection_history (mu : ThetaNonzeroSpectrum) {f : H}
    (hf : f ∈ thetaQuantileDerivativeHistory) : thetaLocalRieszProjection mu f = 0 :=
  thetaQuantileDerivativeHistory_le_ker_thetaLocalRieszProjection mu hf

theorem thetaLocalRieszProjection_commute (mu : ThetaNonzeroSpectrum) :
    thetaCompactSourceInverse * thetaLocalRieszProjection mu =
      thetaLocalRieszProjection mu * thetaCompactSourceInverse := by
  rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]
  exact rieszProjection_commute thetaKernelOperator
    (thetaRieszRadius_spec mu).1.le (thetaRieszRadius_spec mu).2.2.1

theorem thetaLocalRieszProjection_isTopCompl (mu : ThetaNonzeroSpectrum) :
    (thetaLocalRieszProjection mu).range.IsTopCompl (thetaLocalRieszProjection mu).ker :=
  ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (isIdempotentElem_iff.mpr (thetaLocalRieszProjection_idempotent mu))

theorem range_thetaLocalRieszProjection_eq_sourceRoot (mu : ThetaNonzeroSpectrum) :
    (thetaLocalRieszProjection mu).range =
      Module.End.maxGenEigenspace thetaCompactSourceInverse.toLinearMap (mu : ℂ) := by
  rw [range_thetaLocalRieszProjection]
  exact congrArg (fun T : H →L[ℂ] H => Module.End.maxGenEigenspace T.toLinearMap (mu : ℂ))
    thetaKernelOperator_eq_thetaCompactSourceInverse

theorem thetaLocalRieszProjection_eq_self_of_mem_root (mu : ThetaNonzeroSpectrum) {f : H}
    (hf : f ∈ Module.End.maxGenEigenspace thetaCompactSourceInverse.toLinearMap (mu : ℂ)) :
    thetaLocalRieszProjection mu f = f := by
  have hp : IsIdempotentElem (thetaLocalRieszProjection mu) :=
    isIdempotentElem_iff.mpr (thetaLocalRieszProjection_idempotent mu)
  apply (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp)).mp
  rwa [range_thetaLocalRieszProjection_eq_sourceRoot]

/-- The original contour projection factors continuously through the literal quotient. -/
def thetaDerivativeHistoryRieszLift (mu : ThetaNonzeroSpectrum) :
    ThetaDerivativeHistoryQuotient →L[ℂ] H :=
  RH.liftQL (thetaLocalRieszProjection mu)
    (thetaQuantileDerivativeHistory_le_ker_thetaLocalRieszProjection mu)

theorem thetaDerivativeHistoryRieszLift_projection (mu : ThetaNonzeroSpectrum) (f : H) :
    thetaDerivativeHistoryRieszLift mu (thetaDerivativeHistoryQuotientProjection f) =
      thetaLocalRieszProjection mu f := rfl

/-- The projection induced by the literal full-space Riesz projection. -/
def thetaDerivativeHistoryRieszProjection (mu : ThetaNonzeroSpectrum) :
    ThetaDerivativeHistoryQuotient →L[ℂ] ThetaDerivativeHistoryQuotient :=
  thetaDerivativeHistoryQuotientProjection.comp (thetaDerivativeHistoryRieszLift mu)

theorem thetaDerivativeHistoryRieszProjection_projection (mu : ThetaNonzeroSpectrum) (f : H) :
    thetaDerivativeHistoryRieszProjection mu (thetaDerivativeHistoryQuotientProjection f) =
      thetaDerivativeHistoryQuotientProjection (thetaLocalRieszProjection mu f) := rfl

private theorem history_projection_surjective :
    Function.Surjective thetaDerivativeHistoryQuotientProjection := RH.mkQ_surjective

private theorem thetaLocalRieszProjection_apply_idempotent
    (mu : ThetaNonzeroSpectrum) (f : H) :
    thetaLocalRieszProjection mu (thetaLocalRieszProjection mu f) =
      thetaLocalRieszProjection mu f := by
  exact congrArg (fun T : H →L[ℂ] H => T f) (thetaLocalRieszProjection_idempotent mu)

theorem thetaDerivativeHistoryRieszProjection_idempotent (mu : ThetaNonzeroSpectrum) :
    thetaDerivativeHistoryRieszProjection mu * thetaDerivativeHistoryRieszProjection mu =
      thetaDerivativeHistoryRieszProjection mu := by
  ext y
  obtain ⟨f, rfl⟩ := history_projection_surjective y
  change thetaDerivativeHistoryRieszProjection mu
    (thetaDerivativeHistoryRieszProjection mu (thetaDerivativeHistoryQuotientProjection f)) = _
  rw [thetaDerivativeHistoryRieszProjection_projection,
    thetaDerivativeHistoryRieszProjection_projection, thetaLocalRieszProjection_apply_idempotent]

theorem thetaDerivativeHistoryRieszProjection_commute (mu : ThetaNonzeroSpectrum) :
    thetaDerivativeHistoryQuotientInverse * thetaDerivativeHistoryRieszProjection mu =
      thetaDerivativeHistoryRieszProjection mu * thetaDerivativeHistoryQuotientInverse := by
  ext y
  obtain ⟨f, rfl⟩ := history_projection_surjective y
  change thetaDerivativeHistoryQuotientInverse
    (thetaDerivativeHistoryRieszProjection mu (thetaDerivativeHistoryQuotientProjection f)) =
    thetaDerivativeHistoryRieszProjection mu
      (thetaDerivativeHistoryQuotientInverse (thetaDerivativeHistoryQuotientProjection f))
  rw [thetaDerivativeHistoryRieszProjection_projection,
    thetaDerivativeHistoryQuotientInverse_projection,
    thetaDerivativeHistoryQuotientInverse_projection,
    thetaDerivativeHistoryRieszProjection_projection]
  exact congrArg thetaDerivativeHistoryQuotientProjection
    (congrArg (fun T : H →L[ℂ] H => T f) (thetaLocalRieszProjection_commute mu))

/-- The actual spectral range/kernel decomposition descends to the literal history quotient. -/
theorem thetaDerivativeHistoryRieszProjection_isTopCompl (mu : ThetaNonzeroSpectrum) :
    (thetaDerivativeHistoryRieszProjection mu).range.IsTopCompl
      (thetaDerivativeHistoryRieszProjection mu).ker :=
  ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (isIdempotentElem_iff.mpr (thetaDerivativeHistoryRieszProjection_idempotent mu))

/-- The descended literal projection has precisely the quotient's complete nonzero root block. -/
theorem range_thetaDerivativeHistoryRieszProjection (mu : ThetaNonzeroSpectrum) :
    (thetaDerivativeHistoryRieszProjection mu).range =
      Module.End.maxGenEigenspace thetaDerivativeHistoryQuotientInverse.toLinearMap (mu : ℂ) := by
  let e := thetaDerivativeHistoryQuotientRootEquiv mu.2.2 ⊤
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := history_projection_surjective x
    change thetaDerivativeHistoryRieszProjection mu
      (thetaDerivativeHistoryQuotientProjection f) ∈ _
    rw [thetaDerivativeHistoryRieszProjection_projection]
    have hf : thetaLocalRieszProjection mu f ∈
        Module.End.maxGenEigenspace thetaCompactSourceInverse.toLinearMap (mu : ℂ) := by
      rw [← range_thetaLocalRieszProjection_eq_sourceRoot]
      exact ⟨f, rfl⟩
    exact (e ⟨thetaLocalRieszProjection mu f, hf⟩).property
  · intro y hy
    obtain ⟨v, hv⟩ := e.surjective ⟨y, hy⟩
    refine ⟨thetaDerivativeHistoryQuotientProjection v, ?_⟩
    change thetaDerivativeHistoryRieszProjection mu (thetaDerivativeHistoryQuotientProjection v) = y
    rw [thetaDerivativeHistoryRieszProjection_projection,
      thetaLocalRieszProjection_eq_self_of_mem_root mu v.property]
    simpa only [e, thetaDerivativeHistoryQuotientRootEquiv_apply] using
      congrArg Subtype.val hv

/-- Quotient projection itself identifies the full and descended Riesz ranges. -/
def thetaDerivativeHistoryRieszRangeEquiv (mu : ThetaNonzeroSpectrum) :
    (thetaLocalRieszProjection mu).range ≃ₗ[ℂ]
      (thetaDerivativeHistoryRieszProjection mu).range :=
  (LinearEquiv.ofEq _ _ (range_thetaLocalRieszProjection_eq_sourceRoot mu)).trans
    ((thetaDerivativeHistoryQuotientRootEquiv mu.2.2 ⊤).trans
      (LinearEquiv.ofEq _ _ (range_thetaDerivativeHistoryRieszProjection mu).symm))

theorem thetaDerivativeHistoryRieszRangeEquiv_apply (mu : ThetaNonzeroSpectrum)
    (f : (thetaLocalRieszProjection mu).range) :
    (thetaDerivativeHistoryRieszRangeEquiv mu f : ThetaDerivativeHistoryQuotient) =
      thetaDerivativeHistoryQuotientProjection f := rfl

theorem thetaDerivativeHistoryRieszRangeEquiv_source_action (mu : ThetaNonzeroSpectrum)
    (f : (thetaLocalRieszProjection mu).range) :
    thetaDerivativeHistoryQuotientInverse (thetaDerivativeHistoryRieszRangeEquiv mu f) =
      thetaDerivativeHistoryQuotientProjection (thetaCompactSourceInverse f) := by
  rw [thetaDerivativeHistoryRieszRangeEquiv_apply,
    thetaDerivativeHistoryQuotientInverse_projection]

theorem finiteDimensional_range_thetaDerivativeHistoryRieszProjection
    (mu : ThetaNonzeroSpectrum) :
    FiniteDimensional ℂ (thetaDerivativeHistoryRieszProjection mu).range := by
  haveI : FiniteDimensional ℂ (thetaLocalRieszProjection mu).range :=
    (thetaRieszRadius_spec mu).2.2.2.2.1
  exact (thetaDerivativeHistoryRieszRangeEquiv mu).finiteDimensional

theorem finrank_range_thetaDerivativeHistoryRieszProjection (mu : ThetaNonzeroSpectrum) :
    Module.finrank ℂ (thetaLocalRieszProjection mu).range =
      Module.finrank ℂ (thetaDerivativeHistoryRieszProjection mu).range :=
  (thetaDerivativeHistoryRieszRangeEquiv mu).finrank_eq

theorem thetaDerivativeHistoryRieszProjection_mem_kernel_iff
    (mu : ThetaNonzeroSpectrum) (f : H) :
    thetaDerivativeHistoryQuotientProjection f ∈ (thetaDerivativeHistoryRieszProjection mu).ker ↔
      f ∈ (thetaLocalRieszProjection mu).ker := by
  change thetaDerivativeHistoryRieszProjection mu
    (thetaDerivativeHistoryQuotientProjection f) = 0 ↔ thetaLocalRieszProjection mu f = 0
  rw [thetaDerivativeHistoryRieszProjection_projection]
  constructor
  · intro hzero
    by_contra hne
    have hf : thetaLocalRieszProjection mu f ∈
        Module.End.maxGenEigenspace thetaCompactSourceInverse.toLinearMap (mu : ℂ) := by
      rw [← range_thetaLocalRieszProjection_eq_sourceRoot]
      exact ⟨f, rfl⟩
    exact thetaDerivativeHistoryQuotientProjection_root_ne_zero mu.2.2 hf hne hzero
  · intro hzero
    rw [hzero, map_zero]

/-- The descended spectral kernel is exactly the image of the original spectral kernel. -/
theorem ker_thetaDerivativeHistoryRieszProjection (mu : ThetaNonzeroSpectrum) :
    (thetaDerivativeHistoryRieszProjection mu).ker =
      (thetaLocalRieszProjection mu).ker.map thetaDerivativeHistoryQuotientProjection.toLinearMap := by
  ext y
  constructor
  · intro hy
    obtain ⟨f, rfl⟩ := history_projection_surjective y
    exact ⟨f, (thetaDerivativeHistoryRieszProjection_mem_kernel_iff mu f).mp hy, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact (thetaDerivativeHistoryRieszProjection_mem_kernel_iff mu f).mpr hf

theorem analyticOrderAt_XiC_eq_finrank_range_thetaDerivativeHistoryRieszProjection
    (rho : XiDivisorSupport) :
    analyticOrderAt XiC (xiSpectralPointSupport rho) =
      (Module.finrank ℂ
        (thetaDerivativeHistoryRieszProjection (thetaSpectrumOfXiSupport rho)).range : ℕ∞) := by
  rw [range_thetaDerivativeHistoryRieszProjection, thetaSpectrumOfXiSupport_val]
  exact analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse
    (XiC_xiSpectralPointSupport_eq_zero rho)

end

end RHTower.HedenmalmThetaSource
