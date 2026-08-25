import GaloisForLFunctions.RHTower.HedenmalmThetaGreenSquareBoundaryLaw
import GaloisForLFunctions.RHTower.HedenmalmQuantileBoundaryFlux

/-!
# Fixed theta Fredholm eigenmode Green isotropy

The fixed theta kernel operator turns every eigenvector equation into a quantile root-mode
equation.  Source arithmetic/Stokes duality then gives the exact rank-two pinned Green boundary
current: it is twice the imaginary part of the eigenvalue times the canonical source-metric
energy.

Consequently, universal modewise isotropy is not supplied by reflection-pair cancellation.  It is
exactly the Riemann hypothesis.  The statement of the criterion uses only the fixed source
operator and its source-defined boundary form; the Xi divisor enters afterward, in the proof that
this target-free operator criterion is faithful.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmHilbertSchmidt

namespace HedenmalmThetaSource

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Any eigenmode of the fixed theta kernel operator satisfies the quantile root equation at the
same eigenvalue. -/
theorem thetaKernelOperator_eigen_isQuantileRootMode
    {mu : ℂ} {f : ThetaH} (heigen : thetaKernelOperator f = mu • f) :
    IsQuantileRootMode thetaSource mu f := by
  have hop :
      (thetaKernelOperator f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
        fun t => pinnedKernelField thetaSource t f := by
    simpa [thetaKernelOperator] using
      (pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f)
  have heigenAe :
      (thetaKernelOperator f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
        fun t => mu * f t := by
    rw [heigen]
    exact Lp.coeFn_smul mu f
  have hvolterra := pinnedVolterra_coeFn f
  unfold IsQuantileRootMode
  filter_upwards [hop, heigenAe, hvolterra] with t hopT heigenT hvolterraT
  rw [hvolterraT, ← pinnedKernelField_apply_eq_pinnedVolterraFun]
  rw [← hopT, heigenT]

/-- Source arithmetic/Stokes law on every eigenmode of the fixed theta Fredholm source. -/
theorem inner_pinnedBoundaryCLM_thetaKernelOperator_eigen
    {mu : ℂ} {f : ThetaH} (heigen : thetaKernelOperator f = mu • f) :
    (inner ℂ (pinnedBoundaryCLM f) f : ℂ) =
      ((2 * mu.im : ℝ) : ℂ) *
        inner ℂ (metricOperator thetaSource thetaMetricBound_nonneg
          norm_metricSymbol_thetaSource_le f) f := by
  exact inner_pinnedBoundaryCLM_rootMode thetaSource
    (thetaKernelOperator_eigen_isQuantileRootMode heigen)
    thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le

/-- Every nonzero eigenmode of the fixed theta Fredholm source is isotropic for the rank-two
pinned Green boundary form. -/
def ThetaFredholmEigenmodesPinnedGreenIsotropic : Prop :=
  ∀ (mu : ℂ) (f : ThetaH), f ≠ 0 → thetaKernelOperator f = mu • f →
    (inner ℂ (pinnedBoundaryCLM f) f : ℂ) = 0

/-- Universal fixed-source eigenmode isotropy is exactly the Riemann hypothesis. -/
theorem thetaFredholmEigenmodesPinnedGreenIsotropic_iff_riemannHypothesis :
    ThetaFredholmEigenmodesPinnedGreenIsotropic ↔ RiemannHypothesis := by
  constructor
  · intro hisotropic
    apply thetaGreenBoundaryNeutral_iff_riemannHypothesis.mp
    intro q
    have heigen :
        thetaKernelOperator (thetaXiDivisorEigenvector q) =
          thetaXiReciprocalEigenvalue q • thetaXiDivisorEigenvector q := by
      simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse] using
        thetaCompactSourceInverse_thetaXi_eigen q
    have hzero := hisotropic (thetaXiReciprocalEigenvalue q)
      (thetaXiDivisorEigenvector q) (thetaXiDivisorEigenvector_ne_zero q) heigen
    rw [thetaXiRankTwoBoundaryFlux]
    rw [hzero]
    norm_num
  · intro hRH mu f hf heigen
    rw [inner_pinnedBoundaryCLM_thetaKernelOperator_eigen heigen]
    by_cases hmu : mu = 0
    · simp [hmu]
    · have hevec : Module.End.HasEigenvector
          (thetaKernelOperator : Module.End ℂ ThetaH) mu f :=
        ⟨Module.End.mem_eigenspace_iff.mpr heigen, hf⟩
      have hspec : mu ∈ spectrum ℂ thetaKernelOperator :=
        (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
          isCompactOperator_thetaKernelOperator hmu).1 hevec.hasUnifEigenvalue
      obtain ⟨t, rfl⟩ :=
        (riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real.mp hRH)
          mu hspec hmu
      simp

end HedenmalmThetaSource
end
end RHTower
