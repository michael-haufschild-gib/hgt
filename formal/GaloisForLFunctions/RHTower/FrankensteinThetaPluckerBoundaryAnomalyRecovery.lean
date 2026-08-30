import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerBoundarySpectrum
import GaloisForLFunctions.RHTower.FrankensteinPluckerXiHilbertAdmission
import GaloisForLFunctions.RHTower.FrankensteinThetaPluckerIntertwiningAnomaly
import GaloisForLFunctions.RHTower.PositiveInjectiveBoundaryTransfer

/-!
# Singular recovery of the theta-to-Pluecker anomaly

P-G98 identifies the theta-to-physical intertwining anomaly on every Xi eigencopy with `B v`,
where `B` is P-G95's positive compact injective physical operator and `v` is P-G96's admitted Xi
carrier.  Since zero is continuous spectrum, bounded inversion is impossible.  The canonical
regularized inverse nevertheless satisfies

`(eps + B)⁻¹ (B v) = B (eps + B)⁻¹ v → v`.

This file proves exact inverse blow-up `‖(eps + B)⁻¹‖ = 1 / eps`, maximal failure of norm
convergence `‖B (eps + B)⁻¹ - I‖ = 1`, strong recovery of both admitted carriers, and the exact
RH equivalence saying the boundary-renormalized lower anomaly tends to zero for every Xi copy.
Thus the anomaly is not negligible continuous-spectrum noise: it stores the complete off-line
carrier at the spectral boundary.
-/

open Filter Topology Set
open scoped InnerProductSpace ContinuousFunctionalCalculus

noncomputable section
namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance frankensteinThetaPluckerBoundaryAnomalyRecoveryLocalInst1 : Nontrivial GammaSewnCriticalPhysicalPluckerHilbert := by
  refine ⟨⟨gammaSewnCriticalPhysicalPluckerBasis (0, 0), 0, ?_⟩⟩
  intro h
  have hn := congrArg norm h
  rw [norm_gammaSewnCriticalPhysicalPluckerBasis, norm_zero] at hn
  norm_num at hn

noncomputable def boundaryTransfer (eps : ℝ) :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  GaloisForLFunctions.RHTower.positiveBoundaryTransfer
    gammaSewnCriticalPhysicalPluckerSpectralOperator eps

/-- Regularized inverse at the continuous zero boundary. -/
noncomputable def boundaryInverse (eps : ℝ) :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  GaloisForLFunctions.RHTower.positiveBoundaryInverse
    gammaSewnCriticalPhysicalPluckerSpectralOperator eps

theorem spectrum_real_subset :
    spectrum ℝ gammaSewnCriticalPhysicalPluckerSpectralOperator ⊆
      Set.Icc 0 ‖gammaSewnCriticalPhysicalPluckerSpectralOperator‖ := by
  exact GaloisForLFunctions.RHTower.spectrum_subset_Icc_of_nonneg
    ((ContinuousLinearMap.nonneg_iff_isPositive _).2
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive)

theorem boundaryTransfer_tendsto_id
    (v : GammaSewnCriticalPhysicalPluckerHilbert) :
    Tendsto (fun eps : ℝ => boundaryTransfer eps v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v) := by
  simpa [boundaryTransfer] using
    (GaloisForLFunctions.RHTower.positiveBoundaryTransfer_tendsto_id
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
      gammaSewnCriticalPhysicalPluckerSpectralOperator_injective
      spectrum_real_subset v)

theorem boundaryInverse_operator_apply (eps : ℝ) (heps : 0 < eps)
    (v : GammaSewnCriticalPhysicalPluckerHilbert) :
    boundaryInverse eps
        (gammaSewnCriticalPhysicalPluckerSpectralOperator v) =
      boundaryTransfer eps v := by
  exact GaloisForLFunctions.RHTower.positiveBoundaryInverse_apply_operator
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
    spectrum_real_subset eps heps v

theorem boundaryInverse_lowerAnomaly_eigenvector
    (eps : ℝ) (heps : 0 < eps) (q : RHTower.XiZeroCopy) :
    boundaryInverse eps
        (frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q)) =
      boundaryTransfer eps
        (frankensteinXiLowerPhysicalPluckerHilbertCarrier q) := by
  rw [frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector]
  exact boundaryInverse_operator_apply eps heps _

theorem boundaryInverse_upperAnomaly_eigenvector
    (eps : ℝ) (heps : 0 < eps) (q : RHTower.XiZeroCopy) :
    boundaryInverse eps
        (frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q)) =
      boundaryTransfer eps
        (frankensteinXiUpperPhysicalPluckerHilbertCarrier q) := by
  rw [frankensteinThetaXiUpperPluckerIntertwiningAnomaly_eigenvector]
  exact boundaryInverse_operator_apply eps heps _

theorem boundaryInverse_lowerAnomaly_tendsto_carrier
    (q : RHTower.XiZeroCopy) :
    Tendsto
      (fun eps : ℝ => boundaryInverse eps
        (frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)) := by
  refine (boundaryTransfer_tendsto_id
    (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact (boundaryInverse_lowerAnomaly_eigenvector eps heps q).symm

theorem boundaryInverse_upperAnomaly_tendsto_carrier
    (q : RHTower.XiZeroCopy) :
    Tendsto
      (fun eps : ℝ => boundaryInverse eps
        (frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frankensteinXiUpperPhysicalPluckerHilbertCarrier q)) := by
  refine (boundaryTransfer_tendsto_id
    (frankensteinXiUpperPhysicalPluckerHilbertCarrier q)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact (boundaryInverse_upperAnomaly_eigenvector eps heps q).symm

theorem boundaryInverse_lowerAnomaly_tendsto_zero_iff
    (q : RHTower.XiZeroCopy) :
    Tendsto
      (fun eps : ℝ => boundaryInverse eps
        (frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hcarrier : frankensteinXiLowerPhysicalPluckerHilbertCarrier q = 0 :=
      tendsto_nhds_unique (boundaryInverse_lowerAnomaly_tendsto_carrier q) hzero
    exact (frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff q).1 hcarrier
  · intro hline
    have hanomaly : frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
        (RHTower.thetaXiDivisorEigenvector q) = 0 :=
      (frankensteinThetaXiLowerPluckerIntertwiningAnomaly_eigenvector_eq_zero_iff q).2 hline
    simp only [hanomaly, map_zero]
    exact tendsto_const_nhds

/-- Global statement that every source-pencil anomaly disappears after the canonical singular
boundary inverse. -/
def LowerBoundaryAnomalyCancellation : Prop :=
  ∀ q : RHTower.XiZeroCopy,
    Tendsto
      (fun eps : ℝ => boundaryInverse eps
        (frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

theorem lowerBoundaryAnomalyCancellation_iff_riemannHypothesis :
    LowerBoundaryAnomalyCancellation ↔ RiemannHypothesis := by
  rw [← RHTower.sourceZeroHorizontalCarrierVanishes_iff_riemannHypothesis 0]
  constructor
  · intro hcancel
    funext q
    apply (RHTower.sourceZeroHorizontalCarrierAt_eq_zero_iff 0 q).2
    exact (boundaryInverse_lowerAnomaly_tendsto_zero_iff q).1 (hcancel q)
  · intro hcarrier q
    apply (boundaryInverse_lowerAnomaly_tendsto_zero_iff q).2
    exact (RHTower.sourceZeroHorizontalCarrierAt_eq_zero_iff 0 q).1
      (congrFun hcarrier q)

theorem zero_mem_real_spectrum :
    (0 : ℝ) ∈ spectrum ℝ gammaSewnCriticalPhysicalPluckerSpectralOperator := by
  apply (spectrum.algebraMap_mem_iff ℂ
    (a := gammaSewnCriticalPhysicalPluckerSpectralOperator) (r := (0 : ℝ))).mp
  simpa using
    gammaSewnCriticalPhysicalPluckerSpectralOperator_zero_mem_spectrum

theorem norm_boundaryInverse (eps : ℝ) (heps : 0 < eps) :
    ‖boundaryInverse eps‖ = 1 / eps := by
  exact GaloisForLFunctions.RHTower.norm_positiveBoundaryInverse
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
    spectrum_real_subset zero_mem_real_spectrum eps heps

theorem norm_boundaryTransfer_sub_id (eps : ℝ) (heps : 0 < eps) :
    ‖boundaryTransfer eps - ContinuousLinearMap.id ℂ
      GammaSewnCriticalPhysicalPluckerHilbert‖ = 1 := by
  exact GaloisForLFunctions.RHTower.norm_positiveBoundaryTransfer_sub_id
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
    spectrum_real_subset zero_mem_real_spectrum eps heps

theorem xiLower_boundaryTransfer_tendsto (q : RHTower.XiZeroCopy) :
    Tendsto
      (fun eps : ℝ => boundaryTransfer eps
        (frankensteinXiLowerPhysicalPluckerHilbertCarrier q))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)) :=
  boundaryTransfer_tendsto_id _

theorem xiLower_boundaryMoment_tendsto (q : RHTower.XiZeroCopy) :
    Tendsto
      (fun eps : ℝ => inner ℂ
        (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)
        (boundaryTransfer eps
          (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (‖frankensteinXiLowerPhysicalPluckerHilbertCarrier q‖ ^ 2 : ℂ)) := by
  have h := Filter.Tendsto.inner (𝕜 := ℂ)
    (f := fun _ : ℝ => frankensteinXiLowerPhysicalPluckerHilbertCarrier q)
    (g := fun eps : ℝ => boundaryTransfer eps
      (frankensteinXiLowerPhysicalPluckerHilbertCarrier q))
    tendsto_const_nhds (xiLower_boundaryTransfer_tendsto q)
  simpa [inner_self_eq_norm_sq_to_K] using h

theorem xiLower_boundaryMoment_limit_pos_iff (q : RHTower.XiZeroCopy) :
    0 < ‖frankensteinXiLowerPhysicalPluckerHilbertCarrier q‖ ^ 2 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [sq_pos_iff, norm_ne_zero_iff]
  exact not_congr
    (frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff q)

end RHTower.HedenmalmThetaSource
