import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDifferentialPencil
import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.HedenmalmPinnedBoundaryTwoPort

/-!
# Green law for the closed source-faithful theta differential pencil

The literal theta source inverse satisfies a singular-metric two-port commutator.  The closed
source-faithful differential pencil replaces its centered inverse coordinate by
`k + z • (B k - mean(B k) • 1)`.  This file transports the Green identity exactly through that
closed-graph coordinate.  The two monopole terms remain visible; omitting either would recover a
different pencil and lose the literal Xi divisor.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative
  HedenmalmFredholmRange GaloisForLFunctions.HTGeometry

private abbrev H := Lp ℂ 2 unitIntervalMeasure

private local instance thetaSourceDifferentialGreenComplete : CompleteSpace thetaCentered :=
  thetaCentered_isClosed.completeSpace_coe

/-- On the centered coordinate hyperplane, the closed-pencil inverse coordinate is the literal
theta source inverse. -/
theorem thetaCenteredSourceInverse_eq_thetaKernelOperator (k : thetaCentered) :
    thetaCenteredSourceInverse k = thetaKernelOperator (k : H) := by
  rw [thetaCenteredSourceInverse, ContinuousLinearMap.comp_apply]
  change thetaCompactSourceInverse (k : H) = thetaKernelOperator (k : H)
  rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]

/-- Green identity in the bounded coordinates that parameterize the closed differential domain. -/
theorem thetaCenteredSourceInverse_metricGreen (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) -
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) =
        -Complex.I * inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) := by
  have hgreen := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T (k : H)) (l : H) : ℂ))
    thetaMetric_commutator_thetaKernelOperator
  have hsub :
      (thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) =
        (thetaMetricOperator * thetaKernelOperator) (k : H) -
          (ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) := by
    change
      ((↑(thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) : H →ₗ[ℂ] H)
        (k : H)) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  rw [hsub, mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_left,
    smul_apply, inner_smul_left, ContinuousLinearMap.adjoint_inner_left] at hgreen
  rw [← thetaCenteredSourceInverse_eq_thetaKernelOperator k,
    ← thetaCenteredSourceInverse_eq_thetaKernelOperator l] at hgreen
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := by
    exact Complex.conj_I
  rw [hconjI] at hgreen
  simpa only [neg_mul] using hgreen

/-- The bounded Green defect is exactly the difference of its incoming and outgoing scalar-port
pairings. -/
theorem inner_pinnedBoundaryCLM_eq_twoPort_pair (k l : H) :
    (inner ℂ (pinnedBoundaryCLM k) l : ℂ) =
      (starRingEnd ℂ) (pinnedBoundaryInPort k) * pinnedBoundaryInPort l -
        (starRingEnd ℂ) (pinnedBoundaryOutPort k) * pinnedBoundaryOutPort l := by
  have hsub :
      (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) k =
        (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort) k -
          (pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) k := by
    change
      ((↑(pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) : H →ₗ[ℂ] H) k) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  have hports := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T k) l : ℂ)) pinnedBoundaryCLM_eq_port_difference
  rw [hsub, ContinuousLinearMap.comp_apply,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left] at hports
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] at hports
  simpa only [RCLike.inner_apply'] using hports

/-- The boundary form vanishes between any two centered source coordinates.  It can still send a
centered vector to the constant mode, but that mode is orthogonal to the entire centered carrier. -/
theorem inner_pinnedBoundaryCLM_thetaCentered_eq_zero (k l : thetaCentered) :
    (inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) : ℂ) = 0 := by
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  have hl : pinnedMean (l : H) = 0 :=
    (mem_thetaCentered_iff (l : H)).mp l.property
  have hinnerl : inner ℂ pinnedOne (l : H) = 0 := by
    change thetaPinnedMeanCLM (l : H) = 0
    rw [thetaPinnedMeanCLM_apply, hl]
  rw [pinnedBoundaryCLM_eq_affine_combination, hk]
  simp only [zero_sub, zero_smul, sub_zero, inner_smul_left]
  rw [hinnerl]
  simp

/-- Restoring the omitted scalar coordinate exposes the exact monopole--dipole normal form of
the boundary defect.  The defect pairs this scalar with the centered dipole; neither component
alone carries a nonzero boundary form. -/
theorem pinnedBoundaryCLM_thetaCentered_add_scalar (k : thetaCentered) (m : ℂ) :
    pinnedBoundaryCLM ((k : H) + m • pinnedOne) =
      (-pinnedFirstMoment (k : H)) • pinnedOne - m • pinnedCenter := by
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  rw [pinnedBoundaryCLM_eq_affine_combination,
    pinnedMean_add, pinnedMean_smul, pinnedMean_pinnedOne, hk,
    pinnedFirstMoment_add, pinnedFirstMoment_smul, pinnedFirstMoment_pinnedOne]
  simp only [zero_add, mul_one]
  rw [pinnedCenter]
  module

/-- On the centered source coordinate, the singular-metric commutator leaves exactly one
transverse constant channel.  This identifies the channel that a minimal Pontryagin realization
must couple to; the centered compression itself has no defect. -/
theorem thetaMetric_commutator_thetaCentered_eq_monopole (k : thetaCentered) :
    (thetaMetricOperator * thetaKernelOperator -
      ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) =
        (-Complex.I * pinnedFirstMoment (k : H)) • pinnedOne := by
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  rw [thetaMetric_commutator_thetaKernelOperator, smul_apply,
    pinnedBoundaryCLM_eq_affine_combination, hk]
  module

/-- The centered dipole is a bounded trace in the ordinary Hilbert topology.  It is recorded
separately because its continuity in the singular metric is the capacity bottleneck. -/
def thetaCenteredDipoleTrace : thetaCentered →L[ℂ] ℂ :=
  (innerSL ℂ pinnedCenter).comp thetaCentered.subtypeL

theorem thetaCenteredDipoleTrace_apply (k : thetaCentered) :
    thetaCenteredDipoleTrace k = pinnedFirstMoment (k : H) := by
  change inner ℂ pinnedCenter (k : H) = pinnedFirstMoment (k : H)
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  have hinnerk : inner ℂ pinnedOne (k : H) = 0 := by
    change thetaPinnedMeanCLM (k : H) = 0
    rw [thetaPinnedMeanCLM_apply, hk]
  rw [pinnedCenter, inner_sub_left, inner_smul_left, hinnerk, mul_zero, sub_zero]
  rw [inner_lp_eq, pinnedFirstMoment]
  apply integral_congr_ae
  filter_upwards [pinnedCoordinate_coeFn] with t ht
  rw [ht]
  simp

/-- Closed graph-energy coordinate carrying the literal differential graph and its transverse
dipole trace.  The added trace repairs continuity at the singular boundary without changing the
source coordinate or its Xi kernel. -/
def thetaSourceDifferentialGraphEnergyCoordinate (z : ℂ) :
    thetaCentered →L[ℂ] ((H × H) × ℂ) :=
  (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)).prod
    thetaCenteredDipoleTrace

/-- Adding the dipole trace preserves the exact graph lower bound. -/
theorem thetaSourceDifferentialGraphEnergyCoordinate_antilipschitz (z : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c (thetaSourceDifferentialGraphEnergyCoordinate z) := by
  rcases thetaSourceDifferentialGraphMap_antilipschitz z with ⟨c, hc⟩
  refine ⟨c, (thetaSourceDifferentialGraphEnergyCoordinate z).antilipschitz_of_bound ?_⟩
  intro k
  have hbound := hc.le_mul_dist k 0
  simp only [dist_zero_right, map_zero] at hbound
  refine hbound.trans ?_
  gcongr
  exact norm_fst_le (thetaSourceDifferentialGraphEnergyCoordinate z k)

/-- The dipole-enriched graph coordinate has closed range, yielding a concrete closed energy
carrier for the monopole--dipole completion candidate. -/
theorem thetaSourceDifferentialGraphEnergyCoordinate_isClosed_range (z : ℂ) :
    IsClosed (Set.range (thetaSourceDifferentialGraphEnergyCoordinate z)) := by
  rcases thetaSourceDifferentialGraphEnergyCoordinate_antilipschitz z with ⟨c, hc⟩
  exact hc.isClosed_range (thetaSourceDifferentialGraphEnergyCoordinate z).uniformContinuous

/-- The closed boundary coordinate keeps both channels of the singular Green defect: the source
mean of the primitive and the dipole of the centered derivative coordinate.  It is deliberately
not a quotient of either channel, so its vertical fibre still represents the literal pencil
kernel. -/
def thetaSourceDifferentialBoundaryCoordinate (z : ℂ) :
    thetaCentered →L[ℂ] ((H × H) × (ℂ × ℂ)) :=
  (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)).prod
    ((thetaPinnedMeanCLM.comp thetaCenteredSourceInverse).prod thetaCenteredDipoleTrace)

theorem thetaSourceDifferentialBoundaryCoordinate_apply (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryCoordinate z k =
      ((thetaCenteredSourceInverse k, thetaSourceDifferentialRangeMap z k),
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)) := by
  simp [thetaSourceDifferentialBoundaryCoordinate, thetaPinnedMeanCLM_apply]

/-- The full monopole--dipole coordinate remains an antilipschitz parametrization of its source
carrier.  Hence adjoining the two boundary channels cannot introduce a spurious closure point. -/
theorem thetaSourceDifferentialBoundaryCoordinate_antilipschitz (z : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c (thetaSourceDifferentialBoundaryCoordinate z) := by
  rcases thetaSourceDifferentialGraphMap_antilipschitz z with ⟨c, hc⟩
  refine ⟨c, (thetaSourceDifferentialBoundaryCoordinate z).antilipschitz_of_bound ?_⟩
  intro k
  have hbound := hc.le_mul_dist k 0
  simp only [dist_zero_right, map_zero] at hbound
  calc
    ‖k‖ ≤ c * ‖(thetaCenteredSourceInverse.prod
        (thetaSourceDifferentialRangeMap z)) k‖ := hbound
    _ ≤ c * ‖thetaSourceDifferentialBoundaryCoordinate z k‖ := by
      gcongr
      have hfst : (thetaSourceDifferentialBoundaryCoordinate z k).1 =
          (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k := rfl
      rw [← hfst]
      exact norm_fst_le _

/-- The source-defined closed relation used for the singular completion candidate.  Its first
pair is the literal closed differential graph; its second pair is the complete hyperbolic
boundary record. -/
def thetaSourceDifferentialBoundaryRelation (z : ℂ) : Submodule ℂ ((H × H) × (ℂ × ℂ)) :=
  LinearMap.range (thetaSourceDifferentialBoundaryCoordinate z).toLinearMap

theorem thetaSourceDifferentialBoundaryRelation_isClosed (z : ℂ) :
    IsClosed (thetaSourceDifferentialBoundaryRelation z : Set ((H × H) × (ℂ × ℂ))) := by
  change IsClosed (Set.range (thetaSourceDifferentialBoundaryCoordinate z))
  rcases thetaSourceDifferentialBoundaryCoordinate_antilipschitz z with ⟨c, hc⟩
  exact hc.isClosed_range (thetaSourceDifferentialBoundaryCoordinate z).uniformContinuous

/-- Membership in the closed relation has a unique source witness.  This explicit presentation
prevents completion from silently replacing the source differential by a different graph. -/
theorem thetaSourceDifferentialBoundaryRelation_mem_iff
    (z : ℂ) (r : ((H × H) × (ℂ × ℂ))) :
    r ∈ thetaSourceDifferentialBoundaryRelation z ↔
      ∃ k : thetaCentered, thetaSourceDifferentialBoundaryCoordinate z k = r := by
  rfl

/-- A nonzero vertical fibre of the closed relation is exactly a nonzero source vector killed by
the range coordinate. -/
theorem thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff (z : ℂ) :
    (∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
      r.1.2 = 0 ∧ r.1.1 ≠ 0) ↔
      ∃ k : thetaCentered, thetaSourceDifferentialRangeMap z k = 0 ∧
        thetaCenteredSourceInverse k ≠ 0 := by
  constructor
  · rintro ⟨r, hr, hrange, hsource⟩
    obtain ⟨k, hk⟩ := (thetaSourceDifferentialBoundaryRelation_mem_iff z r).mp hr
    refine ⟨k, ?_, ?_⟩
    · have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.2) hk
      simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h.trans hrange
    · have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.1) hk
      intro hzero
      apply hsource
      simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h.symm.trans hzero
  · rintro ⟨k, hrange, hsource⟩
    refine ⟨thetaSourceDifferentialBoundaryCoordinate z k,
      (thetaSourceDifferentialBoundaryRelation_mem_iff z _).mpr ⟨k, rfl⟩, ?_, ?_⟩
    · simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using hrange
    · simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using hsource

/-- The vertical fibre of the closed boundary relation is source-faithful: it is nontrivial
exactly when the literal closed differential pencil has a nontrivial kernel. -/
theorem thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff_pencil_kernel (z : ℂ) :
    (∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
      r.1.2 = 0 ∧ r.1.1 ≠ 0) ↔
      ∃ f : H, f ≠ 0 ∧ ∃ hf : f ∈ (thetaSourceDifferentialPencil z).domain,
        thetaSourceDifferentialPencil z ⟨f, hf⟩ = 0 := by
  rw [thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff]
  constructor
  · rintro ⟨k, hrange, hsource⟩
    refine ⟨thetaCenteredSourceInverse k, hsource, ?_⟩
    exact ⟨(thetaSourceDifferentialPencil_apply_B z k).1,
      (thetaSourceDifferentialPencil_apply_B z k).2.trans hrange⟩
  · rintro ⟨f, hf, hfdom, hdiff⟩
    have hfrange : f ∈ thetaCenteredSourceInverse.range := by
      simpa only [thetaSourceDifferentialPencil, closedGraphTransform_domain] using hfdom
    obtain ⟨k, hk⟩ := hfrange
    have hkdom : thetaCenteredSourceInverse k ∈ (thetaSourceDifferentialPencil z).domain :=
      (thetaSourceDifferentialPencil_apply_B z k).1
    have heq : (⟨f, hfdom⟩ : (thetaSourceDifferentialPencil z).domain) =
        ⟨thetaCenteredSourceInverse k, hkdom⟩ := Subtype.ext hk.symm
    have hrange : thetaSourceDifferentialRangeMap z k = 0 := by
      calc
        thetaSourceDifferentialRangeMap z k =
            thetaSourceDifferentialPencil z ⟨thetaCenteredSourceInverse k, hkdom⟩ :=
          (thetaSourceDifferentialPencil_apply_B z k).2.symm
        _ = thetaSourceDifferentialPencil z ⟨f, hfdom⟩ := congrArg
          (thetaSourceDifferentialPencil z) heq.symm
        _ = 0 := hdiff
    refine ⟨k, hrange, ?_⟩
    intro hzero
    apply hf
    rw [← hk]
    exact hzero

/-- The closed hyperbolic boundary relation retains the exact completed-Xi divisor rather than a
surrogate spectral equation. -/
theorem XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical (z : ℂ) :
    XiC z = 0 ↔
      ∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
        r.1.2 = 0 ∧ r.1.1 ≠ 0 := by
  exact (XiC_eq_zero_iff_exists_thetaSourceDifferentialPencil_kernel z).trans
    (thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff_pencil_kernel z).symm

/-- Bounded projection that removes precisely the pinned scalar mode retained by the source
correction.  This is the spectral weight in the literal differential pencil. -/
def thetaPinnedMeanProjection : H →L[ℂ] H :=
  1 - thetaPinnedMeanCLM.smulRight pinnedOne

theorem thetaPinnedMeanProjection_apply (f : H) :
    thetaPinnedMeanProjection f = f - pinnedMean f • pinnedOne := by
  simp [thetaPinnedMeanProjection, thetaPinnedMeanCLM_apply]

/-- The repaired differential pencil and the closed weighted derivative have the same source
domain. -/
theorem thetaSourceDifferentialPencil_domain (z : ℂ) :
    (thetaSourceDifferentialPencil z).domain = thetaWeightedDerivative.domain := by
  rw [thetaSourceDifferentialPencil, closedGraphTransform_domain,
    thetaWeightedDerivative, closedHyperplaneInverse_domain]

/-- **Source action identity.** On its literal closed graph the repaired pencil is exactly the
closed weighted derivative plus `z` times the pinned-mean projection.  In particular this does
not replace the Xi source equation by a different compact model. -/
theorem thetaSourceDifferentialPencil_apply_weightedDerivative
    (z : ℂ) (x : (thetaSourceDifferentialPencil z).domain) :
    thetaSourceDifferentialPencil z x =
      thetaWeightedDerivative
          ⟨(x : H), by simpa [thetaSourceDifferentialPencil_domain] using x.property⟩ +
        z • thetaPinnedMeanProjection (x : H) := by
  have hxrange : (x : H) ∈ thetaCenteredSourceInverse.range := by
    simpa only [thetaSourceDifferentialPencil, closedGraphTransform_domain] using x.property
  rcases hxrange with ⟨k, hk⟩
  have hxDiff : x =
      ⟨thetaCenteredSourceInverse k,
        (thetaSourceDifferentialPencil_apply_B z k).1⟩ :=
    Subtype.ext hk.symm
  have hxA : thetaCenteredSourceInverse k ∈ thetaWeightedDerivative.domain :=
    (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective k).1
  have hxeqA :
      (⟨(x : H), by simpa [thetaSourceDifferentialPencil_domain] using x.property⟩ :
        thetaWeightedDerivative.domain) =
      ⟨thetaCenteredSourceInverse k, hxA⟩ := Subtype.ext hk.symm
  have hDiffApply := (thetaSourceDifferentialPencil_apply_B z k).2
  have hAApply := (closedHyperplaneInverse_apply_B thetaCentered
    thetaCenteredSourceInverse thetaCenteredSourceInverse_injective k).2
  have hAApply' :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ = (k : H) := by
    change closedHyperplaneInverse thetaCentered thetaCenteredSourceInverse
      ⟨thetaCenteredSourceInverse k, hxA⟩ = (k : H)
    exact hAApply
  calc
    thetaSourceDifferentialPencil z x =
        thetaSourceDifferentialPencil z
          ⟨thetaCenteredSourceInverse k,
            (thetaSourceDifferentialPencil_apply_B z k).1⟩ :=
      congrArg (thetaSourceDifferentialPencil z) hxDiff
    _ = thetaSourceDifferentialRangeMap z k := hDiffApply
    _ = (k : H) + z •
        (thetaCenteredSourceInverse k -
          pinnedMean (thetaCenteredSourceInverse k) • pinnedOne) :=
      thetaSourceDifferentialRangeMap_apply z k
    _ = thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ +
        z • thetaPinnedMeanProjection (thetaCenteredSourceInverse k) := by
      rw [hAApply', thetaPinnedMeanProjection_apply]
    _ = thetaWeightedDerivative
          ⟨(x : H), by simpa [thetaSourceDifferentialPencil_domain] using x.property⟩ +
        z • thetaPinnedMeanProjection (x : H) := by
      rw [hxeqA]
      exact congrArg (fun y : H =>
        thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ +
          z • thetaPinnedMeanProjection y) hk

/-- The reverse pinned primitive sends the normalized constant precisely to the negative centered
coordinate.  This identifies the dual channel of the source mean. -/
theorem pinnedVolterraAdjoint_pinnedOne_eq_neg_center :
    pinnedVolterraAdjoint pinnedOne = -pinnedCenter := by
  change pinnedVolterraAdjointCLM pinnedOne = -pinnedCenter
  calc
    pinnedVolterraAdjointCLM pinnedOne =
        pinnedVolterraCLM pinnedOne + pinnedVolterraAdjointCLM pinnedOne := by
      rw [pinnedVolterraCLM_pinnedOne, zero_add]
    _ = pinnedBoundaryCLM pinnedOne := by rfl
    _ = (1 / 2 : ℂ) • pinnedOne - pinnedCoordinate :=
      pinnedBoundaryCLM_pinnedOne
    _ = -pinnedCenter := by
      rw [pinnedCenter]
      module

/-- The source trace dual to the pinned mean is exactly the centered dipole.  Thus the two scalar
channels in the spectral-weight Green defect are already present in the closed graph-energy
coordinate: `mean (B k)` and `firstMoment k`. -/
theorem inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse
    (k : thetaCentered) :
    (inner ℂ pinnedOne (thetaMetricOperator (thetaCenteredSourceInverse k)) : ℂ) =
      -Complex.I * thetaCenteredDipoleTrace k := by
  have hGB : thetaMetricOperator (thetaCenteredSourceInverse k) =
      Complex.I • pinnedVolterraCLM (k : H) := by
    rw [thetaCenteredSourceInverse_eq_thetaKernelOperator]
    change (thetaMetricOperator * thetaKernelOperator) (k : H) =
      (Complex.I • pinnedVolterraCLM) (k : H)
    rw [thetaMetricOperator_mul_thetaKernelOperator]
  have hVright :
      (inner ℂ (pinnedVolterra (k : H)) pinnedOne : ℂ) =
        inner ℂ (k : H) (pinnedVolterraAdjoint pinnedOne) :=
    inner_pinnedVolterra_eq_inner_pinnedVolterraAdjoint (k : H) pinnedOne
  have hVleft :
      (inner ℂ pinnedOne (pinnedVolterraCLM (k : H)) : ℂ) =
        -inner ℂ pinnedCenter (k : H) := by
    change (inner ℂ pinnedOne (pinnedVolterra (k : H)) : ℂ) = _
    rw [← inner_conj_symm, hVright, pinnedVolterraAdjoint_pinnedOne_eq_neg_center,
      inner_neg_right, map_neg, inner_conj_symm]
  have hdipole : inner ℂ pinnedCenter (k : H) = thetaCenteredDipoleTrace k := by
    rfl
  rw [hGB, inner_smul_right, hVleft, hdipole]
  ring

/-- **One-channel hyperbolic Green factorization.** The bounded spectral weight in the literal
source pencil has a metric skew defect only through the source mean and centered dipole.  Its
Hermitian boundary form is one hyperbolic plane, hence carries exactly one negative direction
once the closed relation action is completed. -/
theorem thetaPinnedMeanProjection_metricSkew_thetaCenteredSourceInverse
    (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
      (thetaCenteredSourceInverse l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)) =
      Complex.I *
        ((starRingEnd ℂ) (pinnedMean (thetaCenteredSourceInverse k)) *
            thetaCenteredDipoleTrace l +
          pinnedMean (thetaCenteredSourceInverse l) *
            (starRingEnd ℂ) (thetaCenteredDipoleTrace k)) := by
  have hleft :
      (inner ℂ (thetaMetricOperator pinnedOne)
        (thetaCenteredSourceInverse l) : ℂ) =
        inner ℂ pinnedOne
          (thetaMetricOperator (thetaCenteredSourceInverse l)) := by
    calc
      inner ℂ (thetaMetricOperator pinnedOne) (thetaCenteredSourceInverse l) =
          inner ℂ (thetaMetricOperator.adjoint pinnedOne)
            (thetaCenteredSourceInverse l) := by rw [adjoint_thetaMetricOperator]
      _ = inner ℂ pinnedOne
          (thetaMetricOperator (thetaCenteredSourceInverse l)) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
  have hright :
      (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) pinnedOne : ℂ) =
        (starRingEnd ℂ)
          (inner ℂ pinnedOne
            (thetaMetricOperator (thetaCenteredSourceInverse k))) := by
    rw [inner_conj_symm]
  rw [thetaPinnedMeanProjection_apply, thetaPinnedMeanProjection_apply,
    map_sub, map_smul, inner_sub_left, inner_smul_left,
    inner_sub_right, inner_smul_right, hleft, hright,
    inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse k,
    inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse l]
  simp only [map_neg, map_mul, Complex.conj_I]
  ring

/-- The unperturbed closed source action is symmetric for the singular theta metric on its exact
source graph.  Thus every failure of a Pontryagin realization of `D_z` is concentrated in the
bounded pinned-mean spectral weight and its one transverse defect channel. -/
theorem thetaWeightedDerivative_metricSymmetric_on_sourceGraph
    (k l : thetaCentered)
    (hk : thetaCenteredSourceInverse k ∈ thetaWeightedDerivative.domain)
    (hl : thetaCenteredSourceInverse l ∈ thetaWeightedDerivative.domain) :
    (inner ℂ (thetaMetricOperator
        (thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hk⟩))
      (thetaCenteredSourceInverse l) : ℂ) =
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaWeightedDerivative ⟨thetaCenteredSourceInverse l, hl⟩) := by
  have hgreen := thetaCenteredSourceInverse_metricGreen k l
  have hzero := inner_pinnedBoundaryCLM_thetaCentered_eq_zero k l
  rw [hzero, mul_zero] at hgreen
  have hswap :
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) =
        inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) :=
    sub_eq_zero.mp hgreen
  have hkApply :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hk⟩ = (k : H) := by
    have h := (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective k).2
    have h' : thetaWeightedDerivative
        ⟨thetaCenteredSourceInverse k,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective k).1⟩ = (k : H) := by
      simpa only [thetaWeightedDerivative] using h
    have heq : (⟨thetaCenteredSourceInverse k, hk⟩ : thetaWeightedDerivative.domain) =
        ⟨thetaCenteredSourceInverse k,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective k).1⟩ := Subtype.ext rfl
    exact (congrArg thetaWeightedDerivative heq).trans h'
  have hlApply :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse l, hl⟩ = (l : H) := by
    have h := (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective l).2
    have h' : thetaWeightedDerivative
        ⟨thetaCenteredSourceInverse l,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective l).1⟩ = (l : H) := by
      simpa only [thetaWeightedDerivative] using h
    have heq : (⟨thetaCenteredSourceInverse l, hl⟩ : thetaWeightedDerivative.domain) =
        ⟨thetaCenteredSourceInverse l,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective l).1⟩ := Subtype.ext rfl
    exact (congrArg thetaWeightedDerivative heq).trans h'
  rw [hkApply, hlApply]
  exact hswap.symm

/-- The two scalar boundary ports are hyperbolically isotropic on the exact bounded coordinate of
the closed source pencil.  Thus this coordinate alone cannot supply its required negative square. -/
theorem thetaCentered_twoPort_isotropic (k l : thetaCentered) :
    (starRingEnd ℂ) (pinnedBoundaryInPort (k : H)) * pinnedBoundaryInPort (l : H) =
      (starRingEnd ℂ) (pinnedBoundaryOutPort (k : H)) * pinnedBoundaryOutPort (l : H) := by
  have hzero := inner_pinnedBoundaryCLM_thetaCentered_eq_zero k l
  rw [inner_pinnedBoundaryCLM_eq_twoPort_pair] at hzero
  exact sub_eq_zero.mp hzero

/-- Green identity in the literal incoming/outgoing coordinates on the closed-pencil graph. -/
theorem thetaCenteredSourceInverse_twoPortGreen (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) -
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) =
        -Complex.I *
          ((starRingEnd ℂ) (pinnedBoundaryInPort (k : H)) *
              pinnedBoundaryInPort (l : H) -
            (starRingEnd ℂ) (pinnedBoundaryOutPort (k : H)) *
              pinnedBoundaryOutPort (l : H)) := by
  rw [thetaCenteredSourceInverse_metricGreen,
    inner_pinnedBoundaryCLM_eq_twoPort_pair]

/-- On the centered coordinate, the source inverse is symmetric for the singular metric. -/
theorem thetaCenteredSourceInverse_metricSymmetric (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) =
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) := by
  apply sub_eq_zero.mp
  rw [thetaCenteredSourceInverse_metricGreen,
    inner_pinnedBoundaryCLM_thetaCentered_eq_zero]
  ring

/-- Exact parameterized Green law for the closed source-faithful differential pencil.  The
additional two terms are its required monopole correction; they are not a removable boundary
normalization. -/
theorem thetaSourceDifferentialRangeMap_metricGreen
    (z w : ℂ) (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap w l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
      -Complex.I * inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) +
        w * inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
          (thetaCenteredSourceInverse l -
            pinnedMean (thetaCenteredSourceInverse l) • pinnedOne) -
        (starRingEnd ℂ) z *
          inner ℂ (thetaMetricOperator
            (thetaCenteredSourceInverse k -
              pinnedMean (thetaCenteredSourceInverse k) • pinnedOne))
            (thetaCenteredSourceInverse l) := by
  rw [thetaSourceDifferentialRangeMap_apply,
    thetaSourceDifferentialRangeMap_apply,
    map_add, map_smul, inner_add_right, inner_smul_right,
    inner_add_left, inner_smul_left]
  linear_combination thetaCenteredSourceInverse_metricGreen k l

end

end RHTower.HedenmalmThetaSource
