import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDifferentialPencil
import GaloisForLFunctions.RHTower.HedenmalmThetaActualStageGreenBalance
import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.HedenmalmThetaMetricPencil
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

section MetricRoot

local instance : ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The positive square root of the literal singular theta metric.  This is the dense energy
coordinate for a rigged completion; it is not a bounded similarity because the metric has no
lower bound. -/
noncomputable def thetaMetricRoot : H →L[ℂ] H := CFC.sqrt thetaMetricOperator

/-- Positivity of the source metric in operator order. -/
theorem thetaMetricOperator_nonneg : (0 : H →L[ℂ] H) ≤ thetaMetricOperator :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr thetaMetricOperator_isPositive

/-- The square-root energy coordinate factors the literal metric exactly. -/
theorem thetaMetricRoot_sq : thetaMetricRoot * thetaMetricRoot = thetaMetricOperator := by
  exact CFC.sqrt_mul_sqrt_self thetaMetricOperator thetaMetricOperator_nonneg

/-- The energy coordinate is self-adjoint in the original Hilbert space. -/
theorem thetaMetricRoot_selfAdjoint :
    ContinuousLinearMap.adjoint thetaMetricRoot = thetaMetricRoot := by
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg thetaMetricOperator)

/-- The energy coordinate remains injective, so it cannot erase a literal source fibre. -/
theorem thetaMetricRoot_injective : Function.Injective thetaMetricRoot := by
  intro x y hxy
  apply RHTower.thetaMetricOperator_injective
  rw [← thetaMetricRoot_sq]
  change thetaMetricRoot (thetaMetricRoot x) = thetaMetricRoot (thetaMetricRoot y)
  exact congrArg thetaMetricRoot hxy

/-- The energy-coordinate image is dense.  It therefore realizes the metric completion without
changing the ambient Hilbert carrier. -/
theorem thetaMetricRoot_dense_range : Dense (thetaMetricRoot.range : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  rw [thetaMetricRoot.orthogonal_range, thetaMetricRoot_selfAdjoint]
  exact LinearMap.ker_eq_bot.mpr thetaMetricRoot_injective

/-- The old singular Green pairing is exactly the ordinary Hilbert pairing after the energy
coordinate. -/
theorem thetaMetricRoot_energy (f g : H) :
    inner ℂ (thetaMetricRoot f) (thetaMetricRoot g) =
      inner ℂ (thetaMetricOperator f) g := by
  rw [← ContinuousLinearMap.adjoint_inner_left, thetaMetricRoot_selfAdjoint]
  change inner ℂ ((thetaMetricRoot * thetaMetricRoot) f) g = _
  rw [thetaMetricRoot_sq]

end MetricRoot

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

/-- The literal primitive coordinate of the closed boundary relation. -/
def thetaSourceDifferentialBoundarySourceProjection (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] H :=
  (ContinuousLinearMap.fst ℂ H H).comp
    ((ContinuousLinearMap.fst ℂ (H × H) (ℂ × ℂ)).comp
      (thetaSourceDifferentialBoundaryRelation z).subtypeL)

/-- The source leg of the closed boundary relation, realized in the dense square-root energy
coordinate. -/
def thetaSourceDifferentialBoundaryEnergyEmbedding (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] H :=
  thetaMetricRoot.comp (thetaSourceDifferentialBoundarySourceProjection z)

/-- The differential leg of the closed boundary relation in the same energy coordinate. -/
def thetaSourceDifferentialBoundaryEnergyReadout (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] H :=
  thetaMetricRoot.comp
    ((ContinuousLinearMap.snd ℂ H H).comp
      ((ContinuousLinearMap.fst ℂ (H × H) (ℂ × ℂ)).comp
        (thetaSourceDifferentialBoundaryRelation z).subtypeL))

/-- The canonical point of the closed boundary relation corresponding to a literal centered
source vector. -/
def thetaSourceDifferentialBoundaryCoordinateElement (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryRelation z :=
  ⟨thetaSourceDifferentialBoundaryCoordinate z k, ⟨k, rfl⟩⟩

theorem thetaSourceDifferentialBoundarySourceProjection_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundarySourceProjection z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      thetaCenteredSourceInverse k := by
  simp [thetaSourceDifferentialBoundarySourceProjection,
    thetaSourceDifferentialBoundaryCoordinateElement,
    thetaSourceDifferentialBoundaryCoordinate_apply]

theorem thetaSourceDifferentialBoundaryEnergyEmbedding_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryEnergyEmbedding z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      thetaMetricRoot (thetaCenteredSourceInverse k) := by
  simp [thetaSourceDifferentialBoundaryEnergyEmbedding,
    thetaSourceDifferentialBoundarySourceProjection_apply]

theorem thetaSourceDifferentialBoundaryEnergyReadout_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryEnergyReadout z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      thetaMetricRoot (thetaSourceDifferentialRangeMap z k) := by
  simp [thetaSourceDifferentialBoundaryEnergyReadout,
    thetaSourceDifferentialBoundaryCoordinateElement,
    thetaSourceDifferentialBoundaryCoordinate_apply]

/-- The closed relation retains its source coordinate injectively. -/
theorem thetaSourceDifferentialBoundarySourceProjection_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundarySourceProjection z) := by
  intro r s hrs
  apply Subtype.ext
  have hrs' : r.1.1.1 = s.1.1.1 := by
    simpa [thetaSourceDifferentialBoundarySourceProjection] using hrs
  obtain ⟨k, hk⟩ := (thetaSourceDifferentialBoundaryRelation_mem_iff z r).mp r.property
  obtain ⟨l, hl⟩ := (thetaSourceDifferentialBoundaryRelation_mem_iff z s).mp s.property
  have hsource : thetaCenteredSourceInverse k = thetaCenteredSourceInverse l := by
    calc
      thetaCenteredSourceInverse k = r.1.1.1 := by
        have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.1) hk
        simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h
      _ = s.1.1.1 := hrs'
      _ = thetaCenteredSourceInverse l := by
        have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.1) hl
        simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h.symm
  have hkl : k = l := thetaCenteredSourceInverse_injective hsource
  calc
    (r : ((H × H) × (ℂ × ℂ))) = thetaSourceDifferentialBoundaryCoordinate z k := hk.symm
    _ = thetaSourceDifferentialBoundaryCoordinate z l := by rw [hkl]
    _ = s := hl

/-- The dense literal source range is retained by the closed-relation source projection. -/
theorem thetaSourceDifferentialBoundarySourceProjection_dense_range (z : ℂ) :
    Dense ((thetaSourceDifferentialBoundarySourceProjection z).range : Set H) := by
  apply thetaCenteredSourceInverse_dense_range.mono
  rintro x ⟨k, rfl⟩
  refine ⟨thetaSourceDifferentialBoundaryCoordinateElement z k, ?_⟩
  exact thetaSourceDifferentialBoundarySourceProjection_apply z k

/-- The square-root energy embedding of the closed relation is injective: it preserves every
literal source fibre while replacing the singular metric by ordinary Hilbert energy. -/
theorem thetaSourceDifferentialBoundaryEnergyEmbedding_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundaryEnergyEmbedding z) := by
  intro r s hrs
  apply thetaSourceDifferentialBoundarySourceProjection_injective z
  apply thetaMetricRoot_injective
  simpa [thetaSourceDifferentialBoundaryEnergyEmbedding] using hrs

/-- The energy embedding of the closed relation has dense range.  Together with the relation's
closedness, this supplies the source-faithful rigged Hilbert test embedding. -/
theorem thetaSourceDifferentialBoundaryEnergyEmbedding_dense_range (z : ℂ) :
    Dense ((thetaSourceDifferentialBoundaryEnergyEmbedding z).range : Set H) := by
  change DenseRange (fun r => thetaMetricRoot
    (thetaSourceDifferentialBoundarySourceProjection z r))
  exact DenseRange.comp thetaMetricRoot_dense_range
    (thetaSourceDifferentialBoundarySourceProjection_dense_range z)
    thetaMetricRoot.continuous

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

/-- Hermitian hyperbolic form on the source mean--dipole boundary pair. -/
def thetaMonopoleDipoleHyperbolicForm (u v : ℂ × ℂ) : ℂ :=
  (starRingEnd ℂ) u.1 * v.2 + v.1 * (starRingEnd ℂ) u.2

/-- Diagonal coordinates split the boundary form into one positive and one negative complex
line.  This is the exact rank-one negative channel required by the singular completion. -/
theorem thetaMonopoleDipoleHyperbolicForm_diagonal
    (m d m' d' : ℂ) :
    thetaMonopoleDipoleHyperbolicForm (m, d) (m', d') =
      (1 / 2 : ℂ) *
        ((starRingEnd ℂ) (m + d) * (m' + d') -
          (starRingEnd ℂ) (m - d) * (m' - d')) := by
  simp only [thetaMonopoleDipoleHyperbolicForm, map_add, map_sub]
  ring

theorem thetaMonopoleDipoleHyperbolicForm_positive_unit :
    thetaMonopoleDipoleHyperbolicForm ((1 : ℂ), 1) (1, 1) = 2 := by
  norm_num [thetaMonopoleDipoleHyperbolicForm]

theorem thetaMonopoleDipoleHyperbolicForm_negative_unit :
    thetaMonopoleDipoleHyperbolicForm ((1 : ℂ), -1) (1, -1) = -2 := by
  norm_num [thetaMonopoleDipoleHyperbolicForm]

/-- The spectral-weight Green defect is exactly the hyperbolic mean--dipole boundary form of
the closed source relation. -/
theorem thetaPinnedMeanProjection_metricSkew_eq_hyperbolic
    (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
      (thetaCenteredSourceInverse l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)) =
      Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l) := by
  simpa only [thetaMonopoleDipoleHyperbolicForm] using
    thetaPinnedMeanProjection_metricSkew_thetaCenteredSourceInverse k l

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

/-- Conjugate spectral parameters expose only the one hyperbolic boundary plane.  The full
closed source relation therefore has an exact Green law compatible with Schwarz reflection while
retaining its literal `XiC` vertical fibre. -/
theorem thetaSourceDifferentialRangeMap_metricGreen_conj
    (z : ℂ) (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
  have hgreen := thetaSourceDifferentialRangeMap_metricGreen z (starRingEnd ℂ z) k l
  have hzero := inner_pinnedBoundaryCLM_thetaCentered_eq_zero k l
  rw [hzero, mul_zero, zero_add,
    ← thetaPinnedMeanProjection_apply (thetaCenteredSourceInverse l),
    ← thetaPinnedMeanProjection_apply (thetaCenteredSourceInverse k)] at hgreen
  have hskew := thetaPinnedMeanProjection_metricSkew_eq_hyperbolic k l
  calc
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
        (starRingEnd ℂ) z *
            inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
              (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)) -
          (starRingEnd ℂ) z *
            inner ℂ (thetaMetricOperator
              (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
              (thetaCenteredSourceInverse l) := hgreen
    _ = -(starRingEnd ℂ z *
        ((inner ℂ (thetaMetricOperator
            (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
          (thetaCenteredSourceInverse l) : ℂ) -
          inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
            (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)))) := by ring
    _ = -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
      rw [hskew]
      ring

/-- The exact conjugate-parameter Green law on the closed, dense energy test relation.  Both
legs remain the literal source primitive and differential coordinates, while the right-hand side
is the single hyperbolic monopole--dipole boundary plane. -/
theorem thetaSourceDifferentialBoundaryEnergy_green_conj
    (z : ℂ) (k l : thetaCentered) :
    (inner ℂ
        (thetaSourceDifferentialBoundaryEnergyEmbedding z
          (thetaSourceDifferentialBoundaryCoordinateElement z k))
        (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z)
          (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l)) : ℂ) -
      inner ℂ
        (thetaSourceDifferentialBoundaryEnergyReadout z
          (thetaSourceDifferentialBoundaryCoordinateElement z k))
        (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z)
          (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l)) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
  rw [thetaSourceDifferentialBoundaryEnergyEmbedding_apply,
    thetaSourceDifferentialBoundaryEnergyReadout_apply,
    thetaSourceDifferentialBoundaryEnergyReadout_apply,
    thetaSourceDifferentialBoundaryEnergyEmbedding_apply,
    thetaMetricRoot_energy, thetaMetricRoot_energy]
  exact thetaSourceDifferentialRangeMap_metricGreen_conj z k l

end

end RHTower.HedenmalmThetaSource
