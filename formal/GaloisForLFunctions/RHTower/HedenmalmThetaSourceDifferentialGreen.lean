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

/-- The complete monopole--dipole boundary record, read directly from an arbitrary element of
the closed source relation. -/
def thetaSourceDifferentialBoundaryPort (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℂ (H × H) (ℂ × ℂ)).comp
    (thetaSourceDifferentialBoundaryRelation z).subtypeL

theorem thetaSourceDifferentialBoundaryPort_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryPort z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k) := by
  simp [thetaSourceDifferentialBoundaryPort,
    thetaSourceDifferentialBoundaryCoordinateElement,
    thetaSourceDifferentialBoundaryCoordinate_apply]

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

/-- The Riesz map of the energy relation into its continuous complex dual. It is necessarily
conjugate-linear in the ambient Hilbert coordinate: complex Hilbert spaces embed in the
continuous anti-dual, rather than linearly in the ordinary dual. -/
noncomputable def thetaSourceDifferentialBoundaryEnergyAntiDualLM (z : ℂ) :
    H →ₛₗ[starRingEnd ℂ]
      (thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ) where
  toFun := fun h => (innerSL ℂ h).comp
    (thetaSourceDifferentialBoundaryEnergyEmbedding z)
  map_add' := by
    intro x y
    apply ContinuousLinearMap.ext
    intro e
    change inner ℂ (x + y) (thetaSourceDifferentialBoundaryEnergyEmbedding z e) =
      inner ℂ x (thetaSourceDifferentialBoundaryEnergyEmbedding z e) +
        inner ℂ y (thetaSourceDifferentialBoundaryEnergyEmbedding z e)
    rw [inner_add_left]
  map_smul' := by
    intro q x
    apply ContinuousLinearMap.ext
    intro e
    change inner ℂ (q • x) (thetaSourceDifferentialBoundaryEnergyEmbedding z e) =
      (starRingEnd ℂ q) * inner ℂ x (thetaSourceDifferentialBoundaryEnergyEmbedding z e)
    rw [inner_smul_left]

/-- Continuous anti-dual realization of the literal dense energy embedding. -/
noncomputable def thetaSourceDifferentialBoundaryEnergyAntiDual (z : ℂ) :
    H →SL[starRingEnd ℂ]
      (thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ) :=
  @LinearMap.mkContinuous ℂ ℂ H
    (thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ) _ _ _ _ _ _
    (starRingEnd ℂ) (thetaSourceDifferentialBoundaryEnergyAntiDualLM z)
    ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ (by
      intro h
      change ‖(innerSL ℂ h).comp (thetaSourceDifferentialBoundaryEnergyEmbedding z)‖ ≤
        ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖h‖
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro e
      change ‖inner ℂ h (thetaSourceDifferentialBoundaryEnergyEmbedding z e)‖ ≤
        ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖h‖ * ‖e‖
      calc
        ‖inner ℂ h (thetaSourceDifferentialBoundaryEnergyEmbedding z e)‖ ≤
            ‖h‖ * ‖thetaSourceDifferentialBoundaryEnergyEmbedding z e‖ :=
          norm_inner_le_norm h (thetaSourceDifferentialBoundaryEnergyEmbedding z e)
        _ ≤ ‖h‖ * (‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖e‖) := by
          gcongr
          exact (thetaSourceDifferentialBoundaryEnergyEmbedding z).le_opNorm e
        _ = ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖h‖ * ‖e‖ := by ring)

@[simp] theorem thetaSourceDifferentialBoundaryEnergyAntiDual_apply
    (z : ℂ) (h : H) (e : thetaSourceDifferentialBoundaryRelation z) :
    thetaSourceDifferentialBoundaryEnergyAntiDual z h e =
      inner ℂ h (thetaSourceDifferentialBoundaryEnergyEmbedding z e) := rfl

/-- Dense energy range makes the anti-dual embedding injective. -/
theorem thetaSourceDifferentialBoundaryEnergyAntiDual_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundaryEnergyAntiDual z) := by
  intro x y hxy
  apply (thetaSourceDifferentialBoundaryEnergyEmbedding_dense_range z).eq_of_inner_left ℂ
  rintro _ ⟨e, rfl⟩
  have he := congrArg (fun φ : thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ => φ e) hxy
  simpa using he

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

/-- Literal conjugation on the source monopole--dipole boundary plane. -/
def thetaMonopoleDipoleBoundaryConj (u : ℂ × ℂ) : ℂ × ℂ :=
  (-(starRingEnd ℂ u.1), (starRingEnd ℂ u.2))

/-- The Hodge operator forced by the source boundary reflection and exchange of the two
hyperbolic channels. -/
def thetaMonopoleDipoleHodge (u : ℂ × ℂ) : ℂ × ℂ :=
  (-(starRingEnd ℂ u.2), (starRingEnd ℂ u.1))

/-- The source boundary Hodge operator is anti-complex with square `-1`. -/
theorem thetaMonopoleDipoleHodge_sq (u : ℂ × ℂ) :
    thetaMonopoleDipoleHodge (thetaMonopoleDipoleHodge u) = -u := by
  ext <;> simp [thetaMonopoleDipoleHodge]

theorem thetaMonopoleDipoleHodge_add (u v : ℂ × ℂ) :
    thetaMonopoleDipoleHodge (u + v) =
      thetaMonopoleDipoleHodge u + thetaMonopoleDipoleHodge v := by
  ext <;> simp [thetaMonopoleDipoleHodge, map_add, add_comm]

theorem thetaMonopoleDipoleHodge_smul (c : ℂ) (u : ℂ × ℂ) :
    thetaMonopoleDipoleHodge (c • u) =
      (starRingEnd ℂ c) • thetaMonopoleDipoleHodge u := by
  ext <;> simp [thetaMonopoleDipoleHodge, smul_eq_mul]

/-- The source boundary Hodge operator as a conjugate-semilinear map. -/
def thetaMonopoleDipoleHodgeSLM :
    (ℂ × ℂ) →ₛₗ[starRingEnd ℂ] (ℂ × ℂ) where
  toFun := thetaMonopoleDipoleHodge
  map_add' := thetaMonopoleDipoleHodge_add
  map_smul' := thetaMonopoleDipoleHodge_smul

/-- Bilinear boundary cup form obtained from the literal reflected hyperbolic Green form. -/
def thetaMonopoleDipoleCup (u v : ℂ × ℂ) : ℂ :=
  -thetaMonopoleDipoleHyperbolicForm (thetaMonopoleDipoleBoundaryConj u) v

/-- The reflected hyperbolic boundary plane has a positive Hodge diagonal. -/
theorem thetaMonopoleDipoleCup_hodge (u : ℂ × ℂ) :
    thetaMonopoleDipoleCup u (thetaMonopoleDipoleHodge u) =
      (Complex.normSq u.1 : ℂ) + (Complex.normSq u.2 : ℂ) := by
  simp only [thetaMonopoleDipoleCup, thetaMonopoleDipoleHyperbolicForm,
    thetaMonopoleDipoleBoundaryConj, thetaMonopoleDipoleHodge, map_neg,
    starRingEnd_self_apply, neg_mul]
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  ring

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

/-- The same Green defect expressed in the only complex-linear dual category available to the
energy relation: the first term is the conjugate of an anti-dual evaluation, while the second
is a reflected anti-dual evaluation. -/
theorem thetaSourceDifferentialBoundaryEnergyAntiDual_green_conj
    (z : ℂ) (k l : thetaCentered) :
    (starRingEnd ℂ)
        (thetaSourceDifferentialBoundaryEnergyAntiDual z
          (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z)
            (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l))
          (thetaSourceDifferentialBoundaryCoordinateElement z k)) -
      thetaSourceDifferentialBoundaryEnergyAntiDual (starRingEnd ℂ z)
        (thetaSourceDifferentialBoundaryEnergyReadout z
          (thetaSourceDifferentialBoundaryCoordinateElement z k))
        (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
  rw [thetaSourceDifferentialBoundaryEnergyAntiDual_apply,
    thetaSourceDifferentialBoundaryEnergyAntiDual_apply, inner_conj_symm]
  exact thetaSourceDifferentialBoundaryEnergy_green_conj z k l

/-- Universal anti-dual Green identity.  Every closed-relation element has a unique literal
source representative, so the hyperbolic boundary defect is a relation invariant rather than a
formula limited to chosen coordinates. -/
theorem thetaSourceDifferentialBoundaryEnergyAntiDual_green_conj_all
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z)
    (s : thetaSourceDifferentialBoundaryRelation (starRingEnd ℂ z)) :
    (starRingEnd ℂ)
        (thetaSourceDifferentialBoundaryEnergyAntiDual z
          (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z) s) r) -
      thetaSourceDifferentialBoundaryEnergyAntiDual (starRingEnd ℂ z)
        (thetaSourceDifferentialBoundaryEnergyReadout z r) s =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (thetaSourceDifferentialBoundaryPort z r)
        (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) := by
  obtain ⟨k, hk⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff z (r : ((H × H) × (ℂ × ℂ)))).mp r.property
  obtain ⟨l, hl⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff (starRingEnd ℂ z)
      (s : ((H × H) × (ℂ × ℂ)))).mp s.property
  have hr : r = thetaSourceDifferentialBoundaryCoordinateElement z k := by
    apply Subtype.ext
    exact hk.symm
  have hs : s = thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l := by
    apply Subtype.ext
    exact hl.symm
  rw [hr, hs, thetaSourceDifferentialBoundaryPort_apply,
    thetaSourceDifferentialBoundaryPort_apply]
  exact thetaSourceDifferentialBoundaryEnergyAntiDual_green_conj z k l

/-- Universal energy-form Green identity on the closed source relation.  Unique literal source
witnesses transport the coordinate calculation to every completed relation element. -/
theorem thetaSourceDifferentialBoundaryEnergy_green_conj_all
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z)
    (s : thetaSourceDifferentialBoundaryRelation (starRingEnd ℂ z)) :
    (inner ℂ
        (thetaSourceDifferentialBoundaryEnergyEmbedding z r)
        (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z) s) : ℂ) -
      inner ℂ
        (thetaSourceDifferentialBoundaryEnergyReadout z r)
        (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z) s) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (thetaSourceDifferentialBoundaryPort z r)
        (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) := by
  obtain ⟨k, hk⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff z
      (r : ((H × H) × (ℂ × ℂ)))).mp r.property
  obtain ⟨l, hl⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff (starRingEnd ℂ z)
      (s : ((H × H) × (ℂ × ℂ)))).mp s.property
  have hr : r = thetaSourceDifferentialBoundaryCoordinateElement z k := by
    apply Subtype.ext
    exact hk.symm
  have hs : s = thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l := by
    apply Subtype.ext
    exact hl.symm
  rw [hr, hs, thetaSourceDifferentialBoundaryPort_apply,
    thetaSourceDifferentialBoundaryPort_apply]
  exact thetaSourceDifferentialBoundaryEnergy_green_conj z k l

/-- The completed source embedding retains both the literal energy vector and its complete
monopole--dipole boundary record. -/
def thetaSourceDifferentialBoundaryAugmentedEmbedding (z : ℂ)
    (r : thetaSourceDifferentialBoundaryRelation z) : H × (ℂ × ℂ) :=
  (thetaSourceDifferentialBoundaryEnergyEmbedding z r,
    thetaSourceDifferentialBoundaryPort z r)

/-- The unique scalar boundary flow which cancels the exact Green defect of the closed source
relation. -/
def thetaSourceDifferentialBoundaryAugmentedReadout (z : ℂ)
    (r : thetaSourceDifferentialBoundaryRelation z) : H × (ℂ × ℂ) :=
  (thetaSourceDifferentialBoundaryEnergyReadout z r,
    (Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)

/-- Energy plus the source monopole--dipole Green form on the augmented carrier. -/
def thetaSourceDifferentialBoundaryAugmentedGreenPair
    (x y : H × (ℂ × ℂ)) : ℂ :=
  inner ℂ x.1 y.1 + thetaMonopoleDipoleHyperbolicForm x.2 y.2

/-- The augmented closed source relation satisfies an exact conjugate-parameter Green law.
The coefficient `I / 2` is forced: its boundary skew term cancels the literal rank-two defect. -/
theorem thetaSourceDifferentialBoundaryAugmented_green_conj
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z)
    (s : thetaSourceDifferentialBoundaryRelation (starRingEnd ℂ z)) :
    thetaSourceDifferentialBoundaryAugmentedGreenPair
        (thetaSourceDifferentialBoundaryAugmentedEmbedding z r)
        (thetaSourceDifferentialBoundaryAugmentedReadout (starRingEnd ℂ z) s) =
      thetaSourceDifferentialBoundaryAugmentedGreenPair
        (thetaSourceDifferentialBoundaryAugmentedReadout z r)
        (thetaSourceDifferentialBoundaryAugmentedEmbedding (starRingEnd ℂ z) s) := by
  unfold thetaSourceDifferentialBoundaryAugmentedGreenPair
    thetaSourceDifferentialBoundaryAugmentedEmbedding
    thetaSourceDifferentialBoundaryAugmentedReadout
  dsimp only
  have hgreen := thetaSourceDifferentialBoundaryEnergy_green_conj_all z r s
  have hboundary :
      thetaMonopoleDipoleHyperbolicForm
          (thetaSourceDifferentialBoundaryPort z r)
          ((Complex.I / 2 * (starRingEnd ℂ z)) •
            thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) -
        thetaMonopoleDipoleHyperbolicForm
          ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)
          (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) =
        Complex.I * (starRingEnd ℂ z) *
          thetaMonopoleDipoleHyperbolicForm
            (thetaSourceDifferentialBoundaryPort z r)
            (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) := by
    simp only [thetaMonopoleDipoleHyperbolicForm, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, map_mul, map_div₀, Complex.conj_I, map_ofNat]
    ring
  calc
    _ =
        (inner ℂ (thetaSourceDifferentialBoundaryEnergyEmbedding z r)
            (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z) s) -
          inner ℂ (thetaSourceDifferentialBoundaryEnergyReadout z r)
            (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z) s)) +
          (thetaMonopoleDipoleHyperbolicForm
              (thetaSourceDifferentialBoundaryPort z r)
              ((Complex.I / 2 * (starRingEnd ℂ z)) •
                thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) -
            thetaMonopoleDipoleHyperbolicForm
              ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)
              (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) +
            (inner ℂ (thetaSourceDifferentialBoundaryEnergyReadout z r)
                (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z) s) +
              thetaMonopoleDipoleHyperbolicForm
                ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)
                (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) := by ring
    _ = _ := by rw [hgreen, hboundary]; ring

/-- The finite monopole--dipole correction is represented in an ordinary Hilbert product by
the bounded channel exchange.  This is the fundamental symmetry which turns the exact Green
law into a bounded adjoint equation. -/
def thetaMonopoleDipoleFundamentalSymmetry :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem thetaMonopoleDipoleFundamentalSymmetry_apply (u : ℂ × ℂ) :
    thetaMonopoleDipoleFundamentalSymmetry u = (u.2, u.1) := rfl

/-- The hyperbolic Green form is the Hilbert inner product twisted by its fundamental
symmetry. -/
theorem thetaMonopoleDipoleHyperbolicForm_eq_inner_fundamentalSymmetry
    (u v : ℂ × ℂ) :
    thetaMonopoleDipoleHyperbolicForm u v =
      inner ℂ (thetaMonopoleDipoleFundamentalSymmetry u) v := by
  rw [thetaMonopoleDipoleFundamentalSymmetry_apply, WithLp.prod_inner_apply]
  change (starRingEnd ℂ) u.1 * v.2 + v.1 * (starRingEnd ℂ) u.2 =
    (starRingEnd ℂ) u.2 * v.1 + (starRingEnd ℂ) u.1 * v.2
  ring

theorem thetaMonopoleDipoleFundamentalSymmetry_isSymmetric
    (u v : ℂ × ℂ) :
    inner ℂ (thetaMonopoleDipoleFundamentalSymmetry u) v =
      inner ℂ u (thetaMonopoleDipoleFundamentalSymmetry v) := by
  rw [thetaMonopoleDipoleFundamentalSymmetry_apply,
    thetaMonopoleDipoleFundamentalSymmetry_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  ring

theorem thetaMonopoleDipoleFundamentalSymmetry_sq (u : ℂ × ℂ) :
    thetaMonopoleDipoleFundamentalSymmetry
      (thetaMonopoleDipoleFundamentalSymmetry u) = u := by
  ext <;> rfl

/-- The Hilbert fundamental symmetry on energy plus the complete finite source boundary. -/
def thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry :
    (H × (ℂ × ℂ)) →L[ℂ] (H × (ℂ × ℂ)) :=
  (ContinuousLinearMap.fst ℂ H (ℂ × ℂ)).prod
    (thetaMonopoleDipoleFundamentalSymmetry.comp
      (ContinuousLinearMap.snd ℂ H (ℂ × ℂ)))

theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply
    (x : H × (ℂ × ℂ)) :
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x =
      (x.1, (x.2.2, x.2.1)) := rfl

theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_isSymmetric
    (x y : H × (ℂ × ℂ)) :
    inner ℂ (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x) y =
      inner ℂ x (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry y) := by
  rw [thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply,
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  congr 1
  exact thetaMonopoleDipoleFundamentalSymmetry_isSymmetric _ _

/-- The completed Green pairing is an ordinary Hilbert pairing after the finite fundamental
symmetry. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenPair_eq_inner_fundamentalSymmetry
    (x y : H × (ℂ × ℂ)) :
    thetaSourceDifferentialBoundaryAugmentedGreenPair x y =
      inner ℂ (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x) y := by
  rw [thetaSourceDifferentialBoundaryAugmentedGreenPair,
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply,
    WithLp.prod_inner_apply,
    ← thetaMonopoleDipoleHyperbolicForm_eq_inner_fundamentalSymmetry]

/-- Hermitian symmetry of the completed Green pairing. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenPair_conj_symm
    (x y : H × (ℂ × ℂ)) :
    thetaSourceDifferentialBoundaryAugmentedGreenPair x y =
      (starRingEnd ℂ) (thetaSourceDifferentialBoundaryAugmentedGreenPair y x) := by
  simp only [thetaSourceDifferentialBoundaryAugmentedGreenPair,
    thetaMonopoleDipoleHyperbolicForm, map_add, map_mul,
    starRingEnd_self_apply, inner_conj_symm]
  ring

/-- Bounded source embedding of the completed Green carrier. -/
def thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] (H × (ℂ × ℂ)) :=
  (thetaSourceDifferentialBoundaryEnergyEmbedding z).prod
    (thetaSourceDifferentialBoundaryPort z)

theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_apply
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z) :
    thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z r =
      thetaSourceDifferentialBoundaryAugmentedEmbedding z r := by
  rfl

/-- Bounded source readout after the unique finite boundary flow. -/
def thetaSourceDifferentialBoundaryAugmentedReadoutCLM (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] (H × (ℂ × ℂ)) :=
  (thetaSourceDifferentialBoundaryEnergyReadout z).prod
    ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z)

theorem thetaSourceDifferentialBoundaryAugmentedReadoutCLM_apply
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z) :
    thetaSourceDifferentialBoundaryAugmentedReadoutCLM z r =
      thetaSourceDifferentialBoundaryAugmentedReadout z r := by
  rfl

/-- Exact bounded adjoint intertwining of the literal source embedding and differential
readout.  The remaining maximality problem is now precisely whether this bounded intertwining
extends to the closed unbounded graph, not a missing finite Green correction. -/
theorem thetaSourceDifferentialBoundaryAugmented_adjoint_intertwining (z : ℂ) :
    (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z).adjoint.comp
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z))) =
    (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z).adjoint.comp
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z))) := by
  apply ContinuousLinearMap.ext
  intro s
  apply ext_inner_right ℂ
  intro r
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z).adjoint_inner_left,
    (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z).adjoint_inner_left]
  have hgreen := thetaSourceDifferentialBoundaryAugmented_green_conj z r s
  rw [← thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_apply,
    ← thetaSourceDifferentialBoundaryAugmentedReadoutCLM_apply,
    ← thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_apply,
    ← thetaSourceDifferentialBoundaryAugmentedReadoutCLM_apply] at hgreen
  calc
    inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) s))
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z r) =
      thetaSourceDifferentialBoundaryAugmentedGreenPair
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) s)
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z r) := by
          rw [thetaSourceDifferentialBoundaryAugmentedGreenPair_eq_inner_fundamentalSymmetry]
    _ = (starRingEnd ℂ)
        (thetaSourceDifferentialBoundaryAugmentedGreenPair
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z r)
          (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) s)) :=
      (thetaSourceDifferentialBoundaryAugmentedGreenPair_conj_symm _ _).symm
    _ = (starRingEnd ℂ)
        (thetaSourceDifferentialBoundaryAugmentedGreenPair
          (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z r)
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z) s)) := by
      rw [hgreen]
    _ = thetaSourceDifferentialBoundaryAugmentedGreenPair
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z) s)
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z r) :=
      (thetaSourceDifferentialBoundaryAugmentedGreenPair_conj_symm _ _)
    _ = inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z) s))
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z r) := by
          rw [thetaSourceDifferentialBoundaryAugmentedGreenPair_eq_inner_fundamentalSymmetry]

/-! ## Literal conjugation and reflected source fibres -/

/-- Pointwise conjugation on the quantile `L²` carrier. -/
def thetaLpConj (f : H) : H :=
  ((Lp.memLp f).mono
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun _ => by simp)).toLp
      (fun t => (starRingEnd ℂ) ((f : ℝ → ℂ) t))

theorem thetaLpConj_coeFn_ae (f : H) :
    ⇑(thetaLpConj f) =ᵐ[unitIntervalMeasure]
      fun t => (starRingEnd ℂ) ((f : ℝ → ℂ) t) :=
  ((Lp.memLp f).mono
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun _ => by simp)).coeFn_toLp

theorem thetaLpConj_add (f g : H) :
    thetaLpConj (f + g) = thetaLpConj f + thetaLpConj g := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (f + g), thetaLpConj_coeFn_ae f,
    thetaLpConj_coeFn_ae g, Lp.coeFn_add f g, Lp.coeFn_add (thetaLpConj f) (thetaLpConj g)]
      with t hfg hf hg hadd hout
  rw [hfg, hout, hadd]
  simp only [Pi.add_apply]
  rw [hf, hg]
  simp

theorem thetaLpConj_smul (c : ℂ) (f : H) :
    thetaLpConj (c • f) = (starRingEnd ℂ c) • thetaLpConj f := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (c • f), thetaLpConj_coeFn_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul (starRingEnd ℂ c) (thetaLpConj f)]
      with t hcf hf hin hout
  rw [hcf, hout, hin]
  simp only [Pi.smul_apply]
  rw [hf]
  simp [smul_eq_mul]

theorem thetaLpConj_involutive (f : H) : thetaLpConj (thetaLpConj f) = f := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (thetaLpConj f), thetaLpConj_coeFn_ae f]
      with t houter hinner
  rw [houter, hinner]
  simp

theorem thetaLpConj_zero : thetaLpConj (0 : H) = 0 := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (0 : H), Lp.coeFn_zero ℂ (2 : ENNReal)
    unitIntervalMeasure] with t hconj hzero
  rw [hconj, hzero]
  simp

theorem thetaLpConj_injective : Function.Injective thetaLpConj := by
  intro f g hfg
  have h := congrArg thetaLpConj hfg
  rw [thetaLpConj_involutive, thetaLpConj_involutive] at h
  exact h

/-- Pointwise conjugation is antiunitary for the literal `L²` inner product.  This is the
positive ingredient needed to turn the real reflection into a doubled Hodge star. -/
theorem inner_thetaLpConj (f g : H) :
    inner ℂ (thetaLpConj f) (thetaLpConj g) =
      (starRingEnd ℂ) (inner ℂ f g) := by
  rw [MeasureTheory.L2.inner_def]
  change (∫ t : ℝ, inner ℂ ((thetaLpConj f : H) t) ((thetaLpConj g : H) t)
      ∂unitIntervalMeasure) =
    (starRingEnd ℂ) (∫ t : ℝ, inner ℂ ((f : H) t) ((g : H) t) ∂unitIntervalMeasure)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [thetaLpConj_coeFn_ae f, thetaLpConj_coeFn_ae g] with t hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_self_apply]

/-- The literal positive theta metric is real, hence commutes with pointwise conjugation. -/
theorem thetaMetricOperator_thetaLpConj (f : H) :
    thetaMetricOperator (thetaLpConj f) = thetaLpConj (thetaMetricOperator f) := by
  apply Lp.ext
  filter_upwards
      [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le (thetaLpConj f),
       thetaLpConj_coeFn_ae (thetaMetricOperator f),
       metricOperator_coeFn thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le f,
       thetaLpConj_coeFn_ae f] with t hleft hright hmetric hconj
  change
    ((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
      (thetaLpConj f) : H) t =
      (thetaLpConj
        ((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
          f) : H) t
  change
    (thetaLpConj
      ((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
        f) : H) t =
      (starRingEnd ℂ)
        (((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
          f : H) t) at hright
  rw [hleft, hright, hmetric, hconj, map_mul, starRingEnd_metricSymbol]

/-- Doubling the literal real reflection gives an anti-linear almost-complex source action.
Unlike pointwise conjugation itself, its square is `-1`. -/
def thetaDoubledHodge (u : H × H) : H × H :=
  (-thetaLpConj u.2, thetaLpConj u.1)

theorem thetaDoubledHodge_add (u v : H × H) :
    thetaDoubledHodge (u + v) = thetaDoubledHodge u + thetaDoubledHodge v := by
  ext <;> simp [thetaDoubledHodge, thetaLpConj_add, add_comm]

theorem thetaDoubledHodge_smul (c : ℂ) (u : H × H) :
    thetaDoubledHodge (c • u) = (starRingEnd ℂ c) • thetaDoubledHodge u := by
  ext <;> simp [thetaDoubledHodge, thetaLpConj_smul]

def thetaDoubledHodgeSLM :
    (H × H) →ₛₗ[starRingEnd ℂ] (H × H) where
  toFun := thetaDoubledHodge
  map_add' := thetaDoubledHodge_add
  map_smul' := thetaDoubledHodge_smul

theorem thetaDoubledHodge_sq (u : H × H) :
    thetaDoubledHodge (thetaDoubledHodge u) = -u := by
  have hneg (f : H) : thetaLpConj (-f) = -thetaLpConj f := by
    simpa using thetaLpConj_smul (-1 : ℂ) f
  ext <;> simp [thetaDoubledHodge, hneg, thetaLpConj_involutive]

/-- The bilinear cup candidate induced by source conjugation on the doubled carrier. -/
def thetaDoubledCup (u v : H × H) : ℂ :=
  inner ℂ (thetaLpConj u.1) v.2 - inner ℂ (thetaLpConj u.2) v.1

/-- Evaluating the doubled cup form against the doubled Hodge star is the sum of two literal
Hilbert energies. -/
theorem thetaDoubledCup_hodge (u : H × H) :
    thetaDoubledCup u (thetaDoubledHodge u) =
      inner ℂ (thetaLpConj u.1) (thetaLpConj u.1) +
        inner ℂ (thetaLpConj u.2) (thetaLpConj u.2) := by
  simp only [thetaDoubledCup, thetaDoubledHodge, inner_neg_right, sub_neg_eq_add]

/-- The source-plus-boundary carrier combines the doubled literal source with its exact
monopole--dipole Green completion. -/
def thetaSourceGreenHodge (r : (H × H) × (ℂ × ℂ)) : (H × H) × (ℂ × ℂ) :=
  (thetaDoubledHodge r.1, thetaMonopoleDipoleHodge r.2)

theorem thetaSourceGreenHodge_add (r s : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenHodge (r + s) = thetaSourceGreenHodge r + thetaSourceGreenHodge s := by
  ext <;> simp [thetaSourceGreenHodge, thetaDoubledHodge_add,
    thetaMonopoleDipoleHodge_add]

theorem thetaSourceGreenHodge_smul (c : ℂ) (r : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenHodge (c • r) =
      (starRingEnd ℂ c) • thetaSourceGreenHodge r := by
  ext <;> simp [thetaSourceGreenHodge, thetaDoubledHodge_smul,
    thetaMonopoleDipoleHodge_smul]

/-- The completed source Hodge star is conjugate-semilinear. -/
def thetaSourceGreenHodgeSLM :
    ((H × H) × (ℂ × ℂ)) →ₛₗ[starRingEnd ℂ] ((H × H) × (ℂ × ℂ)) where
  toFun := thetaSourceGreenHodge
  map_add' := thetaSourceGreenHodge_add
  map_smul' := thetaSourceGreenHodge_smul

/-- The source-plus-boundary Hodge star has square `-1`. -/
theorem thetaSourceGreenHodge_sq (r : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenHodge (thetaSourceGreenHodge r) = -r := by
  ext <;> simp [thetaSourceGreenHodge, thetaDoubledHodge_sq,
    thetaMonopoleDipoleHodge_sq]

/-- Bilinear cup form on the completed source carrier. -/
def thetaSourceGreenCup (r s : (H × H) × (ℂ × ℂ)) : ℂ :=
  thetaDoubledCup r.1 s.1 + thetaMonopoleDipoleCup r.2 s.2

/-- The completed source cup has the explicit positive Hodge diagonal. -/
theorem thetaSourceGreenCup_hodge (r : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenCup r (thetaSourceGreenHodge r) =
      inner ℂ (thetaLpConj r.1.1) (thetaLpConj r.1.1) +
        inner ℂ (thetaLpConj r.1.2) (thetaLpConj r.1.2) +
          (Complex.normSq r.2.1 : ℂ) + (Complex.normSq r.2.2 : ℂ) := by
  rw [thetaSourceGreenCup, thetaSourceGreenHodge,
    thetaDoubledCup_hodge, thetaMonopoleDipoleCup_hodge]
  ring

theorem pinnedMean_thetaLpConj (f : H) :
    pinnedMean (thetaLpConj f) = (starRingEnd ℂ) (pinnedMean f) := by
  symm
  rw [pinnedMean, ← integral_conj]
  apply integral_congr_ae
  exact (thetaLpConj_coeFn_ae f).symm

theorem pinnedPrefix_thetaLpConj (f : H) (t : ℝ) :
    pinnedPrefix (thetaLpConj f) t = (starRingEnd ℂ) (pinnedPrefix f t) := by
  symm
  rw [pinnedPrefix, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [thetaLpConj_coeFn_ae f] with u hu
  simp only [indicator_apply]
  split_ifs <;> simp [hu]

theorem pinnedVolterraFun_thetaLpConj (f : H) (t : ℝ) :
    pinnedVolterraFun (thetaLpConj f) t =
      (starRingEnd ℂ) (pinnedVolterraFun f t) := by
  change pinnedPrefix (thetaLpConj f) t - (t : ℂ) * pinnedMean (thetaLpConj f) =
    (starRingEnd ℂ) (pinnedPrefix f t - (t : ℂ) * pinnedMean f)
  rw [pinnedPrefix_thetaLpConj, pinnedMean_thetaLpConj]
  simp only [map_sub, map_mul, Complex.conj_ofReal]

/-- The literal theta source inverse anticommutes with pointwise conjugation.  The sign comes
from its intrinsic imaginary kernel factor, and is what realizes reflection across the critical
axis. -/
theorem thetaCompactSourceInverse_thetaLpConj (f : H) :
    thetaLpConj (thetaCompactSourceInverse f) =
      -thetaCompactSourceInverse (thetaLpConj f) := by
  have hBf : (thetaCompactSourceInverse f : H) =ᵐ[unitIntervalMeasure]
      fun t => pinnedKernelField thetaSource t f := by
    simpa [thetaCompactSourceInverse] using
      (pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f)
  have hBCf : (thetaCompactSourceInverse (thetaLpConj f) : H) =ᵐ[unitIntervalMeasure]
      fun t => pinnedKernelField thetaSource t (thetaLpConj f) := by
    simpa [thetaCompactSourceInverse] using
      (pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource (thetaLpConj f))
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (thetaCompactSourceInverse f),
    Lp.coeFn_neg (thetaCompactSourceInverse (thetaLpConj f)), hBf, hBCf]
      with t hconj hneg hBf hBCf
  rw [hconj, hneg, hBf]
  simp only [Pi.neg_apply]
  rw [hBCf, pinnedKernelField_apply_eq_pinnedVolterraFun,
    pinnedKernelField_apply_eq_pinnedVolterraFun,
    pinnedVolterraFun_thetaLpConj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem thetaLpConj_neg (f : H) : thetaLpConj (-f) = -thetaLpConj f := by
  simpa using thetaLpConj_smul (-1 : ℂ) f

/-- The metric-conjugate bilinear pairing carried by the literal theta source. -/
def thetaMetricConjBilinear (f g : H) : ℂ :=
  inner ℂ (thetaMetricOperator (thetaLpConj f)) g

/-- The source flow fails to preserve the metric-conjugate pairing by exactly the rank-two
Green boundary form.  The sign is fixed by conjugate-linearity in the first Hilbert argument. -/
theorem thetaMetricConjBilinear_thetaKernel_defect (f g : H) :
    thetaMetricConjBilinear (thetaKernelOperator f) g +
        thetaMetricConjBilinear f (thetaKernelOperator g) =
      Complex.I * inner ℂ (pinnedBoundaryCLM (thetaLpConj f)) g := by
  have hgreen := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T (thetaLpConj f)) g : ℂ))
    thetaMetric_commutator_thetaKernelOperator
  have hsub :
      (thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator)
          (thetaLpConj f) =
        (thetaMetricOperator * thetaKernelOperator) (thetaLpConj f) -
          (ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator)
            (thetaLpConj f) := by
    change
      ((↑(thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) : H →ₗ[ℂ] H)
        (thetaLpConj f)) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  rw [hsub, mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_left,
    smul_apply, inner_smul_left, ContinuousLinearMap.adjoint_inner_left] at hgreen
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  rw [hconjI] at hgreen
  have hsourceConj : thetaLpConj (thetaKernelOperator f) =
      -thetaKernelOperator (thetaLpConj f) := by
    simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse] using
      thetaCompactSourceInverse_thetaLpConj f
  unfold thetaMetricConjBilinear
  rw [hsourceConj, map_neg, inner_neg_left]
  linear_combination -hgreen

/-- In the exact port coordinates, the metric-conjugate Green defect is incoming intensity
minus outgoing intensity. -/
theorem thetaMetricConjBilinear_thetaKernel_twoPort (f g : H) :
    thetaMetricConjBilinear (thetaKernelOperator f) g +
        thetaMetricConjBilinear f (thetaKernelOperator g) =
      Complex.I * ((starRingEnd ℂ) (pinnedBoundaryInPort (thetaLpConj f)) *
          pinnedBoundaryInPort g -
        (starRingEnd ℂ) (pinnedBoundaryOutPort (thetaLpConj f)) *
          pinnedBoundaryOutPort g) := by
  rw [thetaMetricConjBilinear_thetaKernel_defect,
    inner_pinnedBoundaryCLM_eq_twoPort_pair]

theorem thetaLpConj_sub (f g : H) :
    thetaLpConj (f - g) = thetaLpConj f - thetaLpConj g := by
  rw [sub_eq_add_neg, thetaLpConj_add, thetaLpConj_neg, sub_eq_add_neg]

theorem thetaLpConj_pinnedOne : thetaLpConj pinnedOne = pinnedOne := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae pinnedOne, pinnedOne_coeFn] with t hconj hone
  rw [hconj, hone]
  simp

/-- Conjugation restricts to the literal mean-zero source coordinate. -/
def thetaCenteredConj (k : thetaCentered) : thetaCentered :=
  ⟨thetaLpConj k, (mem_thetaCentered_iff _).mpr (by
    rw [pinnedMean_thetaLpConj, (mem_thetaCentered_iff _).mp k.property]
    simp)⟩

theorem thetaCenteredConj_coe (k : thetaCentered) :
    (thetaCenteredConj k : H) = thetaLpConj k := rfl

theorem thetaCenteredConj_involutive (k : thetaCentered) :
    thetaCenteredConj (thetaCenteredConj k) = k := by
  apply Subtype.ext
  exact thetaLpConj_involutive k

theorem thetaCenteredSourceInverse_thetaCenteredConj (k : thetaCentered) :
    thetaCenteredSourceInverse (thetaCenteredConj k) =
      -thetaLpConj (thetaCenteredSourceInverse k) := by
  have h := congrArg Neg.neg (thetaCompactSourceInverse_thetaLpConj (k : H))
  simpa [thetaCenteredSourceInverse, thetaCenteredConj] using h.symm

theorem pinnedMean_neg (f : H) : pinnedMean (-f) = -pinnedMean f := by
  simpa using pinnedMean_smul (-1 : ℂ) f

/-- The literal closed differential coordinate is equivariant for the critical-axis reflection
`z ↦ -conj z`. -/
theorem thetaSourceDifferentialRangeMap_thetaCenteredConj (z : ℂ) (k : thetaCentered) :
    thetaLpConj (thetaSourceDifferentialRangeMap z k) =
      thetaSourceDifferentialRangeMap (-(starRingEnd ℂ z)) (thetaCenteredConj k) := by
  rw [thetaSourceDifferentialRangeMap_apply, thetaLpConj_add, thetaLpConj_smul,
    thetaLpConj_sub, thetaLpConj_smul, thetaLpConj_pinnedOne,
    thetaSourceDifferentialRangeMap_apply, thetaCenteredConj_coe,
    thetaCenteredSourceInverse_thetaCenteredConj, pinnedMean_neg,
    pinnedMean_thetaLpConj]
  module

theorem pinnedFirstMoment_thetaLpConj (f : H) :
    pinnedFirstMoment (thetaLpConj f) = (starRingEnd ℂ) (pinnedFirstMoment f) := by
  symm
  rw [pinnedFirstMoment, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [thetaLpConj_coeFn_ae f] with t ht
  rw [map_mul, Complex.conj_ofReal, ht]

/-- The second scalar port is also real-coordinate conjugation covariant. -/
theorem thetaCenteredDipoleTrace_thetaCenteredConj (k : thetaCentered) :
    thetaCenteredDipoleTrace (thetaCenteredConj k) =
      (starRingEnd ℂ) (thetaCenteredDipoleTrace k) := by
  rw [thetaCenteredDipoleTrace_apply, thetaCenteredDipoleTrace_apply,
    thetaCenteredConj_coe]
  exact pinnedFirstMoment_thetaLpConj (k : H)

/-- The antilinear action on the full literal source and boundary record.  The two leading minus
signs are forced by the imaginary source kernel; the boundary signs are then fixed by the same
source action. -/
def thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))) :
    ((H × H) × (ℂ × ℂ)) :=
  ((-thetaLpConj r.1.1, thetaLpConj r.1.2),
    (-(starRingEnd ℂ r.2.1), starRingEnd ℂ r.2.2))

/-- The source/differential exchange on a complete boundary record. -/
def thetaSourceDifferentialBoundarySwap (r : ((H × H) × (ℂ × ℂ))) :
    ((H × H) × (ℂ × ℂ)) :=
  ((r.1.2, r.1.1), (r.2.2, r.2.1))

/-- The completed Hodge star is exactly literal record reflection after exchanging source and
differential legs.  Hence the unresolved Hodge-flow law is precisely a closed adjoint-swap
transport problem for the source relation. -/
theorem thetaSourceGreenHodge_eq_boundaryConj_swap (r : ((H × H) × (ℂ × ℂ))) :
    thetaSourceGreenHodge r =
      thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundarySwap r) := by
  rfl

/-- The explicit boundary action maps every literal source coordinate at `z` to the coordinate
at the critical-axis reflection `-conj z`. -/
theorem thetaSourceDifferentialBoundaryConj_coordinate (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundaryCoordinate z k) =
      thetaSourceDifferentialBoundaryCoordinate (-(starRingEnd ℂ z)) (thetaCenteredConj k) := by
  rw [thetaSourceDifferentialBoundaryCoordinate_apply,
    thetaSourceDifferentialBoundaryCoordinate_apply]
  simp only [thetaSourceDifferentialBoundaryConj]
  rw [thetaCenteredSourceInverse_thetaCenteredConj,
    thetaSourceDifferentialRangeMap_thetaCenteredConj,
    pinnedMean_neg, pinnedMean_thetaLpConj,
    thetaCenteredDipoleTrace_thetaCenteredConj]

theorem thetaSourceDifferentialBoundaryConj_add (r s : ((H × H) × (ℂ × ℂ))) :
    thetaSourceDifferentialBoundaryConj (r + s) =
      thetaSourceDifferentialBoundaryConj r + thetaSourceDifferentialBoundaryConj s := by
  ext <;> simp [thetaSourceDifferentialBoundaryConj, thetaLpConj_add, add_comm]

theorem thetaSourceDifferentialBoundaryConj_smul (c : ℂ) (r : ((H × H) × (ℂ × ℂ))) :
    thetaSourceDifferentialBoundaryConj (c • r) =
      (starRingEnd ℂ c) • thetaSourceDifferentialBoundaryConj r := by
  ext <;> simp [thetaSourceDifferentialBoundaryConj, thetaLpConj_smul]

theorem thetaSourceDifferentialBoundaryConj_involutive (r : ((H × H) × (ℂ × ℂ))) :
    thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundaryConj r) = r := by
  ext <;> simp [thetaSourceDifferentialBoundaryConj, thetaLpConj_neg,
    thetaLpConj_involutive]

/-- The complete record reflection as a conjugate-semilinear map. -/
def thetaSourceDifferentialBoundaryConjSLM :
    ((H × H) × (ℂ × ℂ)) →ₛₗ[starRingEnd ℂ] ((H × H) × (ℂ × ℂ)) where
  toFun := thetaSourceDifferentialBoundaryConj
  map_add' := thetaSourceDifferentialBoundaryConj_add
  map_smul' := thetaSourceDifferentialBoundaryConj_smul

theorem thetaSourceDifferentialBoundaryConj_mem
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z) :
    thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))) ∈
      thetaSourceDifferentialBoundaryRelation (-(starRingEnd ℂ z)) := by
  obtain ⟨k, hk⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff z
      (r : ((H × H) × (ℂ × ℂ)))).mp r.property
  refine (thetaSourceDifferentialBoundaryRelation_mem_iff (-(starRingEnd ℂ z))
    (thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))))).mpr ?_
  refine ⟨thetaCenteredConj k, ?_⟩
  calc
    thetaSourceDifferentialBoundaryCoordinate (-(starRingEnd ℂ z)) (thetaCenteredConj k) =
        thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundaryCoordinate z k) :=
      (thetaSourceDifferentialBoundaryConj_coordinate z k).symm
    _ = thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))) := by rw [hk]

/-- Closed source-relation reflection induced by the literal theta kernel. -/
def thetaSourceDifferentialBoundaryRelationConj (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →ₛₗ[starRingEnd ℂ]
      thetaSourceDifferentialBoundaryRelation (-(starRingEnd ℂ z)) where
  toFun r := ⟨thetaSourceDifferentialBoundaryConj r,
    thetaSourceDifferentialBoundaryConj_mem z r⟩
  map_add' r s := by
    apply Subtype.ext
    exact thetaSourceDifferentialBoundaryConj_add r s
  map_smul' c r := by
    apply Subtype.ext
    exact thetaSourceDifferentialBoundaryConj_smul c r

theorem thetaSourceDifferentialBoundaryRelationConj_coordinate
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryRelationConj z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
        thetaSourceDifferentialBoundaryCoordinateElement (-(starRingEnd ℂ z))
          (thetaCenteredConj k) := by
  apply Subtype.ext
  exact thetaSourceDifferentialBoundaryConj_coordinate z k

/-- Reflection carries every nonzero vertical fibre of the literal closed relation to a nonzero
vertical fibre at the reflected parameter. -/
theorem thetaSourceDifferentialBoundaryRelation_nonzero_vertical_reflect
    (z : ℂ) :
    (∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
      r.1.2 = 0 ∧ r.1.1 ≠ 0) →
      ∃ s : ((H × H) × (ℂ × ℂ)),
        s ∈ thetaSourceDifferentialBoundaryRelation (-(starRingEnd ℂ z)) ∧
          s.1.2 = 0 ∧ s.1.1 ≠ 0 := by
  rintro ⟨r, hr, hrange, hsource⟩
  refine ⟨thetaSourceDifferentialBoundaryConj r,
    thetaSourceDifferentialBoundaryConj_mem z ⟨r, hr⟩, ?_, ?_⟩
  · change thetaLpConj r.1.2 = 0
    rw [hrange, thetaLpConj_zero]
  · change -thetaLpConj r.1.1 ≠ 0
    intro hzero
    apply hsource
    apply thetaLpConj_injective
    have hc : thetaLpConj r.1.1 = 0 := neg_eq_zero.mp hzero
    rw [hc, thetaLpConj_zero]

/-- Source-faithful conjugation proves the expected reality reflection of the completed Xi zero
set directly through its literal closed relation. -/
theorem XiC_eq_zero_reflect_of_XiC_eq_zero {z : ℂ} (hz : XiC z = 0) :
    XiC (-(starRingEnd ℂ z)) = 0 := by
  apply (XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical
    (-(starRingEnd ℂ z))).mpr
  apply thetaSourceDifferentialBoundaryRelation_nonzero_vertical_reflect z
  exact (XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical z).mp hz

/-- The reflected boundary action reverses the hyperbolic signature.  Hence a completion that
extends this literal action cannot treat the action as an ordinary Pontryagin isometry. -/
theorem thetaMonopoleDipoleHyperbolicForm_boundaryConj
    (u v : ℂ × ℂ) :
    thetaMonopoleDipoleHyperbolicForm
      (-(starRingEnd ℂ u.1), starRingEnd ℂ u.2)
      (-(starRingEnd ℂ v.1), starRingEnd ℂ v.2) =
      -(starRingEnd ℂ) (thetaMonopoleDipoleHyperbolicForm u v) := by
  simp only [thetaMonopoleDipoleHyperbolicForm, map_neg, map_add, map_mul,
    starRingEnd_self_apply]
  ring

end

end RHTower.HedenmalmThetaSource
