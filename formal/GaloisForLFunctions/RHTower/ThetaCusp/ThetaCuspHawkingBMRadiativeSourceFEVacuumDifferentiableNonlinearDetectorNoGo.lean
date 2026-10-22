import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFEFaithfulDetectorScalarizationRigidity

/-!
# Vacuum-differentiable nonlinear radiative-detector scalarization: no-go

The actual BM horizon/boundary source-FE cocycle has two physical readouts. HC93 classifies every
complex-linear scalarization: off the critical line it must delete one entire readout axis. This
module closes nonlinear complex-amplitude postprocessing as an escape.

For an arbitrary nonlinear two-readout detector, assume only a complex-linear first variation
along real source amplitudes at vacuum. Exact scalarization differentiates to the HC93 linear
intertwiner. Hence off line the first variation kills the horizon or boundary axis. A locally
faithful first variation exists exactly on the critical wall, and even copy-dependent nonlinear
detectors scalarize every Xi fibre exactly under RH.

No continuity away from vacuum, locality, polynomiality, positivity, invertibility, or finite
perturbative order is assumed. Survivors must be singular at vacuum or erase a physical readout to
first order.

`[NEW] [HB NO-GO] [NONLINEAR DETECTOR] [FIRST VARIATION] [LEAN-PROVED]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Real-ray vacuum first variation of a possibly nonlinear two-readout detector. -/
def HBXiRadiativeNonlinearDetectorVacuumFirstVariation
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (detector : HBXiRadiativeDetectorCarrier → V)
    (linearization : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) : Prop :=
  ∀ x : HBXiRadiativeDetectorCarrier,
    Tendsto
      (fun amplitude : ℝ =>
        (amplitude : ℂ)⁻¹ • detector ((amplitude : ℂ) • x))
      (𝓝[≠] 0) (𝓝 (linearization x))

/-- Exact scalar FE gain seen after arbitrary nonlinear detector postprocessing. -/
def HBXiRadiativeNonlinearDetectorScalarizes
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (detector : HBXiRadiativeDetectorCarrier → V)
    (c : ℂ) (q : XiZeroCopy) : Prop :=
  ∀ x : HBXiRadiativeDetectorCarrier,
    detector (hbXiRadiativeHorizonBoundaryDetectorCocycle q x) = c • detector x

/-- Exact nonlinear scalarization differentiates to the HC93 linear intertwiner. -/
theorem hbXiRadiativeNonlinearDetectorVacuumFirstVariation_scalarizes
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [T2Space V] [ContinuousConstSMul ℂ V]
    (detector : HBXiRadiativeDetectorCarrier → V)
    (linearization : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V)
    (c : ℂ) (q : XiZeroCopy)
    (hlinear : HBXiRadiativeNonlinearDetectorVacuumFirstVariation detector linearization)
    (hscalar : HBXiRadiativeNonlinearDetectorScalarizes detector c q) :
    HBXiRadiativeDetectorScalarizes linearization c q := by
  intro x
  have hleft := hlinear (hbXiRadiativeHorizonBoundaryDetectorCocycle q x)
  have hright := (hlinear x).const_smul c
  have heq :
      (fun amplitude : ℝ =>
        (amplitude : ℂ)⁻¹ • detector
          ((amplitude : ℂ) •
            hbXiRadiativeHorizonBoundaryDetectorCocycle q x)) =
      (fun amplitude : ℝ =>
        c • ((amplitude : ℂ)⁻¹ • detector ((amplitude : ℂ) • x))) := by
    funext amplitude
    rw [← (hbXiRadiativeHorizonBoundaryDetectorCocycle q).map_smul,
      hscalar]
    simp only [smul_smul]
    congr 1
    ring
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Every linear detector is its own real-ray vacuum first variation. -/
theorem hbXiRadiativeNonlinearDetectorVacuumFirstVariation_linear
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (linearization : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) :
    HBXiRadiativeNonlinearDetectorVacuumFirstVariation
      (fun x => linearization x) linearization := by
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with amplitude hamplitude
  have hamplitude0 : amplitude ≠ 0 := by
    simpa using hamplitude
  have hamplitudeC : (amplitude : ℂ) ≠ 0 := by
    exact_mod_cast hamplitude0
  rw [linearization.map_smul]
  rw [smul_smul, inv_mul_cancel₀ hamplitudeC, one_smul]

/-- Sharp survivor: off line, first-order response of every regular nonlinear scalarizer loses
one complete physical detector axis. -/
theorem hbXiRadiativeNonlinearDetector_firstVariation_axisLoss_of_offLine
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [T2Space V] [ContinuousConstSMul ℂ V]
    (detector : HBXiRadiativeDetectorCarrier → V)
    (linearization : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V)
    (c : ℂ) (q : XiZeroCopy)
    (hlinear : HBXiRadiativeNonlinearDetectorVacuumFirstVariation detector linearization)
    (hscalar : HBXiRadiativeNonlinearDetectorScalarizes detector c q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    linearization hbXiRadiativeHorizonDetectorBasis = 0 ∨
      linearization hbXiRadiativeBoundaryDetectorBasis = 0 := by
  exact hbXiRadiativeDetectorScalarization_kills_axis_of_offLine
    linearization c q
      (hbXiRadiativeNonlinearDetectorVacuumFirstVariation_scalarizes
        detector linearization c q hlinear hscalar) hoff

/-- Existence of a vacuum-regular nonlinear detector with locally faithful first variation and one
scalar FE gain. -/
def HBXiRadiativeExistsVacuumDifferentiableFaithfulDetectorScalarizationAt
    (q : XiZeroCopy) : Prop :=
  ∃ detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier,
    ∃ linearization :
        HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier,
      ∃ c : ℂ,
        HBXiRadiativeNonlinearDetectorVacuumFirstVariation detector linearization ∧
        Function.Injective linearization ∧
        HBXiRadiativeNonlinearDetectorScalarizes detector c q

/-- Locally faithful differentiable nonlinear scalarization exists exactly on critical wall. -/
theorem hbXiRadiativeExistsVacuumDifferentiableFaithfulDetectorScalarizationAt_iff_re_eq_half
    (q : XiZeroCopy) :
    HBXiRadiativeExistsVacuumDifferentiableFaithfulDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨detector, linearization, c, hlinear, hfaithful, hscalar⟩
    exact hbXiRadiativeFaithfulDetectorScalarization_forces_re_eq_half
      linearization hfaithful c q
        (hbXiRadiativeNonlinearDetectorVacuumFirstVariation_scalarizes
          detector linearization c q hlinear hscalar)
  · intro hline
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    refine ⟨id, LinearMap.id,
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q,
      hbXiRadiativeNonlinearDetectorVacuumFirstVariation_linear LinearMap.id,
      Function.injective_id, ?_⟩
    intro x
    apply Prod.ext <;>
      simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, heq]

/-- Even copy-dependent nonlinear detectors cannot scalarize every physical two-readout cocycle
with faithful vacuum derivative unless RH holds. -/
def HBXiRadiativeGlobalVacuumDifferentiableFaithfulDetectorScalarization : Prop :=
  ∃ detector : XiZeroCopy →
      (HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier),
    ∃ linearization : XiZeroCopy →
        (HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier),
      ∃ c : XiZeroCopy → ℂ,
        ∀ q : XiZeroCopy,
          HBXiRadiativeNonlinearDetectorVacuumFirstVariation
              (detector q) (linearization q) ∧
          Function.Injective (linearization q) ∧
          HBXiRadiativeNonlinearDetectorScalarizes (detector q) (c q) q

theorem hbXiRadiativeGlobalVacuumDifferentiableFaithfulDetectorScalarization_iff_rh :
    HBXiRadiativeGlobalVacuumDifferentiableFaithfulDetectorScalarization ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨detector, linearization, c, h⟩
    apply hbXiRadiativeGlobalFaithfulDetectorScalarization_iff_rh.mp
    refine ⟨linearization, fun q => (h q).2.1, c, ?_⟩
    intro q
    exact hbXiRadiativeNonlinearDetectorVacuumFirstVariation_scalarizes
      (detector q) (linearization q) (c q) q (h q).1 (h q).2.2
  · intro hRH
    rcases hbXiRadiativeGlobalFaithfulDetectorScalarization_iff_rh.mpr hRH with
      ⟨linearization, hfaithful, c, hscalar⟩
    refine ⟨fun q x => linearization q x, linearization, c, ?_⟩
    intro q
    exact ⟨
      hbXiRadiativeNonlinearDetectorVacuumFirstVariation_linear (linearization q),
      hfaithful q,
      hscalar q⟩

/-- Closed nonlinear-detector route classification. -/
def D4HBVacuumDifferentiableNonlinearDetectorScalarizationRouteKilled : Prop :=
  (∀ q : XiZeroCopy,
    HBXiRadiativeExistsVacuumDifferentiableFaithfulDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  (∀ (detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier)
      (linearization :
        HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier)
      (c : ℂ) (q : XiZeroCopy),
    HBXiRadiativeNonlinearDetectorVacuumFirstVariation detector linearization →
    HBXiRadiativeNonlinearDetectorScalarizes detector c q →
    (q.1 : ℂ).re ≠ 1 / 2 →
      linearization hbXiRadiativeHorizonDetectorBasis = 0 ∨
        linearization hbXiRadiativeBoundaryDetectorBasis = 0) ∧
  (HBXiRadiativeGlobalVacuumDifferentiableFaithfulDetectorScalarization ↔
    RiemannHypothesis)

/-- Premise-free certificate: regular nonlinear detector postprocessing cannot manufacture HB
source-FE covariance while retaining both physical readouts to first order. -/
theorem d4HBVacuumDifferentiableNonlinearDetectorScalarizationRouteKilled :
    D4HBVacuumDifferentiableNonlinearDetectorScalarizationRouteKilled := by
  exact ⟨
    hbXiRadiativeExistsVacuumDifferentiableFaithfulDetectorScalarizationAt_iff_re_eq_half,
    fun detector linearization c q =>
      hbXiRadiativeNonlinearDetector_firstVariation_axisLoss_of_offLine
        detector linearization c q,
    hbXiRadiativeGlobalVacuumDifferentiableFaithfulDetectorScalarization_iff_rh⟩

end

end RHTower
