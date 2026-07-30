import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# Two-mass self-calibration of clock propagators

Complete source-to-receiver response is normally dressed by endpoint gains. If the same unknown
invertible gains dress two scalar clock species whose squared masses are distinct, the difference
of the two measured inverse operators cancels the entire differential operator and isolates the
endpoint-calibration product.

This file proves that operator identity in an arbitrary noncommutative algebra. It also proves the
pointwise principal-symbol reconstruction formula: the mass difference identifies calibration,
after which the calibrated principal symbol identifies the metric coefficient.

Physical use still requires Green operators on the correct support domains, species-independent
endpoint gains, a normally hyperbolic principal symbol, and experimental recovery of the complete
dressed responses.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

open GaloisForLFunctions
open scoped Differential

/-- A complete response dressed by receiver gain on the left and source gain on the right. -/
def endpointDressedGreen
    {A : Type u} [Ring A]
    (receiverGain green sourceGain : A) : A :=
  receiverGain * green * sourceGain

/-- Candidate inverse of an endpoint-dressed Green element. -/
def endpointDressedInverse
    {A : Type u} [Ring A]
    (sourceGainInv operator receiverGainInv : A) : A :=
  sourceGainInv * operator * receiverGainInv

/-- Endpoint dressing preserves a two-sided Green inverse, with the inverse gains appearing in
reverse order. -/
theorem endpointDressedInverse_isTwoSided
    {A : Type u} [Ring A]
    (operator green receiverGain receiverGainInv sourceGain sourceGainInv : A)
    (hOperatorGreen : operator * green = 1)
    (hGreenOperator : green * operator = 1)
    (hReceiverInv : receiverGainInv * receiverGain = 1)
    (hReceiver : receiverGain * receiverGainInv = 1)
    (hSourceInv : sourceGainInv * sourceGain = 1)
    (hSource : sourceGain * sourceGainInv = 1) :
    endpointDressedInverse sourceGainInv operator receiverGainInv *
          endpointDressedGreen receiverGain green sourceGain = 1 ∧
      endpointDressedGreen receiverGain green sourceGain *
          endpointDressedInverse sourceGainInv operator receiverGainInv = 1 := by
  constructor
  · simp only [endpointDressedInverse, endpointDressedGreen]
    calc
      (sourceGainInv * operator * receiverGainInv) *
          (receiverGain * green * sourceGain) =
          sourceGainInv * operator * (receiverGainInv * receiverGain) *
            green * sourceGain := by noncomm_ring
      _ = sourceGainInv * (operator * green) * sourceGain := by
        rw [hReceiverInv]
        simp only [mul_one]
        noncomm_ring
      _ = 1 := by rw [hOperatorGreen, mul_one, hSourceInv]
  · simp only [endpointDressedInverse, endpointDressedGreen]
    calc
      (receiverGain * green * sourceGain) *
          (sourceGainInv * operator * receiverGainInv) =
          receiverGain * green * (sourceGain * sourceGainInv) *
            operator * receiverGainInv := by noncomm_ring
      _ = receiverGain * (green * operator) * receiverGainInv := by
        rw [hSource]
        simp only [mul_one]
        noncomm_ring
      _ = 1 := by rw [hGreenOperator, mul_one, hReceiver]

/-- Inverse measured operator for a species of squared mass `massSq`. The geometric operator may
be noncommutative with the endpoint gains; the scalar mass is central through the algebra map. -/
def measuredClockInverse
    {K : Type u} {A : Type v}
    [Field K] [Ring A] [Algebra K A]
    (geometricOperator sourceGainInv receiverGainInv : A)
    (massSq : K) : A :=
  sourceGainInv *
    (geometricOperator + algebraMap K A massSq) *
      receiverGainInv

/-- **Two-mass endpoint self-calibration law.**

Subtracting measured inverse operators for two masses cancels every geometric and derivative term.
Only the central mass difference times the common endpoint-calibration product remains.
-/
theorem measuredClockInverse_difference
    {K : Type u} {A : Type v}
    [Field K] [Ring A] [Algebra K A]
    (geometricOperator sourceGainInv receiverGainInv : A)
    (massSq₁ massSq₂ : K) :
    measuredClockInverse geometricOperator sourceGainInv receiverGainInv massSq₁ -
        measuredClockInverse geometricOperator sourceGainInv receiverGainInv massSq₂ =
      algebraMap K A (massSq₁ - massSq₂) *
        (sourceGainInv * receiverGainInv) := by
  simp only [measuredClockInverse]
  calc
    sourceGainInv *
          (geometricOperator + algebraMap K A massSq₁) *
          receiverGainInv -
        sourceGainInv *
          (geometricOperator + algebraMap K A massSq₂) *
          receiverGainInv =
        sourceGainInv *
          (algebraMap K A massSq₁ - algebraMap K A massSq₂) *
          receiverGainInv := by noncomm_ring
    _ = sourceGainInv * algebraMap K A (massSq₁ - massSq₂) *
          receiverGainInv := by rw [map_sub]
    _ = algebraMap K A (massSq₁ - massSq₂) *
        (sourceGainInv * receiverGainInv) := by
      rw [← Algebra.commutes (massSq₁ - massSq₂) sourceGainInv]
      simp only [mul_assoc]

/-- Distinct masses reconstruct the unknown endpoint-calibration product exactly. -/
theorem endpointCalibrationProduct_reconstruction
    {K : Type u} {A : Type v}
    [Field K] [Ring A] [Algebra K A]
    (geometricOperator sourceGainInv receiverGainInv : A)
    {massSq₁ massSq₂ : K} (hmass : massSq₁ ≠ massSq₂) :
    algebraMap K A (massSq₁ - massSq₂)⁻¹ *
        (measuredClockInverse geometricOperator sourceGainInv receiverGainInv massSq₁ -
          measuredClockInverse geometricOperator sourceGainInv receiverGainInv massSq₂) =
      sourceGainInv * receiverGainInv := by
  rw [measuredClockInverse_difference]
  rw [← mul_assoc, ← map_mul]
  rw [inv_mul_cancel₀ (sub_ne_zero.mpr hmass), map_one, one_mul]

/-- Frequency-dependent scalar form of the two-clock inverse locality residual. -/
def twoClockLocalityResidual
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (massSq₁ massSq₂ : F) (calibration : E) : E :=
  algebraMap F E (massSq₁ - massSq₂) * calibration

/-- A differentially algebraic endpoint calibration forces the two-clock inverse residual to be
differentially algebraic. Forward propagators need not be differentially algebraic. -/
theorem differentialAlgebraicOver_twoClockLocalityResidual
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (massSq₁ massSq₂ : F) {calibration : E}
    (hcalibration : DifferentialAlgebraicOver F calibration) :
    DifferentialAlgebraicOver F
      (twoClockLocalityResidual massSq₁ massSq₂ calibration) := by
  exact differentialAlgebraicOver_mul
    (differentialAlgebraicOver_algebraMap (massSq₁ - massSq₂))
    hcalibration

/-- **Hypertranscendental inverse-residual obstruction.** Under a DA calibration model, a
two-clock locality residual cannot be hypertranscendental. An HT residual therefore falsifies at
least one hypothesis of the common local single-metric model. -/
theorem not_hypertranscendentalOver_twoClockLocalityResidual
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (massSq₁ massSq₂ : F) {calibration : E}
    (hcalibration : DifferentialAlgebraicOver F calibration) :
    ¬ HypertranscendentalOver F
      (twoClockLocalityResidual massSq₁ massSq₂ calibration) := by
  intro hresidual
  exact hresidual
    (differentialAlgebraicOver_twoClockLocalityResidual
      massSq₁ massSq₂ hcalibration)

/-- Pointwise data carried by two measured inverse operators: their zeroth-order difference and
the common calibrated principal-symbol value. -/
def twoMassCalibrationMetricData
    {K : Type u} [Field K]
    (massSq₁ massSq₂ calibration metricSymbol : K) : K × K :=
  ((massSq₁ - massSq₂) * calibration, calibration * metricSymbol)

/-- The first component of the two-mass data reconstructs endpoint calibration. -/
theorem twoMassCalibration_reconstruction
    {K : Type u} [Field K]
    {massSq₁ massSq₂ : K} (hmass : massSq₁ ≠ massSq₂)
    (calibration metricSymbol : K) :
    (twoMassCalibrationMetricData massSq₁ massSq₂ calibration metricSymbol).1 /
        (massSq₁ - massSq₂) =
      calibration := by
  simp only [twoMassCalibrationMetricData]
  exact mul_div_cancel_left₀ calibration (sub_ne_zero.mpr hmass)

/-- **Two-mass metric-symbol reconstruction.**

When endpoint calibration is nonzero, the mass difference and the two measured symbol channels
recover the undressed metric principal symbol exactly.
-/
theorem twoMassMetricSymbol_reconstruction
    {K : Type u} [Field K]
    {massSq₁ massSq₂ : K} (hmass : massSq₁ ≠ massSq₂)
    {calibration : K} (hcalibration : calibration ≠ 0)
    (metricSymbol : K) :
    (massSq₁ - massSq₂) *
          (twoMassCalibrationMetricData
            massSq₁ massSq₂ calibration metricSymbol).2 /
        (twoMassCalibrationMetricData
          massSq₁ massSq₂ calibration metricSymbol).1 =
      metricSymbol := by
  simp only [twoMassCalibrationMetricData]
  field_simp [sub_ne_zero.mpr hmass, hcalibration]

/-- The joint calibration and metric-symbol data are injective for distinct masses and nonzero
endpoint calibration. -/
theorem twoMassCalibrationMetricData_injective
    {K : Type u} [Field K]
    {massSq₁ massSq₂ : K} (hmass : massSq₁ ≠ massSq₂)
    {data₁ data₂ : K × K} (hcalibration₂ : data₂.1 ≠ 0)
    (hdata :
      twoMassCalibrationMetricData massSq₁ massSq₂ data₁.1 data₁.2 =
        twoMassCalibrationMetricData massSq₁ massSq₂ data₂.1 data₂.2) :
    data₁ = data₂ := by
  have hfirst := congrArg Prod.fst hdata
  have hsecond := congrArg Prod.snd hdata
  simp only [twoMassCalibrationMetricData] at hfirst hsecond
  have hmassDifference : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
  have hcalibration : data₁.1 = data₂.1 :=
    mul_left_cancel₀ hmassDifference hfirst
  apply Prod.ext
  · exact hcalibration
  · rw [hcalibration] at hsecond
    exact mul_left_cancel₀ hcalibration₂ hsecond

/-! ## Continuum metric and nonlinear gravity-operator rigidity -/

/-- A coordinate-trivialized inverse-metric field observed through an unknown nonzero local
endpoint-calibration product. -/
structure SelfCalibratingMetricField
    (Event : Type u) (Covector : Type v)
    [AddCommGroup Covector] [Module ℝ Covector] where
  calibration : Event → ℝ
  calibration_ne_zero : ∀ event, calibration event ≠ 0
  form : Event → LinearMap.BilinForm ℝ Covector
  symmetric : ∀ event u v, form event u v = form event v u

namespace SelfCalibratingMetricField

variable {Event : Type u} {Covector : Type v}
  [AddCommGroup Covector] [Module ℝ Covector]

/-- Equality of calibration and bilinear-form fields gives equality of self-calibrating metric
fields. -/
@[ext]
theorem ext {g h : SelfCalibratingMetricField Event Covector}
    (hcalibration : g.calibration = h.calibration)
    (hform : g.form = h.form) :
    g = h := by
  cases g
  cases h
  simp_all

/-- Complete two-mass observation: inverse-operator difference and calibrated quadratic principal
symbol at every event and covector. -/
def twoMassObservation
    (massSq₁ massSq₂ : ℝ)
    (g : SelfCalibratingMetricField Event Covector) :
    (Event → ℝ) × (Event → Covector → ℝ) :=
  (fun event => (massSq₁ - massSq₂) * g.calibration event,
    fun event covector =>
      g.calibration event * g.form event covector covector)

/-- Polarization recovers every inverse-metric component from calibrated diagonal symbol values
once local endpoint calibration is known. -/
theorem form_eq_half_calibratedSymbol_polarization
    (g : SelfCalibratingMetricField Event Covector)
    (event : Event) (u v : Covector) :
    g.calibration event * g.form event u v =
      ((twoMassObservation 1 0 g).2 event (u + v) -
        (twoMassObservation 1 0 g).2 event u -
        (twoMassObservation 1 0 g).2 event v) / 2 := by
  simp only [twoMassObservation, map_add, LinearMap.add_apply]
  rw [g.symmetric event v u]
  ring

/-- **Two masses self-calibrate a complete continuum inverse-metric field.** -/
theorem twoMassObservation_injective
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) :
    Function.Injective
      (twoMassObservation massSq₁ massSq₂ :
        SelfCalibratingMetricField Event Covector →
          (Event → ℝ) × (Event → Covector → ℝ)) := by
  intro g h hdata
  have hfirst := congrArg Prod.fst hdata
  have hsecond := congrArg Prod.snd hdata
  have hmassDifference : massSq₁ - massSq₂ ≠ 0 :=
    sub_ne_zero.mpr hmass
  have hcalibration : g.calibration = h.calibration := by
    funext event
    exact mul_left_cancel₀ hmassDifference (congrFun hfirst event)
  have hdiagonal :
      (fun event covector => g.form event covector covector) =
        fun event covector => h.form event covector covector := by
    funext event covector
    have hsymbol := congrFun (congrFun hsecond event) covector
    change
      g.calibration event * g.form event covector covector =
        h.calibration event * h.form event covector covector at hsymbol
    rw [hcalibration] at hsymbol
    exact mul_left_cancel₀ (h.calibration_ne_zero event) hsymbol
  apply ext hcalibration
  funext event
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  have hpolarized :=
    congrFun (congrFun hdiagonal event) (u + v)
  have hu := congrFun (congrFun hdiagonal event) u
  have hv := congrFun (congrFun hdiagonal event) v
  calc
    g.form event u v =
        (g.form event (u + v) (u + v) -
          g.form event u u - g.form event v v) / 2 := by
      simp only [map_add, LinearMap.add_apply]
      rw [g.symmetric event v u]
      ring
    _ = (h.form event (u + v) (u + v) -
          h.form event u u - h.form event v v) / 2 := by
      rw [hpolarized, hu, hv]
    _ = h.form event u v := by
      simp only [map_add, LinearMap.add_apply]
      rw [h.symmetric event v u]
      ring

end SelfCalibratingMetricField

/-- Branch-safe source/observation graph for a self-calibrating continuum gravity operator. -/
def selfCalibratingGravityGraph
    {Geometry : Type u} {Source : Type v} {Observation : Type*}
    (encode : Geometry → Observation) (law : Geometry → Source) :
    Set (Source × Observation) :=
  Set.range fun geometry => (law geometry, encode geometry)

/-- **Two-mass self-calibrating continuum gravity rigidity.**

Equality of complete two-mass metric-symbol graphs is equivalent to equality of arbitrary
nonlinear source operators. Multiple solution branches remain distinct because the unknown
calibration and complete metric field are jointly encoded injectively.
-/
theorem twoMassSelfCalibratingContinuumGravityRigidity
    {Event : Type u} {Covector : Type v}
    [AddCommGroup Covector] [Module ℝ Covector]
    {Source : Type*}
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    (law₁ law₂ : SelfCalibratingMetricField Event Covector → Source) :
    selfCalibratingGravityGraph
        (SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂) law₁ =
        selfCalibratingGravityGraph
          (SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂) law₂ ↔
      law₁ = law₂ := by
  constructor
  · intro hgraph
    funext geometry
    have hmem :
        (law₁ geometry,
            SelfCalibratingMetricField.twoMassObservation
              massSq₁ massSq₂ geometry) ∈
          selfCalibratingGravityGraph
            (SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂) law₂ := by
      rw [← hgraph]
      exact ⟨geometry, rfl⟩
    rcases hmem with ⟨other, hother⟩
    have hsource : law₂ other = law₁ geometry :=
      congrArg Prod.fst hother
    have hobservation :
        SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂ other =
          SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂ geometry :=
      congrArg Prod.snd hother
    have hgeometry : other = geometry :=
      SelfCalibratingMetricField.twoMassObservation_injective hmass hobservation
    subst other
    exact hsource.symm
  · intro hlaw
    subst law₂
    rfl

/-! ## Exact probe-backreaction subtraction -/

/-- Schur complement seen by a probe coupled to a hidden target channel. -/
def probeSchurComplement
    {A : Type*} [Ring A]
    (probeOperator receiverCoupling targetGreen sourceCoupling : A) : A :=
  probeOperator - receiverCoupling * targetGreen * sourceCoupling

/-- Candidate target-target block of the inverse coupled two-channel operator. -/
def targetSchurInverseBlock
    {A : Type*} [Ring A]
    (targetGreen sourceCoupling probeGreen receiverCoupling : A) : A :=
  targetGreen +
    targetGreen * sourceCoupling * probeGreen * receiverCoupling * targetGreen

/-- Candidate target-to-probe block of the inverse coupled two-channel operator. -/
def targetToProbeInverseBlock
    {A : Type*} [Ring A]
    (targetGreen sourceCoupling probeGreen : A) : A :=
  -(targetGreen * sourceCoupling * probeGreen)

/-- Candidate probe-to-target block of the inverse coupled two-channel operator. -/
def probeToTargetInverseBlock
    {A : Type*} [Ring A]
    (probeGreen receiverCoupling targetGreen : A) : A :=
  -(probeGreen * receiverCoupling * targetGreen)

/-- Exhaustive block equations saying that two two-channel operators are two-sided inverses. -/
structure TwoChannelInverseLaws
    {A : Type*} [Ring A]
    (P R S Q A00 A01 A10 A11 : A) : Prop where
  left00 : P * A00 + R * A10 = 1
  left01 : P * A01 + R * A11 = 0
  left10 : S * A00 + Q * A10 = 0
  left11 : S * A01 + Q * A11 = 1
  right00 : A00 * P + A01 * S = 1
  right01 : A00 * R + A01 * Q = 0
  right10 : A10 * P + A11 * S = 0
  right11 : A10 * R + A11 * Q = 1

/-- **Exact noncommutative Schur inversion.** The dressed probe Green element is the inverse of
`Q - S * G * R`; no weak-coupling expansion is used. -/
theorem twoChannel_schurInverseLaws
    {A : Type*} [Ring A]
    (P R S Q G H : A)
    (hPG : P * G = 1) (hGP : G * P = 1)
    (hKH : probeSchurComplement Q S G R * H = 1)
    (hHK : H * probeSchurComplement Q S G R = 1) :
    TwoChannelInverseLaws P R S Q
      (targetSchurInverseBlock G R H S)
      (targetToProbeInverseBlock G R H)
      (probeToTargetInverseBlock H S G)
      H := by
  constructor
  · simp only [targetSchurInverseBlock, probeToTargetInverseBlock]
    calc
      P * (G + G * R * H * S * G) + R * (-(H * S * G)) =
          P * G + (P * G) * R * H * S * G - R * H * S * G := by
            noncomm_ring
      _ = 1 := by rw [hPG]; noncomm_ring
  · simp only [targetToProbeInverseBlock]
    calc
      P * (-(G * R * H)) + R * H =
          -(P * G) * R * H + R * H := by noncomm_ring
      _ = 0 := by rw [hPG]; noncomm_ring
  · simp only [targetSchurInverseBlock, probeToTargetInverseBlock]
    have hQH : Q * H - S * G * R * H = 1 := by
      simpa only [probeSchurComplement, sub_mul] using hKH
    calc
      S * (G + G * R * H * S * G) +
          Q * (-(H * S * G)) =
        S * G - (Q * H - S * G * R * H) * S * G := by
          noncomm_ring
      _ = 0 := by rw [hQH, one_mul, sub_self]
  · simp only [targetToProbeInverseBlock]
    calc
      S * (-(G * R * H)) + Q * H =
          (Q - S * G * R) * H := by noncomm_ring
      _ = 1 := hKH
  · simp only [targetSchurInverseBlock, targetToProbeInverseBlock]
    calc
      (G + G * R * H * S * G) * P + (-(G * R * H)) * S =
          G * P + G * R * H * S * (G * P) - G * R * H * S := by
            noncomm_ring
      _ = 1 := by rw [hGP]; noncomm_ring
  · simp only [targetSchurInverseBlock, targetToProbeInverseBlock]
    have hHQ : H * Q - H * S * G * R = 1 := by
      calc
        H * Q - H * S * G * R =
            H * (Q - S * G * R) := by noncomm_ring
        _ = 1 := hHK
    calc
      (G + G * R * H * S * G) * R +
          (-(G * R * H)) * Q =
        G * R - G * R * (H * Q - H * S * G * R) := by
          noncomm_ring
      _ = 0 := by rw [hHQ, mul_one, sub_self]
  · simp only [probeToTargetInverseBlock]
    calc
      -(H * S * G) * P + H * S =
          -H * S * (G * P) + H * S := by noncomm_ring
      _ = 0 := by rw [hGP]; noncomm_ring
  · simp only [probeToTargetInverseBlock]
    calc
      -(H * S * G) * R + H * Q =
          H * (Q - S * G * R) := by noncomm_ring
      _ = 1 := hHK

/-- Difference between coupling-off and coupling-on measured inverse probe responses. -/
def backreactionSubtractedHiddenGreen
    {A : Type*} [Ring A]
    (probeOperator sourceGainInv receiverCoupling targetGreen
      sourceCoupling receiverGainInv : A) : A :=
  endpointDressedInverse sourceGainInv probeOperator receiverGainInv -
    endpointDressedInverse sourceGainInv
      (probeSchurComplement
        probeOperator receiverCoupling targetGreen sourceCoupling)
      receiverGainInv

/-- **Exact backreaction-subtraction law.**

Switching the target-probe coupling off and on, then subtracting the two measured inverse probe
responses, isolates the hidden target Green element. Unknown endpoint gains and coupling maps
remain only as common left/right dressing. -/
theorem backreactionSubtractedHiddenGreen_eq_endpointDressedGreen
    {A : Type*} [Ring A]
    (probeOperator sourceGainInv receiverCoupling targetGreen
      sourceCoupling receiverGainInv : A) :
    backreactionSubtractedHiddenGreen
        probeOperator sourceGainInv receiverCoupling targetGreen
        sourceCoupling receiverGainInv =
      endpointDressedGreen
        (sourceGainInv * receiverCoupling)
        targetGreen
        (sourceCoupling * receiverGainInv) := by
  simp only [backreactionSubtractedHiddenGreen, endpointDressedInverse,
    probeSchurComplement, endpointDressedGreen]
  noncomm_ring

end GaloisForLFunctions.HTGeometry
