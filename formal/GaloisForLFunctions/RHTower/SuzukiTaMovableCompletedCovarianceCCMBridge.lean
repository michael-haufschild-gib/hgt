import GaloisForLFunctions.RHTower.SuzukiTaMovableCompletedCovarianceSchur
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarSourceCancellation

/-!
# Movable completed covariance in exact constrained CCM coordinates

The movable Suzuki covariance source is transported back to the complete CCM form domain before
scalarization.  Its two literal pole coordinates are exactly raw-deficiency Gram coefficients.
Subtracting the canonical biorthogonal pole section therefore produces an actual constrained CCM
head while retaining those coefficients, rather than discarding them as abstract correction data.

Each retained pole charge is also identified with a full completed CCM form matrix coefficient
plus the shifted covariance overlap.  Consequently both literal prime action and completed
Gamma--prime--polar boundary action land on the same corrected movable source.  No positivity,
asymptotic cancellation, or RH premise is introduced.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
open GaloisForLFunctions.HTGeometry

/-- Pre-scalar CCM form response carried by the movable completed covariance source. -/
def suzukiTaMovableCompletedCovarianceCCMResponse
    (a : SuzukiPositiveAperture) (c : ℝ) : CCMArchimedeanFormDomain a :=
  suzukiTaToFormCLM a (suzukiTaRawDeficiency a c)

/-- The form embedding of the movable response is the literal completed covariance density. -/
theorem suzukiWeilIntervalFormEmbedding_movableCompletedCovarianceCCMResponse
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiWeilIntervalFormEmbedding a
        (suzukiTaMovableCompletedCovarianceCCMResponse a c) =
      suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c) := by
  change suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a c) = _
  exact suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance a c

/-- Exact physical-coordinate transport of the movable CCM response. -/
theorem ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse
    (a : SuzukiPositiveAperture) (c : ℝ) :
    ccmArchimedeanFormToAperture a
        (suzukiTaMovableCompletedCovarianceCCMResponse a c) =
      suzukiApertureL2Equiv a
        (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c)) := by
  apply (suzukiApertureL2Equiv a).symm.injective
  change suzukiWeilIntervalFormEmbedding a
      (suzukiTaMovableCompletedCovarianceCCMResponse a c) = _
  rw [suzukiWeilIntervalFormEmbedding_movableCompletedCovarianceCCMResponse]
  exact ((suzukiApertureL2Equiv a).symm_apply_apply _).symm

/-- Whole-line CCM representative is the previously constructed movable completed source. -/
theorem ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse_eq_source
    (a : SuzukiPositiveAperture) (c : ℝ) :
    (ccmArchimedeanFormToAperture a
      (suzukiTaMovableCompletedCovarianceCCMResponse a c) : SoninL2) =
        suzukiTaMovableCompletedCovarianceSource a c := by
  rw [ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse,
    suzukiTaMovableCompletedCovarianceSource]
  rfl

/-- Zero extension identifies interval exponentials with literal CCM pole profiles at every
real slope.  This is the normalization-sensitive bridge needed for movable pole coordinates. -/
theorem suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector
    (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiApertureZeroExtendL2 (suzukiTaExponentialL2 a s) =
      ccmPolarL2Vector a s := by
  apply Lp.ext
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    have hz : (fun x : SuzukiApertureInterval a.1 =>
        (suzukiApertureZeroExtendL2 (suzukiTaExponentialL2 a s) : ℝ → ℂ) x) =ᵐ[volume]
          fun x => suzukiApertureZeroExtend (suzukiTaExponentialL2 a s) x :=
      (ae_restrict_iff_subtype (s := Icc (-a.1) a.1) measurableSet_Icc).mp
        (ae_restrict_of_ae
          (suzukiApertureZeroExtendL2_coeFn (suzukiTaExponentialL2 a s)))
    have hp : (fun x : SuzukiApertureInterval a.1 =>
        (ccmPolarL2Vector a s : ℝ → ℂ) x) =ᵐ[volume]
          fun x => (centralInterval a.1).indicator (ccmPolarProfile s) x :=
      (ae_restrict_iff_subtype (s := Icc (-a.1) a.1) measurableSet_Icc).mp
        (ae_restrict_of_ae (ccmPolarL2Vector_coeFn a s))
    filter_upwards [hz, hp,
      suzukiApertureRepresentative_ae (suzukiTaExponentialL2 a s),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaExponentialContinuous a s)] with x hzx hpx hrep hexp
    rw [hzx, hpx, suzukiApertureZeroExtend_apply, hrep]
    have hexp' : (suzukiTaExponentialL2 a s :
        SuzukiApertureInterval a.1 → ℂ) x =
          (Real.exp (s * (x : ℝ)) : ℂ) := by
      simpa [suzukiTaExponentialL2, suzukiTaExponentialContinuous] using hexp
    have hx' : (x : ℝ) ∈ centralInterval a.1 := by
      change (x : ℝ) ∈ Icc (-a.1) a.1
      exact x.property
    rw [hexp', indicator_of_mem hx']
    rfl
  · filter_upwards [
      (suzukiApertureZeroExtendL2_coeFn
        (suzukiTaExponentialL2 a s)).filter_mono
          (ae_mono Measure.restrict_le_self),
      (ccmPolarL2Vector_coeFn a s).filter_mono
        (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hz hp hx
    have hx' : x ∉ centralInterval a.1 := by
      simpa [centralInterval] using hx
    rw [hz, hp, suzukiApertureZeroExtend_eq_zero_of_notMem _ hx,
      indicator_of_notMem hx']

/-- Every movable pole coordinate is the corresponding raw-deficiency Gram coefficient. -/
theorem ccmPolarCoordinate_movableCompletedCovarianceCCMResponse
    (a : SuzukiPositiveAperture) (c s : ℝ) :
    ccmPolarCoordinate a s (suzukiTaMovableCompletedCovarianceCCMResponse a c) =
      inner ℂ (suzukiTaRawDeficiency a s) (suzukiTaRawDeficiency a c) := by
  rw [suzukiTaRawDeficiency_inner]
  change inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a
        (suzukiTaMovableCompletedCovarianceCCMResponse a c)) =
    inner ℂ (suzukiTaExponentialL2 a s)
      (suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a c))
  rw [ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse]
  change inner ℂ (ccmPolarL2Vector a s)
      (suzukiApertureZeroExtendL2
        (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c))) = _
  rw [← suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector,
    inner_suzukiApertureZeroExtendL2,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance]

/-- Canonically corrected movable response in the complete two-pole constrained form domain. -/
def suzukiTaMovableCompletedCovariancePolarConstrainedResponse
    (a : SuzukiPositiveAperture) (c : ℝ) : ccmPolarConstraintSubmodule a :=
  ⟨ccmPolarCoordinateCorrection a
      (suzukiTaMovableCompletedCovarianceCCMResponse a c),
    isPolarConstrained_ccmPolarCoordinateCorrection a _⟩

/-- Exact pre-scalar correction law.  The retained coefficients are raw-deficiency Gram charges,
not independently chosen cancellation parameters. -/
theorem ccmArchimedeanFormToAperture_movablePolarConstrainedResponse
    (a : SuzukiPositiveAperture) (c : ℝ) :
    ccmArchimedeanFormToAperture a
        (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c).1 =
      suzukiApertureL2Equiv a
          (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c)) -
        inner ℂ (suzukiTaRawDeficiency a (1 / 2))
            (suzukiTaRawDeficiency a c) •
          ccmArchimedeanFormToAperture a (ccmPolarCoordinateSection a 1 0) -
        inner ℂ (suzukiTaRawDeficiency a (-1 / 2))
            (suzukiTaRawDeficiency a c) •
          ccmArchimedeanFormToAperture a (ccmPolarCoordinateSection a 0 1) := by
  change ccmArchimedeanFormToAperture a
      (ccmPolarCoordinateCorrection a
        (suzukiTaMovableCompletedCovarianceCCMResponse a c)) = _
  rw [ccmPolarCoordinateCorrection, map_sub, map_smul, map_sub, map_smul,
    ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse,
    ccmPolarCoordinate_movableCompletedCovarianceCCMResponse,
    ccmPolarCoordinate_movableCompletedCovarianceCCMResponse]

/-- A movable pole charge retains full prime--polar--Gamma cancellation inside the completed CCM
form, with only the canonical positive shift separated as covariance overlap. -/
theorem ccmPolarCoordinate_movableCompletedCovarianceCCMResponse_eq_completedForm
    (a : SuzukiPositiveAperture) (c s : ℝ) :
    ccmPolarCoordinate a s (suzukiTaMovableCompletedCovarianceCCMResponse a c) =
      ccmRestrictedWeilForm a
          (suzukiTaMovableCompletedCovarianceCCMResponse a s)
          (suzukiTaMovableCompletedCovarianceCCMResponse a c) +
        (boundedPerturbedFormShift
            (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
          inner ℂ
            (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a s))
            (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c)) := by
  rw [ccmPolarCoordinate_movableCompletedCovarianceCCMResponse,
    inner_suzukiTa_eq, suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance]
  rfl

/-- Diagonal completed source law for each movable response.  It identifies literal CCM source
quadratic with energy Gram mass minus the exact shifted covariance mass. -/
theorem ccmRestrictedWeilSourceQuadratic_movableCompletedCovarianceCCMResponse
    (a : SuzukiPositiveAperture) (c : ℝ) :
    ccmRestrictedWeilSourceQuadratic a
        (suzukiTaMovableCompletedCovarianceCCMResponse a c) =
      ‖suzukiTaRawDeficiency a c‖ ^ 2 -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
          ‖suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a c)‖ ^ 2 := by
  have h := inner_suzukiTa_eq a (suzukiTaRawDeficiency a c)
      (suzukiTaRawDeficiency a c)
  rw [inner_self_eq_norm_sq_to_K,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    inner_self_eq_norm_sq_to_K] at h
  have hre := congrArg Complex.re h
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre
  have hre' := hre
  rw [suzukiWeilIntervalForm_self_re_eq_source] at hre'
  change ‖suzukiTaRawDeficiency a c‖ * ‖suzukiTaRawDeficiency a c‖ =
      ccmRestrictedWeilSourceQuadratic a
        (suzukiTaMovableCompletedCovarianceCCMResponse a c) + _ at hre'
  simp only [pow_two]
  linarith

/-- Literal finite-prime action lands on the actual corrected movable covariance head, with the
Chebyshev and reciprocal-Mangoldt channels still coupled inside one signed integral. -/
theorem inner_polar_prime_movablePolarConstrainedResponse_eq_arithmetic_integral
    (a : SuzukiPositiveAperture) (c : ℝ) :
    inner ℂ (ccmPolarApertureVector a (1 / 2))
        (ccmFinitePrimeOperator a
          (ccmArchimedeanFormToAperture a
            (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c).1)) =
      ∫ x : ℝ, (centralInterval a.1).indicator (fun x =>
          (Real.exp (x / 2) : ℂ) *
            (((Chebyshev.psi (Real.exp (a.1 - x)) - Real.exp (a.1 - x) : ℝ) : ℂ) +
              (ccmReciprocalMangoldtError (a.1 + x) : ℂ) + (x : ℂ))) x *
        (ccmArchimedeanFormToAperture a
          (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c).1 : SoninL2) x := by
  exact inner_polar_prime_constrained_eq_arithmetic_integral a
    (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c)

/-- Completed Gamma--prime--polar action lands on the same actual constrained movable head.  Main
profiles have already cancelled in `ccmPolarBoundaryArithmeticProfile`; no regionwise estimate or
absolute-value separation occurs. -/
theorem inner_polarWeil_movablePolarConstrainedResponse_eq_boundaryArithmetic_integral
    (a : SuzukiPositiveAperture) (c : ℝ) :
    inner ℂ (ccmRestrictedWeilOperator a
      ⟨ccmPolarApertureVector a (1 / 2),
        ccmPolarApertureVector_mem_weilOperator_domain a (1 / 2)⟩)
        (ccmArchimedeanFormToAperture a
          (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c).1) =
      ∫ x : ℝ, (centralInterval a.1).indicator
          (ccmPolarBoundaryArithmeticProfile a) x *
        (ccmArchimedeanFormToAperture a
          (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c).1 : SoninL2) x := by
  exact inner_polarWeil_on_constrained_eq_boundaryArithmetic_integral a
    (suzukiTaMovableCompletedCovariancePolarConstrainedResponse a c)

end RHTower
