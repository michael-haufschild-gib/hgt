import GaloisForLFunctions.RHTower.EulerPreScalarGammaOrthogonalFourPlusFourLaw

/-!
# Route P: pointed four-unit transverse reporter

The eight-unit full-Euler pre-scalar reporter contains two orthogonal four-unit records.  This
file proves that the radial record is pure gauge after graph normalization: its normalized
coefficient is independent of the inward node.  Hence every pointed normalized coefficient
difference is carried exactly by the transverse Fisher record, whose critical energy is four.

Adding the pointed archimedean difference produces the exact pointed continued Xi trace.  This
is a lossless four-unit reduction for pointed data, not a projection of the full coefficient
family.
-/

open Complex Filter Set
open scoped Topology

namespace RHTower

noncomputable section

/-- The retained full-Euler graph denominator never vanishes on the real inward ray. -/
theorem eulerPositivePreScalarGraphDenominator_ne_zero
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositivePreScalarGraphDenominator sigma u ≠ 0 := by
  unfold eulerPositivePreScalarGraphDenominator eulerAffineBoundaryOverlap
  apply mul_ne_zero
  · exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  · apply div_ne_zero
    · apply riemannZeta_ne_zero_of_one_lt_re
      push_cast
      simpa [eulerPositiveCriticalBoundaryParameter] using
        one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
    · exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)

/-- The radial four-unit record reports only the base prime current times the graph
denominator. -/
theorem inner_eulerPositivePreScalarGammaRadialSource_dampedState
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositivePreScalarGammaRadialSource sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      2 * eulerPositivePreScalarGraphDenominator sigma u *
        infinitePrimeFlux (sigma : ℂ) := by
  rw [eulerPositivePreScalarGammaRadialSource, inner_smul_left,
    inner_eulerPositiveState_dampedState_eq_affineOverlap hsigma hu]
  have hmean :
      (eulerPositiveLogMoment 1 sigma : ℂ) =
        infinitePrimeFlux (sigma : ℂ) := by
    rw [ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux hsigma]
  have hstar :
      (starRingEnd ℂ)
          (((2 * (sigma - 1) * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ)) =
        (((2 * (sigma - 1) * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ)) :=
    Complex.conj_ofReal _
  rw [hstar]
  unfold eulerPositivePreScalarGraphDenominator
  push_cast
  rw [hmean]
  ring

/-- The transverse four-unit record reports exactly the pointed prime-current difference times
the same retained graph denominator. -/
theorem inner_eulerPositivePreScalarGammaTransverseSource_dampedState
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      2 * eulerPositivePreScalarGraphDenominator sigma u *
        (infinitePrimeFlux
            (eulerPositiveCriticalBoundaryParameter sigma u : ℂ) -
          infinitePrimeFlux (sigma : ℂ)) := by
  rw [eulerPositivePreScalarGammaTransverseSource, inner_neg_left,
    inner_eulerPositiveFisherTangent_dampedState_eq_affineScore hsigma hu]
  have hshift :
      1 < (((sigma : ℂ) +
        (u : ℂ) * ((sigma - 1 : ℝ) : ℂ))).re := by
    push_cast
    simpa [eulerPositiveCriticalBoundaryParameter] using
      one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  rw [eulerAffineFisherScore_eq_current_difference
    (by simpa using hsigma) hshift]
  have hparameter :
      ((sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ)) =
        (eulerPositiveCriticalBoundaryParameter sigma u : ℂ) := by
    apply Complex.ext <;>
      simp [eulerPositiveCriticalBoundaryParameter]
  rw [hparameter]
  unfold eulerPositivePreScalarGraphDenominator
  ring

/-- Graph-normalized coefficient of an actual full-Euler source against the inward damped
state. -/
def eulerPositivePreScalarGraphNormalizedCoefficient
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (source : EulerPositiveL2) : ℂ :=
  inner ℂ source
      (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) /
    eulerPositivePreScalarGraphDenominator sigma u

/-- **Radial gauge law.**  After graph normalization the entire radial channel is constant in
the inward node. -/
theorem eulerPositivePreScalarGraphNormalizedCoefficient_radial
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositivePreScalarGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaRadialSource sigma hsigma) =
      2 * infinitePrimeFlux (sigma : ℂ) := by
  rw [eulerPositivePreScalarGraphNormalizedCoefficient,
    inner_eulerPositivePreScalarGammaRadialSource_dampedState hsigma hu]
  field_simp [eulerPositivePreScalarGraphDenominator_ne_zero hsigma hu]

/-- The graph-normalized transverse coefficient is exactly the pointed prime-current
difference. -/
theorem eulerPositivePreScalarGraphNormalizedCoefficient_transverse
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositivePreScalarGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) =
      2 * (infinitePrimeFlux
            (eulerPositiveCriticalBoundaryParameter sigma u : ℂ) -
          infinitePrimeFlux (sigma : ℂ)) := by
  rw [eulerPositivePreScalarGraphNormalizedCoefficient,
    inner_eulerPositivePreScalarGammaTransverseSource_dampedState hsigma hu]
  field_simp [eulerPositivePreScalarGraphDenominator_ne_zero hsigma hu]

/-- At the base node the transverse pointed reporter vanishes exactly. -/
@[simp] theorem eulerPositivePreScalarGraphNormalizedCoefficient_transverse_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositivePreScalarGraphNormalizedCoefficient sigma 0 hsigma
        (le_refl 0)
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) = 0 := by
  rw [eulerPositivePreScalarGraphNormalizedCoefficient_transverse hsigma (le_refl 0)]
  simp [eulerPositiveCriticalBoundaryParameter]

/-- **Pointed four-unit cancellation.**  The normalized full-reporter difference between an
inward node and the base node is exactly the normalized transverse coefficient at the inward
node.  The radial four-unit record cancels without loss. -/
theorem eulerPositivePreScalarGraphNormalizedCoefficient_source_sub_base_eq_transverse
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositivePreScalarGraphNormalizedCoefficient sigma u hsigma hu
          (eulerPositivePreScalarGammaSource sigma hsigma) -
        eulerPositivePreScalarGraphNormalizedCoefficient sigma 0 hsigma
          (le_refl 0) (eulerPositivePreScalarGammaSource sigma hsigma) =
      eulerPositivePreScalarGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) := by
  have h_add (v : ℝ) (hv : 0 ≤ v) (x y : EulerPositiveL2) :
      eulerPositivePreScalarGraphNormalizedCoefficient sigma v hsigma hv (x + y) =
        eulerPositivePreScalarGraphNormalizedCoefficient sigma v hsigma hv x +
          eulerPositivePreScalarGraphNormalizedCoefficient sigma v hsigma hv y := by
    unfold eulerPositivePreScalarGraphNormalizedCoefficient
    rw [inner_add_left, add_div]
  rw [eulerPositivePreScalarGammaSource_eq_radial_add_transverse hsigma]
  rw [h_add u hu, h_add 0 (le_refl 0)]
  rw [eulerPositivePreScalarGraphNormalizedCoefficient_radial hsigma hu,
    eulerPositivePreScalarGraphNormalizedCoefficient_radial hsigma (le_refl 0),
    eulerPositivePreScalarGraphNormalizedCoefficient_transverse_zero hsigma]
  ring

/-- Pointed completed reporter obtained from only the transverse four-unit source record plus
the explicit archimedean difference. -/
def eulerPositiveTransverseGammaXiPointedReporter
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) : ℂ :=
  (-I / 2) *
    (eulerPositivePreScalarGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) -
      2 * (logDeriv archFactor
              (eulerPositiveCriticalBoundaryParameter sigma u : ℂ) -
            logDeriv archFactor (sigma : ℂ)))

/-- **Four-unit pointed Xi reporter.**  The transverse full-Euler source, whose critical energy
is four, reconstructs every pointed continued Xi trace difference exactly after the explicit
Gamma correction. -/
theorem eulerPositiveTransverseGammaXiPointedReporter_eq_continued_sub_base
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositiveTransverseGammaXiPointedReporter sigma u hsigma hu =
      continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (sigma : ℂ)) := by
  rw [eulerPositiveTransverseGammaXiPointedReporter,
    eulerPositivePreScalarGraphNormalizedCoefficient_transverse hsigma hu]
  simp only [continuedPrimeArchSourceRelativeTrace,
    xiWardCenteredCoordinate_source]
  ring

/-- The source used by the exact pointed Xi reporter has sharp critical energy four. -/
theorem tendsto_norm_eulerPositiveTransverseGammaXiPointedReporter_source_sq :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖eulerPositivePreScalarGammaTransverseSource sigma hsigma‖ ^ (2 : ℕ)
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 4) :=
  tendsto_norm_eulerPositivePreScalarGammaTransverseSource_sq

end

end RHTower
