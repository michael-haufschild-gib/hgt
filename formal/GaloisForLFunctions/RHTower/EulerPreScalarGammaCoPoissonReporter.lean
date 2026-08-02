import GaloisForLFunctions.RHTower.EulerPositiveGammaPoleCancellation
import GaloisForLFunctions.RHTower.EulerAffineGammaXiWardTransport

/-!
# Full-Euler pre-scalar Gamma/co-Poisson reporter

The full-Euler Fisher tangent reconstructs the completed Xi current only after division by the
vanishing overlap factor `(sigma - 1) B_sigma(u)`.  This file keeps that factor and all affine
prime/Gamma terms before division.

Multiplying the literal pole-cancelled Euler vector by `sigma - 1` gives one actual positive
Hilbert source.  Its coefficient against every damped Euler state is exactly the division-free
prime numerator.  Adding the archimedean affine term, still before division, gives the completed
Xi numerator and factors it as

`graphDenominator * continuedPrimeArchSourceRelativeTrace`.

The construction has a sharp obstruction: its squared source norm tends to `8`, not the
four-unit Ward budget.  Thus the desired pre-scalar source object exists, but no direct positive
scalar use of this literal carrier can supply four-unit completion.  Any successful compression
must remove the exact factor-two excess while preserving the division-free coefficient family.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section
namespace RHTower

/-- Actual full-Euler source after moving the polar cancellation before overlap division. -/
def eulerPositivePreScalarGammaSource
    (sigma : ℝ) (hsigma : 1 < sigma) : EulerPositiveL2 :=
  (((sigma - 1 : ℝ) : ℂ) •
    eulerPositiveGammaPoleCancelledLp sigma hsigma)

/-- Before division, pole cancellation is a bounded affine combination of the normalized Euler
state and its centered Fisher tangent. -/
theorem eulerPositivePreScalarGammaSource_eq_base_sub_tangent
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositivePreScalarGammaSource sigma hsigma =
      (((2 * (sigma - 1) * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) •
        eulerPositiveStateLp sigma hsigma) -
      eulerPositiveCriticalFisherTangentLp sigma hsigma := by
  apply lp.ext
  funext n
  change
    ((sigma - 1 : ℝ) : ℂ) *
        eulerPositiveGammaPoleCancelledWeight sigma n =
      ((2 * (sigma - 1) * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) *
          eulerPositiveStateWeight sigma n -
        eulerPositiveCriticalFisherTangentWeight sigma n
  rw [eulerPositiveGammaPoleCancelledWeight,
    eulerPositiveCriticalFisherTangentWeight]
  push_cast
  ring

/-- Exact source capacity before taking the critical limit. -/
theorem norm_eulerPositivePreScalarGammaSource_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositivePreScalarGammaSource sigma hsigma‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * eulerPositiveLogMoment 2 sigma := by
  rw [eulerPositivePreScalarGammaSource, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hsigma)]
  rw [show
    ((sigma - 1) *
      ‖eulerPositiveGammaPoleCancelledLp sigma hsigma‖) ^ 2 =
      (sigma - 1) ^ 2 *
        ‖eulerPositiveGammaPoleCancelledLp sigma hsigma‖ ^ 2 by ring,
    norm_eulerPositiveGammaPoleCancelledLp_sq hsigma]
  ring

/-- The positive pre-scalar source has sharp limiting energy eight. -/
theorem tendsto_norm_eulerPositivePreScalarGammaSource_sq :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖eulerPositivePreScalarGammaSource sigma hsigma‖ ^ 2
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 8) := by
  apply
    tendsto_sub_one_sq_mul_norm_eulerPositiveGammaPoleCancelledLp_sq.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  rw [norm_eulerPositivePreScalarGammaSource_sq hsigma,
    norm_eulerPositiveGammaPoleCancelledLp_sq hsigma]
  ring

/-- Consequently the literal positive source eventually exceeds the four-unit Ward budget. -/
theorem eventually_four_lt_norm_eulerPositivePreScalarGammaSource_sq :
    ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      if hsigma : 1 < sigma then
        4 < ‖eulerPositivePreScalarGammaSource sigma hsigma‖ ^ 2
      else False := by
  have hopen : Ioi (4 : ℝ) ∈ 𝓝 (8 : ℝ) := Ioi_mem_nhds (by norm_num)
  have hevent :=
    tendsto_norm_eulerPositivePreScalarGammaSource_sq.eventually hopen
  filter_upwards [hevent, self_mem_nhdsWithin] with sigma hfour hsigma
  change 1 < sigma at hsigma
  simpa [hsigma] using hfour

/-- The damped Euler family represents the full-Euler overlap as one Hilbert coefficient. -/
theorem inner_eulerPositiveState_dampedState_eq_affineOverlap
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositiveStateLp sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      eulerAffineBoundaryOverlap
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveStateLp,
    eulerPositiveCriticalDampedStateLp, RCLike.inner_apply]
  rw [show
    (fun n : ℕ+ =>
      eulerPositiveCriticalDampedStateWeight sigma u n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
      fun n : ℕ+ =>
        ((eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n : ℝ) : ℂ) by
    funext n
    rw [eulerPositiveCriticalDampedStateWeight]
    have hnorm :
        eulerPositiveStateWeight sigma n *
          (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_eulerPositiveStateWeight_sq hsigma]
    rw [show
      (eulerPositiveCriticalDamping sigma u n : ℂ) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveCriticalDamping sigma u n : ℂ) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) by ring,
      hnorm]
    push_cast
    ring]
  rw [← Complex.ofReal_tsum,
    tsum_eulerPositiveProbability_mul_criticalDamping hsigma hu,
    Complex.ofReal_div,
    ofReal_eulerPositiveTotal_eq_riemannZeta
      (one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu),
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]
  unfold eulerAffineBoundaryOverlap
  congr 2
  apply Complex.ext <;>
    simp [eulerPositiveCriticalBoundaryParameter]

/-- The graph denominator is itself a source coefficient, retained without inversion. -/
def eulerPositivePreScalarGraphDenominator
    (sigma u : ℝ) : ℂ :=
  ((sigma - 1 : ℝ) : ℂ) *
    eulerAffineBoundaryOverlap
      (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ)

/-- The pre-scalar source coefficient is exactly the affine prime numerator. -/
theorem inner_eulerPositivePreScalarGammaSource_dampedState
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositivePreScalarGammaSource sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      2 * eulerPositivePreScalarGraphDenominator sigma u *
          infinitePrimeFlux (sigma : ℂ) -
        eulerAffineFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  rw [eulerPositivePreScalarGammaSource_eq_base_sub_tangent hsigma,
    inner_sub_left, inner_smul_left,
    inner_eulerPositiveState_dampedState_eq_affineOverlap hsigma hu,
    inner_eulerPositiveFisherTangent_dampedState_eq_affineScore hsigma hu]
  have hstateMean :
      (eulerPositiveLogMoment 1 sigma : ℂ) =
        infinitePrimeFlux (sigma : ℂ) := by
    rw [ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux hsigma]
  have hstarCoeff :
      (starRingEnd ℂ)
          (((2 * (sigma - 1) *
          eulerPositiveLogMoment 1 sigma : ℝ) : ℂ)) =
        (((2 * (sigma - 1) *
          eulerPositiveLogMoment 1 sigma : ℝ) : ℂ)) := by
    exact Complex.conj_ofReal _
  rw [hstarCoeff]
  unfold eulerPositivePreScalarGraphDenominator
  push_cast
  rw [hstateMean]
  ring

/-- After the source identity, the prime numerator is the shifted prime flux times the retained
graph denominator.  No overlap division is used. -/
theorem inner_eulerPositivePreScalarGammaSource_dampedState_eq_shiftedFlux
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositivePreScalarGammaSource sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      2 * eulerPositivePreScalarGraphDenominator sigma u *
        infinitePrimeFlux
          (eulerPositiveCriticalBoundaryParameter sigma u : ℂ) := by
  rw [inner_eulerPositivePreScalarGammaSource_dampedState hsigma hu]
  have hshift :
      1 < (((sigma : ℂ) +
        (u : ℂ) * ((sigma - 1 : ℝ) : ℂ))).re := by
    push_cast
    simpa [eulerPositiveCriticalBoundaryParameter] using
      one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  rw [eulerAffineFisherScore_eq_current_difference
    (by simpa using hsigma) hshift]
  have hparameter :
      ((sigma : ℂ) +
        (u : ℂ) * ((sigma - 1 : ℝ) : ℂ)) =
      (eulerPositiveCriticalBoundaryParameter sigma u : ℂ) := by
    apply Complex.ext <;>
      simp [eulerPositiveCriticalBoundaryParameter]
  rw [hparameter]
  unfold eulerPositivePreScalarGraphDenominator
  ring

/-- Completed division-free affine numerator: the archimedean term is added before any scalar
overlap division. -/
def eulerPositivePreScalarGammaXiNumerator
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) : ℂ :=
  (-I / 2) *
    (inner ℂ
        (eulerPositivePreScalarGammaSource sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) -
      2 * eulerPositivePreScalarGraphDenominator sigma u *
        logDeriv archFactor
          (eulerPositiveCriticalBoundaryParameter sigma u : ℂ))

/-- **Pre-scalar Gamma/co-Poisson/Xi graph factorization.**  The literal positive Euler source,
the affine Gamma term, and the continued Xi source trace form one exact division-free graph. -/
theorem eulerPositivePreScalarGammaXiNumerator_eq_denominator_mul_continued
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositivePreScalarGammaXiNumerator sigma u hsigma hu =
      eulerPositivePreScalarGraphDenominator sigma u *
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)) := by
  rw [eulerPositivePreScalarGammaXiNumerator,
    inner_eulerPositivePreScalarGammaSource_dampedState_eq_shiftedFlux
      hsigma hu,
    continuedPrimeArchSourceRelativeTrace,
    xiWardCenteredCoordinate_source]
  ring

end RHTower
