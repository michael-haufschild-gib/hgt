import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimitiveCompletedInteraction
import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Cofinal rigidity of EWQ gauges on the complete Riemann source

The primitive Euler--Wick interaction supplies only unit-modulus quadratic signs at every
unramified prime-depth coordinate.  This file tests the strongest possible coefficientwise use of
those signs on the complete positive Riemann resolution: the sign may vary arbitrarily with the
cofinal shell depth, but it must transport the normalized source tail at `s` to the tail at the
functional-equation reflection `1 - star s` exactly.

Such a transport exists exactly on the critical line.  The proof does not assume convergence of
the chosen gauges.  Taking norms removes every sign pointwise; the two complete-source tails then
converge to prime-two shell characters with equal norm, whose logarithmic moduli are opposite
horizontal displacements.  Hence the displacement is zero.

This is a strict EWQ no-go and a positive route classifier.  Scalar functional-equation phases,
arbitrary unramified quadratic sign schedules, and cofinal gauge switching cannot turn completed
EWQ reflection into the missing Riemann-source orientation law.  A surviving EWQ route must use a
non-unitary magnitude-changing incidence before the complete-source tail is formed.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Direct complete-resolution source point in the open right half-plane. -/
def ewqCompleteResolutionPoint
    (s : _root_.RHTower.CompleteResolutionOpenCriticalStrip) :
    _root_.RHTower.CompleteResolutionRightHalfPlane :=
  ⟨s.1, s.2.1⟩

/-- Functional-equation reflection of a complete-resolution strip point. -/
def ewqCompleteResolutionReflectionPoint
    (s : _root_.RHTower.CompleteResolutionOpenCriticalStrip) :
    _root_.RHTower.CompleteResolutionRightHalfPlane :=
  ⟨1 - star s.1, by
    have hstarRe : (star s.1).re = s.1.re := by simp
    simp only [sub_re, one_re]
    rw [hstarRe]
    linarith [s.2.2]⟩

/-- Strongest cofinal unit-gauge transport supplied by the primitive EWQ packet.  The selected
unramified prime-depth coordinate may change at every shell depth. -/
def EWQCompleteResolutionCofinalGaugeTransportAt
    (K : ℕ) (s : _root_.RHTower.CompleteResolutionOpenCriticalStrip) : Prop :=
  ∃ clock : ℕ → PrimePowerClockIndex,
    (∀ n, IsUnit ((((clock n).1 : ℕ) : ZMod 12))) ∧
      ∀ n : ℕ,
        _root_.RHTower.completeResolutionNormalizedSourceTailRatio K n
            (ewqCompleteResolutionReflectionPoint s) =
          eulerWickQuadraticDepthCharacter (clock n) *
            _root_.RHTower.completeResolutionNormalizedSourceTailRatio K n
              (ewqCompleteResolutionPoint s)

/-- **Cofinal EWQ rigidity.**  Even an arbitrary depth-dependent schedule of primitive quadratic
gauges transports the complete source to its reflection exactly only at the critical line. -/
theorem ewqCompleteResolutionCofinalGaugeTransportAt_iff
    (K : ℕ) (s : _root_.RHTower.CompleteResolutionOpenCriticalStrip) :
    EWQCompleteResolutionCofinalGaugeTransportAt K s ↔ s.1.re = 1 / 2 := by
  constructor
  · rintro ⟨clock, _hunramified, htransport⟩
    have hdirect :=
      _root_.RHTower.completeResolutionNormalizedSourceTailRatio_orientation K
        (ewqCompleteResolutionPoint s)
    have hreflected :=
      _root_.RHTower.completeResolutionNormalizedSourceTailRatio_orientation K
        (ewqCompleteResolutionReflectionPoint s)
    have hnormFunctions :
        (fun n : ℕ =>
          ‖_root_.RHTower.completeResolutionNormalizedSourceTailRatio K n
            (ewqCompleteResolutionReflectionPoint s)‖) =
        (fun n : ℕ =>
          ‖_root_.RHTower.completeResolutionNormalizedSourceTailRatio K n
            (ewqCompleteResolutionPoint s)‖) := by
      funext n
      rw [htransport n, norm_mul]
      rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one (clock n) with h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num
    have hdirectNorm := hdirect.1.norm
    have hreflectedNorm := hreflected.1.norm
    rw [hnormFunctions] at hreflectedNorm
    have hlimitNorm :
        ‖_root_.RHTower.shellTransferCharacter
            (ewqCompleteResolutionPoint s).1‖ =
          ‖_root_.RHTower.shellTransferCharacter
            (ewqCompleteResolutionReflectionPoint s).1‖ :=
      tendsto_nhds_unique hdirectNorm hreflectedNorm
    have hlog := congrArg Real.log hlimitNorm
    rw [hdirect.2, hreflected.2] at hlog
    have hreflectionRe :
        (ewqCompleteResolutionReflectionPoint s).1.re = 1 - s.1.re := by
      simp [ewqCompleteResolutionReflectionPoint]
    have hdirectRe :
        (ewqCompleteResolutionPoint s).1.re = s.1.re := rfl
    rw [hreflectionRe, hdirectRe] at hlog
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    ring_nf at hlog
    have hfactor : (1 - 2 * s.1.re) * Real.log 2 = 0 := by
      nlinarith
    have hlinear : 1 - 2 * s.1.re = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hlogTwo.ne'
    linarith
  · intro hline
    let p : Nat.Primes := ⟨13, by norm_num⟩
    let x : PrimePowerClockIndex := (p, 1)
    have hp : IsUnit (((p : ℕ) : ZMod 12)) := by
      rw [ZMod.isUnit_iff_coprime]
      norm_num
    have hx : eulerWickQuadraticDepthCharacter x = 1 := by
      rw [eulerWickQuadraticDepthCharacter]
      change quadraticResidueProductPrimeCoefficient p ^ 2 = 1
      exact quadraticResidueProductPrimeCoefficient_sq p
    have hreflect : (1 - star s.1) = s.1 := by
      rw [Complex.ext_iff]
      constructor
      · simp [hline]
        norm_num
      · simp
    refine ⟨fun _ => x, fun _ => hp, fun n => ?_⟩
    rw [hx, one_mul]
    congr 1
    apply Subtype.ext
    exact hreflect

/-- Every actual Xi divisor supplies a point of the complete-resolution critical strip. -/
def ewqXiDivisorCompleteResolutionPoint
    (rho : _root_.RHTower.XiDivisorSupport) :
    _root_.RHTower.CompleteResolutionOpenCriticalStrip :=
  ⟨(rho : ℂ), _root_.RHTower.xi_divisor_support_re_mem_open_unit rho⟩

/-- Cofinal primitive EWQ gauge transport at one actual Xi divisor. -/
def EWQXiDivisorCofinalGaugeTransportAt
    (K : ℕ) (rho : _root_.RHTower.XiDivisorSupport) : Prop :=
  EWQCompleteResolutionCofinalGaugeTransportAt K
    (ewqXiDivisorCompleteResolutionPoint rho)

/-- Divisor-selected form of the cofinal rigidity classifier. -/
theorem ewqXiDivisorCofinalGaugeTransportAt_iff
    (K : ℕ) (rho : _root_.RHTower.XiDivisorSupport) :
    EWQXiDivisorCofinalGaugeTransportAt K rho ↔ (rho : ℂ).re = 1 / 2 := by
  exact ewqCompleteResolutionCofinalGaugeTransportAt_iff K
    (ewqXiDivisorCompleteResolutionPoint rho)

/-- No primitive EWQ sign schedule can repair an off-line complete-source reflection tail. -/
theorem no_ewqXiDivisorCofinalGaugeTransportAt_of_re_ne_half
    (K : ℕ) (rho : _root_.RHTower.XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬EWQXiDivisorCofinalGaugeTransportAt K rho := by
  exact fun h => hoff ((ewqXiDivisorCofinalGaugeTransportAt_iff K rho).1 h)

/-- Global cofinal EWQ gauge-transport law over the actual Xi divisor. -/
def EveryEWQXiDivisorCofinalGaugeTransport (K : ℕ) : Prop :=
  ∀ rho : _root_.RHTower.XiDivisorSupport,
    EWQXiDivisorCofinalGaugeTransportAt K rho

/-- Global endpoint: cofinal primitive EWQ gauge transport is exactly RH, for every fixed
complete-resolution cutoff.  The theorem classifies the missing producer; it does not assert it. -/
theorem everyEWQXiDivisorCofinalGaugeTransport_iff_riemannHypothesis
    (K : ℕ) :
    EveryEWQXiDivisorCofinalGaugeTransport K ↔ _root_.RiemannHypothesis := by
  constructor
  · intro htransport
    apply _root_.RHTower.riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (ewqXiDivisorCofinalGaugeTransportAt_iff K rho).1 (htransport rho)
  · intro hRH rho
    exact (ewqXiDivisorCofinalGaugeTransportAt_iff K rho).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end GaloisForLFunctions.RHTower
