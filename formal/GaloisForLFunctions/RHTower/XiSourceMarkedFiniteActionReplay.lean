import GaloisForLFunctions.RHTower.ConstitutiveGammaCoronaTailRoosEmbedding
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Source-marked finite-action replay endpoint

The source-native Gamma Bockstein retains horizontal Xi grade at every ordinary-prime
Euler--Fisher coordinate.  This module gives the corresponding global endpoint: replaying each
Xi grade cofinally at one fixed coordinate while spending finite total transverse action is
equivalent to RH.

The condition is falsifiable at a single off-line divisor.  Its nonzero centered grade makes the
target coordinate nonzero, while finite action forces every cofinally recurrent coordinate to
vanish.  No prime-tail norm, zero-selected operator, or post-response marker is used.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- At one fixed ordinary-prime coordinate, every Xi divisor grade can be replayed cofinally by
a source history of finite total transverse action. -/
def XiSourceMarkedFiniteActionReplayAt (n : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    ∃ history : ℕ → RouteRTraceSequence × RouteRTraceSequence,
      Summable (fun j => collisionTransverseAction
        (routeRTraceCoordinateMarker n).toAddMonoidHom (history j)) ∧
      IsCofinalCollisionChargeRecurrent
        (routeRTraceCoordinateMarker n).toAddMonoidHom history
        (routeRPrimeGammaBocksteinSequence
          (primeDepthBVWoldXiCenteredRate q.1), 0)

/-- A finite-action recurrent replay at one source-native prime coordinate annihilates every Xi
horizontal grade and therefore proves RH. -/
theorem riemannHypothesis_of_xiSourceMarkedFiniteActionReplayAt
    (n : ℕ) (hreplay : XiSourceMarkedFiniteActionReplayAt n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro rho
  let q : XiZeroCopy := ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  obtain ⟨history, hsummable, hrecurrent⟩ := hreplay q
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 := by
    by_contra hne
    exact no_routeRPrimeGammaBockstein_summableCoordinateReplay
      n hne history hsummable hrecurrent
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hrate

/-- Under RH every Xi horizontal grade is zero, so the constant zero source history realizes the
finite-action recurrent replay law at every ordinary-prime coordinate. -/
theorem xiSourceMarkedFiniteActionReplayAt_of_riemannHypothesis
    (n : ℕ) (hRH : RiemannHypothesis) :
    XiSourceMarkedFiniteActionReplayAt n := by
  intro q
  let history : ℕ → RouteRTraceSequence × RouteRTraceSequence := fun _ => (0, 0)
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  refine ⟨history, ?_, ?_⟩
  · simp [history, collisionTransverseAction, collisionTransverseCharge]
  · intro ε hε N
    refine ⟨N, le_rfl, ?_⟩
    simp [history, hrate, collisionTransverseCharge,
      routeRPrimeGammaBocksteinSequence, hε]

/-- **One-prime finite-action replay law.** Source-marked cofinal recurrence with finite
transverse action at any fixed ordinary-prime coordinate is exactly RH. -/
theorem xiSourceMarkedFiniteActionReplayAt_iff_riemannHypothesis (n : ℕ) :
    XiSourceMarkedFiniteActionReplayAt n ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_xiSourceMarkedFiniteActionReplayAt n,
    xiSourceMarkedFiniteActionReplayAt_of_riemannHypothesis n⟩

end

end RHTower
