import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationLocalAnalyticBranchNoGo

/-!
# HB pre-divisor analytic left-QNM two-leg no-go

The exact moving-horizon/AIME cancellation coefficient is the horizontal pre-divisor optical
susceptibility.  Allowing the left QNM covector and right response to vary independently does not
restore a holomorphic compensation channel: continuous-dual evaluation is complex bilinear, so
jointly analytic legs still produce an analytic scalar coefficient.

Consequently no such pair can match the forced susceptibility on any nonempty open patch of the
critical strip.  The obstruction is dimension-free and requires no completeness assumption on the
response space.  Antiholomorphic, Hermitian, distributional, support-changing, or sheet-changing
legs remain outside its scope.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Closed proposition excluding a jointly analytic complex-bilinear left-QNM/right-response
realization of the pre-divisor optical cancellation profile. -/
def D4HBPreDivisorAnalyticLeftQNMTwoLegRouteKilled : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E],
    ¬ ∃ (Ω : Set ℂ) (left : ℂ → E →L[ℂ] ℂ) (right : ℂ → E),
      IsOpen Ω ∧
      Ω.Nonempty ∧
      Ω ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
      AnalyticOnNhd ℂ left Ω ∧
      AnalyticOnNhd ℂ right Ω ∧
      ∀ z ∈ Ω,
        left z (right z) =
          (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ)

/-- **HB analytic two-leg route-class kill.** Joint complex analyticity of independently varying
dual and response legs cannot realize the forced horizontal HB compensation profile on any
nonempty open critical-strip patch. -/
theorem d4HBPreDivisorAnalyticLeftQNMTwoLegRouteKilled :
    D4HBPreDivisorAnalyticLeftQNMTwoLegRouteKilled := by
  intro E _ _
  rintro ⟨Ω, left, right, hΩ, hΩne, hΩsub, hleft, hright, hprofile⟩
  apply not_exists_localAnalyticBranch_preDivisorOpticalCancellationSusceptibility
  refine ⟨Ω, (fun z => left z (right z)), hΩ, hΩne, hΩsub, ?_, hprofile⟩
  apply DifferentiableOn.analyticOnNhd _ hΩ
  intro z hz
  exact ((hleft z hz).differentiableAt.clm_apply
    (hright z hz).differentiableAt).differentiableWithinAt

end

end RHTower
