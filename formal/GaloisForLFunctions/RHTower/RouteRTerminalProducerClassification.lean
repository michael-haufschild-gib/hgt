import GaloisForLFunctions.RHTower.RouteRPrepolarTerminalNoGo
import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugePositivePolarUniversalityNoGo
import GaloisForLFunctions.RHTower.RouteRSourceTopologyObserverDichotomy
import GaloisForLFunctions.RHTower.RouteRStrongApproximationCompactEscape
import GaloisForLFunctions.RHTower.RouteRXiMultiplierCalkinGrowthObstruction
import GaloisForLFunctions.RHTower.RouteRXiJetPrincipalCalkinNonErasure
import GaloisForLFunctions.RHTower.RouteRReciprocalLogFisherEntranceWall
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality

/-!
# Route R terminal producer classification

The intrinsic pre-polar producer category is empty.  The only surviving interfaces in the Route R
frontier audit are:

1. the external positive polar comparison;
2. source-selected pointwise two-orientation positive non-amplification;
3. divisor-specialized gauge-invariant prime-isotropy observer selection;
4. collective compactness of the fixed `(2,3)` receiver;
5. a singular coefficient-faithful Xi/Calkin factorization;
6. a compact first-Xi-jet principal coefficient modulo the compact ideal;
7. loss-zero landing of the fixed inverse-log Fisher vector.

This module proves that every one of those surviving interfaces is equivalent to RH.  Their
disjunction is therefore not a weaker source theorem and supplies no independent producer.  This
is the formal terminal classification of the audited Route R architecture, not a proof of RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- Singular coefficient-faithful Xi/Calkin landing for the fixed aperture-one receiver. -/
def RouteRXiCalkinFactorization : Prop :=
  ∀ rho : XiDivisorSupport,
    ∃ S K : RouteRPhysicalOperator,
      IsCompactOperator K ∧
      routeRTwoThreeStokesSoninCommutator 1
          (primeDepthBVWoldXiCenteredRate rho) =
        XiC (xiSpectralPointSupport rho) • S + K

/-- The singular Xi/Calkin interface is exactly RH.  In the reverse direction RH makes the
receiver itself compact; no singular multiplier construction is needed. -/
theorem routeRXiCalkinFactorization_iff_riemannHypothesis :
    RouteRXiCalkinFactorization ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_routeRTwoThree_XiCalkinFactorization (by norm_num)
  · intro hRH rho
    let T := routeRTwoThreeStokesSoninCommutator 1
      (primeDepthBVWoldXiCenteredRate rho)
    have hrate : primeDepthBVWoldXiCenteredRate rho = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
    have hcompact : IsCompactOperator T := by
      dsimp [T]
      exact (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff
        (by norm_num) _).2 hrate
    refine ⟨0, T, hcompact, ?_⟩
    simp [T]

/-- Loss-zero fixed-vector landing: the literal inverse-log Fisher potential, with its nonzero
unit coefficient, lands in the fixed prime `ℓ²` carrier on every Xi divisor fibre. -/
def RouteRLossZeroFisherPhysicalLanding : Prop :=
  ∀ rho : XiDivisorSupport,
    Memℓp (fun p : Nat.Primes =>
      (1 : ℂ) * (((p : ℕ) : ℝ) : ℂ) ^ ((rho : ℂ) - 1 / 2) *
        (routeRFisherLogPotential p : ℂ)) 2

/-- Landing on all fibres includes the functional-equation reflected fibre, so the one-sided
entrance wall becomes equality.  Hence the fixed-vector interface is exactly RH. -/
theorem routeRLossZeroFisherPhysicalLanding_iff_riemannHypothesis :
    RouteRLossZeroFisherPhysicalLanding ↔ RiemannHypothesis := by
  constructor
  · intro hlanding
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    have hupper : (rho : ℂ).re ≤ 1 / 2 :=
      (memℓp_two_xiDivisor_coefficient_iff (1 : ℂ) one_ne_zero rho).1
        (hlanding rho)
    have hreflected : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).re ≤ 1 / 2 :=
      (memℓp_two_xiDivisor_coefficient_iff (1 : ℂ) one_ne_zero
        (xiZeroLineConjEquiv rho)).1 (hlanding (xiZeroLineConjEquiv rho))
    rw [xiZeroLineConjEquiv_apply] at hreflected
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hreflected
    change z.re = 1 / 2
    change z.re ≤ 1 / 2 at hupper
    change 1 - z.re ≤ 1 / 2 at hreflected
    linarith
  · intro hRH rho
    exact (memℓp_two_xiDivisor_coefficient_iff (1 : ℂ) one_ne_zero rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho).le

/-- Complete branch list left after the dependency audit.  The first branch is the intrinsic
category already proved empty; the remaining branches are the explicit external receiver
interfaces, not hidden assumptions. -/
inductive RouteRSurvivingProducer where
  | intrinsic : RouteRPrepolarIntrinsicAnnihilator → RouteRSurvivingProducer
  | externalPositivePolar : RouteRExternalPositivePolarHandoff → RouteRSurvivingProducer
  | pointwiseTwoOrientationPositivePolar :
      RouteRPointwiseTwoOrientationPositivePolarHandoff →
        RouteRSurvivingProducer
  | gaugeInvariantPrimeIsotropyObserver :
      (∀ rho : XiDivisorSupport,
        RouteRPrimeIsotropyGaugeInvariantPhysicalObserver rho) →
      RouteRSurvivingProducer
  | collectiveCompactness :
      (∀ rho : XiDivisorSupport,
        IsCollectivelyCompactStronglyApproximable
          (routeRTwoThreeStokesSoninCommutator 1
            (primeDepthBVWoldXiCenteredRate rho))) →
      RouteRSurvivingProducer
  | singularXiCalkin : RouteRXiCalkinFactorization → RouteRSurvivingProducer
  | singularXiJetPrincipal :
      RouteRCompactXiJetPrincipalLanding 1 → RouteRSurvivingProducer
  | lossZeroFisher : RouteRLossZeroFisherPhysicalLanding → RouteRSurvivingProducer

/-- **Terminal Route R theorem.**  The audited producer category is inhabited exactly when RH is
already available.  Intrinsic source structure contributes no inhabitant; every surviving
external branch is an RH-equivalent receiver. -/
theorem nonempty_routeRSurvivingProducer_iff_riemannHypothesis :
    Nonempty RouteRSurvivingProducer ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨P⟩
    cases P with
    | intrinsic P =>
        exact False.elim
          (routeRPrepolarIntrinsicProducer_cannot_annihilate_horizontalCarrier ⟨P⟩)
    | externalPositivePolar P => exact P.riemannHypothesis
    | pointwiseTwoOrientationPositivePolar P =>
        exact routeRPointwiseTwoOrientationPositivePolarHandoff_iff_rh.mp P
    | gaugeInvariantPrimeIsotropyObserver P =>
        exact global_routeRPrimeIsotropyGaugeInvariantPhysicalObserver_iff_rh.mp P
    | collectiveCompactness P =>
        exact (routeRTwoThreeStokesSoninCommutator_globalCollectivelyCompactStronglyApproximable_iff_rh
          (by norm_num)).1 P
    | singularXiCalkin P =>
        exact routeRXiCalkinFactorization_iff_riemannHypothesis.mp P
    | singularXiJetPrincipal P =>
        exact (routeRCompactXiJetPrincipalLanding_iff_rh
          (A := 1) (by norm_num)).mp P
    | lossZeroFisher P =>
        exact routeRLossZeroFisherPhysicalLanding_iff_riemannHypothesis.mp P
  · intro hRH
    obtain ⟨P⟩ :=
      nonempty_routeRExternalPositivePolarHandoff_iff_riemannHypothesis.mpr hRH
    exact ⟨RouteRSurvivingProducer.externalPositivePolar P⟩

/-- No strictly intrinsic Route R producer survives the audit, while adding any admitted external
producer is logically equivalent to adding RH itself. -/
theorem routeR_intrinsic_dead_external_equivalent :
    (¬ Nonempty RouteRPrepolarIntrinsicAnnihilator) ∧
      (Nonempty RouteRSurvivingProducer ↔ RiemannHypothesis) :=
  ⟨routeRPrepolarIntrinsicProducer_cannot_annihilate_horizontalCarrier,
    nonempty_routeRSurvivingProducer_iff_riemannHypothesis⟩

end

end RHTower
