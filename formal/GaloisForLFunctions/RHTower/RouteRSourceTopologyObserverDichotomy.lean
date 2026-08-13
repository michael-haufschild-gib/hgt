import GaloisForLFunctions.RHTower.RouteRPreDivisorGammaCoronaGlobalizationNoGo
import GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyVerticalGauge
import GaloisForLFunctions.RHTower.DeningerArithmeticAdelicKummerNoGo

/-!
# Route R source topology / observer dichotomy

This module closes the topology and observer choices around the retained
rational-adelic prime-isotropy class and the singular cross-prime corona.

* A continuous map from the packet Hilbert space into any Hausdorff normed
  target which kills the finite arithmetic core is zero, because that core
  is dense.  It therefore cannot retain the full-support horizon.
* On algebraic source `H¹`, a marked Stokes splitting realizes every target
  vector, including the fixed physical corona action.  Mere algebraic
  descent contains no selection information.
* Requiring invariance under the source's full vertical shear gauge erases
  the retained ordinary-prime class.  For the actual physical corona target,
  such an invariant observer exists exactly on the critical line.
* Before divisor specialization, an invariant observer valid at every grade
  and retained coefficient is impossible, witnessed at `(a,c)=(1,1)`.

No RH, critical-line placement, source-dagger identity, same-fibre norm
identity, or physical annihilation premise is used in the no-go statements.
-/

open Complex

namespace RHTower

noncomputable section

private abbrev RouteRPacketHilbert :=
  DeningerCalderonWittCrossPrimePacketHilbert

private abbrev RouteRSingularCorona :=
  DeningerCalderonWittCrossPrimeSingularCorona

private abbrev RouteRPrimeSourceH1 :=
  (ccmRationalAdelicPrimeRelativeComplex routeRTwoPrime).H1

/-! ## Hausdorff continuous horn -/

/-- Every continuous reporter killing the finite arithmetic core is zero. -/
theorem routeR_continuousReporter_eq_zero_of_arithmeticCore
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (q : RouteRPacketHilbert →L[ℂ] Y)
    (hkill : ∀ x : RouteRPacketHilbert,
      x ∈ deningerCalderonWittCrossPrimeArithmeticPacketCore → q x = 0) :
    q = 0 := by
  have hfun : (q : RouteRPacketHilbert → Y) = 0 :=
    GaloisForLFunctions.RHTower.deningerAdelicKummer_continuous_eq_zero_of_dense
      q q.continuous
      (deningerCalderonWittCrossPrimeArithmeticPacketCore :
        Set RouteRPacketHilbert)
      deningerCalderonWittCrossPrimeArithmeticPacketCore_dense hkill
  ext x
  exact congrFun hfun x

/-- Proposed Hausdorff continuous quotient which kills every finite source
packet but retains the full-support horizon. -/
structure RouteRContinuousArithmeticCoreHorizonLanding
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℂ Y] where
  reporter : RouteRPacketHilbert →L[ℂ] Y
  kills_arithmeticCore : ∀ x : RouteRPacketHilbert,
    x ∈ deningerCalderonWittCrossPrimeArithmeticPacketCore → reporter x = 0
  retains_horizon : reporter deningerCalderonWittCrossPrimePacketHorizon ≠ 0

/-- The Hausdorff continuous horn is empty for every normed target. -/
theorem routeR_no_continuousArithmeticCoreHorizonLanding
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℂ Y] :
    ¬ Nonempty (RouteRContinuousArithmeticCoreHorizonLanding Y) := by
  rintro ⟨P⟩
  have hzero := routeR_continuousReporter_eq_zero_of_arithmeticCore
    P.reporter P.kills_arithmeticCore
  exact P.retains_horizon (by rw [hzero]; rfl)

/-! ## Algebraic marked horn -/

/-- The actual physical singular-corona value which a source observer would
have to select. -/
def routeRPrimeIsotropyPhysicalCoronaTarget
    (rho : XiDivisorSupport) : RouteRSingularCorona :=
  routeRTwoThreeGammaSingularCoronaAction rho
    (routeRTwoThreeGammaSingularCoronaPhysicalLift rho)

/-- Marking a Stokes splitting makes the actual physical target available at
every Xi fibre, independently of its grade.  Thus algebraic existence alone
cannot be a producer. -/
theorem exists_routeRPrimeIsotropyMarkedPhysicalObserver
    (rho : XiDivisorSupport) :
    ∃ P : RouteRPrimeSourceH1 →ₗ[ℂ] RouteRSingularCorona,
      P (ccmRationalAdelicPrimeRelativeClass routeRTwoPrime) =
        routeRPrimeIsotropyPhysicalCoronaTarget rho := by
  exact
    ⟨ccmRationalAdelicPrimeStokesObserver routeRTwoPrime
        (routeRPrimeIsotropyPhysicalCoronaTarget rho),
      ccmRationalAdelicPrimeStokesObserver_class routeRTwoPrime _⟩

/-! ## Gauge-invariant horn -/

/-- Gauge-invariant algebraic observer whose retained-class value is the
actual fixed physical singular-corona action. -/
def RouteRPrimeIsotropyGaugeInvariantPhysicalObserver
    (rho : XiDivisorSupport) : Prop :=
  ∃ P : RouteRPrimeSourceH1 →ₗ[ℂ] RouteRSingularCorona,
    (∀ lam : ℂ, ∀ h : RouteRPrimeSourceH1,
      P ((ccmRationalAdelicPrimeVerticalShearHom routeRTwoPrime
          (ccmRationalAdelicPrimeHaarShear_mem routeRTwoPrime lam)).H1map h) =
        P h) ∧
    P (ccmRationalAdelicPrimeRelativeClass routeRTwoPrime) =
      routeRPrimeIsotropyPhysicalCoronaTarget rho

/-- Exact pointwise dichotomy: source-gauge-invariant observer selection is
possible precisely at neutral grade. -/
theorem routeRPrimeIsotropyGaugeInvariantPhysicalObserver_iff_re_eq_half
    (rho : XiDivisorSupport) :
    RouteRPrimeIsotropyGaugeInvariantPhysicalObserver rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨P, hinvariant, hphysical⟩
    have herases := ccmRationalAdelicPrimeGaugeInvariantReader_erases
      routeRTwoPrime P hinvariant
    have htarget : routeRPrimeIsotropyPhysicalCoronaTarget rho = 0 := by
      rw [← hphysical]
      exact herases
    have hflat : CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat rho :=
      htarget
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp
      ((twoThreeGammaSingularCoronaFlat_iff_centeredRate_eq_zero rho).mp hflat)
  · intro hline
    refine ⟨0, ?_, ?_⟩
    · intro lam h
      rfl
    · have hrate := (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr hline
      have hflat :=
        (twoThreeGammaSingularCoronaFlat_iff_centeredRate_eq_zero rho).mpr hrate
      exact hflat.symm

/-- Global gauge-invariant physical observer selection is exactly RH. -/
theorem
    global_routeRPrimeIsotropyGaugeInvariantPhysicalObserver_iff_rh :
    (∀ rho : XiDivisorSupport,
      RouteRPrimeIsotropyGaugeInvariantPhysicalObserver rho) ↔
      RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h z hz
    let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact
      (routeRPrimeIsotropyGaugeInvariantPhysicalObserver_iff_re_eq_half rho).mp
        (h rho)
  · intro h rho
    exact
      (routeRPrimeIsotropyGaugeInvariantPhysicalObserver_iff_re_eq_half rho).mpr
        (h (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho))

/-! ## Uniform pre-divisor source observer is impossible -/

/-- Variable-grade physical corona target before divisor specialization. -/
def routeRPreDivisorPrimeIsotropyCoronaTarget (a : ℝ) (c : ℂ) :
    RouteRSingularCorona :=
  routeRTwoThreePreDivisorGammaGlobalAction a
    (routeRTwoThreePreDivisorGammaPhysicalLift c)

/-- Proposed source-natural observer valid before divisor specialization,
for every horizontal grade and every retained coefficient. -/
structure RouteRPreDivisorGaugeInvariantCoronaObserver where
  observer : ∀ (_a : ℝ) (_c : ℂ),
    RouteRPrimeSourceH1 →ₗ[ℂ] RouteRSingularCorona
  gauge_invariant : ∀ (a : ℝ) (c lam : ℂ) (h : RouteRPrimeSourceH1),
    observer a c
        ((ccmRationalAdelicPrimeVerticalShearHom routeRTwoPrime
          (ccmRationalAdelicPrimeHaarShear_mem routeRTwoPrime lam)).H1map h) =
      observer a c h
  physical : ∀ (a : ℝ) (c : ℂ),
    observer a c (ccmRationalAdelicPrimeRelativeClass routeRTwoPrime) =
      routeRPreDivisorPrimeIsotropyCoronaTarget a c

/-- Full source-gauge invariance erases the retained class, while grade one
and unit coefficient give a nonzero full-support physical target. -/
theorem routeR_no_preDivisorGaugeInvariantCoronaObserver :
    ¬ Nonempty RouteRPreDivisorGaugeInvariantCoronaObserver := by
  rintro ⟨P⟩
  let observer := P.observer 1 1
  have herases :
      observer (ccmRationalAdelicPrimeRelativeClass routeRTwoPrime) = 0 :=
    ccmRationalAdelicPrimeGaugeInvariantReader_erases routeRTwoPrime observer
      (P.gauge_invariant 1 1)
  have htarget : routeRPreDivisorPrimeIsotropyCoronaTarget 1 1 = 0 := by
    rw [← P.physical 1 1]
    exact herases
  have hlocal :=
    deningerCalderonWittCrossPrimeSingularCoronaClass_preDivisorLocalAction
      1 (routeRTwoThreePreDivisorGammaPacketLift 1)
  have hglobalLocal :
      routeRTwoThreePreDivisorGammaGlobalAction 1
          (routeRTwoThreePreDivisorGammaPhysicalLift 1) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreePreDivisorGammaLocalPacketAction 1
            (routeRTwoThreePreDivisorGammaPacketLift 1)) := by
    rw [hlocal]
    exact htarget
  have hneutralOrErased :=
    (routeRTwoThreePreDivisorGamma_global_eq_local_iff 1 1).mp hglobalLocal
  norm_num at hneutralOrErased

end

end RHTower
