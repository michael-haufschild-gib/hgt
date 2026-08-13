import GaloisForLFunctions.RHTower.RouteRDegreeSixGammaCoronaLocalGlobalFracture

/-!
# Route R pre-divisor Gamma-corona globalization no-go

The divisor-specialized local/global comparison is RH-equivalent.  This file
tests the stronger statement that was supposed to produce it: a comparison
derived before divisor specialization and therefore valid for the variable
horizontal grade and variable retained Cartier coefficient.

The result is exact.  The literal `(2,3)` source-local action always has
finite packet support and is zero in the singular corona.  The full-support
physical action agrees with it precisely when either the horizontal grade is
neutral or the retained coefficient is erased.  In particular there is no
coefficient-faithful uniform pre-divisor globalization.

No Xi zero, critical-line placement, RH, source-dagger identity, same-fibre
norm identity, or physical annihilation premise is used.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

noncomputable local instance :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-- Variable-grade source coefficient before divisor specialization. -/
def routeRTwoThreePreDivisorGammaCoefficient (a : ℝ) : ℂ :=
  (xiGammaEulerPrimitiveCoorientedReflectionOddExterior a
    (routeRTwoPrime, 0) (routeRThreePrime, 0) : ℂ)

/-- Variable-coefficient full-support physical lift. -/
def routeRTwoThreePreDivisorGammaPhysicalLift (c : ℂ) :
    DeningerCalderonWittCrossPrimeSingularCorona :=
  c • deningerCalderonWittCrossPrimeSingularCoronaHorizon

/-- Variable-coefficient packet lift before the singular quotient. -/
def routeRTwoThreePreDivisorGammaPacketLift (c : ℂ) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  c • deningerCalderonWittCrossPrimePacketHorizon

/-- Full-support variable-grade physical action. -/
def routeRTwoThreePreDivisorGammaGlobalAction (a : ℝ) :
    DeningerCalderonWittCrossPrimeSingularCorona →ₗ[ℂ]
      DeningerCalderonWittCrossPrimeSingularCorona :=
  routeRTwoThreePreDivisorGammaCoefficient a • LinearMap.id

/-- Literal source-local variable-grade action on the fixed `(2,3)` packet
coordinate. -/
def routeRTwoThreePreDivisorGammaLocalPacketAction (a : ℝ) :
    DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert :=
  routeRTwoThreePreDivisorGammaCoefficient a •
    lpCoordinateProjection
      ({deningerCalderonWittTwoThreePacketIndex} :
        Set DeningerCalderonWittCrossPrimePacketIndex)

theorem routeRTwoThreePreDivisorGammaLocalPacketAction_eq_single
    (a : ℝ) (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    routeRTwoThreePreDivisorGammaLocalPacketAction a z =
      lp.single 2 deningerCalderonWittTwoThreePacketIndex
        (routeRTwoThreePreDivisorGammaCoefficient a *
          z deningerCalderonWittTwoThreePacketIndex) := by
  apply lp.ext
  funext i
  by_cases hi : i = deningerCalderonWittTwoThreePacketIndex
  · subst i
    simp [routeRTwoThreePreDivisorGammaLocalPacketAction,
      lpCoordinateProjection_apply]
  · simp [routeRTwoThreePreDivisorGammaLocalPacketAction,
      lpCoordinateProjection_apply, hi]

/-- Every variable-grade local output remains in the finite arithmetic core. -/
theorem routeRTwoThreePreDivisorGammaLocalPacketAction_mem_arithmeticCore
    (a : ℝ) (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    routeRTwoThreePreDivisorGammaLocalPacketAction a z ∈
      deningerCalderonWittCrossPrimeArithmeticPacketCore := by
  let packet : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
    Finsupp.single deningerCalderonWittTwoThreePacketIndex
      (routeRTwoThreePreDivisorGammaCoefficient a *
        z deningerCalderonWittTwoThreePacketIndex)
  refine
    ⟨deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan packet, ?_⟩
  rw [deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_finsupp,
    routeRTwoThreePreDivisorGammaLocalPacketAction_eq_single,
    deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert_single]

/-- The literal pre-divisor local action is identically zero after the
singular-corona projection. -/
theorem deningerCalderonWittCrossPrimeSingularCoronaClass_preDivisorLocalAction
    (a : ℝ) (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    deningerCalderonWittCrossPrimeSingularCoronaClass
        (routeRTwoThreePreDivisorGammaLocalPacketAction a z) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact
    routeRTwoThreePreDivisorGammaLocalPacketAction_mem_arithmeticCore a z

/-- Exact full-support value before divisor specialization. -/
theorem routeRTwoThreePreDivisorGammaGlobalAction_physicalLift
    (a : ℝ) (c : ℂ) :
    routeRTwoThreePreDivisorGammaGlobalAction a
        (routeRTwoThreePreDivisorGammaPhysicalLift c) =
      (routeRTwoThreePreDivisorGammaCoefficient a * c) •
        deningerCalderonWittCrossPrimeSingularCoronaHorizon := by
  rw [routeRTwoThreePreDivisorGammaGlobalAction,
    routeRTwoThreePreDivisorGammaPhysicalLift,
    LinearMap.smul_apply, LinearMap.id_apply, smul_smul]

/-- The variable `(2,3)` Gamma coefficient has no accidental zero. -/
theorem routeRTwoThreePreDivisorGammaCoefficient_eq_zero_iff (a : ℝ) :
    routeRTwoThreePreDivisorGammaCoefficient a = 0 ↔ a = 0 := by
  rw [routeRTwoThreePreDivisorGammaCoefficient,
    ofReal_eq_zero,
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge,
    mul_eq_zero]
  have hgauge :
      xiGammaEulerPrimitiveCoorientedReflectionGauge a
          (routeRTwoPrime, 0) (routeRThreePrime, 0) ≠ 0 :=
    (xiGammaEulerPrimitiveCoorientedReflectionGauge_pos a
      (routeRTwoPrime, 0) (routeRThreePrime, 0)
      (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth
        routeRTwoPrime_ne_routeRThreePrime 0)).ne'
  exact or_iff_left hgauge

/-- **Exact pre-divisor local/global fracture.**  Global and source-local
actions agree precisely on the neutral locus or after erasing the retained
coefficient. -/
theorem routeRTwoThreePreDivisorGamma_global_eq_local_iff
    (a : ℝ) (c : ℂ) :
    routeRTwoThreePreDivisorGammaGlobalAction a
          (routeRTwoThreePreDivisorGammaPhysicalLift c) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreePreDivisorGammaLocalPacketAction a
            (routeRTwoThreePreDivisorGammaPacketLift c)) ↔
      a = 0 ∨ c = 0 := by
  rw [deningerCalderonWittCrossPrimeSingularCoronaClass_preDivisorLocalAction,
    routeRTwoThreePreDivisorGammaGlobalAction_physicalLift]
  constructor
  · intro hzero
    have hcoefficient :
        routeRTwoThreePreDivisorGammaCoefficient a * c = 0 :=
      (smul_eq_zero.mp hzero).resolve_right
        deningerCalderonWittCrossPrimeSingularCoronaHorizon_ne_zero
    rcases mul_eq_zero.mp hcoefficient with ha | hc
    · exact Or.inl
        ((routeRTwoThreePreDivisorGammaCoefficient_eq_zero_iff a).mp ha)
    · exact Or.inr hc
  · rintro (ha | hc)
    · rw [ha,
        (routeRTwoThreePreDivisorGammaCoefficient_eq_zero_iff 0).mpr rfl,
        zero_mul, zero_smul]
    · rw [hc, mul_zero, zero_smul]

/-- A uniform comparison genuinely derived before divisor specialization is
false: grade one with a retained unit coefficient is an explicit model of
all source-local laws where the full-support action survives. -/
theorem not_forall_routeRTwoThreePreDivisorGamma_global_eq_local :
    ¬ ∀ (a : ℝ) (c : ℂ),
      routeRTwoThreePreDivisorGammaGlobalAction a
          (routeRTwoThreePreDivisorGammaPhysicalLift c) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreePreDivisorGammaLocalPacketAction a
            (routeRTwoThreePreDivisorGammaPacketLift c)) := by
  intro hglobal
  have h :=
    (routeRTwoThreePreDivisorGamma_global_eq_local_iff 1 1).mp
      (hglobal 1 1)
  norm_num at h

/-- Impossible pre-divisor producer interface, isolated for the terminal
dependency audit. -/
structure RouteRPreDivisorGammaCoronaGlobalizer where
  globalization : ∀ (a : ℝ) (c : ℂ),
    routeRTwoThreePreDivisorGammaGlobalAction a
        (routeRTwoThreePreDivisorGammaPhysicalLift c) =
      deningerCalderonWittCrossPrimeSingularCoronaClass
        (routeRTwoThreePreDivisorGammaLocalPacketAction a
          (routeRTwoThreePreDivisorGammaPacketLift c))

theorem routeR_no_preDivisorGammaCoronaGlobalizer :
    ¬ Nonempty RouteRPreDivisorGammaCoronaGlobalizer := by
  rintro ⟨P⟩
  exact not_forall_routeRTwoThreePreDivisorGamma_global_eq_local
    P.globalization

end

end RHTower
