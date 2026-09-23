import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenPhysicalCyclicDescentWall
import GaloisForLFunctions.RHTower.RouteRTwoThreeGammaSingularCoronaProducer

/-!
# Route R degree-six Gamma-corona local/global fracture

The fixed degree-six BV--Green physical boundary and the canonical ordered
`(2,3)` Gamma/Cartier port obey an exact division-free identity.  This
identifies their values, not only their zero sets.

The literal `(2,3)` source action is coordinate-local on the all-cross-prime
packet.  Its range is contained in the finite arithmetic source core, so it
vanishes after passage to the singular algebraic corona.  The fixed physical
action is different: it multiplies the full-support corona horizon.  Hence the
remaining Route R theorem is exactly the local-to-global comparison between
these two explicit actions.

No flatness, critical-line, source-dagger, same-fibre norm, or RH premise is
used here.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

noncomputable local instance routeRDegreeSixGammaCoronaLocalGlobalFractureInst1 : DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-! ## Exact degree-six / Gamma value comparison -/

/-- Positive comparison gauge between the linear centered rate and the
degree-six hyperbolic BV--Green boundary. -/
def routeRDegreeSixBVGreenGammaComparisonGauge
    (rho : XiDivisorSupport) : ℝ :=
  2 * Real.log 6 *
    routeRDeningerHyperbolicSinc
      (primeDepthBVWoldXiCenteredRate rho * Real.log 6)

theorem routeRDegreeSixBVGreenGammaComparisonGauge_pos
    (rho : XiDivisorSupport) :
    0 < routeRDegreeSixBVGreenGammaComparisonGauge rho := by
  rw [routeRDegreeSixBVGreenGammaComparisonGauge]
  exact mul_pos
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (routeRDeningerHyperbolicSinc_pos _)

/-- The fixed reflected degree-six physical boundary is the centered rate
times a strictly positive analytic gauge. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_centeredRate_mul_gammaGauge
    (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho =
      primeDepthBVWoldXiCenteredRate rho *
        routeRDegreeSixBVGreenGammaComparisonGauge rho := by
  rw [routeRDeningerBVGreenReflectedBoundary]
  calc
    6 *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (rho : ℂ) -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6
            (1 - star (rho : ℂ))) =
        deningerTensorSquareRadialMateCurvature 6 (rho : ℂ) := by
          simpa using deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
            (n := 6) (by norm_num) (rho : ℂ)
    _ = 2 * Real.sinh
        (primeDepthBVWoldXiCenteredRate rho * Real.log 6) := by
          rw [deningerTensorSquareRadialMateCurvature_eq_sinh
            6 (rho : ℂ) (by norm_num)]
          rfl
    _ = primeDepthBVWoldXiCenteredRate rho *
        routeRDegreeSixBVGreenGammaComparisonGauge rho := by
          rw [routeRDegreeSixBVGreenGammaComparisonGauge,
            ← mul_routeRDeningerHyperbolicSinc
              (primeDepthBVWoldXiCenteredRate rho * Real.log 6)]
          ring

/-- **Exact division-free degree-six/Gamma bridge.**  The fixed physical
BV--Green value and the canonical `(2,3)` Gamma/Cartier port agree after
multiplication by independently nonzero source gauges. -/
theorem routeRDegreeSixBVGreenGammaCartier_divisionFreeComparison
    (rho : XiDivisorSupport) :
    (((routeRTwoThreeGammaCoorientedGauge rho : ℝ) : ℂ) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho) *
          (routeRDeningerBVGreenReflectedBoundary rho : ℂ) =
      (routeRDegreeSixBVGreenGammaComparisonGauge rho : ℂ) *
        routeRTwoThreeGammaCartierTransportPort rho := by
  rw [routeRDeningerBVGreenReflectedBoundary_eq_centeredRate_mul_gammaGauge,
    routeRTwoThreeGammaCartierTransportPort_eq_centeredRate_mul_gauge]
  push_cast
  ring

/-! ## Literal source-local action -/

/-- Packet-space physical lift before the algebraic singular-corona
projection. -/
def routeRTwoThreeGammaPacketPhysicalLift
    (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho •
    deningerCalderonWittCrossPrimePacketHorizon

/-- Literal source-local `(2,3)` Gamma action: the Gamma coefficient acts
only in the coordinate of its defining ordered source witness. -/
def routeRTwoThreeGammaLocalPacketAction
    (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert :=
  routeRTwoThreeGammaSingularCoronaActionCoefficient rho •
    lpCoordinateProjection
      ({deningerCalderonWittTwoThreePacketIndex} :
        Set DeningerCalderonWittCrossPrimePacketIndex)

theorem routeRTwoThreeGammaLocalPacketAction_eq_single
    (rho : XiDivisorSupport)
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    routeRTwoThreeGammaLocalPacketAction rho z =
      lp.single 2 deningerCalderonWittTwoThreePacketIndex
        (routeRTwoThreeGammaSingularCoronaActionCoefficient rho *
          z deningerCalderonWittTwoThreePacketIndex) := by
  apply lp.ext
  funext i
  by_cases hi : i = deningerCalderonWittTwoThreePacketIndex
  · subst i
    simp [routeRTwoThreeGammaLocalPacketAction,
      lpCoordinateProjection_apply]
  · simp [routeRTwoThreeGammaLocalPacketAction,
      lpCoordinateProjection_apply, hi]

theorem deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert_single
    (i : DeningerCalderonWittCrossPrimePacketIndex) (c : ℂ) :
    deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert
        (Finsupp.single i c) =
      lp.single 2 i c := by
  apply lp.ext
  funext j
  rw [deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Every output of the literal source-local action belongs to the concrete
finite arithmetic source core. -/
theorem routeRTwoThreeGammaLocalPacketAction_mem_arithmeticCore
    (rho : XiDivisorSupport)
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    routeRTwoThreeGammaLocalPacketAction rho z ∈
      deningerCalderonWittCrossPrimeArithmeticPacketCore := by
  let a : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
    Finsupp.single deningerCalderonWittTwoThreePacketIndex
      (routeRTwoThreeGammaSingularCoronaActionCoefficient rho *
        z deningerCalderonWittTwoThreePacketIndex)
  refine ⟨deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan a, ?_⟩
  rw [deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_finsupp,
    routeRTwoThreeGammaLocalPacketAction_eq_single,
    deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert_single]

/-- **Unconditional source-corona annihilation.**  The literal local action
is killed by the singular quotient on every packet, without a divisor
location premise. -/
theorem deningerCalderonWittCrossPrimeSingularCoronaClass_localPacketAction
    (rho : XiDivisorSupport)
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    deningerCalderonWittCrossPrimeSingularCoronaClass
        (routeRTwoThreeGammaLocalPacketAction rho z) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact routeRTwoThreeGammaLocalPacketAction_mem_arithmeticCore rho z

/-- The packet physical lift projects to the already fixed nonzero corona
physical lift. -/
theorem deningerCalderonWittCrossPrimeSingularCoronaClass_packetPhysicalLift
    (rho : XiDivisorSupport) :
    deningerCalderonWittCrossPrimeSingularCoronaClass
        (routeRTwoThreeGammaPacketPhysicalLift rho) =
      routeRTwoThreeGammaSingularCoronaPhysicalLift rho := by
  rw [routeRTwoThreeGammaPacketPhysicalLift,
    routeRTwoThreeGammaSingularCoronaPhysicalLift, map_smul]
  rfl

/-! ## Exact local/global fracture -/

/-- The difference between the fixed physical global action and the literal
source-local action is exactly the retained Gamma/Cartier port on the
nonzero corona horizon. -/
theorem routeRTwoThreeGammaCorona_global_sub_local_eq_port
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaSingularCoronaPhysicalLift rho) -
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaPacketPhysicalLift rho)) =
      routeRTwoThreeGammaCartierTransportPort rho •
        deningerCalderonWittCrossPrimeSingularCoronaHorizon := by
  rw [routeRTwoThreeGammaSingularCoronaAction_physicalLift,
    deningerCalderonWittCrossPrimeSingularCoronaClass_localPacketAction,
    sub_zero]

/-- Local source action and fixed physical global action agree exactly when
the explicit Gamma/Cartier port vanishes. -/
theorem routeRTwoThreeGammaCorona_global_eq_local_iff_port_eq_zero
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaPacketPhysicalLift rho)) ↔
      routeRTwoThreeGammaCartierTransportPort rho = 0 := by
  rw [deningerCalderonWittCrossPrimeSingularCoronaClass_localPacketAction,
    routeRTwoThreeGammaSingularCoronaAction_physicalLift]
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_right
      deningerCalderonWittCrossPrimeSingularCoronaHorizon_ne_zero
  · intro h
    rw [h, zero_smul]

/-- Literal statement of the requested fixed-reader comparison. -/
def RouteRDegreeSixBVGreenFixedReaderEquality
    (rho : XiDivisorSupport) : Prop :=
  (routeRDeningerBVGreenReflectedBoundary rho : ℂ) =
    deningerDegreeSixBVGreenCyclicReader
      (deningerOrdinaryIntegerBVGreenStokesBoundary 6)

theorem routeRDegreeSixBVGreenFixedReaderEquality_iff_boundary_zero
    (rho : XiDivisorSupport) :
    RouteRDegreeSixBVGreenFixedReaderEquality rho ↔
      routeRDeningerBVGreenReflectedBoundary rho = 0 := by
  rw [RouteRDegreeSixBVGreenFixedReaderEquality,
    deningerDegreeSixBVGreenCyclicReader_boundary]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    simp [h]

/-- **Exact remaining Route R operation.**  The requested degree-six reader
equality is precisely equality of the independently constructed local source
action and the fixed full-support physical action. -/
theorem routeRTwoThreeGammaCorona_global_eq_local_iff_degreeSixFixedReaderEquality
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaPacketPhysicalLift rho)) ↔
      RouteRDegreeSixBVGreenFixedReaderEquality rho := by
  rw [routeRTwoThreeGammaCorona_global_eq_local_iff_port_eq_zero,
    routeRTwoThreeGammaCartierTransportPort_eq_zero_iff,
    routeRDegreeSixBVGreenFixedReaderEquality_iff_boundary_zero]
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).trans
    (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_re_eq_half rho).symm

end

end RHTower
