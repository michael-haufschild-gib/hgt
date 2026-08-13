import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugePositivePolarUniversalityNoGo
import GaloisForLFunctions.RHTower.RouteRDegreeSixGammaCoronaLocalGlobalFracture

/-!
# Route R hyperbolic-gauge quartic physical producer

The positive-polar obstruction is specific to quadratic forms.  The retained
forward/reciprocal source plane has the nonzero gauge-invariant monomial
`z₊ z₋`.  Its norm square is a canonical nonnegative quartic energy.

Putting the normalized BV--Wold connection coefficient in the forward slot
and the vertical conormal in the reciprocal slot identifies this quartic
energy exactly with the already constructed physical Stokes excess.  This is
an unconditional, coefficient-faithful source-to-physical comparison and is
natural for the full hyperbolic source gauge.

The remaining Route R burden is thereby reduced to annihilation of one
explicit gauge-invariant complex amplitude on every Xi fibre.  No quadratic
polarization, target completion, or same-fibre metric comparison remains in
that statement.
-/

open Complex Real

namespace RHTower

noncomputable section

/-! ## Gauge-invariant nonlinear positive polarization -/

/-- Multiplicative forward/reciprocal source amplitude. -/
def routeRHyperbolicInvariantAmplitude
    (z : RouteRHyperbolicSourcePlane) : ℂ :=
  z.1 * z.2

/-- Positive quartic energy of the invariant amplitude. -/
def routeRHyperbolicInvariantQuarticEnergy
    (z : RouteRHyperbolicSourcePlane) : ℝ :=
  Complex.normSq (routeRHyperbolicInvariantAmplitude z)

theorem routeRHyperbolicInvariantAmplitude_gauge
    (a : ℝ) (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicInvariantAmplitude
        (routeRHyperbolicSourceGauge a z) =
      routeRHyperbolicInvariantAmplitude z := by
  change
    (((Real.exp a : ℝ) : ℂ) * z.1) *
        (((Real.exp (-a) : ℝ) : ℂ) * z.2) = z.1 * z.2
  calc
    (((Real.exp a : ℝ) : ℂ) * z.1) *
        (((Real.exp (-a) : ℝ) : ℂ) * z.2) =
      ((((Real.exp a : ℝ) : ℂ) *
        ((Real.exp (-a) : ℝ) : ℂ)) * (z.1 * z.2)) := by ring
    _ = z.1 * z.2 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp

theorem routeRHyperbolicInvariantQuarticEnergy_gauge
    (a : ℝ) (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicInvariantQuarticEnergy
        (routeRHyperbolicSourceGauge a z) =
      routeRHyperbolicInvariantQuarticEnergy z := by
  rw [routeRHyperbolicInvariantQuarticEnergy,
    routeRHyperbolicInvariantQuarticEnergy,
    routeRHyperbolicInvariantAmplitude_gauge]

theorem routeRHyperbolicInvariantQuarticEnergy_nonneg
    (z : RouteRHyperbolicSourcePlane) :
    0 ≤ routeRHyperbolicInvariantQuarticEnergy z :=
  Complex.normSq_nonneg _

theorem routeRHyperbolicInvariantQuarticEnergy_eq_zero_iff
    (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicInvariantQuarticEnergy z = 0 ↔
      routeRHyperbolicInvariantAmplitude z = 0 := by
  exact Complex.normSq_eq_zero

/-- The surviving positive invariant is genuinely nonlinear: no real
quadratic form on the retained plane represents it pointwise. -/
theorem routeRHyperbolicInvariantQuarticEnergy_not_quadratic :
    ¬ ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
      ∀ z, Q z = routeRHyperbolicInvariantQuarticEnergy z := by
  rintro ⟨Q, hQ⟩
  let z : RouteRHyperbolicSourcePlane := (1, 1)
  have hmap := Q.map_smul (2 : ℝ) z
  rw [hQ ((2 : ℝ) • z), hQ z] at hmap
  norm_num [z, routeRHyperbolicInvariantQuarticEnergy,
    routeRHyperbolicInvariantAmplitude, Complex.normSq_mul,
    Complex.normSq_ofReal] at hmap

/-! ## Exact BV--Wold physical comparison -/

/-- Coefficient-faithful quartic carrier.  Prime, depth, connection, clock,
centered-rate, and conormal data remain literal coordinates. -/
def routeRPrimeDepthStokesQuarticCarrier
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    RouteRHyperbolicSourcePlane :=
  ((((a * primeDepthBVWoldConnection i j /
      (xiGammaEulerPrimitivePrimeDepthLogClock i *
        xiGammaEulerPrimitivePrimeDepthLogClock j) : ℝ) : ℂ)), c)

theorem routeRHyperbolicInvariantAmplitude_stokesCarrier
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    routeRHyperbolicInvariantAmplitude
        (routeRPrimeDepthStokesQuarticCarrier a i j c) =
      (((a * primeDepthBVWoldConnection i j /
        (xiGammaEulerPrimitivePrimeDepthLogClock i *
          xiGammaEulerPrimitivePrimeDepthLogClock j) : ℝ) : ℂ) * c) := rfl

/-- **Unconditional source-to-physical landing.**  Quartic source energy is
exactly the fixed physical Stokes excess, with no Xi or line hypothesis. -/
theorem routeRHyperbolicInvariantQuarticEnergy_stokesCarrier
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    routeRHyperbolicInvariantQuarticEnergy
        (routeRPrimeDepthStokesQuarticCarrier a i j c) =
      primeDepthBVWoldSourcePolarizationStokesExcess a i j c := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq_normSq]
  rfl

/-- The exact comparison survives every pre-polar hyperbolic gauge move. -/
theorem routeRHyperbolicInvariantQuarticEnergy_gauge_stokesCarrier
    (b a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    routeRHyperbolicInvariantQuarticEnergy
        (routeRHyperbolicSourceGauge b
          (routeRPrimeDepthStokesQuarticCarrier a i j c)) =
      primeDepthBVWoldSourcePolarizationStokesExcess a i j c := by
  rw [routeRHyperbolicInvariantQuarticEnergy_gauge,
    routeRHyperbolicInvariantQuarticEnergy_stokesCarrier]

/-! ## Actual Xi carrier and exact remaining annihilation -/

/-- Literal quartic carrier on the actual Xi conormal and witness edge. -/
def routeRXiHyperbolicInvariantQuarticCarrier
    (rho : XiDivisorSupport) : RouteRHyperbolicSourcePlane :=
  routeRPrimeDepthStokesQuarticCarrier
    (primeDepthBVWoldXiCenteredRate rho)
    primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
    (iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho))

theorem routeRXiHyperbolicInvariantQuarticEnergy_eq_physicalExcess
    (rho : XiDivisorSupport) :
    routeRHyperbolicInvariantQuarticEnergy
        (routeRXiHyperbolicInvariantQuarticCarrier rho) =
      primeDepthBVWoldSourcePolarizationStokesExcess
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) := by
  exact routeRHyperbolicInvariantQuarticEnergy_stokesCarrier _ _ _ _

/-- The explicit invariant amplitude vanishes precisely at neutral grade. -/
theorem routeRXiHyperbolicInvariantAmplitude_eq_zero_iff
    (rho : XiDivisorSupport) :
    routeRHyperbolicInvariantAmplitude
        (routeRXiHyperbolicInvariantQuarticCarrier rho) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [← routeRHyperbolicInvariantQuarticEnergy_eq_zero_iff,
    routeRXiHyperbolicInvariantQuarticEnergy_eq_physicalExcess,
    primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff]

/-! ## Division-free comparison with the explicit degree-six boundary -/

/-- Nonzero coefficient carrying the literal witness edge and first nonzero
Xi conormal from the quartic carrier into the degree-six BV--Green chart. -/
def routeRXiQuarticBVGreenComparisonCoefficient
    (rho : XiDivisorSupport) : ℂ :=
  (((primeDepthBVWoldConnection primeDepthBVWoldWitnessZero
      primeDepthBVWoldWitnessOne /
      (xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessZero *
        xiGammaEulerPrimitivePrimeDepthLogClock
          primeDepthBVWoldWitnessOne) : ℝ) : ℂ) *
    iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho))

theorem routeRXiQuarticBVGreenComparisonCoefficient_ne_zero
    (rho : XiDivisorSupport) :
    routeRXiQuarticBVGreenComparisonCoefficient rho ≠ 0 := by
  rw [routeRXiQuarticBVGreenComparisonCoefficient]
  apply mul_ne_zero
  · exact_mod_cast div_ne_zero primeDepthBVWoldConnection_witness_pos.ne'
      (mul_ne_zero
        (xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero _)
        (xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero _))
  · exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho

theorem routeRXiHyperbolicInvariantAmplitude_eq_centeredRate_mul_bvGreenCoefficient
    (rho : XiDivisorSupport) :
    routeRHyperbolicInvariantAmplitude
        (routeRXiHyperbolicInvariantQuarticCarrier rho) =
      ((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
        routeRXiQuarticBVGreenComparisonCoefficient rho := by
  rw [routeRXiHyperbolicInvariantQuarticCarrier,
    routeRHyperbolicInvariantAmplitude_stokesCarrier,
    routeRXiQuarticBVGreenComparisonCoefficient]
  push_cast
  ring

/-- **Exact degree-six sewing, without division.**  Multiplication by two
independently nonzero source coefficients identifies the constructed
gauge-invariant amplitude with the fixed physical reading of the literal
degree-six BV--Green Hochschild boundary. -/
theorem routeRXiQuarticAmplitude_bvGreenBoundary_divisionFree
    (rho : XiDivisorSupport) :
    (routeRDegreeSixBVGreenGammaComparisonGauge rho : ℂ) *
        routeRHyperbolicInvariantAmplitude
          (routeRXiHyperbolicInvariantQuarticCarrier rho) =
      routeRXiQuarticBVGreenComparisonCoefficient rho *
        (routeRDeningerBVGreenReflectedBoundary rho : ℂ) := by
  rw [routeRXiHyperbolicInvariantAmplitude_eq_centeredRate_mul_bvGreenCoefficient,
    routeRDeningerBVGreenReflectedBoundary_eq_centeredRate_mul_gammaGauge]
  push_cast
  ring

/-- Annihilating the quartic amplitude is exactly physical cyclic descent of
the already explicit degree-six Hochschild boundary.  Source cyclicity alone
still only proves `τ₆(B₆)=0`; this theorem identifies the one missing reader
comparison rather than assuming it. -/
theorem routeRXiHyperbolicInvariantAmplitude_eq_zero_iff_degreeSixPhysicalCyclicDescent
    (rho : XiDivisorSupport) :
    routeRHyperbolicInvariantAmplitude
        (routeRXiHyperbolicInvariantQuarticCarrier rho) = 0 ↔
      RouteRDegreeSixBVGreenPhysicalCyclicDescent rho := by
  rw [routeRXiHyperbolicInvariantAmplitude_eq_zero_iff,
    routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_re_eq_half]

/-- Exact source-native endpoint exposed by the quartic producer. -/
def RouteRXiHyperbolicInvariantAmplitudeAnnihilated : Prop :=
  ∀ rho : XiDivisorSupport,
    routeRHyperbolicInvariantAmplitude
      (routeRXiHyperbolicInvariantQuarticCarrier rho) = 0

/-- Global annihilation of the constructed invariant amplitude is exactly
the existing RH endpoint.  This theorem packages no comparison premise: the
comparison itself was proved above. -/
theorem routeRXiHyperbolicInvariantAmplitudeAnnihilated_iff_rh :
    RouteRXiHyperbolicInvariantAmplitudeAnnihilated ↔ RiemannHypothesis := by
  constructor
  · intro hannihilated
    apply primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis.mp
    intro rho
    rw [← routeRXiHyperbolicInvariantQuarticEnergy_eq_physicalExcess,
      routeRHyperbolicInvariantQuarticEnergy_eq_zero_iff]
    exact hannihilated rho
  · intro hRH rho
    exact (routeRXiHyperbolicInvariantAmplitude_eq_zero_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
