import GaloisForLFunctions.RHTower.ChargeMotion
import GaloisForLFunctions.RHTower.DeningerFailureNerveMixedDaggerCoboundary
import GaloisForLFunctions.RHTower.DeningerOneSidedFramedMateCurvatureTransgression
import GaloisForLFunctions.RHTower.DeningerPlaceCountable
import GaloisForLFunctions.RHTower.DeningerRestrictedPrimeGluing
import GaloisForLFunctions.RHTower.DirectionalQuantumReturnGeometryLaw
import GaloisForLFunctions.RHTower.MobiusFixedTokenReservoirConservation
import GaloisForLFunctions.RHTower.PermutationInvariantQubitClockRealization
import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCurvature
import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugePolarReductionNoGo
import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugeQuarticPhysicalProducer
import GaloisForLFunctions.RHTower.SuzukiCriticalRootedBianchiCofinalNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaClockDescent
import GaloisForLFunctions.RHTower.XiCayleyFockOrderSpaceConservation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket
import GaloisForLFunctions.RHTower.XiSourceCayleyOrderSpaceConservationLaw
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation
import GaloisForLFunctions.RHTower.XiWoldPoissonBivariateConormal

/-!
# Noether applications in the arithmetic and Xi corpus

Premise-free arithmetic applications of first-Noether conservation, second-Noether Bianchi/Ward
identities, topological charge invariance, and algebraic Noetherianity.  The final section records a
closed obstruction: one natural rooted Bianchi charge is not summable over primes.
-/

noncomputable section

namespace RHTower

open Complex Filter Set
open scoped Topology
open GaloisForLFunctions.HTGeometry

/-! ## Second-Noether identities -/

/-- Multiplicative exchange curvature satisfies its nonabelian Bianchi identity. -/
theorem noetherSecond_exchangeCurvatureBianchi
    {k : Type*} [Field k] (χ : ℕ+ →* kˣ) (l m n : ℕ+) :
    exchangeCurvature χ l m * exchangeTransport χ n + exchangeCurvature χ (l * m) n =
      exchangeTransport χ l * exchangeCurvature χ m n + exchangeCurvature χ l (m * n) :=
  exchangeCurvature_bianchi χ l m n

/-- Two prime directions obey the mixed Deninger square Bianchi identity. -/
theorem noetherSecond_deningerMixedDefectBianchi (Sp Sq Ap Aq : ℂ) :
    Sp * (Sq - Aq) + (Sp - Ap) * Aq =
      Sq * (Sp - Ap) + (Sq - Aq) * Ap :=
  deningerMixedDefect_bianchi Sp Sq Ap Aq

/-- Framed Deninger composition curvature satisfies the matrix Bianchi identity. -/
theorem noetherSecond_deningerFramedCompositionBianchi
    (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (l m n : ℕ) :
    deningerFramedCompositionCurvature T l m * T n +
        deningerFramedCompositionCurvature T (l * m) n =
      T l * deningerFramedCompositionCurvature T m n +
        deningerFramedCompositionCurvature T l (m * n) :=
  deningerFramedCompositionCurvature_bianchi T l m n

/-- Truncating the finite exponential jet exposes exactly one Gamma-clock curvature face. -/
theorem noetherSecond_finiteGammaAnomalyBianchi
    {P : Type*} [Fintype P] (weight frequency : P → ℂ) (x : ℂ) (N : ℕ) :
    (gammaClockTruncate N).comp (finiteExponentialGammaAnomaly weight frequency x (N + 1)) -
        finiteExponentialGammaAnomaly weight frequency x N =
      (gammaClockCurvature N).comp (finiteExponentialJetObservation weight frequency x (N + 1)) :=
  finiteExponentialGammaAnomaly_bianchi weight frequency x N

/-- Coordinate form of the same second-Noether Gamma-clock current. -/
theorem noetherSecond_finiteGammaAnomalyBianchiApply
    {P : Type*} [Fintype P] (weight frequency : P → ℂ) (x : ℂ)
    (N : ℕ) (a : P → ℂ) (i : Fin N) :
    ((gammaClockTruncate N).comp (finiteExponentialGammaAnomaly weight frequency x (N + 1)) -
        finiteExponentialGammaAnomaly weight frequency x N) a i =
      finiteExponentialJetObservation weight frequency x (N + 1) a (Fin.last N) /
        (N - i).factorial :=
  finiteExponentialGammaAnomaly_bianchi_apply weight frequency x N a i

/-! ## First-Noether and current conservation -/

/-- Xi Cayley--Ward derivative energy is an exact Poisson order packet. -/
theorem noetherFirst_xiCayleyWardPoisson
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * ‖xiCayleyWardCoherentJet q x r‖ ^ 2 =
      xiEndpointWardPairWeight q * Real.exp (xiCayleyFockExponent q * x) *
        poissonOrderWeight (xiCayleyFockDrift q * x) r :=
  xiCayleyWardCoherentJet_poisson_conservation q x r

/-- Removing rotating phase by the adjacent-order exterior determinant preserves the Xi packet. -/
theorem noetherFirst_xiCayleyExteriorPoisson
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * -(xiCayleyWardExteriorPacket q x r).re =
      4 * xiEndpointWardPairWeight q * (xiCayleyFockShift q).im ^ 2 *
        Real.exp (xiCayleyFockExponent q * x) *
        poissonOrderWeight (xiCayleyFockDrift q * x) r :=
  neg_re_xiCayleyWardExteriorPacket_poisson_conservation q x r

/-- Source-residue Xi Cayley--Ward flow has its own exact Poisson packet. -/
theorem noetherFirst_xiSourceCayleyWardPoisson
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * ‖xiSourceCayleyWardCoherentJet q x r‖ ^ 2 =
      xiEndpointWardPairWeight q * Real.exp (xiSourceCayleyExponent q * x) *
        poissonOrderWeight (xiSourceCayleyDrift q * x) r :=
  xiSourceCayleyWardCoherentJet_poisson_conservation q x r

/-- Phase removal also preserves the source-residue Xi packet. -/
theorem noetherFirst_xiSourceCayleyExteriorPoisson
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * -(xiSourceCayleyWardExteriorPacket q x r).re =
      4 * xiEndpointWardPairWeight q * (xiSourceCayleyShift q).im ^ 2 *
        Real.exp (xiSourceCayleyExponent q * x) *
        poissonOrderWeight (xiSourceCayleyDrift q * x) r :=
  neg_re_xiSourceCayleyWardExteriorPacket_poisson_conservation q x r

/-- A fixed zero source removes the only noncollision premise from Wold--Poisson conormal
conservation. -/
theorem noetherFirst_zeroSourceWoldPoisson (n : ℕ) (tau : ℝ) (r : ℕ) :
    let x := sourceCayleyObservationTime 1 0 tau
    x ^ r / r.factorial *
        ‖iteratedDeriv r (xiWoldPoissonBivariateConormalResidueMode n 0) (x : ℂ)‖ ^ 2 =
      ‖shellMultiplier n 0 * (analyticOrderAt xi 0).toNat‖ ^ 2 *
        Real.exp (sourceCayleyTransverseRate 1 0 * tau) *
        poissonOrderWeight tau r := by
  simpa using xiWoldPoissonBivariateConormalResidueMode_poisson_conservation
    n (rho := 0) tau r zero_ne_one

/-- Prouhet completion splits endpoint action into two identical conserved halves. -/
theorem noetherFirst_prouhetEndpointCompletion (N : ℕ) (tau : ℝ) :
    2 ^ N * tau / 2 - 1 / 2 - (2 ^ N * tau - 1) / 4 =
      (2 ^ N * tau - 1) / 4 :=
  prouhetEndpoint_completion_conservation N tau

/-- Fixed token removal conserves reservoir balance up to the exact subset-shift excursion. -/
theorem noetherFirst_fixedTokenReservoir
    {ι : Type*} [Fintype ι]
    (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ) :
    |fixedTokenReservoirTotal reservoirBreadth -
        (fixedTokenSourceTotal sourceBreadth - tokenBreadth * Fintype.card ι)| ≤
      subsetShiftExcursion (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) :=
  fixedToken_reservoir_conservation sourceBreadth reservoirBreadth tokenBreadth

/-- Concrete topological Noether law: multiplying the unit-circle carrier by an exponential gauge
does not change its box charge. -/
theorem noetherFirst_exponentialGaugeBoxCharge (k : ℕ) :
    boxCharge k (fun z : ℂ => z) 0 1 =
      boxCharge k (fun z : ℂ => z * Complex.exp z) 0 1 := by
  simpa using boxCharge_conserved k
    (f := fun sigma z => z * Complex.exp ((sigma : ℂ) * z))
    (c := 0) (r := 1)
    (by fun_prop)
    (by
      intro sigma theta
      apply mul_ne_zero
      · simpa only [Complex.ofReal_one, one_mul, zero_add] using
          Complex.exp_ne_zero (Complex.I * (theta : ℂ))
      · exact Complex.exp_ne_zero _)

/-- Hyperbolic gauge flow preserves its quartic physical energy exactly. -/
theorem noetherFirst_routeRHyperbolicQuarticEnergy
    (a : ℝ) (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicInvariantQuarticEnergy (routeRHyperbolicSourceGauge a z) =
      routeRHyperbolicInvariantQuarticEnergy z :=
  routeRHyperbolicInvariantQuarticEnergy_gauge a z

/-- The invariant hyperbolic energy cannot be compressed into any quadratic charge. -/
theorem noetherObstruction_routeRInvariantEnergyNotQuadratic :
    ¬ ∃ Q : QuadraticForm ℝ RouteRHyperbolicSourcePlane,
      ∀ z, Q z = routeRHyperbolicInvariantQuarticEnergy z :=
  routeRHyperbolicInvariantQuarticEnergy_not_quadratic

/-- The tempting fixed-polar energy is not a conserved hyperbolic gauge charge. -/
theorem noetherObstruction_routeRFixedPolarEnergy :
    ¬ ∀ a z, routeRFixedPolarEnergy (routeRHyperbolicSourceGauge a z) =
      routeRFixedPolarEnergy z :=
  routeRFixedPolarEnergy_not_gaugeInvariant

/-- Permuting uniform qubit sites preserves the clock energy. -/
theorem noetherFirst_uniformQubitPermutationEnergy
    (T : ℝ) (n : ℕ) (e : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    ParityForecast.uniformQubitFieldEnergy T n (S.map e.toEmbedding) =
      ParityForecast.uniformQubitFieldEnergy T n S :=
  ParityForecast.uniformQubitFieldEnergy_permutation_invariant T n e S

/-- Common translation leaves every directional quantum-return record unchanged. -/
theorem noetherFirst_directionalReturnTranslation
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (shift : V) :
    ∀ i j time,
      directionalPairReturnRecord (fun k => energy k + shift) i j time =
        directionalPairReturnRecord energy i j time :=
  directionalPairReturnRecord_translation_invariant energy shift

/-- Reflection followed by common translation leaves directional return records unchanged. -/
theorem noetherFirst_directionalReturnReflection
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (shift : V) :
    ∀ i j time,
      directionalPairReturnRecord (fun k => -energy k + shift) i j time =
        directionalPairReturnRecord energy i j time :=
  directionalPairReturnRecord_inversion_invariant energy shift

/-- Common energy translation preserves the full temporal difference module. -/
theorem noetherFirst_temporalModuleTranslation
    {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : I → V) (shift : V) :
    jointTemporalModule (fun i => energy i + shift) = jointTemporalModule energy :=
  jointTemporalModule_translation_invariant energy shift

/-- Energy reflection and translation preserve the full temporal difference module. -/
theorem noetherFirst_temporalModuleReflection
    {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : I → V) (shift : V) :
    jointTemporalModule (fun i => -energy i + shift) = jointTemporalModule energy :=
  jointTemporalModule_inversion_invariant energy shift

/-- Xi nearby-cycle, divisor, and reflected-source currents share one closed orientation charge. -/
theorem noetherFirst_xiSourceBoundaryOrientation (rho : ℂ) :
    let m := (analyticOrderAt xi rho).toNat
    Tendsto
        (fun w : ℂ =>
          w⁻¹ * (depthSuccessorNearbyCycle (rho - 1 / 2) m w⁻¹ - 1))
        (𝓝[≠] 0)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
      Tendsto
        (fun s : ℂ => (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
      (-((rho - 1 / 2) * (m : ℂ))).re =
        (m : ℝ) / (2 * Real.log 2) *
          (Real.log ‖shellTransferCharacter rho‖ -
            Real.log ‖shellTransferCharacter (1 - star rho)‖) ∧
      sourceCayleyTransverseRate 1 rho =
        -(Real.log ‖shellTransferCharacter rho‖ -
            Real.log ‖shellTransferCharacter (1 - star rho)‖) /
          Real.log 2 :=
  xiDepthNearby_sourceBoundaryOrientationConservation rho

/-! ## Algebraic Noether applications -/

/-- A countable Noetherian ring has only countably many ideals. -/
theorem noetherian_deningerIdealsCountable
    {R : Type*} [CommRing R] [IsNoetherianRing R] [Countable R] :
    Countable (Ideal R) :=
  deningerIdeal_countable

/-- Every arithmetic open of `Spec ℤ` is compact by Noetherianity. -/
theorem noetherian_deningerArithmeticOpenCompact
    (U : TopologicalSpace.Opens (PrimeSpectrum ℤ)) :
    IsCompact (↑U : Set (PrimeSpectrum ℤ)) :=
  deningerArithmeticOpen_isCompact U

/-! ## What happens: a Noether/Bianchi charge can be too large -/

/-- The rooted Suzuki Bianchi amplitude squares exactly to its prime mass. -/
theorem noetherObstruction_suzukiBianchiAmplitudeSq (p : Nat.Primes) :
    suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2 =
      suzukiCriticalRootedBianchiPrimeMass p :=
  suzukiCriticalRootedBianchiPrimeAmplitude_sq p

/-- The associated prime Bianchi mass is not summable. -/
theorem noetherObstruction_suzukiBianchiMassNotSummable :
    ¬ Summable suzukiCriticalRootedBianchiPrimeMass :=
  not_summable_suzukiCriticalRootedBianchiPrimeMass

/-- Equivalently, the rooted Bianchi amplitude is not square summable. -/
theorem noetherObstruction_suzukiBianchiAmplitudeNotSquareSummable :
    ¬ Summable (fun p => suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2) :=
  not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude

end RHTower
