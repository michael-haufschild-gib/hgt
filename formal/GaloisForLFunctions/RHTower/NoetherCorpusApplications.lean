import GaloisForLFunctions.RHTower.ChargeMotion
import GaloisForLFunctions.RHTower.DeningerFailureNerveMixedDaggerCoboundary
import GaloisForLFunctions.RHTower.DeningerOneSidedFramedMateCurvatureTransgression
import GaloisForLFunctions.RHTower.DeningerPlaceCountable
import GaloisForLFunctions.RHTower.DeningerRestrictedPrimeGluing
import GaloisForLFunctions.RHTower.MobiusFixedTokenReservoirConservation
import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCurvature
import GaloisForLFunctions.RHTower.SuzukiCriticalRootedBianchiCofinalNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaClockDescent
import GaloisForLFunctions.RHTower.XiCayleyFockOrderSpaceConservation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket
import GaloisForLFunctions.RHTower.XiSourceCayleyOrderSpaceConservationLaw
import GaloisForLFunctions.RHTower.XiWoldPoissonBivariateConormal

/-!
# Noether applications in the arithmetic and Xi corpus

Premise-free arithmetic applications of first-Noether conservation, second-Noether Bianchi/Ward
identities, topological charge invariance, and algebraic Noetherianity.  The final section records a
closed obstruction: one natural rooted Bianchi charge is not summable over primes.
-/

noncomputable section

namespace RHTower

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
