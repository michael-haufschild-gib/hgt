import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCenteredLogConnection
import GaloisForLFunctions.RHTower.HedenmalmThetaXiMassCompensatedAsymptoticCarrier

/-!
# Wold / theta-Green anomaly compensation

The trace-class Wold reduction may be inserted before the phase-linear theta-Green compensation.
The resulting theta-plus-pure-Wold packet is unconditionally bounded and has the same two-residue
future carrier as the original theta-plus-valuation-one packet: the finite Euler trace correction
is vertically dispersive.  Thus the RH-strength Wold and theta currents form one anti-diagonal
anomaly modulo the bounded dispersive ideal.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Phase-linear sum of the polarized theta Green current and the pure depth-one Wold current. -/
def xiHeatCassiniWoldThetaGreenCompensatedPacket
    (a c : ℝ) (tau : ℂ) : ℂ :=
  xiMassThetaQuantileMetricSymplecticIntegral a c tau +
    Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
      xiHeatCassiniPureWoldHalfDensityLayer a tau

/-- Replacing valuation one by pure Wold removes exactly the finite Euler trace current. -/
theorem xiHeatCassiniWoldThetaGreenCompensatedPacket_eq_connection_sub_trace
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    (c : ℝ) {tau : ℂ} (htau : 0 < tau.re) :
    xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau =
      xiMassThetaPrimeConnectionCompensatedPacket a c tau -
        (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
          xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a tau := by
  have hsource :=
    xiMassValuationOnePrimeLayer_eq_pureWoldHalfDensity_add_traceCorrection
      hhalf hda htau
  have hconnection :=
    xiMassPrimeHalfDensityConnectionLayer_eq_valuationOne hhalf hda htau
  unfold xiHeatCassiniWoldThetaGreenCompensatedPacket
    xiMassThetaPrimeConnectionCompensatedPacket
  rw [hconnection, hsource]
  ring

/-- **Wold / theta-Green Ward identity.**  The pure Wold packet leaves only the archimedean face,
higher prime powers, and the finite Euler trace correction. -/
theorem xiHeatCassiniWoldThetaGreenCompensatedPacket_eq_arch_sub_nonPrime_sub_trace
    {a c d : ℝ} (hdepth : 1 / 2 < d) (hda : d < a)
    (hhalf : 1 / 2 < c) (hca : c < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau =
      (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        (xiMassBottomArchIntegral a c tau -
          (xiMassPrimeSquareLayer a tau + xiMassHighPrimePowerTail a tau) -
          xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a tau) := by
  rw [xiHeatCassiniWoldThetaGreenCompensatedPacket_eq_connection_sub_trace
      hdepth hda c htau,
    xiMassThetaPrimeConnectionCompensatedPacket_eq_arch_sub_nonPrime
      hhalf hca htau]
  ring

/-- The finite Wold Euler trace current becomes extinct in future vertical time. -/
theorem tendsto_xiHeatCassiniWoldHalfDensityTraceCorrectionLayer_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a
        ((sigma : ℂ) + u * I)) atTop (𝓝 0) := by
  unfold xiHeatCassiniWoldHalfDensityTraceCorrectionLayer
  have hpoint : ∀ p : Nat.Primes,
      Tendsto (fun u : ℝ =>
        xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a
          ((sigma : ℂ) + u * I) p) atTop (𝓝 0) := by
    intro p
    have hfourier :=
      tendsto_stripFourier_xiMassAnalyticTest_vertical_atTop_zero
        ha hsigma (Real.log (p : ℝ))
    simpa [xiHeatCassiniWoldHalfDensityTraceCorrectionAtom,
      xiHeatCassiniPrimeMassFourierProfile] using
        hfourier.const_mul
          (xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient p : ℂ)
  let J : ℝ := ∫ x : ℝ, Real.exp (-sigma * |x|)
  have hmajor : Summable (fun p : Nat.Primes =>
      3 * xiMassPrimeSquareEulerWeight (1 / 4) p * J) :=
    ((summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_left 3).mul_right J
  have hdom : ∀ᶠ u : ℝ in atTop, ∀ p : Nat.Primes,
      ‖xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a
          ((sigma : ℂ) + u * I) p‖ ≤
        3 * xiMassPrimeSquareEulerWeight (1 / 4) p * J :=
    Eventually.of_forall fun u p => by
      simpa only [J] using
        norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom_vertical_le
          ha hsigma u p
  simpa using tendsto_tsum_of_dominated_convergence hmajor hpoint hdom

/-- The Wold / theta-Green packet is unconditionally bounded on every positive vertical line. -/
theorem exists_norm_xiHeatCassiniWoldThetaGreenCompensatedPacket_vertical_bound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖xiHeatCassiniWoldThetaGreenCompensatedPacket a c
        ((sigma : ℂ) + u * I)‖ ≤ C := by
  let d : ℝ := (a + 1 / 2) / 2
  have hdepth : 1 / 2 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have ha : 0 < a := by linarith
  obtain ⟨C, hC⟩ :=
    exists_norm_xiMassThetaPrimeConnectionCompensatedPacket_vertical_bound
      hhalf hca hsigma
  let B : ℝ :=
    3 * (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 4) p) *
      (∫ x : ℝ, Real.exp (-sigma * |x|))
  let q : ℂ := Complex.I * pinnedFirstMoment thetaQuantileCoordinate
  refine ⟨C + ‖q‖ * B, fun u => ?_⟩
  rw [xiHeatCassiniWoldThetaGreenCompensatedPacket_eq_connection_sub_trace
    hdepth hda c (by simpa using hsigma)]
  calc
    ‖xiMassThetaPrimeConnectionCompensatedPacket a c ((sigma : ℂ) + u * I) -
        q * xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a
          ((sigma : ℂ) + u * I)‖ ≤
      ‖xiMassThetaPrimeConnectionCompensatedPacket a c ((sigma : ℂ) + u * I)‖ +
        ‖q * xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a
          ((sigma : ℂ) + u * I)‖ := norm_sub_le _ _
    _ ≤ C + ‖q‖ * B := by
      rw [norm_mul]
      have htraceBound :
          ‖xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a
            ((sigma : ℂ) + u * I)‖ ≤ B := by
        simpa only [B] using
          (norm_xiHeatCassiniWoldHalfDensityTraceCorrectionLayer_vertical_le
            (a := a) (σ := sigma) ha hsigma u)
      exact add_le_add (hC u)
        (mul_le_mul_of_nonneg_left htraceBound (norm_nonneg q))

/-- **Carrier rigidity under Wold reduction.**  The finite Euler trace current is dispersive, so
the compensated pure-Wold packet has exactly the original crossed-arch / prime-square carrier. -/
theorem tendsto_xiHeatCassiniWoldThetaGreenCompensatedPacket_sub_carrier_atTop_zero
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiHeatCassiniWoldThetaGreenCompensatedPacket a c
          ((sigma : ℂ) + u * I) -
        xiMassThetaPrimeConnectionAsymptoticCarrier a
          ((sigma : ℂ) + u * I)) atTop (𝓝 0) := by
  let d : ℝ := (a + 1 / 2) / 2
  have hdepth : 1 / 2 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have ha : 0 < a := by linarith
  have hbase :=
    tendsto_xiMassThetaPrimeConnectionCompensatedPacket_sub_carrier_atTop_zero
      hhalf hca hsigma
  have htrace :=
    tendsto_xiHeatCassiniWoldHalfDensityTraceCorrectionLayer_vertical_atTop_zero
      ha hsigma
  have hscaled := htrace.const_mul
    (Complex.I * pinnedFirstMoment thetaQuantileCoordinate)
  have hdiff := hbase.sub hscaled
  have hdiff' : Tendsto (fun u : ℝ =>
      (xiMassThetaPrimeConnectionCompensatedPacket a c
          ((sigma : ℂ) + u * I) -
        xiMassThetaPrimeConnectionAsymptoticCarrier a
          ((sigma : ℂ) + u * I)) -
      (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a
          ((sigma : ℂ) + u * I)) atTop (𝓝 0) := by
    simpa using hdiff
  refine hdiff'.congr' (Eventually.of_forall fun u => ?_)
  change
    (xiMassThetaPrimeConnectionCompensatedPacket a c
          ((sigma : ℂ) + u * I) -
        xiMassThetaPrimeConnectionAsymptoticCarrier a
          ((sigma : ℂ) + u * I)) -
      (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a
          ((sigma : ℂ) + u * I) =
    xiHeatCassiniWoldThetaGreenCompensatedPacket a c
          ((sigma : ℂ) + u * I) -
        xiMassThetaPrimeConnectionAsymptoticCarrier a
          ((sigma : ℂ) + u * I)
  rw [xiHeatCassiniWoldThetaGreenCompensatedPacket_eq_connection_sub_trace
    hdepth hda c (by simpa using hsigma)]
  ring

end

end RHTower
