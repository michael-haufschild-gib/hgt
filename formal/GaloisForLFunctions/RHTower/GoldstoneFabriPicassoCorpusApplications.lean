import GaloisForLFunctions.RHTower.CCMConnesConsaniKernelGrowth
import GaloisForLFunctions.RHTower.CCMGuinandWeilCodiagonalObserverDimension
import GaloisForLFunctions.RHTower.CCMGuinandWeilFullSourceObserver
import GaloisForLFunctions.RHTower.CCMOddResponseQuotientCentralZero
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGammaSlepianDecomposition
import GaloisForLFunctions.RHTower.BurnolCofiniteHorizonGerm
import GaloisForLFunctions.RHTower.CompactOpenKolchinWardChargeEscape
import GaloisForLFunctions.RHTower.DeningerBigWittPrimeSeamDirichletTransport
import GaloisForLFunctions.RHTower.GaussReciprocalCharacterAdmission
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerSpectralMatrix
import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniPermutationSectorNoGo
import GaloisForLFunctions.RHTower.InfinitePhaseLadderLocalHorizonLaw
import GaloisForLFunctions.RHTower.JuliaCriticalFactorialDefectMeasureCompletion
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseGroundState
import GaloisForLFunctions.RHTower.RouteRClosedPositiveCoinvariantCompletionNoGo
import GaloisForLFunctions.RHTower.SoninSemilocalGradingBounds
import GaloisForLFunctions.RHTower.SquarefreeCriticalFockEscape
import GaloisForLFunctions.RHTower.SuzukiCofinalPositiveFinitePartNoGo
import GaloisForLFunctions.RHTower.SuzukiCriticalRootedBianchiCofinalNoGo
import GaloisForLFunctions.RHTower.XiAperturePoissonFullApertureHilbertTransport
import GaloisForLFunctions.RHTower.XiHeatCassiniMassCriticalSmoothingWall
import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent
import GaloisForLFunctions.RHTower.XiReflectionChargeCriticalSourceEscape

/-!
# Goldstone and Fabri--Picasso applications in the arithmetic corpus

This module records closed mechanical applications of zero-mode, charge-neutrality, unbounded
current, and Hilbert-completion obstructions already proved throughout the arithmetic corpus.
They are structural analogues, not claims that arithmetic objects satisfy physical QFT axioms.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- The first theta-cusp state is a nowhere-zero exact zero-energy mode. -/
theorem goldstone_thetaCuspMorseMode :
    (∀ x : ℝ,
      -deriv (deriv (thetaCuspMorseGroundState 1)) x +
          thetaCuspMorsePotentialMinus (5 / 4 : ℝ) 1 x *
            thetaCuspMorseGroundState 1 x = 0) ∧
      ∀ x : ℝ, thetaCuspMorseGroundState 1 x ≠ 0 := by
  constructor
  · exact thetaCuspMorseGroundState_schrodinger_zero 1
  · intro x
    simp [thetaCuspMorseGroundState, thetaCuspMorseZeroMode]

/-- Circle compression creates a nonzero zero mode outside both packet and original kernel. -/
theorem goldstone_compressedCircleZeroMode (L : CCMCircleLength) :
    ccmConnesConsaniCompressedDirac L (ccmSymmetricPairPacket L)
        ⟨(ccmAntisymmetricPair L : DiagonalL2 ℤ), by
          change (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∈
            (ccmCircleDirac (L : ℝ)).domain
          exact (ccmAntisymmetricPair L).property⟩ = 0 ∧
      (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∉
        GaloisForLFunctions.HTGeometry.smoothPacketSpan
          (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L) ∧
      ccmCircleDirac (L : ℝ) (ccmAntisymmetricPair L) ≠ 0 :=
  connesConsani_propDpert1_exactRankCounterexample L

/-- Even/odd sector imbalance leaves a nonzero central mode after quotienting a zero odd line. -/
theorem goldstone_oddEvenResidualZero
    (N : ℕ) (C : CCMEvenSector N →ₗ[ℂ] CCMOddSector N) :
    ∃ q : CCMGradedSector N ⧸ ccmOddRadicalLine (0 : CCMOddSector N),
      q ≠ 0 ∧
        ccmOddRadicalQuotientCompletion
          (0 : CCMOddSector N →ₗ[ℂ] CCMEvenSector N) C 0 (by simp) q = 0 := by
  simpa using exists_nonzero_kernel_ccmOddRadicalQuotientCompletion
    (B := (0 : CCMOddSector N →ₗ[ℂ] CCMEvenSector N)) C
    (0 : CCMOddSector N) (by simp)

/-- The residual Goldstone mode forces a central quotient characteristic zero. -/
theorem goldstone_oddEvenResidualCharacteristicZero
    (N : ℕ) (C : CCMEvenSector N →ₗ[ℂ] CCMOddSector N) :
    (ccmOddRadicalQuotientCompletion
        (0 : CCMOddSector N →ₗ[ℂ] CCMEvenSector N) C 0 (by simp)).charpoly.eval 0 = 0 := by
  simpa using ccmOddRadicalQuotientCompletion_charpoly_eval_zero
    (B := (0 : CCMOddSector N →ₗ[ℂ] CCMEvenSector N)) C
    (0 : CCMOddSector N) (by simp)

/-- A coupled two-prime spectral matrix creates a zero mode absent from every bare node. -/
theorem goldstone_twoPrimeCoupledZeroMode (e : ℕ) :
    (∃ x : Fin 4 → ℝ, x ≠ 0 ∧
      (HedenmalmThetaSource.gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e
        ⟨2, Nat.prime_two⟩ ⟨3, Nat.prime_three⟩).mulVec x = 0) ∧
      ∀ i : Fin 4,
        HedenmalmThetaSource.gammaSewnCriticalPrimeDepthPacket_node e
          ⟨2, Nat.prime_two⟩ ⟨3, Nat.prime_three⟩ i ≠ 0 := by
  apply HedenmalmThetaSource.gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_zeroMode_off_bareNodeGrid
  norm_num

/-- The exact Gamma--Slepian operator realizes the unbroken branch: no invisible zero mode. -/
theorem goldstone_gammaSlepianUnbroken (a : SuzukiPositiveAperture) :
    ccmGammaSlepianEigenspace a 0 = ⊥ :=
  ccmGammaSlepianEigenspace_zero_eq_bot a

/-- One more reflection orbit than observed modes creates an invisible nonzero imbalance. -/
theorem goldstone_overcompleteCodiagonalZeroMode
    (N : ℕ) (angle : Fin (N + 1) → ℝ) :
    ∃ imbalance : Fin (N + 1) → ℝ, imbalance ≠ 0 ∧
      ∀ k : Fin N,
        ∑ i, imbalance i *
          Real.sin (((k : ℕ) + 1 : ℝ) * angle i) = 0 := by
  exact ccmGuinandWeilRectangularSineMoment_exists_nonzero_kernel
    (by omega) angle

/-- Exceeding full finite source-coordinate dimension creates an invisible signed source. -/
theorem goldstone_overcompleteSourceObserverZeroMode
    (N : ℕ) (horizon : Fin (2 * N + 2) → ℝ) :
    ∃ weight : Fin (2 * N + 2) → ℝ, weight ≠ 0 ∧
      ccmGuinandWeilFiniteSourceCoordinateObserver (N := N) horizon weight = 0 := by
  exact ccmGuinandWeilFiniteSourceCoordinateObserver_exists_nonzero_kernel
    (by omega) horizon

/-- The same overcomplete signed source annihilates the finite event-packet matrix. -/
theorem goldstone_overcompleteEventPacketZeroMode
    (N : ℕ) (horizon : Fin (2 * N + 2) → ℝ) :
    ∃ weight : Fin (2 * N + 2) → ℝ, weight ≠ 0 ∧
      ccmGuinandWeilFiniteEventPacketMatrix (N := N) weight horizon = 0 := by
  exact ccmGuinandWeilFiniteEventPacketMatrix_exists_nonzero_kernel
    (by omega) horizon

/-- Prime two's ground commutator row escapes every finite bound. -/
theorem fabriPicasso_primeTwoGroundCommutatorUnbounded :
    ∀ B : ℝ, ∃ k : ℕ, 0 < k ∧
      B < |semilocalOnePrimeGroundCommutatorRow 2 k| :=
  semilocalOnePrimeGroundCommutatorRow_unbounded Nat.prime_two

/-- Critical squarefree source has no strong Fock limit although its tangent residue survives. -/
theorem fabriPicasso_squarefreeCriticalFockEscape :
    (¬ ∃ v : lp (fun _ : ℕ => ℂ) 2,
        Tendsto criticalSquarefreeSourceFamily (𝓝[>] (1 : ℝ)) (𝓝 v)) ∧
      Tendsto (fun sigma : ℝ =>
          if hsigma : 1 < sigma then
            ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
          else 0)
        (𝓝[>] (1 : ℝ)) (𝓝 4) :=
  squarefreeCriticalFockEscape

/-- Rooted Bianchi amplitudes have infinite total squared charge. -/
theorem fabriPicasso_suzukiBianchiChargeNotSquareSummable :
    ¬ Summable (fun p => suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2) :=
  not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude

/-- The canonical Burnol critical germ does not define an all-prime Hilbert vector. -/
theorem fabriPicasso_burnolCriticalGermOutsideHilbert :
    ¬ Summable (fun p : Nat.Primes =>
      ‖((1 : ℂ) / ((Real.sqrt ((p : ℕ) : ℝ) : ℝ) : ℂ))‖ ^ 2) :=
  burnolGermWitness_not_summable

/-- The Big-Witt physical half-density has divergent squared norm. -/
theorem fabriPicasso_deningerBigWittHalfDensityOutsideHilbert :
    ¬ Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      deningerBigWittCrossPrimeHalfDensity i ^ 2) :=
  not_summable_sq_deningerBigWittCrossPrimeHalfDensity

/-- No Big-Witt cross-prime Hilbert packet realizes every physical coordinate energy. -/
theorem fabriPicasso_noDeningerBigWittPhysicalPacket :
    ¬ ∃ z : DeningerCalderonWittCrossPrimePacketHilbert,
      ∀ i : DeningerCalderonWittCrossPrimePacketIndex,
        ‖z i‖ ^ 2 = deningerBigWittCrossPrimePhysicalAtom i :=
  no_deningerBigWittPhysicalHalfDensity_packet

/-- Universal theta-sector critical amplitude lies outside prime `ell^(2 : ℕ)`. -/
theorem fabriPicasso_thetaUniversalCriticalChannelOutsideHilbert :
    ¬ Summable (fun p : Nat.Primes =>
      routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2) :=
  HedenmalmThetaSource.not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq

/-- Unit-aperture Xi response gain has infinite total squared charge. -/
theorem fabriPicasso_unitXiApertureGainNotSummable :
    ¬ Summable (xiAperturePrimeFusedResponseGainSq 1) :=
  not_summable_xiAperturePrimeFusedResponseGainSq_one

/-- Julia critical boundary has divergent total squared coefficient mass. -/
theorem fabriPicasso_juliaCriticalBoundaryOutsideHilbert :
    ¬ Summable (fun pj : Nat.Primes × ℕ =>
      juliaCriticalEvenFactorialBoundaryEnergy pj.1 pj.2) :=
  not_summable_juliaCriticalEvenFactorialBoundaryEnergy

/-- Unsmoothed Xi valuation-one critical coefficient lies outside prime `ell^(2 : ℕ)`. -/
theorem fabriPicasso_xiValuationOneCriticalCoefficientOutsideHilbert :
    ¬ Summable (fun p : Nat.Primes =>
      xiMassValuationOneCriticalCoefficient p ^ 2) :=
  not_summable_xiMassValuationOneCriticalCoefficient_sq

/-- Suzuki critical sharp-prime source has infinite total mass. -/
theorem fabriPicasso_suzukiSharpPrimeMassNotSummable :
    ¬ Summable suzukiCriticalSharpPrimeMass :=
  not_summable_suzukiCriticalSharpPrimeMass

/-- Rational prime-two dilation used for the fixed-vacuum test. -/
def fabriPicassoPrimeTwoRationalUnit : GaloisForLFunctions.RHTower.CCMRationalUnit :=
  Units.mk0 (2 : ℚ) (by norm_num)

/-- Prime-two dilation has no nonzero fixed vector in the rational Morita Hilbert space. -/
theorem fabriPicasso_noPrimeDilationInvariantMoritaVacuum :
    ¬ ∃ f : GaloisForLFunctions.RHTower.CCMRationalMoritaHilbert,
      f ≠ 0 ∧
        GaloisForLFunctions.RHTower.ccmRationalMoritaHilbertLeftScale
          fabriPicassoPrimeTwoRationalUnit f = f := by
  rintro ⟨f, hf, hfixed⟩
  apply hf
  exact GaloisForLFunctions.RHTower.ccmRationalMoritaHilbertLeftScale_fixed_eq_zero
    fabriPicassoPrimeTwoRationalUnit (by norm_num [fabriPicassoPrimeTwoRationalUnit])
    (by norm_num [fabriPicassoPrimeTwoRationalUnit]) f hfixed

/-- Gauss--Hodge global charge exists exactly on the neutral centered-rate sector. -/
theorem fabriPicasso_gaussHodgeCurrent_iff_neutral (q : XiZeroCopy) :
    Summable (gaussHodgeMassCurrent 1 q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 :=
  summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero (by norm_num) q

/-- Raw determinant-curvature charge exists exactly on the same neutral sector. -/
theorem fabriPicasso_gammaSixCurrent_iff_neutral (q : XiZeroCopy) :
    Summable (gammaSixSuspensionDeterminantPrimeCurrent 1 q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 :=
  summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero
    (by norm_num) q

/-- Horizontal-collision current exists exactly when its finite-window charge vanishes. -/
theorem fabriPicasso_horizontalCollisionCurrent_iff_zeroCharge (T : ℝ) :
    Summable (xiHorizontalCollisionGaussHodgePrimeCurrent 1 T) ↔
      xiHorizontalCollisionCharge T = 0 :=
  summable_xiHorizontalCollisionGaussHodgePrimeCurrent_iff_charge_eq_zero
    (by norm_num) T

/-- Every finite phase ladder has unbounded lift energy at unit period. -/
theorem fabriPicasso_phaseLadderEnergyUnbounded
    {m : ℕ} (energy : Fin (m + 1) → ℝ) :
    ∀ C : ℝ, ∃ k : ℕ,
      C < ParityForecast.phaseLadderEnergy 1 energy (0, k) := by
  intro C
  exact ParityForecast.phaseLadderEnergy_unbounded (by norm_num) energy C

/-- Reflection charge either vanishes or forces unbounded discrete source flux. -/
theorem fabriPicasso_reflectionCharge_discreteFlux (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = 0 ∨
      ∀ C : ℝ, ∃ u : ℝ, 0 ≤ u ∧
        C < ‖xiMassCriticalDiscreteRemainderFlux 2 1 u‖ := by
  by_cases h : xiReflectionSelfIntersectionCharge T = 0
  · exact Or.inl h
  · right
    intro C
    exact xiMassCriticalDiscreteRemainderFlux_unbounded_of_reflectionCharge_ne_zero
      (a := 2) (c := 1) (sigma := 1) (T := T)
      (by norm_num) (by norm_num) (by norm_num) h C

/-- Reflection charge either vanishes or forces unbounded centered atom-cone charge. -/
theorem fabriPicasso_reflectionCharge_centeredAtomCone (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = 0 ∨
      ∀ C : ℝ, ∃ u : ℝ, 0 ≤ u ∧
        C < ‖xiMassCriticalCenteredAtomConeSum 2 1 1 u‖ := by
  by_cases h : xiReflectionSelfIntersectionCharge T = 0
  · exact Or.inl h
  · right
    intro C
    exact xiMassCriticalCenteredAtomConeSum_unbounded_of_reflectionCharge_ne_zero
      (a := 2) (c := 1) (sigma := 1) (d := 1) (T := T)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h C

/-- Reflection charge either vanishes or forces an unbounded centered Dirichlet pairing. -/
theorem fabriPicasso_reflectionCharge_centeredDirichletPairing (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = 0 ∨
      ∀ C : ℝ, ∃ u : ℝ, 0 ≤ u ∧
        C < ‖∫ x : ℝ,
          xiMassAnalyticTest 2 ((1 : ℂ) + (u : ℂ) * Complex.I) (x : ℂ) *
            xiMassCriticalCenteredDirichletConePolynomial 1 u x‖ := by
  by_cases h : xiReflectionSelfIntersectionCharge T = 0
  · exact Or.inl h
  · right
    intro C
    simpa using
      (xiMassCriticalCenteredDirichletConePairing_unbounded_of_reflectionCharge_ne_zero
        (a := 2) (c := 1) (sigma := 1) (d := 1) (T := T)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h C)

/-- Reflection charge either vanishes or forces unbounded half-density Weil charge. -/
theorem fabriPicasso_reflectionCharge_halfDensityWeil (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = 0 ∨
      ∀ C : ℝ, ∃ u : ℝ, 0 ≤ u ∧
        C < ‖xiMassCriticalHalfDensityWeilPairing 2 1 u‖ := by
  by_cases h : xiReflectionSelfIntersectionCharge T = 0
  · exact Or.inl h
  · right
    intro C
    exact xiMassCriticalHalfDensityWeilPairing_unbounded_of_reflectionCharge_ne_zero
      (a := 2) (c := 1) (sigma := 1) (d := 1) (T := T)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h C

/-- Reflection charge either vanishes or forces unbounded Deninger cross-current charge. -/
theorem fabriPicasso_reflectionCharge_deningerCrossCurrent (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = 0 ∨
      ∀ C : ℝ, ∃ u : ℝ, 0 ≤ u ∧
        C < ‖xiMassCriticalDeningerCrossCurrentCone 2 1 1 u‖ := by
  by_cases h : xiReflectionSelfIntersectionCharge T = 0
  · exact Or.inl h
  · right
    intro C
    exact xiMassCriticalDeningerCrossCurrentCone_unbounded_of_reflectionCharge_ne_zero
      (a := 2) (c := 1) (sigma := 1) (d := 1) (T := T)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h C

/-- Ward densities vanish on bounded windows while total mass grows by arbitrary quanta. -/
theorem fabriPicasso_localWardInvisibility_globalMassEscape :
    ∀ N : ℕ,
      (∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
        (fun n => multiplicityEscapingQuartetWardDensity (1 / 4 : ℝ) (N + 1) n)
        (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}) ∧
      ∀ n, multiplicityEscapingQuartetWardMass (1 / 4 : ℝ) (N + 1) n =
        (N + 1) • ENNReal.ofReal (8 * Real.pi) := by
  intro N
  rcases unboundedCompactOpenKolchinWardChargeEscape_law
      (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (N + 1) (Nat.succ_pos N) with
    ⟨_, _, _, _, _, _, hlocal, hmass, _⟩
  exact ⟨hlocal, hmass⟩

end RHTower
