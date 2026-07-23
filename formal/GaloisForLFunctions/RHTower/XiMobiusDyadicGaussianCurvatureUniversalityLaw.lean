import GaloisForLFunctions.RHTower.XiMobiusDyadicTransverseMatroidUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase

/-!
# Xi Möbius dyadic Gaussian-curvature universality

The integral Möbius dyadic theorem already identifies innovation-Gram positivity with continuous
Szegő positivity, two canonical reconstruction interfaces, two cofinite reconstruction
interfaces, and differential independence over both valuation bases.  The transverse
HilbertMetric theorem turns the final cofinite reconstruction interface into an injective
Gaussian background.

This file composes those existing exact classifications.  Adding the sharp packet-rank condition
gives strict Gaussian log-volume curvature, the exact self-commutator energy identity,
nonnormality of the square-root similarity, and global log-determinant concavity.  The resulting
phase is uniform in both primes, jet depth, and nonnegative metric scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped ComplexOrder Differential

local instance xiMobiusDyadicCurvatureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiMobiusDyadicCurvatureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiMobiusDyadicCurvatureUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiMobiusDyadicCurvatureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiMobiusDyadicCurvatureCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiMobiusDyadicCurvatureCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiMobiusDyadicCurvatureAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiMobiusDyadicCurvatureAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- **Dyadic innovation/curvature connector.**  Unit-mesh Möbius innovation positivity, together
with the sharp rank-two condition, is exactly the transverse cofinite-Hilbert Gaussian-curvature
phase at every prime, depth, and nonnegative scale. -/
theorem
    xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    ((xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∧
        2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t := by
  calc
    _ ↔ XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
          2 ≤ N :=
      and_congr
        ((xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
          shift).trans
            (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
              shift m).symm)
        Iff.rfl
    _ ↔ _ :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        shift m p t ht).symm

/-- Exact continuous Möbius reconstruction discharges the cofinite-reconstruction premise in the
Gaussian-curvature phase; only the sharp packet-rank condition remains. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (shift : Fin N → ℕ) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime ∧
        2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        shift m metricPrime t := by
  calc
    _ ↔ XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
          2 ≤ N :=
      and_congr
        (xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
          shift m sourcePrime)
        Iff.rfl
    _ ↔ _ :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        shift m metricPrime t ht).symm

/-- Cofinite dyadic-depth reconstruction at one prime also discharges the transverse Gaussian
background condition at every other prime. -/
theorem
    xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (shift : Fin N → ℕ) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
          2 (fun j => (shift j : ℝ)) sourcePrime ∧
        2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        shift m metricPrime t := by
  calc
    _ ↔ (xiMobiusContinuousApertureDyadicInnovationGram 2
            (fun j => (shift j : ℝ))).PosDef ∧
          2 ≤ N :=
      and_congr
        ((xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift sourcePrime).trans
            (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
              shift).symm)
        Iff.rfl
    _ ↔ _ :=
      xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
        shift m metricPrime t ht

/-- Full exact-Hilbert and Gaussian geometry certificate attached to an integral Möbius dyadic
packet. -/
structure XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
    {N : ℕ} (shift : Fin N → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  dyadicInnovationGram :
    (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef
  mobiusSzegoGram :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift sourcePrime).PosDef
  mobiusCanonicalReconstruction :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime
  mobiusDyadicCofiniteReconstruction :
    XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
      2 (fun j => (shift j : ℝ)) sourcePrime
  transverseCanonicalReconstruction :
    XiTransversePrimeValuationCanonicalReconstruction shift sourcePrime
  rationalDifferentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun j => xiTransverseShiftUpperEndCarrier (shift j))
  allValuationDifferentialIndependent :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun j => xiTransverseShiftUpperEndCarrier (shift j))
  cofinitePrimeJetExactRecovery :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m
  curvatureCommutatorIdentity :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift metricPrime s).det)) t =
      -2 * matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift metricPrime t))
  gaussianLogDetConcaveOn :
    ConcaveOn ℝ (Set.Ici 0) (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift metricPrime s).det)
  strictGaussianCurvature :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift metricPrime s).det)) t < 0
  gaussianSimilarityNonnormal :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity shift metricPrime t) ≠ 0

/-- **Curvature-enhanced exact-Hilbert universality.**  Dyadic innovation positivity and packet
rank at least two are equivalent to the simultaneous Möbius, transverse, differential, cofinite,
curvature-energy, concavity, and operator-nonnormality package. -/
theorem xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
    {N : ℕ} (shift : Fin N → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∧
        2 ≤ N) ↔
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨hdyadic, htwo⟩
    have huniversality :=
      xiMobiusIntegralAperture_dyadicTransverseExactHilbertUniversality
        shift m sourcePrime
    dsimp only at huniversality
    rcases huniversality with
      ⟨hszego, hmobiusCanonical, hmobiusDyadic, htransverseCanonical,
        hrational, hallValuation, hcofinite⟩
    have hrec := hcofinite.1 hdyadic
    have hphase :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
        shift m metricPrime t ht).1 ⟨hdyadic, htwo⟩
    have hnonnormal :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_nonnormal
        shift m metricPrime t ht).1 hphase
    exact {
      dyadicInnovationGram := hdyadic
      mobiusSzegoGram := hszego.1 hdyadic
      mobiusCanonicalReconstruction := hmobiusCanonical.1 hdyadic
      mobiusDyadicCofiniteReconstruction := hmobiusDyadic.1 hdyadic
      transverseCanonicalReconstruction := htransverseCanonical.1 hdyadic
      rationalDifferentialIndependent := hrational.1 hdyadic
      allValuationDifferentialIndependent := hallValuation.1 hdyadic
      cofinitePrimeJetExactRecovery := hrec
      curvatureCommutatorIdentity :=
        xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_selfCommutatorEnergy_of_cofiniteHilbertReconstruction
          shift m metricPrime hrec t ht
      gaussianLogDetConcaveOn :=
        xiTransversePrimeValuationRankOneGaussianMetric_logDet_concaveOn_of_cofiniteHilbertReconstruction
          shift m metricPrime hrec
      strictGaussianCurvature := hphase.2
      gaussianSimilarityNonnormal := hnonnormal.2 }
  · intro hcertificate
    have htwo :=
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
        shift m metricPrime hcertificate.cofinitePrimeJetExactRecovery t ht).1
          hcertificate.strictGaussianCurvature
    exact ⟨hcertificate.dyadicInnovationGram, htwo⟩

/-- **Universal Möbius dyadic curvature law.**  One dyadic innovation phase and the rank-two
condition hold exactly when the full exact-Hilbert curvature certificate holds for every source
prime, metric prime, jet depth, and nonnegative scale. -/
theorem
    xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_every_curvatureExactHilbertCertificate
    {N : ℕ} (shift : Fin N → ℕ) :
    ((xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∧
        2 ≤ N) ↔
      ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
          shift sourcePrime metricPrime m t := by
  constructor
  · intro h sourcePrime metricPrime m t ht
    exact
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        shift sourcePrime metricPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall p p 0 0 le_rfl
    exact
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        shift p p 0 0 le_rfl).2 hcertificate

/-- **Sharp failure complement.**  Outside the strict curvature phase, failure is exhausted by
the pre-existing zero/collision radical of the dyadic innovation Gram or by packet rank at most
one. -/
theorem xiMobiusIntegralAperture_gaussianCurvaturePhase_failure_iff
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    ¬ XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∨
        N ≤ 1 := by
  have hequivalence :=
    xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
      shift m p t ht
  constructor
  · intro hfailure
    by_cases hdyadic :
        (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef
    · right
      by_contra hlarge
      apply hfailure
      exact hequivalence.1 ⟨hdyadic, by omega⟩
    · exact Or.inl hdyadic
  · rintro (hdyadic | hsmall) hphase
    · exact hdyadic (hequivalence.2 hphase).1
    · have htwo := (hequivalence.2 hphase).2
      omega

end

end RHTower
