import GaloisForLFunctions.RHTower.XiMobiusDyadicTransverseMatroidUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianIntrinsicDimensionUniversalityLaw

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

/-- Unit-mesh Möbius innovation positivity and rank two are exactly Gaussian reconstruction
sign duality at any fixed depth, prime, and nonnegative metric scale. -/
theorem
    xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    ((xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∧
        2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m p t := by
  calc
    _ ↔ XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t :=
      xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
        shift m p t ht
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        shift m p t

/-- Unit-mesh Möbius innovation positivity and rank two are exactly Gaussian reconstruction
sign duality simultaneously at every depth, prime, and nonnegative metric scale. -/
theorem
    xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_every_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) :
    ((xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∧
        2 ≤ N) ↔
      ∀ (m : ℕ) (p : Nat.Primes) (t : ℝ), 0 ≤ t →
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          shift m p t := by
  let sourcePrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  calc
    _ ↔ XiTransversePrimeJetApertureGaussianCurvaturePhase
          shift 0 sourcePrime 0 :=
      xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
        shift 0 sourcePrime 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        shift 0 sourcePrime 0 le_rfl

/-- Canonical Möbius reconstruction and rank two are exactly Gaussian reconstruction sign
duality at any fixed depth, prime, and nonnegative metric scale. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_and_two_le_iff_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime ∧
        2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m metricPrime t := by
  calc
    _ ↔ XiTransversePrimeJetApertureGaussianCurvaturePhase
          shift m metricPrime t :=
      xiMobiusPrimeIntegralApertureCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        shift sourcePrime metricPrime m t ht
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        shift m metricPrime t

/-- Canonical Möbius reconstruction and rank two are exactly Gaussian reconstruction sign
duality simultaneously at every depth, prime, and nonnegative metric scale. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_and_two_le_iff_every_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (sourcePrime : Nat.Primes) :
    (XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime ∧
        2 ≤ N) ↔
      ∀ (m : ℕ) (p : Nat.Primes) (t : ℝ), 0 ≤ t →
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          shift m p t := by
  calc
    _ ↔ XiTransversePrimeJetApertureGaussianCurvaturePhase
          shift 0 sourcePrime 0 :=
      xiMobiusPrimeIntegralApertureCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        shift sourcePrime sourcePrime 0 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        shift 0 sourcePrime 0 le_rfl

/-- Cofinite dyadic Möbius reconstruction and rank two are exactly Gaussian reconstruction sign
duality at any fixed depth, prime, and nonnegative metric scale. -/
theorem
    xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_and_two_le_iff_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
          2 (fun j => (shift j : ℝ)) sourcePrime ∧
        2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m metricPrime t := by
  calc
    _ ↔ XiTransversePrimeJetApertureGaussianCurvaturePhase
          shift m metricPrime t :=
      xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_and_two_le_iff_gaussianCurvaturePhase
        shift sourcePrime metricPrime m t ht
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        shift m metricPrime t

/-- Cofinite dyadic Möbius reconstruction and rank two are exactly Gaussian reconstruction sign
duality simultaneously at every depth, prime, and nonnegative metric scale. -/
theorem
    xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_and_two_le_iff_every_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (sourcePrime : Nat.Primes) :
    (XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
          2 (fun j => (shift j : ℝ)) sourcePrime ∧
        2 ≤ N) ↔
      ∀ (m : ℕ) (p : Nat.Primes) (t : ℝ), 0 ≤ t →
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          shift m p t := by
  calc
    _ ↔ XiTransversePrimeJetApertureGaussianCurvaturePhase
          shift 0 sourcePrime 0 :=
      xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_and_two_le_iff_gaussianCurvaturePhase
        shift sourcePrime sourcePrime 0 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        shift 0 sourcePrime 0 le_rfl

/-- Minimal exact-Hilbert Gaussian-curvature certificate for an integral Möbius dyadic packet.
Innovation positivity supplies every reconstruction and differential interface.  The
scale-sensitive commutator identity and strict curvature remain independent stored data;
nonnormality follows from those two fields. -/
structure XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
    {N : ℕ} (shift : Fin N → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  dyadicInnovationGram :
    (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef
  curvatureCommutatorIdentity :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift metricPrime s).det)) t =
      -2 * matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift metricPrime t))
  strictGaussianCurvature :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift metricPrime s).det)) t < 0

namespace XiMobiusDyadicGaussianCurvatureExactHilbertCertificate

/-- Innovation positivity discharges exactly injectivity and exclusion of zero. -/
theorem injectiveAndNeZero
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    Function.Injective shift ∧ ∀ j, shift j ≠ 0 :=
  (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
    shift).1 hcertificate.dyadicInnovationGram

/-- Innovation positivity supplies the complete seven-component Möbius/transverse exact-Hilbert
package already proved by the dyadic universality theorem. -/
theorem exactHilbertUniversality
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift sourcePrime).PosDef ∧
      XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime ∧
      XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        2 (fun j => (shift j : ℝ)) sourcePrime ∧
      XiTransversePrimeValuationCanonicalReconstruction shift sourcePrime ∧
      DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ∧
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ∧
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m := by
  have huniversality :=
    xiMobiusIntegralAperture_dyadicTransverseExactHilbertUniversality
      shift m sourcePrime
  dsimp only at huniversality
  rcases huniversality with
    ⟨hszego, hmobiusCanonical, hmobiusDyadic, htransverseCanonical,
      hrational, hallValuation, hcofinite⟩
  exact ⟨
    hszego.1 hcertificate.dyadicInnovationGram,
    hmobiusCanonical.1 hcertificate.dyadicInnovationGram,
    hmobiusDyadic.1 hcertificate.dyadicInnovationGram,
    htransverseCanonical.1 hcertificate.dyadicInnovationGram,
    hrational.1 hcertificate.dyadicInnovationGram,
    hallValuation.1 hcertificate.dyadicInnovationGram,
    hcofinite.1 hcertificate.dyadicInnovationGram⟩

/-- One-prime Möbius Szegő positivity is derived from innovation positivity. -/
theorem mobiusSzegoGram
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift sourcePrime).PosDef :=
  hcertificate.exactHilbertUniversality.1

/-- Möbius canonical reconstruction is derived from innovation positivity. -/
theorem mobiusCanonicalReconstruction
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime :=
  hcertificate.exactHilbertUniversality.2.1

/-- Möbius dyadic cofinite reconstruction is derived from innovation positivity. -/
theorem mobiusDyadicCofiniteReconstruction
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
      2 (fun j => (shift j : ℝ)) sourcePrime :=
  hcertificate.exactHilbertUniversality.2.2.1

/-- Transverse canonical reconstruction is derived from innovation positivity. -/
theorem transverseCanonicalReconstruction
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    XiTransversePrimeValuationCanonicalReconstruction shift sourcePrime :=
  hcertificate.exactHilbertUniversality.2.2.2.1

/-- Rational-base transverse differential independence is derived. -/
theorem rationalDifferentialIndependent
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun j => xiTransverseShiftUpperEndCarrier (shift j)) :=
  hcertificate.exactHilbertUniversality.2.2.2.2.1

/-- All-valuation transverse differential independence is derived. -/
theorem allValuationDifferentialIndependent
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun j => xiTransverseShiftUpperEndCarrier (shift j)) :=
  hcertificate.exactHilbertUniversality.2.2.2.2.2.1

/-- Innovation positivity supplies cofinite transverse recovery at every jet depth. -/
theorem cofinitePrimeJetExactRecoveryAt
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t)
    (jetDepth : ℕ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift jetDepth :=
  (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
    shift jetDepth).2 hcertificate.injectiveAndNeZero

/-- Stored-depth cofinite recovery remains available as a derived dot API. -/
theorem cofinitePrimeJetExactRecovery
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m :=
  hcertificate.cofinitePrimeJetExactRecoveryAt m

/-- Global Gaussian log-determinant concavity is derived from cofinite recovery. -/
theorem gaussianLogDetConcaveOn
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    ConcaveOn ℝ (Set.Ici 0) (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          shift metricPrime s).det) :=
  xiTransversePrimeValuationRankOneGaussianMetric_logDet_concaveOn_of_cofiniteHilbertReconstruction
    shift m metricPrime hcertificate.cofinitePrimeJetExactRecovery

/-- The stored energy identity and strict negative curvature force operator nonnormality
without an additional scale hypothesis. -/
theorem gaussianSimilarityNonnormal
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t) :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity shift metricPrime t) ≠ 0 := by
  intro hnormal
  have henergy :
      matrixHilbertSchmidtEnergy
          (matrixSelfCommutator
            (xiTransversePrimeValuationRankOneGaussianSimilarity
              shift metricPrime t)) = 0 :=
    (matrixHilbertSchmidtEnergy_eq_zero_iff _).2 hnormal
  have hsecondZero :
      deriv (deriv (fun s =>
        Real.log
          (xiTransversePrimeValuationRankOneGaussianMetricGram
            shift metricPrime s).det)) t = 0 := by
    rw [hcertificate.curvatureCommutatorIdentity, henergy, mul_zero]
  have : (0 : ℝ) < 0 := by
    simpa only [hsecondZero] using hcertificate.strictGaussianCurvature
  exact (lt_irrefl 0) this

/-- At a nonnegative stored scale, strict curvature discharges packet rank two. -/
theorem rankTwo
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t)
    (ht : 0 ≤ t) :
    2 ≤ N :=
  (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
    shift m metricPrime hcertificate.cofinitePrimeJetExactRecovery t ht).1
      hcertificate.strictGaussianCurvature

/-- The dyadic certificate supplies intrinsic one-dimensional geometry at every prime. -/
theorem intrinsicDimensionCertificate
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      shift intrinsicPrime :=
  (xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
    shift intrinsicPrime).1
      ⟨hcertificate.injectiveAndNeZero.1, hcertificate.rankTwo ht⟩

/-- **Dyadic full sign-duality discharge.**  One exact-Hilbert curvature certificate forces
reconstruction sign duality at every independently chosen depth, prime, and nonnegative scale. -/
theorem curvatureSignDualityCertificate
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
      shift jetDepth valuationPrime valuationScale :=
  (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
    shift jetDepth valuationPrime valuationScale hvaluationScale).1
      ⟨hcertificate.cofinitePrimeJetExactRecoveryAt jetDepth,
        hcertificate.rankTwo ht⟩

/-- **Dyadic valuation universality connector.**  Innovation positivity alone forces the complete
curvature, nonnormality, intrinsic-dimension, and differential-rank equivalence chain at
independently chosen primes and nonnegative scales. -/
theorem valuationUniversalityPhase
    {N : ℕ} {shift : Fin N → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    shift valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale
    hcertificate.injectiveAndNeZero.1

end XiMobiusDyadicGaussianCurvatureExactHilbertCertificate

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
    have hrec :
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift m).2
          ((xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
            shift).1 hdyadic)
    have hphase :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_and_two_le_iff_gaussianCurvaturePhase
        shift m metricPrime t ht).1 ⟨hdyadic, htwo⟩
    exact {
      dyadicInnovationGram := hdyadic
      curvatureCommutatorIdentity :=
        xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_selfCommutatorEnergy_of_cofiniteHilbertReconstruction
          shift m metricPrime hrec t ht
      strictGaussianCurvature := hphase.2 }
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

/-- **Exact Möbius/sign-duality connector.**  A Möbius dyadic exact-Hilbert curvature
certificate at one source prime, metric prime, depth, and nonnegative scale is exactly
reconstruction sign duality at any independently chosen depth, prime, and nonnegative scale. -/
theorem
    xiMobius_dyadicGaussianCurvatureExactHilbertCertificate_iff_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (xiMobiusContinuousApertureDyadicInnovationGram 2
            (fun j => (shift j : ℝ))).PosDef ∧
          2 ≤ N :=
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        shift sourcePrime metricPrime m t ht).symm
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
            shift jetDepth ∧
          2 ≤ N :=
      and_congr
        ((xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
          shift).trans
            (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
              shift jetDepth).symm)
        Iff.rfl
    _ ↔ _ :=
      xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
        shift jetDepth valuationPrime valuationScale hvaluationScale

/-- **Universal Möbius/sign-duality law.**  One Möbius dyadic exact-Hilbert curvature
certificate at a nonnegative stored scale is exactly reconstruction sign duality at every
target depth, prime, and nonnegative scale. -/
theorem
    xiMobius_dyadicGaussianCurvatureExactHilbertCertificate_iff_every_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        shift sourcePrime metricPrime m t ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            shift jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (xiMobiusContinuousApertureDyadicInnovationGram 2
            (fun j => (shift j : ℝ))).PosDef ∧
          2 ≤ N :=
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        shift sourcePrime metricPrime m t ht).symm
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
          2 ≤ N :=
      and_congr
        ((xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
          shift).trans
            (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
              shift m).symm)
        Iff.rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_two_le_iff_every_gaussianCurvatureSignDualityCertificate
        shift m

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
