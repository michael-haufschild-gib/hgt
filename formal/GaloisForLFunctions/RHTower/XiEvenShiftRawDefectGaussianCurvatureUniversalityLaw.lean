import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiMobiusDyadicGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianIntrinsicDimensionUniversalityLaw
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Raw even-shift Xi defects and Gaussian curvature

Actual uncorrected even-shift logarithmic-derivative defects already have an unconditional
cofinite Hilbert phase: literal exact recovery is equivalent to corrected-defect recovery and to
raw-carrier differential independence over both valuation bases.  Doubling the grade labels
preserves exactly their pointed collision locus.

This file composes that established raw phase with the Möbius dyadic and HilbertMetric curvature
laws.  Literal raw-Xi recovery together with packet rank at least two becomes one exact phase
carrying corrected recovery, raw differential independence, dyadic and Szegő positivity,
canonical and cofinite reconstruction, global Gaussian concavity, strict curvature, the exact
self-commutator energy identity, and operator nonnormality.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

open scoped UpperEndDifferentialInstances

/-- **Raw-defect/Gaussian-curvature connector.**  Literal cofinite recovery from actual raw Xi
defects, together with the sharp rank-two condition, is exactly the transverse Gaussian-curvature
phase of the corrected doubled-grade packet. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_and_two_le_iff_gaussianCurvaturePhase
    {d : ℕ} (grade : Fin d → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (fun i => 2 * grade i) m p t := by
  calc
    _ ↔
        (Function.Injective grade ∧ ∀ i, grade i ≠ 0) ∧
          2 ≤ d :=
      and_congr
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade)
        Iff.rfl
    _ ↔
        (Function.Injective (fun i => 2 * grade i) ∧
            ∀ i, 2 * grade i ≠ 0) ∧
          2 ≤ d :=
      and_congr (injective_two_mul_and_ne_zero_iff grade).symm Iff.rfl
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
            (fun i => 2 * grade i) m ∧
          2 ≤ d :=
      and_congr
        (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          (fun i => 2 * grade i) m).symm
        Iff.rfl
    _ ↔ _ :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        (fun i => 2 * grade i) m p t ht).symm

/-- **Raw-defect/sign-duality connector.**  Literal raw-Xi cofinite reconstruction and packet
rank two are exactly doubled-aperture reconstruction sign duality at any chosen depth, prime,
and nonnegative scale. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_and_two_le_iff_curvatureSignDuality
    {d : ℕ} (grade : Fin d → ℕ)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (fun i => 2 * grade i) jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (fun i => 2 * grade i)
          jetDepth valuationPrime valuationScale :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_and_two_le_iff_gaussianCurvaturePhase
        grade jetDepth valuationPrime valuationScale hvaluationScale
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        (fun i => 2 * grade i)
        jetDepth valuationPrime valuationScale

/-- **Universal raw-defect/sign-duality law.**  Literal raw-Xi cofinite reconstruction and
packet rank two are exactly doubled-aperture reconstruction sign duality at every depth, prime,
and nonnegative scale. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_and_two_le_iff_every_curvatureSignDuality
    {d : ℕ} (grade : Fin d → ℕ) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (fun i => 2 * grade i)
            jetDepth valuationPrime valuationScale := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (fun i => 2 * grade i) 0 p 0 :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_and_two_le_iff_gaussianCurvaturePhase
        grade 0 p 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        (fun i => 2 * grade i) 0 p 0 le_rfl

/-- Minimal raw-defect/doubled-aperture Gaussian certificate.  Doubled-aperture exact-Hilbert
curvature already forces the pointed collision-free grade condition, hence literal and corrected
raw reconstruction, differential independence, and cross-prime intrinsic geometry. -/
structure XiEvenShiftRawDefectGaussianCurvatureCertificate
    {d : ℕ} (grade : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  doubledApertureExactHilbertCurvature :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      (fun i => 2 * grade i) sourcePrime metricPrime m t

namespace XiEvenShiftRawDefectGaussianCurvatureCertificate

/-- Doubled exact-Hilbert curvature supplies its complete pointed collision condition. -/
theorem doubledApertureInjectiveAndNeZero
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    Function.Injective (fun i => 2 * grade i) ∧
      ∀ i, 2 * grade i ≠ 0 :=
  hcertificate.doubledApertureExactHilbertCurvature.injectiveAndNeZero

/-- Doubled exact-Hilbert curvature discharges the pointed collision-free grade condition. -/
theorem gradeInjectiveAndNeZero
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    Function.Injective grade ∧ ∀ i, grade i ≠ 0 :=
  (injective_two_mul_and_ne_zero_iff grade).1
    hcertificate.doubledApertureInjectiveAndNeZero

/-- Literal raw reconstruction is derived from doubled exact-Hilbert curvature. -/
theorem rawCofiniteReconstruction
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade :=
  (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).2
    hcertificate.gradeInjectiveAndNeZero

/-- Raw reconstruction already contains the full corrected/raw Hilbert-differential phase. -/
theorem rawCofiniteHilbertPhase
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
        (fun i => 2 * grade i) ∧
      DifferentialIndependent upperEndRationalCoordinateField
        (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) ∧
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) :=
  (xiEvenShiftRawLogDerivDefectCofiniteHilbertPhase_iff grade).1
    hcertificate.rawCofiniteReconstruction

/-- Corrected doubled-grade recovery is derived from literal raw recovery. -/
theorem correctedCofiniteReconstruction
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
      (fun i => 2 * grade i) :=
  hcertificate.rawCofiniteHilbertPhase.1

/-- Rational-base raw differential independence is derived from literal raw recovery. -/
theorem rawRationalDifferentialIndependent
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) :=
  hcertificate.rawCofiniteHilbertPhase.2.1

/-- All-valuation raw differential independence is derived from literal raw recovery. -/
theorem rawAllValuationDifferentialIndependent
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) :=
  hcertificate.rawCofiniteHilbertPhase.2.2

/-- The stored strict-curvature package discharges packet rank at its nonnegative scale. -/
theorem rankTwo
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t)
    (ht : 0 ≤ t) :
    2 ≤ d :=
  ((xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
    (fun i => 2 * grade i) sourcePrime metricPrime m t ht).2
      hcertificate.doubledApertureExactHilbertCurvature).2

/-- At a nonnegative stored scale, the raw certificate supplies intrinsic one-dimensional
Gaussian geometry at every independently chosen prime. -/
theorem doubledApertureIntrinsicDimensionCertificate
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (fun i => 2 * grade i) intrinsicPrime :=
  (xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
    (fun i => 2 * grade i) intrinsicPrime).1
      ⟨hcertificate.doubledApertureInjectiveAndNeZero.1,
        hcertificate.rankTwo ht⟩

/-- The raw certificate forces doubled-aperture collision sign duality at every independently
chosen valuation prime and nonnegative scale. -/
theorem doubledApertureCollisionSignDualityCertificate
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t)
    (ht : 0 ≤ t)
    (valuationPrime intrinsicPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
      (fun i => 2 * grade i) valuationPrime valuationScale :=
  (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_intrinsicDimensionCertificate
    (fun i => 2 * grade i) valuationPrime intrinsicPrime
    valuationScale hvaluationScale).2
      (hcertificate.doubledApertureIntrinsicDimensionCertificate ht intrinsicPrime)

/-- **Raw-Xi/valuation universality connector.**  Literal raw reconstruction already forces the
full curvature, nonnormality, intrinsic-dimension, and differential-rank equivalence chain for
the doubled aperture at arbitrary primes and nonnegative scales.  No sign condition on the scale
stored in the raw certificate is needed. -/
theorem doubledApertureValuationUniversalityPhase
    {d : ℕ} {grade : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (fun i => 2 * grade i)
      valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    (fun i => 2 * grade i)
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale
    hcertificate.doubledApertureInjectiveAndNeZero.1

end XiEvenShiftRawDefectGaussianCurvatureCertificate

/-- **Raw-defect curvature-enhanced Hilbert universality.**  The existing literal raw-Xi Hilbert
phase and rank at least two are equivalent to the full corrected, differential, Möbius,
transverse, and Gaussian metric certificate. -/
theorem xiEvenShiftRawLogDerivDefect_gaussianCurvatureCertificate_iff
    {d : ℕ} (grade : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨hraw, htwo⟩
    have hcondition :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).1 hraw
    have hdoubledCondition :=
      (injective_two_mul_and_ne_zero_iff grade).2 hcondition
    have hdyadic :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
        (fun i => 2 * grade i)).2 hdoubledCondition
    exact {
      doubledApertureExactHilbertCurvature :=
        (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
          (fun i => 2 * grade i) sourcePrime metricPrime m t ht).1
            ⟨hdyadic, htwo⟩ }
  · intro hcertificate
    have hdyadicRank :=
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        (fun i => 2 * grade i) sourcePrime metricPrime m t ht).2
          hcertificate.doubledApertureExactHilbertCurvature
    exact ⟨hcertificate.rawCofiniteReconstruction, hdyadicRank.2⟩

/-- **Sharp raw-defect curvature classification.**  The complete literal/differential/metric
certificate is exactly absence of zero or repeated grades together with packet rank at least two. -/
theorem xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_injective_ne_zero_two_le
    {d : ℕ} (grade : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((Function.Injective grade ∧ ∀ i, grade i ≠ 0) ∧
        2 ≤ d) ↔
      XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t := by
  calc
    _ ↔ XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
          2 ≤ d :=
      and_congr
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).symm
        Iff.rfl
    _ ↔ _ :=
      xiEvenShiftRawLogDerivDefect_gaussianCurvatureCertificate_iff
        grade sourcePrime metricPrime m t ht

/-- **Universal raw-defect curvature law.**  The pointed collision-free raw-Xi phase of rank at
least two is exactly the phase in which the complete literal, differential, reconstruction, and
Gaussian geometry certificate holds at every pair of primes, every depth, and every nonnegative
scale. -/
theorem
    xiEvenShiftRawDefect_injective_ne_zero_two_le_iff_every_gaussianCurvatureCertificate
    {d : ℕ} (grade : Fin d → ℕ) :
    ((Function.Injective grade ∧ ∀ i, grade i ≠ 0) ∧
        2 ≤ d) ↔
      ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiEvenShiftRawDefectGaussianCurvatureCertificate
          grade sourcePrime metricPrime m t := by
  constructor
  · intro h sourcePrime metricPrime m t ht
    exact
      (xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_injective_ne_zero_two_le
        grade sourcePrime metricPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall p p 0 0 le_rfl
    exact
      (xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_injective_ne_zero_two_le
        grade p p 0 0 le_rfl).2 hcertificate

/-- **Exact raw-defect/sign-duality connector.**  One raw-defect curvature certificate is
exactly reconstruction sign duality for the doubled aperture at any independently chosen
depth, prime, and nonnegative scale. -/
theorem
    xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_curvatureSignDuality
    {d : ℕ} (grade : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (fun i => 2 * grade i) jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
          (fun i => 2 * grade i) sourcePrime metricPrime m t := by
      constructor
      · exact fun hcertificate =>
          hcertificate.doubledApertureExactHilbertCurvature
      · exact fun hcertificate =>
          ⟨hcertificate⟩
    _ ↔ _ :=
      xiMobius_dyadicGaussianCurvatureExactHilbertCertificate_iff_curvatureSignDuality
        (fun i => 2 * grade i) sourcePrime metricPrime m t ht
        jetDepth valuationPrime valuationScale hvaluationScale

/-- **Universal raw-defect/sign-duality law.**  One raw-defect curvature certificate at a
nonnegative stored scale is exactly doubled-aperture reconstruction sign duality at every
target depth, prime, and nonnegative scale. -/
theorem
    xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_every_curvatureSignDuality
    {d : ℕ} (grade : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiEvenShiftRawDefectGaussianCurvatureCertificate
        grade sourcePrime metricPrime m t ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (fun i => 2 * grade i)
            jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
          (fun i => 2 * grade i) sourcePrime metricPrime m t := by
      constructor
      · exact fun hcertificate =>
          hcertificate.doubledApertureExactHilbertCurvature
      · exact fun hcertificate =>
          ⟨hcertificate⟩
    _ ↔ _ :=
      xiMobius_dyadicGaussianCurvatureExactHilbertCertificate_iff_every_curvatureSignDuality
        (fun i => 2 * grade i) sourcePrime metricPrime m t ht

end

end RHTower
