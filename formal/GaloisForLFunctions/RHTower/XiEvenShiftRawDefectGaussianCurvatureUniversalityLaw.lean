import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiMobiusDyadicGaussianCurvatureUniversalityLaw

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

local instance xiRawDefectCurvatureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiRawDefectCurvatureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiRawDefectCurvatureUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiRawDefectCurvatureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiRawDefectCurvatureCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiRawDefectCurvatureCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiRawDefectCurvatureAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiRawDefectCurvatureAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

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

/-- Literal raw-defect Hilbert and differential data together with complete doubled-aperture
Gaussian geometry. -/
structure XiEvenShiftRawDefectGaussianCurvatureCertificate
    {d : ℕ} (grade : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  rawCofiniteReconstruction :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade
  correctedCofiniteReconstruction :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
      (fun i => 2 * grade i)
  rawRationalDifferentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i))
  rawAllValuationDifferentialIndependent :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i))
  doubledApertureExactHilbertCurvature :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      (fun i => 2 * grade i) sourcePrime metricPrime m t

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
    have hrawPhase :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertPhase_iff grade).1 hraw
    have hcondition :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).1 hraw
    have hdoubledCondition :=
      (injective_two_mul_and_ne_zero_iff grade).2 hcondition
    have hdyadic :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
        (fun i => 2 * grade i)).2 hdoubledCondition
    exact {
      rawCofiniteReconstruction := hraw
      correctedCofiniteReconstruction := hrawPhase.1
      rawRationalDifferentialIndependent := hrawPhase.2.1
      rawAllValuationDifferentialIndependent := hrawPhase.2.2
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

end

end RHTower
