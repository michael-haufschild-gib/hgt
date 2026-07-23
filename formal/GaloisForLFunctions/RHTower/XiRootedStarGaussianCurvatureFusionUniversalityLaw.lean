import GaloisForLFunctions.RHTower.XiRootedStarIncidenceValuationMetricFusionUniversalityLaw
import GaloisForLFunctions.RHTower.XiMobiusDyadicGaussianCurvatureUniversalityLaw

/-!
# Rooted-star Xi Gaussian curvature fusion

The existing rooted-star fusion certificate identifies raw even-shift defect reconstruction with
incidence recovery, valuation and Szegő positivity, nonlinear Gaussian separation, and exact
cofinite prime-jet reconstruction.  The transverse Gaussian curvature law then supplies the
missing rank-two geometry: strict log-volume curvature and nonnormality of the square-root
similarity.

Consequently raw reconstruction together with a packet of size at least two is exactly the full
curvature-enhanced fusion phase.  This characterization is uniform over every injective
zero-preserving shift reparametrization, every prime, every jet depth, and every nonnegative
Gaussian scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped ComplexOrder Differential

/-- Minimal rooted-star incidence/valuation fusion enhanced by strict Gaussian curvature.
Ordinary metric fusion already supplies exact recovery at every depth; strict curvature then
derives operator nonnormality at every nonnegative stored scale. -/
structure XiRootedStarGaussianCurvatureExactMetricFusionCertificate
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  metricFusion :
    XiRootedStarIncidenceValuationMetricFusionCertificate
      grade embed p m
  strictGaussianCurvature :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          (embed ∘ grade) p s).det)) t < 0

namespace XiRootedStarGaussianCurvatureExactMetricFusionCertificate

/-- The nominal exact-metric interface is derived from ordinary metric fusion. -/
theorem exactMetricFusion
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t) :
    XiRootedStarIncidenceValuationExactMetricFusionCertificate
      grade embed p m :=
  (xiRootedStar_incidenceValuationMetricFusion_iff_exactMetricFusion
    grade embed p m).1 hcertificate.metricFusion

/-- Exact metric fusion supplies collision freedom and nonvanishing of the reparametrized
aperture packet. -/
theorem reparamInjectiveAndNeZero
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t) :
    Function.Injective (embed ∘ grade) ∧
      ∀ i, (embed ∘ grade) i ≠ 0 :=
  hcertificate.exactMetricFusion.metricFusion.reparamInjectiveAndNeZero

/-- Strict curvature at a nonnegative stored scale discharges packet rank two. -/
theorem rankTwo
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (ht : 0 ≤ t) :
    2 ≤ d :=
  (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
    (embed ∘ grade) m p
    hcertificate.exactMetricFusion.cofinitePrimeJetExactRecovery t ht).1
      hcertificate.strictGaussianCurvature

/-- Exact recovery and strict curvature derive the former stored nonnormality field. -/
theorem gaussianSimilarityNonnormal
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (ht : 0 ≤ t) :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        (embed ∘ grade) p t) ≠ 0 :=
  (xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_cofiniteHilbertReconstruction
    (embed ∘ grade) m p
    hcertificate.exactMetricFusion.cofinitePrimeJetExactRecovery t ht).2
      (hcertificate.rankTwo ht)

/-- Exact recovery supplies the Gaussian curvature/self-commutator energy identity. -/
theorem curvatureCommutatorIdentity
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          (embed ∘ grade) p s).det)) t =
      -2 * matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity
            (embed ∘ grade) p t)) :=
  xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_selfCommutatorEnergy_of_cofiniteHilbertReconstruction
    (embed ∘ grade) m p
    hcertificate.exactMetricFusion.cofinitePrimeJetExactRecovery t ht

/-- **Rooted-star/Möbius certificate discharge.**  Rooted-star exact metric fusion and strict
curvature produce the minimal Möbius dyadic exact-Hilbert certificate for any source prime. -/
theorem mobiusDyadicExactHilbertCurvatureCertificate
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (ht : 0 ≤ t) (sourcePrime : Nat.Primes) :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      (embed ∘ grade) sourcePrime p m t :=
  { dyadicInnovationGram :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
        (embed ∘ grade)).2 hcertificate.reparamInjectiveAndNeZero
    curvatureCommutatorIdentity := hcertificate.curvatureCommutatorIdentity ht
    strictGaussianCurvature := hcertificate.strictGaussianCurvature }

/-- Rooted-star curvature supplies global Gaussian log-determinant concavity. -/
theorem gaussianLogDetConcaveOn
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t) :
    ConcaveOn ℝ (Set.Ici 0) (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          (embed ∘ grade) p s).det) :=
  xiTransversePrimeValuationRankOneGaussianMetric_logDet_concaveOn_of_cofiniteHilbertReconstruction
    (embed ∘ grade) m p
    hcertificate.exactMetricFusion.cofinitePrimeJetExactRecovery

/-- Rooted-star curvature supplies intrinsic Gaussian dimension at every prime. -/
theorem intrinsicDimensionCertificate
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (embed ∘ grade) intrinsicPrime :=
  (hcertificate.mobiusDyadicExactHilbertCurvatureCertificate
    ht p).intrinsicDimensionCertificate ht intrinsicPrime

/-- Rooted-star curvature supplies reconstruction sign duality at arbitrary depth and scale. -/
theorem curvatureSignDualityCertificate
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (ht : 0 ≤ t) (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
      (embed ∘ grade) jetDepth valuationPrime valuationScale :=
  (hcertificate.mobiusDyadicExactHilbertCurvatureCertificate
    ht p).curvatureSignDualityCertificate
      ht jetDepth valuationPrime valuationScale hvaluationScale

/-- Rooted-star exact metric fusion alone discharges the full cross-prime valuation universality
chain; the stored curvature scale need not be nonnegative for this injectivity consequence. -/
theorem valuationUniversalityPhase
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (embed ∘ grade)
      valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    (embed ∘ grade)
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale
    hcertificate.reparamInjectiveAndNeZero.1

end XiRootedStarGaussianCurvatureExactMetricFusionCertificate

/-- **Raw-Xi/rank-two curvature phase connector.**  Under any injective zero-preserving
reparametrization, raw reconstruction together with packet rank at least two is exactly the
transverse cofinite-Hilbert Gaussian curvature phase. -/
theorem
    xiRootedStar_rawReconstruction_and_two_le_iff_gaussianCurvaturePhase_reparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (embed ∘ grade) m p t := by
  calc
    _ ↔ XiTransversePrimeJetApertureCofiniteHilbertReconstruction
          (embed ∘ grade) m ∧
        2 ≤ d :=
      and_congr
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureHilbertReconstructionReparam
          grade embed hinj hzero m)
        Iff.rfl
    _ ↔ _ :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        (embed ∘ grade) m p t ht).symm

/-- **Rooted-star raw/sign-duality connector.**  Under injective zero-preserving
reparametrization, literal raw-Xi reconstruction and packet rank two are exactly reconstruction
sign duality at any independently chosen target. -/
theorem
    xiRootedStar_rawReconstruction_and_two_le_iff_curvatureSignDuality_reparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (embed ∘ grade) jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (embed ∘ grade) jetDepth valuationPrime valuationScale :=
      xiRootedStar_rawReconstruction_and_two_le_iff_gaussianCurvaturePhase_reparam
        grade embed hinj hzero
        valuationPrime jetDepth valuationScale hvaluationScale
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        (embed ∘ grade) jetDepth valuationPrime valuationScale

/-- **Universal rooted-star raw/sign-duality law.**  Under injective zero-preserving
reparametrization, literal raw-Xi reconstruction and packet rank two are exactly reconstruction
sign duality at every depth, prime, and nonnegative scale. -/
theorem
    xiRootedStar_rawReconstruction_and_two_le_iff_every_curvatureSignDuality_reparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (embed ∘ grade) jetDepth valuationPrime valuationScale := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (embed ∘ grade) 0 p 0 :=
      xiRootedStar_rawReconstruction_and_two_le_iff_gaussianCurvaturePhase_reparam
        grade embed hinj hzero p 0 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        (embed ∘ grade) 0 p 0 le_rfl

/-- **Curvature-enhanced rooted-star fusion law.**  Raw Xi reconstruction and the sharp
rank-two threshold are equivalent to the complete incidence/valuation/exact-recovery certificate,
strict transverse Gaussian curvature, and nonnormality of its square-root similarity. -/
theorem xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed p m t := by
  constructor
  · rintro ⟨hraw, htwo⟩
    have hexact :=
      (xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff
        grade embed hinj hzero p m).1 hraw
    have hrec := hexact.cofinitePrimeJetExactRecovery
    exact {
      metricFusion := hexact.metricFusion
      strictGaussianCurvature :=
        (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
          (embed ∘ grade) m p hrec t ht).2 htwo }
  · intro h
    have hraw :=
      (xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff
        grade embed hinj hzero p m).2 h.exactMetricFusion
    exact ⟨hraw, h.rankTwo ht⟩

/-- **Exact rooted-star/sign-duality connector.**  Under an injective zero-preserving
reparametrization, one complete rooted-star curvature/fusion certificate is exactly
reconstruction sign duality at any independently chosen jet depth, valuation prime, and
nonnegative scale. -/
theorem
    xiRootedStar_gaussianCurvatureExactMetricFusion_iff_curvatureSignDuality
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed metricPrime m t ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (embed ∘ grade) jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
          2 ≤ d :=
      (xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
        grade embed hinj hzero metricPrime m t ht).symm
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
            (embed ∘ grade) jetDepth ∧
          2 ≤ d :=
      and_congr
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureHilbertReconstructionReparam
          grade embed hinj hzero jetDepth)
        Iff.rfl
    _ ↔ _ :=
      xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
        (embed ∘ grade) jetDepth valuationPrime
        valuationScale hvaluationScale

/-- **Universal rooted-star/sign-duality law.**  A rooted-star fusion certificate at one metric
target is exactly reconstruction sign duality at every jet depth, valuation prime, and
nonnegative scale. -/
theorem
    xiRootedStar_gaussianCurvatureExactMetricFusion_iff_every_curvatureSignDuality
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed metricPrime m t ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (embed ∘ grade) jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
          2 ≤ d :=
      (xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
        grade embed hinj hzero metricPrime m t ht).symm
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
            (embed ∘ grade) m ∧
          2 ≤ d :=
      and_congr
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureHilbertReconstructionReparam
          grade embed hinj hzero m)
        Iff.rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_two_le_iff_every_gaussianCurvatureSignDualityCertificate
        (embed ∘ grade) m

/-- **Exact rooted-star/Möbius dyadic curvature connector.**  Under injective zero-preserving
reparametrization, the complete rooted-star incidence/valuation curvature certificate is exactly
the minimal Möbius dyadic exact-Hilbert certificate; the auxiliary source prime is arbitrary. -/
theorem
    xiRootedStar_gaussianCurvatureExactMetricFusion_iff_mobiusDyadicExactHilbertCurvature
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        grade embed metricPrime m t ↔
      XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
        (embed ∘ grade) sourcePrime metricPrime m t := by
  calc
    _ ↔
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
          2 ≤ d :=
      (xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
        grade embed hinj hzero metricPrime m t ht).symm
    _ ↔
        (xiMobiusContinuousApertureDyadicInnovationGram 2
            (fun j => ((embed ∘ grade) j : ℝ))).PosDef ∧
          2 ≤ d :=
      and_congr
        ((xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff
          grade).trans
            ((injective_comp_and_ne_zero_iff
              grade embed hinj hzero).symm.trans
                (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
                  (embed ∘ grade)).symm))
        Iff.rfl
    _ ↔ _ :=
      xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        (embed ∘ grade) sourcePrime metricPrime m t ht

/-- **Universal rooted-star Gaussian curvature law.**  A raw packet is reconstructible and has
rank at least two exactly when every injective zero-preserving reparametrization lies in the
strict Gaussian curvature phase at every prime, jet depth, and nonnegative scale. -/
theorem
    xiRootedStar_rawReconstruction_and_two_le_iff_every_reparam_gaussianCurvaturePhase
    {d : ℕ} (grade : Fin d → ℕ) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      ∀ (embed : ℕ → ℕ), Function.Injective embed → embed 0 = 0 →
        ∀ (p : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
          XiTransversePrimeJetApertureGaussianCurvaturePhase
            (embed ∘ grade) m p t := by
  constructor
  · intro h embed hinj hzero p m t ht
    exact
      (xiRootedStar_rawReconstruction_and_two_le_iff_gaussianCurvaturePhase_reparam
        grade embed hinj hzero p m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hphase := hall id Function.injective_id rfl p 0 0 (by norm_num)
    exact
      (xiRootedStar_rawReconstruction_and_two_le_iff_gaussianCurvaturePhase_reparam
        grade id Function.injective_id rfl p 0 0 (by norm_num)).2 hphase

/-- The universal law can equivalently expose the complete curvature-enhanced fusion certificate,
not merely the named curvature phase. -/
theorem
    xiRootedStar_rawReconstruction_and_two_le_iff_every_curvatureExactMetricFusion
    {d : ℕ} (grade : Fin d → ℕ) :
    (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        2 ≤ d) ↔
      ∀ (embed : ℕ → ℕ), Function.Injective embed → embed 0 = 0 →
        ∀ (p : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
          XiRootedStarGaussianCurvatureExactMetricFusionCertificate
            grade embed p m t := by
  constructor
  · intro h embed hinj hzero p m t ht
    exact
      (xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
        grade embed hinj hzero p m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall id Function.injective_id rfl p 0 0 (by norm_num)
    exact
      (xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
        grade id Function.injective_id rfl p 0 0 (by norm_num)).2 hcertificate

end

end RHTower
