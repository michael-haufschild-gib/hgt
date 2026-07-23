import GaloisForLFunctions.RHTower.XiRootedStarIncidenceValuationMetricFusionUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase

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

/-- Full rooted-star incidence/valuation fusion enhanced by strict Gaussian curvature and
operator nonnormality. -/
structure XiRootedStarGaussianCurvatureExactMetricFusionCertificate
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  exactMetricFusion :
    XiRootedStarIncidenceValuationExactMetricFusionCertificate
      grade embed p m
  strictGaussianCurvature :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          (embed ∘ grade) p s).det)) t < 0
  gaussianSimilarityNonnormal :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        (embed ∘ grade) p t) ≠ 0

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
      exactMetricFusion := hexact
      strictGaussianCurvature :=
        (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
          (embed ∘ grade) m p hrec t ht).2 htwo
      gaussianSimilarityNonnormal :=
        (xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_cofiniteHilbertReconstruction
          (embed ∘ grade) m p hrec t ht).2 htwo }
  · intro h
    have hraw :=
      (xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff
        grade embed hinj hzero p m).2 h.exactMetricFusion
    have htwo :=
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
        (embed ∘ grade) m p
        h.exactMetricFusion.cofinitePrimeJetExactRecovery t ht).1
          h.strictGaussianCurvature
    exact ⟨hraw, htwo⟩

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
