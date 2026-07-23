import GaloisForLFunctions.RHTower.XiRootDeletedDyadicCofiniteHilbertUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedGaussianCurvatureGraphicUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootedStarGaussianCurvatureFusionUniversalityLaw

/-!
# Root-deleted incidence volume and Gaussian curvature

Root-deleted dyadic recovery has two existing exact descriptions.  Combinatorially, the canonical
incidence Gram of the nonroot raw-Xi star is the identity and its determinant is one; failure is
exactly determinant zero.  Analytically, the same recovery phase supplies exact nonroot
prime-source reconstruction.

The HilbertMetric curvature law closes these descriptions.  Incidence volume one together with at
least two retained vertices is exactly strict Gaussian log-volume curvature and operator
nonnormality.  The complementary failure boundary is sharp: curvature fails precisely when the
incidence volume is zero or the retained packet has size at most one.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

/-- **Dyadic/root-deleted curvature connector.**  Cofinite recovery from one nonroot dyadic-depth
family and the rank-two threshold are exactly strict Gaussian curvature at any metric prime,
depth, and nonnegative scale. -/
theorem xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  calc
    _ ↔ XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
          root shift hroot sourcePrime sourcePrime)
        Iff.rfl
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        root shift sourcePrime metricPrime m t ht

/-- The canonical nonroot rooted-star incidence Gram is the identity with at least two leaves
exactly in the strict Gaussian curvature phase. -/
theorem xiMobiusRootDeletedIncidenceGram_eq_one_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin N) (Fin N) ℝ) ∧
      2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  calc
    _ ↔ XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (by
          simpa [xiTransverseRootDeletedShift] using
            (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_eq_one
              root shift hroot sourcePrime).symm)
        Iff.rfl
    _ ↔ _ :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime metricPrime m t ht

/-- **Incidence-volume/metric-curvature law.**  Canonical incidence volume one together with two
retained vertices is exactly strict nonroot Gaussian curvature. -/
theorem xiMobiusRootDeletedIncidenceGram_det_eq_one_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 ∧
      2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  calc
    _ ↔ XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (by
          simpa [xiTransverseRootDeletedShift] using
            (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_det_eq_one
              root shift hroot sourcePrime).symm)
        Iff.rfl
    _ ↔ _ :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime metricPrime m t ht

/-- **Root-deleted dyadic/sign-duality connector.**  One nonroot dyadic reconstruction and the
sharp retained-rank threshold are exactly reconstruction sign duality at any independently
chosen depth, prime, and nonnegative scale. -/
theorem xiMobiusRootDeletedDyadic_and_two_le_iff_curvatureSignDuality
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (xiTransverseRootDeletedShift root shift)
        jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime valuationPrime
        jetDepth valuationScale hvaluationScale
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        (xiTransverseRootDeletedShift root shift)
        jetDepth valuationPrime valuationScale

/-- **Universal root-deleted dyadic/sign-duality law.**  One nonroot dyadic reconstruction and
retained rank two are exactly reconstruction sign duality at every depth, prime, and
nonnegative scale. -/
theorem xiMobiusRootDeletedDyadic_and_two_le_iff_every_curvatureSignDuality
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (xiTransverseRootDeletedShift root shift)
            jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime sourcePrime 0 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 le_rfl

/-- **Incidence-volume/sign-duality law.**  Canonical nonroot incidence volume one and retained
rank two are exactly reconstruction sign duality at any independently chosen target. -/
theorem
    xiMobiusRootDeletedIncidenceGram_det_eq_one_and_two_le_iff_curvatureSignDuality
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    ((pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 ∧
      2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (xiTransverseRootDeletedShift root shift)
        jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale :=
      xiMobiusRootDeletedIncidenceGram_det_eq_one_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime valuationPrime
        jetDepth valuationScale hvaluationScale
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
        (xiTransverseRootDeletedShift root shift)
        jetDepth valuationPrime valuationScale

/-- **Universal incidence-volume/sign-duality law.**  Canonical nonroot incidence volume one
and retained rank two are exactly reconstruction sign duality at every depth, prime, and
nonnegative scale. -/
theorem
    xiMobiusRootDeletedIncidenceGram_det_eq_one_and_two_le_iff_every_curvatureSignDuality
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes) :
    ((pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 ∧
      2 ≤ N) ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (xiTransverseRootDeletedShift root shift)
            jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 :=
      xiMobiusRootDeletedIncidenceGram_det_eq_one_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime sourcePrime 0 0 le_rfl
    _ ↔ _ :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
        (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 le_rfl

/-- **Sharp curvature-failure boundary.**  Strict nonroot Gaussian curvature fails exactly for
zero canonical incidence volume or a retained packet of size at most one. -/
theorem
    not_xiMobiusRootDeletedGaussianCurvaturePhase_iff_incidenceGram_det_eq_zero_or_le_one
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ¬ XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiTransverseRootDeletedShift root shift) m metricPrime t ↔
      (pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 0 ∨
        N ≤ 1 := by
  have hphase :=
    xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
      root shift hroot sourcePrime metricPrime m t ht
  have hfailure :=
    not_xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_det_eq_zero
      root shift hroot sourcePrime
  constructor
  · intro hn
    by_cases hdyadic :
        XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime
    · right
      by_contra hN
      have htwo : 2 ≤ N := by omega
      exact hn (hphase.1 ⟨hdyadic, htwo⟩)
    · left
      simpa [xiTransverseRootDeletedShift] using hfailure.1 hdyadic
  · rintro (hzero | hsmall)
    · intro hcurvature
      have hdyadic := (hphase.2 hcurvature).1
      have hnotDyadic :
          ¬ XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
            root shift sourcePrime :=
        hfailure.2 (by
          simpa [xiTransverseRootDeletedShift] using hzero)
      exact hnotDyadic hdyadic
    · intro hcurvature
      have htwo := (hphase.2 hcurvature).2
      omega

/-- Root-deleted dyadic recovery and retained rank two are equivalent to the complete
curvature-enhanced rooted-star incidence/valuation fusion certificate after any injective
zero-preserving reparametrization. -/
theorem
    xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvatureExactMetricFusion_reparam
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (embed : ℕ → ℕ) (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        (xiTransverseRootDeletedShift root shift) embed metricPrime m t := by
  calc
    _ ↔ XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
          (xiTransverseRootDeletedShift root shift) ∧
        2 ≤ N :=
      and_congr
        (by
          simpa [xiTransverseRootDeletedShift] using
            (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rawRootedStarCofiniteHilbertReconstruction
              root shift hroot sourcePrime))
        Iff.rfl
    _ ↔ _ :=
      xiRootedStar_gaussianCurvatureExactMetricFusion_reparam_iff
        (xiTransverseRootDeletedShift root shift)
        embed hinj hzero metricPrime m t ht

/-- **Universal incidence/valuation/curvature fusion law.**  One root-deleted dyadic recovery
phase and retained rank two hold exactly when every injective zero-preserving reparametrization,
target prime, depth, and nonnegative scale carries the complete curvature-enhanced fusion
certificate. -/
theorem
    xiMobiusRootDeletedDyadic_and_two_le_iff_every_gaussianCurvatureExactMetricFusion
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      ∀ (embed : ℕ → ℕ), Function.Injective embed → embed 0 = 0 →
        ∀ (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
          XiRootedStarGaussianCurvatureExactMetricFusionCertificate
            (xiTransverseRootDeletedShift root shift) embed metricPrime m t := by
  constructor
  · intro h embed hinj hzero metricPrime m t ht
    exact
      (xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvatureExactMetricFusion_reparam
        root shift hroot sourcePrime metricPrime embed hinj hzero m t ht).1 h
  · intro hall
    let metricPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate :=
      hall id Function.injective_id rfl metricPrime 0 0 (by norm_num)
    exact
      (xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvatureExactMetricFusion_reparam
        root shift hroot sourcePrime metricPrime id Function.injective_id rfl
          0 0 (by norm_num)).2 hcertificate

/-- Canonical incidence volume one and rank two have the same fully universal
curvature-enhanced fusion characterization. -/
theorem
    xiMobiusRootDeletedIncidenceGram_det_eq_one_and_two_le_iff_every_gaussianCurvatureExactMetricFusion
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes) :
    ((pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 ∧
      2 ≤ N) ↔
      ∀ (embed : ℕ → ℕ), Function.Injective embed → embed 0 = 0 →
        ∀ (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
          XiRootedStarGaussianCurvatureExactMetricFusionCertificate
            (xiTransverseRootDeletedShift root shift) embed metricPrime m t := by
  calc
    _ ↔ XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (by
          simpa [xiTransverseRootDeletedShift] using
            (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_det_eq_one
              root shift hroot sourcePrime).symm)
        Iff.rfl
    _ ↔ _ :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_every_gaussianCurvatureExactMetricFusion
        root shift hroot sourcePrime

end

end RHTower
