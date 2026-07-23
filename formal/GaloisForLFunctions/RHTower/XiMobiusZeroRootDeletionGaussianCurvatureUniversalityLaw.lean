import GaloisForLFunctions.RHTower.XiMobiusZeroRootDeletionUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedDyadicCofiniteHilbertUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedGaussianCurvatureGraphicUniversalityLaw

/-!
# Xi--Möbius zero-root deletion with Gaussian curvature

The existing zero-root deletion theorem assumes injectivity of the full integral aperture packet
and then proves a sharp split: every full dyadic and canonical recovery interface fails because of
the zero loop, whereas deleting that loop restores dyadic recovery, prime-jet recovery, Gaussian
positivity, and differential graphic universality.

Root-deleted canonical or dyadic recovery already classifies full injectivity, so that hypothesis
can be discharged.  Adding the nonroot rank-two condition also supplies strict HilbertMetric
Gaussian curvature and operator nonnormality at every target prime, depth, and nonnegative scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

/-- Complete zero-root boundary: all full loop-sensitive recovery interfaces fail, while deletion
restores dyadic recovery and the curvature-enhanced graphic certificate. -/
structure XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  fullDyadicInnovationSingular :
    ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef
  fullContinuousDyadicRecoveryFails :
    ¬ XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
      2 (fun j => (shift j : ℝ)) sourcePrime
  fullIntegralCanonicalRecoveryFails :
    ¬ XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime
  fullTransverseCanonicalRecoveryFails :
    ¬ XiTransversePrimeValuationCanonicalReconstruction shift sourcePrime
  rootDeletedDyadicRecovery :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
      root shift sourcePrime
  rootDeletedCurvatureGraphic :
    XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
      root shift tail head sourcePrime metricPrime m t

/-- **Hypothesis-discharged zero-root curvature law.**  Root-deleted canonical recovery and two
retained vertices are exactly the complete zero-root failure/success boundary.  No separate full
injectivity premise remains. -/
theorem xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨hcanonical, htwo⟩
    have hinjective :=
      (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
        root shift hroot sourcePrime).1 hcanonical
    have hboundary :=
      xiMobius_zeroRootDeletion_dyadicSingular_exactHilbert_gaussianGraphic
        root shift hroot hinjective tail head m sourcePrime
          (by norm_num : (0 : ℝ) < 1)
    exact {
      fullDyadicInnovationSingular := hboundary.1
      fullContinuousDyadicRecoveryFails := hboundary.2.1
      fullIntegralCanonicalRecoveryFails := hboundary.2.2.1
      fullTransverseCanonicalRecoveryFails := hboundary.2.2.2.1
      rootDeletedDyadicRecovery := hboundary.2.2.2.2.1
      rootDeletedCurvatureGraphic :=
        (xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff
          root shift hroot tail head sourcePrime metricPrime m t ht).1
            ⟨hcanonical, htwo⟩ }
  · intro h
    exact
      (xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff
        root shift hroot tail head sourcePrime metricPrime m t ht).2
          h.rootDeletedCurvatureGraphic

/-- A single positive full Gaussian collision matrix and the nonroot rank threshold already
classify the entire zero-root dyadic-failure/curvature-success boundary. -/
theorem
    xiMobius_zeroRootDeletion_fullGaussian_posDef_and_two_le_iff_curvatureUniversalityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((xiTransversePrimeFirstValuationGaussianGramMatrix shift metricPrime).PosDef ∧
        2 ≤ N) ↔
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t := by
  calc
    _ ↔ XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGram_posDef
          root shift hroot sourcePrime metricPrime).symm
        Iff.rfl
    _ ↔ _ :=
      xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff
        root shift hroot tail head sourcePrime metricPrime m t ht

/-- Root-deleted dyadic-depth recovery itself can replace canonical recovery in the exact
zero-root curvature classification. -/
theorem
    xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t := by
  calc
    _ ↔ XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
          root shift hroot sourcePrime sourcePrime)
        Iff.rfl
    _ ↔ _ :=
      xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff
        root shift hroot tail head sourcePrime metricPrime m t ht

/-- **Universal zero-root deletion curvature law.**  One root-deleted dyadic recovery phase and
the sharp nonroot rank condition are equivalent to the complete zero-root boundary at every target
prime, jet depth, and nonnegative Gaussian scale. -/
theorem
    xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_every_curvatureUniversalityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime : Nat.Primes) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      ∀ (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
          root shift tail head sourcePrime metricPrime m t := by
  constructor
  · intro h metricPrime m t ht
    exact
      (xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
        root shift hroot tail head sourcePrime metricPrime m t ht).1 h
  · intro hall
    let metricPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall metricPrime 0 0 (by norm_num)
    exact
      (xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
        root shift hroot tail head sourcePrime metricPrime 0 0 (by norm_num)).2
          hcertificate

end

end RHTower
