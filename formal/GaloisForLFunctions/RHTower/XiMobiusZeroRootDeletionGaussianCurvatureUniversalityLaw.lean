import GaloisForLFunctions.RHTower.XiMobiusZeroRootDeletionUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedDyadicCofiniteHilbertUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedGaussianCurvatureGraphicUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedIncidenceGaussianCurvatureUniversalityLaw

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

/-- Minimal complete zero-root boundary.  The root-deleted curvature/graphic certificate now
contains the root equation itself, so every full loop-sensitive failure and restored dyadic
recovery follows from this single field. -/
structure XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  rootDeletedCurvatureGraphic :
    XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
      root shift tail head sourcePrime metricPrime m t

namespace XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate

/-- The nested root-deleted certificate discharges the zero-root equation. -/
theorem rootIsZero
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    shift root = 0 :=
  hcertificate.rootDeletedCurvatureGraphic.rootIsZero

/-- The graphic component already contains full-shift injectivity. -/
theorem fullInjective
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    Function.Injective shift :=
  hcertificate.rootDeletedCurvatureGraphic.graphicNetworkUniversality.1

/-- Existing zero-root deletion universality simultaneously derives all full failure interfaces
and restores root-deleted dyadic recovery. -/
theorem zeroRootBoundary
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ∧
      ¬ XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
          2 (fun j => (shift j : ℝ)) sourcePrime ∧
      ¬ XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime ∧
      ¬ XiTransversePrimeValuationCanonicalReconstruction shift sourcePrime ∧
      XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift sourcePrime := by
  have hboundary :=
    xiMobius_zeroRootDeletion_dyadicSingular_exactHilbert_gaussianGraphic
      root shift hcertificate.rootIsZero hcertificate.fullInjective
      tail head m sourcePrime (by norm_num : (0 : ℝ) < 1)
  exact
    ⟨hboundary.1, hboundary.2.1, hboundary.2.2.1,
      hboundary.2.2.2.1, hboundary.2.2.2.2.1⟩

/-- Legacy singularity projection, now derived from the two-field certificate. -/
theorem fullDyadicInnovationSingular
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef :=
  hcertificate.zeroRootBoundary.1

/-- Legacy full dyadic failure projection, now derived from the zero-root boundary. -/
theorem fullContinuousDyadicRecoveryFails
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    ¬ XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
      2 (fun j => (shift j : ℝ)) sourcePrime :=
  hcertificate.zeroRootBoundary.2.1

/-- Legacy full integral-canonical failure projection, now derived from the zero-root boundary. -/
theorem fullIntegralCanonicalRecoveryFails
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    ¬ XiMobiusPrimeIntegralApertureCanonicalReconstruction shift sourcePrime :=
  hcertificate.zeroRootBoundary.2.2.1

/-- Legacy full transverse-canonical failure projection, now derived from the zero-root boundary. -/
theorem fullTransverseCanonicalRecoveryFails
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    ¬ XiTransversePrimeValuationCanonicalReconstruction shift sourcePrime :=
  hcertificate.zeroRootBoundary.2.2.2.1

/-- Legacy root-deleted dyadic recovery projection, now derived from the zero-root boundary. -/
theorem rootDeletedDyadicRecovery
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
      root shift sourcePrime :=
  hcertificate.zeroRootBoundary.2.2.2.2

/-- The minimal zero-root boundary supplies intrinsic nonroot Gaussian dimension at every prime. -/
theorem nonrootIntrinsicDimensionCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (xiTransverseRootDeletedShift root shift) intrinsicPrime :=
  hcertificate.rootDeletedCurvatureGraphic.nonrootIntrinsicDimensionCertificate
    ht intrinsicPrime

/-- The minimal zero-root boundary supplies nonroot reconstruction/curvature sign duality at
arbitrary depth, prime, and nonnegative scale. -/
theorem nonrootCurvatureSignDualityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
      (xiTransverseRootDeletedShift root shift)
      jetDepth valuationPrime valuationScale :=
  hcertificate.rootDeletedCurvatureGraphic.nonrootCurvatureSignDualityCertificate
    ht jetDepth valuationPrime valuationScale hvaluationScale

/-- The minimal zero-root boundary supplies the full cross-prime nonroot valuation universality
chain. -/
theorem nonrootValuationUniversalityPhase
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (xiTransverseRootDeletedShift root shift)
      valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  hcertificate.rootDeletedCurvatureGraphic.nonrootValuationUniversalityPhase
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale

end XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate

/-- The complete zero-root boundary is exactly the now-minimal root-deleted curvature/graphic
certificate; its extra failure and recovery interfaces are derived views of the same data. -/
theorem
    xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff_rootDeletedGraphic
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) :
    XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t ↔
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t := by
  constructor
  · exact fun h => h.rootDeletedCurvatureGraphic
  · exact fun h => { rootDeletedCurvatureGraphic := h }

/-- **Zero-root failure/sign-duality connector.**  The complete Möbius zero-root boundary is
exactly the root equation together with reconstruction sign duality on the nonroot packet at
every jet depth, valuation prime, and nonnegative scale. -/
theorem
    xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff_zeroRoot_and_every_nonrootCurvatureSignDuality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t ↔
      shift root = 0 ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (xiTransverseRootDeletedShift root shift)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
          root shift tail head sourcePrime metricPrime m t :=
      xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff_rootDeletedGraphic
        root shift tail head sourcePrime metricPrime m t
    _ ↔ _ :=
      xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff_zeroRoot_and_every_curvatureSignDuality
        root shift tail head sourcePrime metricPrime m t ht

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
    exact {
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

/-- **Zero-root deletion/rooted-star metric-fusion connector.**  A complete zero-root boundary is
exactly the curvature-enhanced rooted-star incidence/valuation certificate after any injective
zero-preserving reparametrization. -/
theorem
    xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff_rootedStarExactMetricFusion
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes)
    (embed : ℕ → ℕ) (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t ↔
      XiRootedStarGaussianCurvatureExactMetricFusionCertificate
        (xiTransverseRootDeletedShift root shift) embed metricPrime m t := by
  calc
    _ ↔
        XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
            root shift sourcePrime ∧
          2 ≤ N :=
      (xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
        root shift hroot tail head sourcePrime metricPrime m t ht).symm
    _ ↔ _ :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvatureExactMetricFusion_reparam
        root shift hroot sourcePrime metricPrime embed hinj hzero m t ht

/-- **Universal zero-root deletion/rooted-star law.**  One zero-root boundary certificate at one
metric target is equivalent to exact curvature-enhanced rooted-star fusion for every injective
zero-preserving reparametrization, target prime, depth, and nonnegative scale. -/
theorem
    xiMobius_zeroRootDeletion_gaussianCurvatureUniversalityCertificate_iff_every_rootedStarExactMetricFusion
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
        root shift tail head sourcePrime metricPrime m t ↔
      ∀ (embed : ℕ → ℕ), Function.Injective embed → embed 0 = 0 →
        ∀ (targetPrime : Nat.Primes) (jetDepth : ℕ) (scale : ℝ), 0 ≤ scale →
          XiRootedStarGaussianCurvatureExactMetricFusionCertificate
            (xiTransverseRootDeletedShift root shift)
            embed targetPrime jetDepth scale := by
  calc
    _ ↔
        XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
            root shift sourcePrime ∧
          2 ≤ N :=
      (xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
        root shift hroot tail head sourcePrime metricPrime m t ht).symm
    _ ↔ _ :=
      xiMobiusRootDeletedDyadic_and_two_le_iff_every_gaussianCurvatureExactMetricFusion
        root shift hroot sourcePrime

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
