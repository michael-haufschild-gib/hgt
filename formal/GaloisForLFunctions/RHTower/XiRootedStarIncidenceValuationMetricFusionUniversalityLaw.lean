import GaloisForLFunctions.RHTower.XiCanonicalIncidenceGramHilbertPhase
import GaloisForLFunctions.RHTower.XiRootedStarGaussianCanonicalHilbertPhase

/-!
# Rooted-star fusion of Xi incidence and valuation Hilbert phases

The raw even-shift defect condition separately classifies the canonical rooted-star incidence
geometry and the prime-valuation Gaussian geometry.  Their common analytic carrier therefore
forces one larger phase: incidence Gram volume, coordinate recovery, Kirchhoff rigidity,
one-prime valuation and Szegő positivity, nonlinear Gaussian separation, and every cofinite
prime-jet aperture certificate all appear or fail together.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexOrder Differential

/-- Minimal joint incidence/valuation certificate of a finite rooted-star Xi packet.
Canonical valuation recovery derives every reparametrized valuation and cofinite interface;
rooted-star incidence positivity derives raw reconstruction and every grade-side incidence
interface. -/
structure XiRootedStarIncidenceValuationMetricFusionCertificate
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) : Prop where
  canonicalValuation :
    XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p
  rootedStarIncidenceGram :
    (pointedCollisionIncidenceGram
      (xiShiftRootedStarLabel grade) 0
      xiShiftRootedStarTail xiShiftRootedStarHead).PosDef

namespace XiRootedStarIncidenceValuationMetricFusionCertificate

/-- Canonical valuation recovery is exactly collision freedom and nonvanishing of the
reparametrized packet. -/
theorem reparamInjectiveAndNeZero
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    Function.Injective (embed ∘ grade) ∧
      ∀ i, (embed ∘ grade) i ≠ 0 :=
  (xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero
    (embed ∘ grade) p).1 hcertificate.canonicalValuation

/-- Rooted-star incidence positivity is exactly raw Xi defect reconstruction. -/
theorem rawReconstruction
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade :=
  (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
    grade).2 hcertificate.rootedStarIncidenceGram

/-- Raw reconstruction exposes its elementary grade-side collision classification. -/
theorem gradeInjectiveAndNeZero
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    Function.Injective grade ∧ ∀ i, grade i ≠ 0 :=
  (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff
    grade).1 hcertificate.rawReconstruction

/-- Canonical valuation recovery derives corrected rooted-star reconstruction. -/
theorem correctedRootedStar
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
      (xiShiftRootedStarLabel (embed ∘ grade))
      xiShiftRootedStarTail xiShiftRootedStarHead :=
  (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
    (embed ∘ grade)).2
      ((xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
        (embed ∘ grade) p).2 hcertificate.canonicalValuation)

/-- Finite valuation-Gram positivity is derived from canonical recovery. -/
theorem valuationGram
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    (xiTransversePrimeValuationGramMatrix (embed ∘ grade) p).PosDef :=
  (xiTransversePrimeValuationCanonicalReconstruction_iff_valuationGram_posDef
    (embed ∘ grade) p).1 hcertificate.canonicalValuation

/-- Completed valuation--Szegő positivity is derived from canonical recovery. -/
theorem completedSzegoGram
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    (xiTransversePrimeValuationSzegoGramMatrix (embed ∘ grade) p).PosDef :=
  (xiTransversePrimeValuationCanonicalReconstruction_iff_completedSzegoGram_posDef
    (embed ∘ grade) p).1 hcertificate.canonicalValuation

/-- Raw reconstruction derives first-valuation Gaussian separation and nonzero grades. -/
theorem firstValuationGaussian
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    (xiTransversePrimeFirstValuationGaussianGramMatrix grade p).PosDef ∧
      ∀ i, grade i ≠ 0 :=
  ⟨(xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective
      grade p).2 hcertificate.gradeInjectiveAndNeZero.1,
    hcertificate.gradeInjectiveAndNeZero.2⟩

/-- Canonical recovery derives positive realizations after every finite prime deletion. -/
theorem cofinitePrimeJetApertures
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    ∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : Fin d × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram
          (embed ∘ grade) m forbidden points).PosDef :=
  (xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureGram
    (embed ∘ grade) p m).1 hcertificate.canonicalValuation

/-- Raw defect reconstruction is equivalent to literal raw rooted-star pair recovery. -/
theorem rawRootedStarReconstruction
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
      (xiShiftRootedStarLabel grade)
      xiShiftRootedStarTail xiShiftRootedStarHead :=
  (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
    grade).2 hcertificate.rawReconstruction

/-- Strict rooted-star incidence volume is derived from raw recovery. -/
theorem rootedStarIncidenceVolume
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    0 < (pointedCollisionIncidenceGram
      (xiShiftRootedStarLabel grade) 0
      xiShiftRootedStarTail xiShiftRootedStarHead).det :=
  (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_det_pos
    (xiShiftRootedStarLabel grade)
    xiShiftRootedStarTail xiShiftRootedStarHead).1
      hcertificate.rawRootedStarReconstruction

/-- Rooted-star coordinate recovery is derived from raw recovery. -/
theorem rootedStarCoordinateRecovery
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    PointedCollisionIncidenceCoordinateReconstruction
      (xiShiftRootedStarLabel grade) 0
      xiShiftRootedStarTail xiShiftRootedStarHead :=
  (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
    (xiShiftRootedStarLabel grade)
    xiShiftRootedStarTail xiShiftRootedStarHead).1
      hcertificate.rawRootedStarReconstruction

/-- Rooted-star Kirchhoff rigidity is derived from raw recovery. -/
theorem rootedStarKirchhoffRigidity
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationMetricFusionCertificate
        grade embed p m) :
    ∀ weight : Fin d → ℝ,
      (∀ q : pointedCollisionIncidenceVertex
          (xiShiftRootedStarLabel grade) 0,
        (∑ e, if pointedCollisionIncidenceVertexOf
              (xiShiftRootedStarLabel grade) 0
              (xiShiftRootedStarHead e) = q then weight e else 0) =
          ∑ e, if pointedCollisionIncidenceVertexOf
              (xiShiftRootedStarLabel grade) 0
              (xiShiftRootedStarTail e) = q then weight e else 0) →
        ∀ e, weight e = 0 :=
  (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
    (xiShiftRootedStarLabel grade)
    xiShiftRootedStarTail xiShiftRootedStarHead).1
      hcertificate.rawRootedStarReconstruction

end XiRootedStarIncidenceValuationMetricFusionCertificate

/-- Exact upgrade of the rooted-star fusion certificate.  Besides every existing metric,
incidence, volume, and rigidity component, it records deletion-robust dual recovery of the full
reparametrized prime-jet dictionary. -/
structure XiRootedStarIncidenceValuationExactMetricFusionCertificate
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) : Prop where
  metricFusion :
    XiRootedStarIncidenceValuationMetricFusionCertificate grade embed p m

namespace XiRootedStarIncidenceValuationExactMetricFusionCertificate

/-- Canonical valuation recovery supplies deletion-robust exact recovery at every jet depth. -/
theorem cofinitePrimeJetExactRecoveryAt
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationExactMetricFusionCertificate
        grade embed p m)
    (jetDepth : ℕ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (embed ∘ grade) jetDepth :=
  (xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
    (embed ∘ grade) p jetDepth).1
      hcertificate.metricFusion.canonicalValuation

/-- Stored-depth exact recovery remains available as a derived dot API. -/
theorem cofinitePrimeJetExactRecovery
    {d : ℕ} {grade : Fin d → ℕ} {embed : ℕ → ℕ}
    {p : Nat.Primes} {m : ℕ}
    (hcertificate :
      XiRootedStarIncidenceValuationExactMetricFusionCertificate
        grade embed p m) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (embed ∘ grade) m :=
  hcertificate.cofinitePrimeJetExactRecoveryAt m

end XiRootedStarIncidenceValuationExactMetricFusionCertificate

/-- **Exact-interface discharge.**  Rooted-star metric fusion already contains canonical
valuation recovery, which supplies deletion-robust cofinite prime-jet recovery at every depth.
Consequently the nominal exact-metric wrapper adds no hypothesis. -/
theorem xiRootedStar_incidenceValuationMetricFusion_iff_exactMetricFusion
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) :
    XiRootedStarIncidenceValuationMetricFusionCertificate grade embed p m ↔
      XiRootedStarIncidenceValuationExactMetricFusionCertificate
        grade embed p m := by
  constructor
  · exact fun hcertificate => ⟨hcertificate⟩
  · exact fun hcertificate => hcertificate.metricFusion

/-- **Rooted-star incidence/valuation metric-fusion law.**  Raw Xi defect reconstruction is
equivalent to the simultaneous validity of every canonical incidence, valuation, Gaussian,
Szegő, and cofinite prime-jet Hilbert certificate after arbitrary injective zero-preserving
shift reparametrization. -/
theorem xiRootedStar_incidenceValuationMetricFusion_reparam_iff
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) (m : ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiRootedStarIncidenceValuationMetricFusionCertificate grade embed p m := by
  constructor
  · intro hraw
    exact {
      canonicalValuation :=
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
          grade embed hinj hzero p).1 hraw
      rootedStarIncidenceGram :=
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
          grade).1 hraw }
  · intro h
    exact h.rawReconstruction

/-- **Exact rooted-star fusion law.**  Raw Xi defect reconstruction is equivalent to the full
incidence/valuation/Gaussian/Szegő fusion certificate together with exact dual reconstruction of
the reparametrized prime-jet dictionary after every finite prime deletion. -/
theorem xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) (m : ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiRootedStarIncidenceValuationExactMetricFusionCertificate
        grade embed p m := by
  constructor
  · intro hraw
    exact {
      metricFusion :=
        (xiRootedStar_incidenceValuationMetricFusion_reparam_iff
          grade embed hinj hzero p m).1 hraw }
  · intro h
    exact
      (xiRootedStar_incidenceValuationMetricFusion_reparam_iff
        grade embed hinj hzero p m).2 h.metricFusion

end

end RHTower
