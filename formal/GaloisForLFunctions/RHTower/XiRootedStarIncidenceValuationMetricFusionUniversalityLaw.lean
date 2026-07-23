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

/-- Complete joint incidence/valuation certificate of a finite rooted-star Xi packet. -/
structure XiRootedStarIncidenceValuationMetricFusionCertificate
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) : Prop where
  correctedRootedStar :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
      (xiShiftRootedStarLabel (embed ∘ grade))
      xiShiftRootedStarTail xiShiftRootedStarHead
  canonicalValuation :
    XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p
  valuationGram :
    (xiTransversePrimeValuationGramMatrix (embed ∘ grade) p).PosDef
  completedSzegoGram :
    (xiTransversePrimeValuationSzegoGramMatrix (embed ∘ grade) p).PosDef
  firstValuationGaussian :
    (xiTransversePrimeFirstValuationGaussianGramMatrix grade p).PosDef ∧
      ∀ i, grade i ≠ 0
  cofinitePrimeJetApertures :
    ∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : Fin d × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram
          (embed ∘ grade) m forbidden points).PosDef
  rootedStarIncidenceGram :
    (pointedCollisionIncidenceGram
      (xiShiftRootedStarLabel grade) 0
      xiShiftRootedStarTail xiShiftRootedStarHead).PosDef
  rootedStarIncidenceVolume :
    0 < (pointedCollisionIncidenceGram
      (xiShiftRootedStarLabel grade) 0
      xiShiftRootedStarTail xiShiftRootedStarHead).det
  rootedStarCoordinateRecovery :
    PointedCollisionIncidenceCoordinateReconstruction
      (xiShiftRootedStarLabel grade) 0
      xiShiftRootedStarTail xiShiftRootedStarHead
  rootedStarKirchhoffRigidity :
    ∀ weight : Fin d → ℝ,
      (∀ q : pointedCollisionIncidenceVertex
          (xiShiftRootedStarLabel grade) 0,
        (∑ e, if pointedCollisionIncidenceVertexOf
              (xiShiftRootedStarLabel grade) 0
              (xiShiftRootedStarHead e) = q then weight e else 0) =
          ∑ e, if pointedCollisionIncidenceVertexOf
              (xiShiftRootedStarLabel grade) 0
              (xiShiftRootedStarTail e) = q then weight e else 0) →
        ∀ e, weight e = 0

/-- Exact upgrade of the rooted-star fusion certificate.  Besides every existing metric,
incidence, volume, and rigidity component, it records deletion-robust dual recovery of the full
reparametrized prime-jet dictionary. -/
structure XiRootedStarIncidenceValuationExactMetricFusionCertificate
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (p : Nat.Primes) (m : ℕ) : Prop where
  metricFusion :
    XiRootedStarIncidenceValuationMetricFusionCertificate grade embed p m
  cofinitePrimeJetExactRecovery :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (embed ∘ grade) m

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
    rcases (xiRootedStarGaussianCanonicalCofiniteHilbertPhase_reparam_iff
      grade embed hinj hzero p m).1 hraw with
      ⟨hcorrected, hcanonical, hvaluation, hszego, hgaussian, hcofinite⟩
    have hrawStar :
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          (xiShiftRootedStarLabel grade)
          xiShiftRootedStarTail xiShiftRootedStarHead :=
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        grade).2 hraw
    exact {
      correctedRootedStar := hcorrected
      canonicalValuation := hcanonical
      valuationGram := hvaluation
      completedSzegoGram := hszego
      firstValuationGaussian := hgaussian
      cofinitePrimeJetApertures := hcofinite
      rootedStarIncidenceGram :=
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
          grade).1 hraw
      rootedStarIncidenceVolume :=
        (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_det_pos
          (xiShiftRootedStarLabel grade)
          xiShiftRootedStarTail xiShiftRootedStarHead).1 hrawStar
      rootedStarCoordinateRecovery :=
        (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
          (xiShiftRootedStarLabel grade)
          xiShiftRootedStarTail xiShiftRootedStarHead).1 hrawStar
      rootedStarKirchhoffRigidity :=
        (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
          (xiShiftRootedStarLabel grade)
          xiShiftRootedStarTail xiShiftRootedStarHead).1 hrawStar }
  · intro h
    exact (xiRootedStarGaussianCanonicalCofiniteHilbertPhase_reparam_iff
      grade embed hinj hzero p m).2
      ⟨h.correctedRootedStar, h.canonicalValuation, h.valuationGram,
        h.completedSzegoGram, h.firstValuationGaussian,
        h.cofinitePrimeJetApertures⟩

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
          grade embed hinj hzero p m).1 hraw
      cofinitePrimeJetExactRecovery :=
        (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureHilbertReconstructionReparam
          grade embed hinj hzero m).1 hraw }
  · intro h
    exact
      (xiRootedStar_incidenceValuationMetricFusion_reparam_iff
        grade embed hinj hzero p m).2 h.metricFusion

end

end RHTower
