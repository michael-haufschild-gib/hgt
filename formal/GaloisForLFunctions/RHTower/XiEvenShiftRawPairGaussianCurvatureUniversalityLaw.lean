import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction

/-!
# Raw Xi edge networks and full-vertex Gaussian curvature

The raw/corrected pair-difference Hilbert law gives a complete graph-theoretic phase for an
arbitrary finite edge family: literal raw and corrected recovery, collision-incidence
independence, real incidence-coordinate reconstruction, Kirchhoff rigidity, and differential
independence over both valuation bases are equivalent.

Separately, literal recovery of the full raw vertex packet gives exact doubled-aperture Gaussian
geometry.  Combining the two existing laws yields a general, non-root-deleted graph/curvature
certificate.  Its sharp conditions are the pointed collision-free vertex phase, independence of
the arbitrary edge family in the pointed collision incidence matroid, and vertex-packet rank at
least two.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

local instance xiRawPairCurvatureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiRawPairCurvatureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiRawPairCurvatureUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiRawPairCurvatureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiRawPairCurvatureCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiRawPairCurvatureCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiRawPairCurvatureAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiRawPairCurvatureAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Minimal arbitrary-edge/full-vertex certificate.  The vertex certificate supplies doubled
Gaussian geometry, while one corrected pair reconstruction supplies every raw reconstruction,
incidence, Kirchhoff, and differential-independence law derived below. -/
structure XiEvenShiftRawPairGaussianCurvatureCertificate
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  vertexCurvature :
    XiEvenShiftRawDefectGaussianCurvatureCertificate
      grade sourcePrime metricPrime m t
  correctedPairCofiniteReconstruction :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
      (fun v => 2 * grade v) tail head

namespace XiEvenShiftRawPairGaussianCurvatureCertificate

/-- One corrected reconstruction contains the complete seven-component raw/corrected edge
Hilbert-differential phase. -/
theorem pairCofiniteHilbertPhase
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ∧
      PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head ∧
      (∀ weight : Fin e → ℝ,
        (∀ q : pointedCollisionIncidenceVertex grade 0,
          (∑ edge, if pointedCollisionIncidenceVertexOf grade 0
              (head edge) = q then weight edge else 0) =
            ∑ edge, if pointedCollisionIncidenceVertexOf grade 0
              (tail edge) = q then weight edge else 0) →
          ∀ edge, weight edge = 0) ∧
      DifferentialIndependent upperEndRationalCoordinateField
        (xiTransverseShiftPairDifferenceUpperEndCarrier
          (fun v => 2 * grade v) tail head) ∧
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (xiTransverseShiftPairDifferenceUpperEndCarrier
          (fun v => 2 * grade v) tail head) ∧
      DifferentialIndependent upperEndRationalCoordinateField
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) ∧
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) :=
  (xiPairDifferenceRawCorrectedCofiniteHilbertPhase_iff
    grade tail head).1 hcertificate.correctedPairCofiniteReconstruction

/-- Literal raw edge recovery is derived from corrected doubled-grade recovery. -/
theorem rawPairCofiniteReconstruction
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head :=
  hcertificate.pairCofiniteHilbertPhase.1

/-- Real collision-incidence coordinate reconstruction is derived from the pair phase. -/
theorem incidenceCoordinateReconstruction
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head :=
  hcertificate.pairCofiniteHilbertPhase.2.1

/-- Kirchhoff rigidity is derived from the pair phase. -/
theorem kirchhoffRigidity
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    ∀ weight : Fin e → ℝ,
      (∀ q : pointedCollisionIncidenceVertex grade 0,
        (∑ edge, if pointedCollisionIncidenceVertexOf grade 0
            (head edge) = q then weight edge else 0) =
          ∑ edge, if pointedCollisionIncidenceVertexOf grade 0
            (tail edge) = q then weight edge else 0) →
        ∀ edge, weight edge = 0 :=
  hcertificate.pairCofiniteHilbertPhase.2.2.1

/-- Corrected edge differential independence over the rational coordinate field is derived. -/
theorem correctedPairRationalDifferentialIndependent
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    DifferentialIndependent upperEndRationalCoordinateField
      (xiTransverseShiftPairDifferenceUpperEndCarrier
        (fun v => 2 * grade v) tail head) :=
  hcertificate.pairCofiniteHilbertPhase.2.2.2.1

/-- Corrected edge differential independence over all valuation layers is derived. -/
theorem correctedPairAllValuationDifferentialIndependent
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (xiTransverseShiftPairDifferenceUpperEndCarrier
        (fun v => 2 * grade v) tail head) :=
  hcertificate.pairCofiniteHilbertPhase.2.2.2.2.1

/-- Literal raw edge differential independence over the rational coordinate field is derived. -/
theorem rawPairRationalDifferentialIndependent
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    DifferentialIndependent upperEndRationalCoordinateField
      (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) :=
  hcertificate.pairCofiniteHilbertPhase.2.2.2.2.2.1

/-- Literal raw edge differential independence over all valuation layers is derived. -/
theorem rawPairAllValuationDifferentialIndependent
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) :=
  hcertificate.pairCofiniteHilbertPhase.2.2.2.2.2.2

/-- Vertex geometry supplies intrinsic dimension one for the doubled aperture. -/
theorem doubledApertureIntrinsicDimensionCertificate
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (fun v => 2 * grade v) intrinsicPrime :=
  hcertificate.vertexCurvature.doubledApertureIntrinsicDimensionCertificate
    ht intrinsicPrime

/-- Vertex geometry supplies collision sign duality at arbitrary valuation and intrinsic
primes. -/
theorem doubledApertureCollisionSignDualityCertificate
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t)
    (valuationPrime intrinsicPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
      (fun v => 2 * grade v) valuationPrime valuationScale :=
  hcertificate.vertexCurvature.doubledApertureCollisionSignDualityCertificate
    ht valuationPrime intrinsicPrime valuationScale hvaluationScale

/-- **Raw-edge/full-vertex valuation connector.**  The arbitrary-edge certificate inherits the
complete all-prime curvature, nonnormality, intrinsic-dimension, and differential-rank
equivalence chain of its doubled vertex aperture. -/
theorem doubledApertureValuationUniversalityPhase
    {N e : ℕ} {grade : Fin N → ℕ} {tail head : Fin e → Fin N}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (fun v => 2 * grade v)
      valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  hcertificate.vertexCurvature.doubledApertureValuationUniversalityPhase
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale

end XiEvenShiftRawPairGaussianCurvatureCertificate

/-- **General raw-edge/full-vertex curvature fusion.**  Literal recovery of the full raw vertex
packet and corrected recovery of an arbitrary doubled-grade edge family, together with vertex
rank at least two, are exactly the complete incidence, differential, and Gaussian certificate. -/
theorem xiEvenShiftRawPair_gaussianCurvatureCertificate_iff
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          (fun v => 2 * grade v) tail head) ∧
      2 ≤ N) ↔
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨⟨hvertex, hcorrectedPair⟩, htwo⟩
    exact {
      vertexCurvature :=
        (xiEvenShiftRawLogDerivDefect_gaussianCurvatureCertificate_iff
          grade sourcePrime metricPrime m t ht).1 ⟨hvertex, htwo⟩
      correctedPairCofiniteReconstruction := hcorrectedPair }
  · intro hcertificate
    have hvertexRank :=
      (xiEvenShiftRawLogDerivDefect_gaussianCurvatureCertificate_iff
        grade sourcePrime metricPrime m t ht).2 hcertificate.vertexCurvature
    exact ⟨⟨hvertexRank.1, hcertificate.correctedPairCofiniteReconstruction⟩,
      hvertexRank.2⟩

/-- **Sharp arbitrary-edge curvature classification.**  The full certificate is exactly the
pointed collision-free vertex phase, independence of the selected raw edge family in its pointed
collision incidence matroid, and vertex rank at least two. -/
theorem
    xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
        XiEvenShiftRawPairIncidenceIndependent grade tail head) ∧
      2 ≤ N) ↔
      XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t := by
  calc
    _ ↔
        (XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ∧
          XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
            (fun v => 2 * grade v) tail head) ∧
        2 ≤ N :=
      and_congr
        (and_congr
          (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).symm
          ((xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
            grade tail head).symm.trans
              (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_double_iff_raw
                grade tail head).symm))
        Iff.rfl
    _ ↔ _ :=
      xiEvenShiftRawPair_gaussianCurvatureCertificate_iff
        grade tail head sourcePrime metricPrime m t ht

/-- **Universal arbitrary-edge curvature law.**  The exact vertex/collision/incidence/rank
condition is independent of source prime, metric prime, jet depth, and nonnegative scale. -/
theorem
    xiEvenShiftRawPair_vertex_and_incidence_and_two_le_iff_every_gaussianCurvatureCertificate
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N) :
    (((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
        XiEvenShiftRawPairIncidenceIndependent grade tail head) ∧
      2 ≤ N) ↔
      ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiEvenShiftRawPairGaussianCurvatureCertificate
          grade tail head sourcePrime metricPrime m t := by
  constructor
  · intro h sourcePrime metricPrime m t ht
    exact
      (xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
        grade tail head sourcePrime metricPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall p p 0 0 le_rfl
    exact
      (xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
        grade tail head p p 0 0 le_rfl).2 hcertificate

/-- **Exact raw-pair/sign-duality factorization.**  The full vertex/edge curvature certificate
is exactly independence of the selected edge family in the pointed collision-incidence matroid
together with doubled-aperture sign duality at any independently chosen target. -/
theorem
    xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_incidence_and_curvatureSignDuality
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          (fun i => 2 * grade i) jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
            XiEvenShiftRawPairIncidenceIndependent grade tail head) ∧
          2 ≤ N) :=
      (xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
        grade tail head sourcePrime metricPrime m t ht).symm
    _ ↔
        XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
          ((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
            2 ≤ N) := by
      constructor
      · rintro ⟨⟨hgrade, hincidence⟩, htwo⟩
        exact ⟨hincidence, hgrade, htwo⟩
      · rintro ⟨hincidence, hgrade, htwo⟩
        exact ⟨⟨hgrade, hincidence⟩, htwo⟩
    _ ↔
        XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
          XiEvenShiftRawDefectGaussianCurvatureCertificate
            grade sourcePrime metricPrime m t :=
      and_congr Iff.rfl
        (xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_injective_ne_zero_two_le
          grade sourcePrime metricPrime m t ht)
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_curvatureSignDuality
          grade sourcePrime metricPrime m t ht
          jetDepth valuationPrime valuationScale hvaluationScale)

/-- **Universal raw-pair/sign-duality factorization.**  One full vertex/edge curvature
certificate at a nonnegative stored scale is exactly selected-edge incidence independence plus
doubled-aperture sign duality at every depth, prime, and nonnegative scale. -/
theorem
    xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_incidence_and_every_curvatureSignDuality
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head sourcePrime metricPrime m t ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (fun i => 2 * grade i)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
            XiEvenShiftRawPairIncidenceIndependent grade tail head) ∧
          2 ≤ N) :=
      (xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
        grade tail head sourcePrime metricPrime m t ht).symm
    _ ↔
        XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
          ((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
            2 ≤ N) := by
      constructor
      · rintro ⟨⟨hgrade, hincidence⟩, htwo⟩
        exact ⟨hincidence, hgrade, htwo⟩
      · rintro ⟨hincidence, hgrade, htwo⟩
        exact ⟨⟨hgrade, hincidence⟩, htwo⟩
    _ ↔
        XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
          XiEvenShiftRawDefectGaussianCurvatureCertificate
            grade sourcePrime metricPrime m t :=
      and_congr Iff.rfl
        (xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_injective_ne_zero_two_le
          grade sourcePrime metricPrime m t ht)
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiEvenShiftRawDefect_gaussianCurvatureCertificate_iff_every_curvatureSignDuality
          grade sourcePrime metricPrime m t ht)

end

end RHTower
