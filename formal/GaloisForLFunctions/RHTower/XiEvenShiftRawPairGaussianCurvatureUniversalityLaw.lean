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

/-- Complete arbitrary-edge Hilbert/incidence phase together with full-vertex doubled-aperture
Gaussian geometry. -/
structure XiEvenShiftRawPairGaussianCurvatureCertificate
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  vertexCurvature :
    XiEvenShiftRawDefectGaussianCurvatureCertificate
      grade sourcePrime metricPrime m t
  correctedPairCofiniteReconstruction :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
      (fun v => 2 * grade v) tail head
  rawPairCofiniteReconstruction :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head
  incidenceCoordinateReconstruction :
    PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head
  kirchhoffRigidity :
    ∀ weight : Fin e → ℝ,
      (∀ q : pointedCollisionIncidenceVertex grade 0,
        (∑ edge, if pointedCollisionIncidenceVertexOf grade 0
            (head edge) = q then weight edge else 0) =
          ∑ edge, if pointedCollisionIncidenceVertexOf grade 0
            (tail edge) = q then weight edge else 0) →
        ∀ edge, weight edge = 0
  correctedPairRationalDifferentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (xiTransverseShiftPairDifferenceUpperEndCarrier
        (fun v => 2 * grade v) tail head)
  correctedPairAllValuationDifferentialIndependent :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (xiTransverseShiftPairDifferenceUpperEndCarrier
        (fun v => 2 * grade v) tail head)
  rawPairRationalDifferentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head)
  rawPairAllValuationDifferentialIndependent :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head)

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
    have hedgePhase :=
      (xiPairDifferenceRawCorrectedCofiniteHilbertPhase_iff
        grade tail head).1 hcorrectedPair
    rcases hedgePhase with
      ⟨hrawPair, hcoordinate, hkirchhoff,
        hcorrectedRational, hcorrectedAllValuation,
        hrawRational, hrawAllValuation⟩
    exact {
      vertexCurvature :=
        (xiEvenShiftRawLogDerivDefect_gaussianCurvatureCertificate_iff
          grade sourcePrime metricPrime m t ht).1 ⟨hvertex, htwo⟩
      correctedPairCofiniteReconstruction := hcorrectedPair
      rawPairCofiniteReconstruction := hrawPair
      incidenceCoordinateReconstruction := hcoordinate
      kirchhoffRigidity := hkirchhoff
      correctedPairRationalDifferentialIndependent := hcorrectedRational
      correctedPairAllValuationDifferentialIndependent := hcorrectedAllValuation
      rawPairRationalDifferentialIndependent := hrawRational
      rawPairAllValuationDifferentialIndependent := hrawAllValuation }
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

end

end RHTower
