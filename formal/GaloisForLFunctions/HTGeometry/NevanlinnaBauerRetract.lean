import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFaceLattice
import GaloisForLFunctions.HTGeometry.ProbabilityMeasureSimplex

/-!
# The Nevanlinna Bauer retract

The complete Hamburger-moment fiber contains the closed boundary-carrier simplex.  Its parameter
law is recovered exactly by the projective support label, and the canonical constraint projector
restricts to a continuous retraction of the full moment fiber onto that simplex.  The boundary
leaf family is itself a closed embedded copy of the real projective line.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Set
open scoped OnePoint

noncomputable section

/-- The real projective line is Polish through its explicit closed embedding onto the
Euclidean unit circle.  This supplies the standard-Borel structure needed by the general
probability-simplex extreme-point theorem. -/
local instance onePointRealPolishSpace : PolishSpace (OnePoint ℝ) :=
  onePointRealSphereHomeomorph.isClosedEmbedding.polishSpace

local instance onePointRealStandardBorelSpace : StandardBorelSpace (OnePoint ℝ) :=
  standardBorel_of_polish

/-- Probability solutions of one complete Hamburger moment sequence. -/
abbrev HamburgerMomentProbabilityFiber (s : ℕ → ℝ) :=
  {nu : ProbabilityMeasure ℝ // HasHamburgerMoments s (nu : Measure ℝ)}

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- The boundary barycenter regarded as a point of the exact complete-moment fiber. -/
noncomputable def boundaryCarrierInMomentFiber
    (eta : ProbabilityMeasure (OnePoint ℝ)) : HamburgerMomentProbabilityFiber s :=
  ⟨F.barycenter eta, F.barycenter_hasHamburgerMoments eta⟩

/-- The boundary-carrier embedding into the moment fiber is continuous. -/
theorem continuous_boundaryCarrierInMomentFiber :
    Continuous F.boundaryCarrierInMomentFiber := by
  apply Continuous.subtype_mk
  exact F.barycenter_isClosedEmbedding.continuous

/-- Exact projective label recovery makes the boundary-carrier embedding injective. -/
theorem injective_boundaryCarrierInMomentFiber :
    Function.Injective F.boundaryCarrierInMomentFiber := by
  intro eta theta h
  exact F.barycenter_isClosedEmbedding.injective (congrArg Subtype.val h)

/-- The canonical boundary simplex is a closed embedded subspace of the complete-moment fiber. -/
theorem boundaryCarrierInMomentFiber_isClosedEmbedding :
    Topology.IsClosedEmbedding F.boundaryCarrierInMomentFiber :=
  F.continuous_boundaryCarrierInMomentFiber.isClosedEmbedding
    F.injective_boundaryCarrierInMomentFiber

/-- Every boundary carrier has one and only one projective parameter law. -/
theorem existsUnique_projectiveLaw_of_mem_boundaryCarrierRange
    (nu : ProbabilityMeasure ℝ) (hnu : nu ∈ range F.barycenter) :
    ∃! eta : ProbabilityMeasure (OnePoint ℝ), F.barycenter eta = nu := by
  rcases hnu with ⟨eta, rfl⟩
  exact ⟨eta, rfl, fun theta h => F.barycenter_isClosedEmbedding.injective h⟩

/-- The recovered parameter law of a boundary carrier is literally its original law. -/
@[simp]
theorem projectiveLaw_boundaryCarrierInMomentFiber
    (eta : ProbabilityMeasure (OnePoint ℝ)) :
    F.projectiveLaw (F.boundaryCarrierInMomentFiber eta).1 = eta :=
  F.projectiveLaw_barycenter eta

/-- Restriction of the canonical constraint projector to the full complete-moment fiber. -/
noncomputable def carrierRetractOnMomentFiber
    (nu : HamburgerMomentProbabilityFiber s) : HamburgerMomentProbabilityFiber s :=
  ⟨F.carrierProjector nu.1, F.carrierProjector_hasHamburgerMoments nu.1⟩

/-- The moment-fiber retraction is continuous. -/
theorem continuous_carrierRetractOnMomentFiber :
    Continuous F.carrierRetractOnMomentFiber := by
  apply Continuous.subtype_mk
  exact F.continuous_carrierProjector.comp continuous_subtype_val

/-- The boundary embedding is a section of the moment-fiber retraction. -/
@[simp]
theorem carrierRetractOnMomentFiber_boundaryCarrier
    (eta : ProbabilityMeasure (OnePoint ℝ)) :
    F.carrierRetractOnMomentFiber (F.boundaryCarrierInMomentFiber eta) =
      F.boundaryCarrierInMomentFiber eta := by
  apply Subtype.ext
  exact F.carrierProjector_barycenter eta

/-- The canonical map is an idempotent retraction on the complete-moment fiber. -/
@[simp]
theorem carrierRetractOnMomentFiber_idempotent
    (nu : HamburgerMomentProbabilityFiber s) :
    F.carrierRetractOnMomentFiber (F.carrierRetractOnMomentFiber nu) =
      F.carrierRetractOnMomentFiber nu := by
  apply Subtype.ext
  exact F.carrierProjector_idempotent nu.1

/-- Its image is exactly the embedded boundary simplex. -/
theorem range_carrierRetractOnMomentFiber :
    range F.carrierRetractOnMomentFiber = range F.boundaryCarrierInMomentFiber := by
  apply Subset.antisymm
  · rintro _ ⟨nu, rfl⟩
    exact ⟨F.projectiveLaw nu.1, rfl⟩
  · rintro _ ⟨eta, rfl⟩
    exact ⟨F.boundaryCarrierInMomentFiber eta,
      F.carrierRetractOnMomentFiber_boundaryCarrier eta⟩

/-- A point of the complete-moment fiber is fixed exactly when it lies in the embedded boundary
simplex. -/
theorem carrierRetractOnMomentFiber_eq_self_iff
    (nu : HamburgerMomentProbabilityFiber s) :
    F.carrierRetractOnMomentFiber nu = nu ↔
      nu ∈ range F.boundaryCarrierInMomentFiber := by
  constructor
  · intro h
    exact ⟨F.projectiveLaw nu.1, h⟩
  · rintro ⟨eta, rfl⟩
    exact F.carrierRetractOnMomentFiber_boundaryCarrier eta

/-- Distinct projective labels give distinct boundary leaves. -/
theorem injective_leaf : Function.Injective F.leaf := by
  intro t u h
  have hmeasure : (F.leaf t : Measure ℝ) = (F.leaf u : Measure ℝ) :=
    congrArg ProbabilityMeasure.toMeasure h
  have hmap := congrArg (Measure.map F.matrix.projectiveLabel) hmeasure
  rw [F.map_projectiveLabel_leaf, F.map_projectiveLabel_leaf] at hmap
  exact dirac_eq_dirac_iff.mp hmap

/-- The N-extremal boundary is a closed embedded copy of the real projective line. -/
theorem leaf_isClosedEmbedding : Topology.IsClosedEmbedding F.leaf :=
  F.continuous_leaf.isClosedEmbedding F.injective_leaf

/-- The N-extremal boundary is closed in the carrier probability space. -/
theorem isClosed_range_leaf : IsClosed (range F.leaf) :=
  F.leaf_isClosedEmbedding.isClosed_range

/-- A point leaf is exactly the boundary barycenter of the corresponding Dirac parameter law. -/
theorem barycenter_dirac (t : OnePoint ℝ) :
    F.barycenter ⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ = F.leaf t := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [NevanlinnaBoundaryFamily.barycenter, probabilityBoundaryBarycenter,
    boundaryBarycenter, F.measurable_leaf]

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Set
open scoped OnePoint ENNReal

noncomputable section

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Nevanlinna barycentring preserves genuine two-point probability mixtures. -/
theorem barycenter_probabilityMixture
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (eta theta : ProbabilityMeasure (OnePoint ℝ)) :
    F.barycenter (probabilityMixture t ht eta theta) =
      probabilityMixture t ht (F.barycenter eta) (F.barycenter theta) := by
  apply ProbabilityMeasure.toMeasure_injective
  change boundaryBarycenter
      (t • (eta : Measure (OnePoint ℝ)) +
        (1 - t) • (theta : Measure (OnePoint ℝ)))
      (fun q => (F.leaf q : Measure ℝ)) =
    t • boundaryBarycenter (eta : Measure (OnePoint ℝ))
        (fun q => (F.leaf q : Measure ℝ)) +
      (1 - t) • boundaryBarycenter (theta : Measure (OnePoint ℝ))
        (fun q => (F.leaf q : Measure ℝ))
  rw [boundaryBarycenter_add _ _ _ F.measurable_leaf,
    boundaryBarycenter_smul, boundaryBarycenter_smul]

/-- The extreme points of the Nevanlinna boundary carrier simplex are exactly barycentres of
Dirac parameter laws. -/
theorem isExtremeProbabilityLaw_barycenter_iff_dirac
    (eta : ProbabilityMeasure (OnePoint ℝ)) :
    IsExtremeProbabilityLaw (range F.barycenter) (F.barycenter eta) ↔
      ∃ t : OnePoint ℝ,
        eta = ⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ := by
  constructor
  · intro hextreme
    have hetaExtreme : IsExtremeProbabilityLaw Set.univ eta := by
      refine ⟨Set.mem_univ _, ?_⟩
      intro w hw hw0 hw1 mu nu _ _ hmix
      have hcarrierMix : probabilityMixture w hw (F.barycenter mu) (F.barycenter nu) =
          F.barycenter eta := by
        rw [← F.barycenter_probabilityMixture, hmix]
      have hparts := hextreme.2 w hw hw0 hw1
        (F.barycenter mu) (F.barycenter nu)
        ⟨mu, rfl⟩ ⟨nu, rfl⟩ hcarrierMix
      exact ⟨F.barycenter_isClosedEmbedding.injective hparts.1,
        F.barycenter_isClosedEmbedding.injective hparts.2⟩
    letI : StandardBorelSpace (OnePoint ℝ) :=
      onePointRealStandardBorelSpace
    exact (isExtremeProbabilityLaw_univ_iff_dirac eta).mp hetaExtreme
  · rintro ⟨t, rfl⟩
    refine ⟨⟨⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩, rfl⟩, ?_⟩
    intro w hw hw0 hw1 mu nu hmu hnu hmix
    rcases hmu with ⟨alpha, rfl⟩
    rcases hnu with ⟨beta, rfl⟩
    have hparamMix : probabilityMixture w hw alpha beta =
        (⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ :
          ProbabilityMeasure (OnePoint ℝ)) := by
      apply F.barycenter_isClosedEmbedding.injective
      rw [F.barycenter_probabilityMixture]
      exact hmix
    have hparts := (isExtremeProbabilityLaw_dirac t).2 w hw hw0 hw1
      alpha beta (Set.mem_univ _) (Set.mem_univ _) hparamMix
    exact ⟨congrArg F.barycenter hparts.1, congrArg F.barycenter hparts.2⟩

/-- The extreme boundary of the carrier simplex is literally the N-extremal leaf family. -/
theorem extremeBoundary_carrierRange :
    {nu : ProbabilityMeasure ℝ |
      IsExtremeProbabilityLaw (range F.barycenter) nu} = range F.leaf := by
  ext nu
  constructor
  · intro hnu
    rcases hnu.1 with ⟨eta, rfl⟩
    rcases (F.isExtremeProbabilityLaw_barycenter_iff_dirac eta).mp hnu with ⟨t, rfl⟩
    exact ⟨t, (F.barycenter_dirac t).symm⟩
  · rintro ⟨t, rfl⟩
    rw [← F.barycenter_dirac t]
    exact (F.isExtremeProbabilityLaw_barycenter_iff_dirac
      (⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ :
        ProbabilityMeasure (OnePoint ℝ))).mpr ⟨t, rfl⟩

/-- The Nevanlinna carrier simplex has closed extreme boundary: its Bauer property in exact
probability-mixture form. -/
theorem isClosed_extremeBoundary_carrierRange :
    IsClosed {nu : ProbabilityMeasure ℝ |
      IsExtremeProbabilityLaw (range F.barycenter) nu} := by
  rw [F.extremeBoundary_carrierRange]
  exact F.isClosed_range_leaf

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
