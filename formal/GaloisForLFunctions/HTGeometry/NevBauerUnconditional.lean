import GaloisForLFunctions.HTGeometry.NevExtremalFamily
import GaloisForLFunctions.HTGeometry.NevanlinnaBauerRetract

/-!
# The Bauer retract, unconditionally

The boundary-carrier package was proved for an arbitrary `NevanlinnaBoundaryFamily`, i.e. relative to
a classical Nevanlinna family taken as input.  The constructed family supplies that input for every
indeterminate moment sequence, so the whole package becomes a statement about the sequence: its
complete-moment fiber contains a canonical closed embedded Bauer simplex, and carries a continuous
idempotent retraction onto it.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The boundary family of the constructed classical family. -/
noncomputable def nevBoundaryFamily (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) : GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFamily s :=
  (nevExtremalFamily h h0b h0).toBoundaryFamily

/-- **The moment fiber contains a canonical closed Bauer simplex.**  Unconditionally, for every
indeterminate normalised moment sequence. -/
theorem nevBauer_isClosedEmbedding (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Topology.IsClosedEmbedding
      (nevBoundaryFamily h h0b h0).boundaryCarrierInMomentFiber :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierInMomentFiber_isClosedEmbedding

/-- **The canonical retraction of the whole moment fiber onto the simplex is continuous.** -/
theorem nevBauer_continuous_retract (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Continuous (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber :=
  (nevBoundaryFamily h h0b h0).continuous_carrierRetractOnMomentFiber

/-- **The retraction is idempotent.** -/
theorem nevBauer_retract_idempotent (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1)
    (nu : GaloisForLFunctions.HTGeometry.HamburgerMomentProbabilityFiber s) :
    (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber
        ((nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber nu)
      = (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber nu :=
  (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber_idempotent nu

/-- **The image of the retraction is exactly the embedded simplex.** -/
theorem nevBauer_range_retract (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Set.range (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber
      = Set.range (nevBoundaryFamily h h0b h0).boundaryCarrierInMomentFiber :=
  (nevBoundaryFamily h h0b h0).range_carrierRetractOnMomentFiber

/-- **A point of the moment fiber is fixed by the retraction exactly when it is on the simplex.** -/
theorem nevBauer_fixed_iff (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (nu : GaloisForLFunctions.HTGeometry.HamburgerMomentProbabilityFiber s) :
    (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber nu = nu ↔
      nu ∈ Set.range (nevBoundaryFamily h h0b h0).boundaryCarrierInMomentFiber :=
  (nevBoundaryFamily h h0b h0).carrierRetractOnMomentFiber_eq_self_iff nu

/-- **The leaves are exactly the extreme points of the simplex.**  A barycentre is extreme iff its
parameter law is a point mass. -/
theorem nevBauer_extreme_iff (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (eta : ProbabilityMeasure (OnePoint ℝ)) :
    GaloisForLFunctions.HTGeometry.IsExtremeProbabilityLaw
        (Set.range (nevBoundaryFamily h h0b h0).barycenter)
        ((nevBoundaryFamily h h0b h0).barycenter eta) ↔
      ∃ t : OnePoint ℝ,
        eta = ⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ :=
  (nevBoundaryFamily h h0b h0).isExtremeProbabilityLaw_barycenter_iff_dirac eta

end HTGeometry
