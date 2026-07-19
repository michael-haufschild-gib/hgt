import GaloisForLFunctions.HTGeometry.HamburgerExistence
import GaloisForLFunctions.HTGeometry.NevanlinnaBauerRetract

/-!
# The Hamburger moment fiber is inhabited

`HamburgerMomentProbabilityFiber s` is the space of probability measures representing `s`, the
object whose extreme points the Bauer retract analyses.  Until now it could be shown nonempty
only by
exhibiting a boundary family and taking a barycenter, which presupposes the very structure the fiber
is used to study.

Positive definiteness of the moment form suffices instead: the representing measure constructed from
the sequence lands in the fiber directly.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The moment fiber is inhabited**, for a normalised positive definite moment form. -/
theorem nonempty_hamburgerMomentProbabilityFiber (h : PositiveMomentForm s) (h0 : s 0 = 1) :
    Nonempty (GaloisForLFunctions.HTGeometry.HamburgerMomentProbabilityFiber s) := by
  obtain ⟨mu, hmu⟩ := exists_hasHamburgerMoments_of_moment_zero_eq_one h h0
  exact ⟨⟨mu, hmu⟩⟩

/-- Without a normalisation hypothesis the fiber of the rescaled sequence is inhabited. -/
theorem nonempty_hamburgerMomentProbabilityFiber_normalised (h : PositiveMomentForm s) :
    Nonempty (GaloisForLFunctions.HTGeometry.HamburgerMomentProbabilityFiber
      (fun k => (s 0)⁻¹ * s k)) := by
  obtain ⟨mu, hmu⟩ := exists_hasHamburgerMoments h
  exact ⟨⟨mu, hmu⟩⟩

end HTGeometry
