import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovLinearCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact

/-!
# Topology of the full moment image

The coordinate monomials make the moment map smooth. In positive degree,
projection to its linear coordinates is a left inverse, so the map is
injective. The moments of the closed physical unit cube form a compact set.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Every coordinate of the complete moment map is a finite product of powers. -/
theorem contDiff_canonicalMoment (r k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (canonicalMoment r k) := by
  apply contDiff_pi.mpr
  intro a
  simp only [canonicalMoment_product]
  apply contDiff_prod
  intro i _
  exact (contDiff_apply ℝ ℝ i).pow _

/-- Linear moment coordinates recover the entire physical input. -/
theorem degreeOneProjection_canonicalMoment (r k : ℕ) (x : Fin (r + 2) → ℝ) :
    degreeOneProjection r k (canonicalMoment r (k + 1) x) = x := by
  funext i
  exact canonicalMoment_degreeOneIndex r k x i

/-- The full positive-degree moment map identifies no distinct physical points. -/
theorem canonicalMoment_injective (r k : ℕ) : Function.Injective (canonicalMoment r (k + 1)) := by
  intro x y h
  have hp := congrArg (degreeOneProjection r k) h
  simpa only [degreeOneProjection_canonicalMoment] using hp

/-- The moments of the physical closed unit cube. -/
def unitMomentImage (r k : ℕ) : Set (AffineAxisSpace r k) :=
  canonicalMoment r k '' Set.Icc (0 : Fin (r + 2) → ℝ) 1

/-- The closed physical cube has a compact moment image in every degree. -/
theorem isCompact_unitMomentImage (r k : ℕ) : IsCompact (unitMomentImage r k) :=
  isCompact_Icc.image (contDiff_canonicalMoment r k).continuous

#print axioms contDiff_canonicalMoment
#print axioms degreeOneProjection_canonicalMoment
#print axioms canonicalMoment_injective
#print axioms isCompact_unitMomentImage

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
