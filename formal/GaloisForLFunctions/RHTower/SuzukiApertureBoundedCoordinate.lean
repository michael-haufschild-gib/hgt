import GaloisForLFunctions.HTGeometry.BoundedCoordinateL2Expansion
import GaloisForLFunctions.RHTower.SuzukiWeilFriedrichsOperator

/-!
# The Suzuki aperture interval as a bounded coordinate

Suzuki's operator lives on `L²` of the interval carried as a subtype.  That measure space is finite
and its inclusion coordinate is bounded by the aperture, so it is an instance of the abstract
aperture, and every Taylor expansion along a bounded coordinate applies to it verbatim.

This is the identification that lets the coalescing analysis be run on the literal operator instead
of on a model of the same interval.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem volume_suzukiApertureInterval_univ (a : ℝ) :
    (volume : Measure (SuzukiApertureInterval a)) Set.univ = ENNReal.ofReal (a - -a) := by
  have h : (volume : Measure (SuzukiApertureInterval a)) Set.univ
      = Measure.comap (Subtype.val) (volume : Measure ℝ) Set.univ := rfl
  rw [h, comap_subtype_coe_apply measurableSet_Icc, Subtype.coe_image_univ,
    Real.volume_Icc]

instance instIsFiniteMeasureSuzukiAperture (a : ℝ) :
    IsFiniteMeasure (volume : Measure (SuzukiApertureInterval a)) := by
  constructor
  rw [volume_suzukiApertureInterval_univ a]
  exact ENNReal.ofReal_lt_top

/-- **The Suzuki aperture interval is a bounded coordinate.** -/
def suzukiApertureCoordinate {a : ℝ} (ha : 0 ≤ a) :
    BoundedCoordinate (SuzukiApertureInterval a) volume where
  coord := Subtype.val
  bound := a
  measurable_coord := measurable_subtype_coe
  bound_nonneg := ha
  abs_coord_le := Filter.Eventually.of_forall fun t => abs_le.mpr ⟨t.2.1, t.2.2⟩

@[simp]
theorem suzukiApertureCoordinate_coord {a : ℝ} (ha : 0 ≤ a) :
    (suzukiApertureCoordinate ha).coord = Subtype.val := rfl

@[simp]
theorem suzukiApertureCoordinate_bound {a : ℝ} (ha : 0 ≤ a) :
    (suzukiApertureCoordinate ha).bound = a := rfl

end RHTower
