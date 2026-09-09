import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedInverse

/-!
# Physical radii in coordinates centered on the actual Gibbs barrier

The inverse coordinate constructs positive radii inside the coexistence
interval. Its center is exactly the middle stationary radius at every
state, and its two endpoints remain exactly the two coexisting phases.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakAlignedRadius (w φ τ ψ : ℝ) : ℝ :=
  egbFixedChargeAInteriorRadius w φ τ (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedRadius_pos (w φ τ ψ : ℝ) :
    0 < egbFixedChargeAPeakAlignedRadius w φ τ ψ :=
  egbFixedChargeAInteriorRadius_pos w φ τ (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedRadius_bounds (w φ τ ψ : ℝ) :
    egbFixedChargeASmallRadius w φ τ ≤ egbFixedChargeAPeakAlignedRadius w φ τ ψ ∧
    egbFixedChargeAPeakAlignedRadius w φ τ ψ ≤ egbFixedChargeALargeRadius w φ τ :=
  egbFixedChargeAInteriorRadius_bounds w φ τ (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedRadius_middle_iff (w φ τ ψ : ℝ) :
    egbFixedChargeAPeakAlignedRadius w φ τ ψ = egbFixedChargeAMiddleRadius w φ τ ↔ sin ψ = 0 := by
  unfold egbFixedChargeAPeakAlignedRadius
  rw [egbFixedChargeAInteriorRadius_middle_iff]
  constructor
  · intro hc
    have hz := (egbFixedChargeAPeakAlignedCoordinate_zero_iff τ φ (egbFixedChargeAPeakInverseAngle τ φ ψ)).mpr hc
    have hi := egbFixedChargeAPeakAlignedCoordinate_inverse τ φ ψ
    rw [hz] at hi
    exact hi.symm
  · intro hs
    rw [egbFixedChargeAPeakInverseAngle_sin, egbFixedChargeAPeakInverseCoordinate_formula, hs]
    simp only [zero_add, mul_zero, add_zero, div_one]

theorem egbFixedChargeAPeakAlignedRadius_center (w φ τ : ℝ) :
    egbFixedChargeAPeakAlignedRadius w φ τ 0 = egbFixedChargeAMiddleRadius w φ τ :=
  (egbFixedChargeAPeakAlignedRadius_middle_iff w φ τ 0).mpr sin_zero

theorem egbFixedChargeAPeakAlignedRadius_small_iff (w φ τ ψ : ℝ) :
    egbFixedChargeAPeakAlignedRadius w φ τ ψ = egbFixedChargeASmallRadius w φ τ ↔ sin ψ = -1 := by
  unfold egbFixedChargeAPeakAlignedRadius
  rw [egbFixedChargeAInteriorRadius_small_iff, egbFixedChargeAPeakInverseAngle_sin,
    egbFixedChargeAPeakInverseCoordinate_small_iff]

theorem egbFixedChargeAPeakAlignedRadius_large_iff (w φ τ ψ : ℝ) :
    egbFixedChargeAPeakAlignedRadius w φ τ ψ = egbFixedChargeALargeRadius w φ τ ↔ sin ψ = 1 := by
  unfold egbFixedChargeAPeakAlignedRadius
  rw [egbFixedChargeAInteriorRadius_large_iff, egbFixedChargeAPeakInverseAngle_sin,
    egbFixedChargeAPeakInverseCoordinate_large_iff]

end GaloisForLFunctions.HTGeometry
