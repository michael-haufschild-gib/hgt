import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedProfile

/-!
# Exact inverse of the moving-peak coordinate

The inverse fractional linear map preserves the closed physical phase
interval for every state. Its angle representation reconstructs the
original radius coordinate, and the aligned quartic profile becomes an
exact fixed polynomial in the new coordinate.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakInverseCoordinate (τ φ ψ : ℝ) : ℝ :=
  -egbFixedChargeAPeakAlignedCoordinate τ φ (-ψ)
def egbFixedChargeAPeakInverseAngle (τ φ ψ : ℝ) : ℝ :=
  arcsin (egbFixedChargeAPeakInverseCoordinate τ φ ψ)

theorem egbFixedChargeAPeakInverseCoordinate_formula (τ φ ψ : ℝ) :
    egbFixedChargeAPeakInverseCoordinate τ φ ψ =
      (sin ψ + egbFixedChargeAMiddleGapCoordinate τ φ) / (1 + egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ) := by
  unfold egbFixedChargeAPeakInverseCoordinate egbFixedChargeAPeakAlignedCoordinate
  rw [sin_neg]
  ring

theorem egbFixedChargeAPeakInverseCoordinate_denominator_pos (τ φ ψ : ℝ) :
    0 < 1 + egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ := by
  simpa only [sin_neg, mul_neg, sub_neg_eq_add] using egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ (-ψ)

theorem egbFixedChargeAPeakInverseCoordinate_bounds (τ φ ψ : ℝ) :
    -1 ≤ egbFixedChargeAPeakInverseCoordinate τ φ ψ ∧ egbFixedChargeAPeakInverseCoordinate τ φ ψ ≤ 1 := by
  have h := egbFixedChargeAPeakAlignedCoordinate_bounds τ φ (-ψ)
  unfold egbFixedChargeAPeakInverseCoordinate
  constructor <;> linarith

theorem egbFixedChargeAPeakInverseAngle_sin (τ φ ψ : ℝ) :
    sin (egbFixedChargeAPeakInverseAngle τ φ ψ) = egbFixedChargeAPeakInverseCoordinate τ φ ψ := by
  unfold egbFixedChargeAPeakInverseAngle
  exact sin_arcsin (egbFixedChargeAPeakInverseCoordinate_bounds τ φ ψ).1 (egbFixedChargeAPeakInverseCoordinate_bounds τ φ ψ).2

theorem egbFixedChargeAPeakAlignedCoordinate_inverse (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedCoordinate τ φ (egbFixedChargeAPeakInverseAngle τ φ ψ) = sin ψ := by
  have hp := egbFixedChargeAPeakInverseCoordinate_denominator_pos τ φ ψ
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ (egbFixedChargeAPeakInverseAngle τ φ ψ)
  rw [egbFixedChargeAPeakInverseAngle_sin] at hd
  unfold egbFixedChargeAPeakAlignedCoordinate
  rw [egbFixedChargeAPeakInverseAngle_sin]
  apply (div_eq_iff hd.ne').mpr
  rw [egbFixedChargeAPeakInverseCoordinate_formula]
  have hp' : 1 + sin ψ * egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by simpa only [mul_comm] using hp.ne'
  field_simp [hp.ne', hp'] <;> ring

theorem egbFixedChargeAPeakInverseCoordinate_aligned (τ φ ψ : ℝ) :
    egbFixedChargeAPeakInverseCoordinate τ φ (arcsin (egbFixedChargeAPeakAlignedCoordinate τ φ ψ)) = sin ψ := by
  have hs := sin_arcsin (egbFixedChargeAPeakAlignedCoordinate_bounds τ φ ψ).1
    (egbFixedChargeAPeakAlignedCoordinate_bounds τ φ ψ).2
  have hp := egbFixedChargeAPeakInverseCoordinate_denominator_pos τ φ (arcsin (egbFixedChargeAPeakAlignedCoordinate τ φ ψ))
  rw [hs] at hp
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ
  rw [egbFixedChargeAPeakInverseCoordinate_formula, hs]
  apply (div_eq_iff hp.ne').mpr
  unfold egbFixedChargeAPeakAlignedCoordinate
  have hd' : 1 - sin ψ * egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by simpa only [mul_comm] using hd.ne'
  field_simp [hd.ne', hd'] <;> ring

theorem egbFixedChargeAPeakAlignedProfile_inverse (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedProfile τ φ (egbFixedChargeAPeakInverseAngle τ φ ψ) = cos ψ ^ 4 := by
  unfold egbFixedChargeAPeakAlignedProfile
  rw [egbFixedChargeAPeakAlignedCoordinate_inverse]
  have hs : 1 - sin ψ ^ 2 = cos ψ ^ 2 := by linarith [sin_sq_add_cos_sq ψ]
  rw [hs]
  ring

theorem egbFixedChargeAPeakInverseCoordinate_center (τ φ : ℝ) :
    egbFixedChargeAPeakInverseCoordinate τ φ 0 = egbFixedChargeAMiddleGapCoordinate τ φ := by
  rw [egbFixedChargeAPeakInverseCoordinate_formula]
  simp only [sin_zero, zero_add, mul_zero, add_zero, div_one]

theorem egbFixedChargeAPeakInverseCoordinate_large_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakInverseCoordinate τ φ ψ = 1 ↔ sin ψ = 1 := by
  unfold egbFixedChargeAPeakInverseCoordinate
  have h := egbFixedChargeAPeakAlignedCoordinate_small_iff τ φ (-ψ)
  rw [sin_neg] at h
  constructor
  · intro he
    have hx : egbFixedChargeAPeakAlignedCoordinate τ φ (-ψ) = -1 := by linarith
    linarith [h.mp hx]
  · intro he
    have hx := h.mpr (by linarith)
    linarith

theorem egbFixedChargeAPeakInverseCoordinate_small_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakInverseCoordinate τ φ ψ = -1 ↔ sin ψ = -1 := by
  unfold egbFixedChargeAPeakInverseCoordinate
  have h := egbFixedChargeAPeakAlignedCoordinate_large_iff τ φ (-ψ)
  rw [sin_neg] at h
  constructor
  · intro he
    have hx : egbFixedChargeAPeakAlignedCoordinate τ φ (-ψ) = 1 := by linarith
    linarith [h.mp hx]
  · intro he
    have hx := h.mpr (by linarith)
    linarith

end GaloisForLFunctions.HTGeometry
