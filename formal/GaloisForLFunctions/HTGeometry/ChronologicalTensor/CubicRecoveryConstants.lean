import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicFlow

/-!
# Exact constants for recovery that preserves the physical scaling

The contact point, optimal slope, and positive gap satisfy explicit quadratic
and stationary identities. A polynomial factorization bounds the entire lower
coordinate arc. All radical identities and inequalities are proved symbolically.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set

def cubicRecoveryContact : ℝ := (Real.sqrt 17-3)/4
def cubicRecoverySlope : ℝ := (126+34*Real.sqrt 17)/59
def cubicRecoveryGap : ℝ := (17*Real.sqrt 17-55)/118
def cubicRecoveryLower (c : ℝ) : ℝ := c^2/2-c^3/4


theorem cubicRecoveryContact_bounds : 0 < cubicRecoveryContact ∧ cubicRecoveryContact < 1/3 := by
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 17)
  have hn := Real.sqrt_nonneg (17:ℝ)
  unfold cubicRecoveryContact
  constructor <;> nlinarith

theorem cubicRecoveryContact_equation : 2*cubicRecoveryContact^2+3*cubicRecoveryContact-1=0 := by
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 17)
  unfold cubicRecoveryContact
  nlinarith

theorem cubicRecoverySlope_contact : cubicRecoverySlope=(228+136*cubicRecoveryContact)/59 := by
  unfold cubicRecoverySlope cubicRecoveryContact
  ring

theorem cubicRecoverySlope_gt_four : 4 < cubicRecoverySlope := by
  rw [cubicRecoverySlope_contact]
  have ht := cubicRecoveryContact_equation
  have hb := cubicRecoveryContact_bounds
  have ht4 : 1/4 < cubicRecoveryContact := by nlinarith
  linarith

theorem cubicRecoveryGap_slope : cubicRecoveryGap=cubicRecoverySlope/4-1 := by
  unfold cubicRecoveryGap cubicRecoverySlope
  ring

theorem cubicRecoveryGap_pos : 0 < cubicRecoveryGap := by
  rw [cubicRecoveryGap_slope]
  linarith [cubicRecoverySlope_gt_four]

theorem cubicRecoverySlope_stationary :
    1-cubicRecoverySlope*cubicRecoveryContact+
      3*cubicRecoverySlope*cubicRecoveryContact^2/4=0 := by
  rw [cubicRecoverySlope_contact]
  linear_combination ((51*cubicRecoveryContact-59)/59)*cubicRecoveryContact_equation

theorem cubicRecoveryGap_contact :
    cubicRecoveryContact-cubicRecoverySlope*cubicRecoveryLower cubicRecoveryContact=cubicRecoveryGap := by
  rw [cubicRecoveryGap_slope,cubicRecoverySlope_contact]
  unfold cubicRecoveryLower
  linear_combination ((17*cubicRecoveryContact^2-31*cubicRecoveryContact-2)/59)*
    cubicRecoveryContact_equation

theorem cubicRecoveryLower_contact_pos : 0 < cubicRecoveryLower cubicRecoveryContact := by
  have ht := cubicRecoveryContact_bounds
  have he : cubicRecoveryLower cubicRecoveryContact=
      cubicRecoveryContact^2*(2-cubicRecoveryContact)/4 := by unfold cubicRecoveryLower; ring
  rw [he]
  have hp : 0 < 2-cubicRecoveryContact := by linarith
  have ht0 := ht.1
  positivity

theorem cubicRecoveryGap_factor (c : ℝ) :
    cubicRecoveryGap-(c-cubicRecoverySlope*cubicRecoveryLower c)=
      (cubicRecoverySlope/4)*(c-cubicRecoveryContact)^2*(2-2*cubicRecoveryContact-c) := by
  rw [← cubicRecoveryGap_contact]
  unfold cubicRecoveryLower
  linear_combination (cubicRecoveryContact-c)*cubicRecoverySlope_stationary

theorem cubicRecoveryLower_error :
    ∀ c ∈ Icc (0:ℝ) 1, c-cubicRecoverySlope*cubicRecoveryLower c ≤ cubicRecoveryGap := by
  intro c hc
  have hfac : 0 ≤ 2-2*cubicRecoveryContact-c := by linarith [cubicRecoveryContact_bounds.2,hc.2]
  have hs : 0 ≤ cubicRecoverySlope/4 := by linarith [cubicRecoverySlope_gt_four]
  have h := mul_nonneg (mul_nonneg hs (sq_nonneg (c-cubicRecoveryContact))) hfac
  rw [← cubicRecoveryGap_factor c] at h
  linarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
