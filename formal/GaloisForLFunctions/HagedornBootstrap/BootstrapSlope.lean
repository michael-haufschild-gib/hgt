import GaloisForLFunctions.HTGeometry.CoshHalfPowerLowerBound
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The slope of the spinless modular bootstrap

For a unitary compact two-dimensional CFT with `c > 1` and no extra currents, the spinless modular
bootstrap bounds the gap as `Δ₁ ≤ c/Λ + o(c)`. A family of functionals whose last sign change sits
at the scaled point `x₁` certifies the slope `Λ(x₁) = 1/(1/12 + x₁²/3)`: `x₁ = 0` is the BTZ
threshold `Λ = 12`, and a larger tip gives a smaller slope. The optimal tip is the slit tip
`x* = arsinh(1)/π`, characterized by `sinh(πx*) = 1`, and the optimal slope is

  `Λ_V = 12π²/(π² + 4 arsinh² 1)`.

This file proves the closed-form identities and certified bounds `9.12 < Λ_V < 9.13`; in
particular `Λ_V` exceeds both Hellerman's slope `6` and the earlier rigorous lower bound
`8.503`, and the earlier numerical fits `9.08` lie strictly below it.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

/-- The slope certified by functionals whose scaled last sign change is `x`. -/
def slopeOfTip (x : ℝ) : ℝ := 1 / (1 / 12 + x ^ 2 / 3)

/-- The slit tip `x* = arsinh(1)/π`. -/
def bootstrapTip : ℝ := Real.arsinh 1 / π

/-- The optimal slope `Λ_V = 12π²/(π² + 4 arsinh² 1)`. -/
def viraSlope : ℝ := 12 * π ^ 2 / (π ^ 2 + 4 * Real.arsinh 1 ^ 2)

theorem slopeOfTip_zero : slopeOfTip 0 = 12 := by norm_num [slopeOfTip]

theorem slopeOfTip_pos (x : ℝ) : 0 < slopeOfTip x := by unfold slopeOfTip; positivity

/-- A larger tip certifies a smaller slope. -/
theorem slopeOfTip_strictAntiOn : StrictAntiOn slopeOfTip (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold slopeOfTip
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

/-- The slope at the tip is `Λ_V`. -/
theorem slopeOfTip_bootstrapTip : slopeOfTip bootstrapTip = viraSlope := by
  unfold slopeOfTip bootstrapTip viraSlope
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `Λ_V = 1/(1/12 + ξ*)` with `ξ* = x*²/3`. -/
theorem viraSlope_eq_inv : viraSlope = 1 / (1 / 12 + bootstrapTip ^ 2 / 3) := by
  rw [← slopeOfTip_bootstrapTip]; rfl

/-- The tip is where the edge function `sinh(πx)` reaches `1`. -/
theorem sinh_pi_mul_bootstrapTip : Real.sinh (π * bootstrapTip) = 1 := by
  unfold bootstrapTip
  rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.sinh_arsinh]

theorem bootstrapTip_pos : 0 < bootstrapTip := by
  unfold bootstrapTip
  have : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr one_pos
  positivity

theorem viraSlope_pos : 0 < viraSlope := by unfold viraSlope; positivity

/-- `Λ_V < 12`: the bound stays strictly above the BTZ threshold. -/
theorem viraSlope_lt_twelve : viraSlope < 12 := by
  rw [← slopeOfTip_bootstrapTip, ← slopeOfTip_zero]
  exact slopeOfTip_strictAntiOn Set.self_mem_Ici (Set.mem_Ici.mpr bootstrapTip_pos.le) bootstrapTip_pos

/-! ### Certified bounds for `arsinh 1 = log(1 + √2)` -/

theorem exp_arsinh_one : Real.exp (Real.arsinh 1) = 1 + √2 := by
  rw [Real.exp_arsinh]; norm_num

/-- `arsinh 1 < 0.8825`. -/
theorem arsinh_one_lt : Real.arsinh 1 < 0.8825 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : √2 < 1.41422 := by nlinarith [Real.sqrt_nonneg 2]
  have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.8825 by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  rw [← Real.exp_lt_exp, exp_arsinh_one]
  linarith

/-- `0.881 < arsinh 1`. -/
theorem lt_arsinh_one : 0.881 < Real.arsinh 1 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : 1.4142 < √2 := by nlinarith [Real.sqrt_nonneg 2]
  have hb := Real.exp_bound' (x := 0.881) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  rw [← Real.exp_lt_exp, exp_arsinh_one]
  linarith

/-- **Certified slope:** `9.12 < Λ_V < 9.13`. -/
theorem viraSlope_bounds : 9.12 < viraSlope ∧ viraSlope < 9.13 := by
  have hL1 := arsinh_one_lt
  have hL2 := lt_arsinh_one
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hden : 0 < π ^ 2 + 4 * Real.arsinh 1 ^ 2 := by positivity
  unfold viraSlope
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

/-- `Λ_V` exceeds Hellerman's slope `6`, the earlier rigorous bound `8.503` and the fits `9.08`. -/
theorem viraSlope_gt_earlier : 6 < viraSlope ∧ 8.503 < viraSlope ∧ 9.08 < viraSlope := by
  have h := viraSlope_bounds.1
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The corpus bound `7/8 < arsinh 1` already places the tip beyond `x = 7/(8π)`. -/
theorem seven_div_eight_pi_lt_bootstrapTip : 7 / (8 * π) < bootstrapTip := by
  unfold bootstrapTip
  rw [div_lt_div_iff₀ (by positivity) Real.pi_pos]
  have := HTGeometry.seven_div_eight_lt_arsinh_one
  nlinarith [Real.pi_pos]

end GaloisForLFunctions.HagedornBootstrap
