import GaloisForLFunctions.HTGeometry.TiltedTentTwoFlankSurplus
import GaloisForLFunctions.RHTower.SuzukiMangoldtApexLock

open Set MeasureTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-!
# Critical two-flank geometry of Suzuki's positive channel

At rectangular width two, logarithmic displacement `x` from the moving apex gives exactly the
critical full tilted-tent profile.  The universal bilateral surplus law therefore specializes to
an actual Suzuki-channel surplus strictly exceeding twice its apex height.
-/

/-- Width-two moving-apex lag. -/
def suzukiCriticalMovingApexLag (a : ℝ) : ℝ := 4 * a - 4

/-- Height of the width-two positive channel at its moving apex once the fixed tent is absent. -/
def suzukiCriticalMovingApexHeight (a : ℝ) : ℝ := 2 * Real.exp (a - 1)

/-- Across the full critical support, Suzuki's actual positive channel is exactly its apex height
times the critical normalized tilted tent. -/
theorem suzukiCriticalPositiveArchChannel_eq_apex_mul_tiltedTent
    {a x : ℝ} (ha : 3 ≤ a) (hx : x ∈ Set.Icc (-2 : ℝ) 2) :
    suzukiRectangularPositiveArchSampleChannel 2 a
        (suzukiCriticalMovingApexLag a + 2 * x) =
      suzukiCriticalMovingApexHeight a * tiltedTentFullProfile (1 / 2) 2 x := by
  have ht : 0 ≤ suzukiCriticalMovingApexLag a + 2 * x := by
    rw [suzukiCriticalMovingApexLag]
    linarith [hx.1]
  rw [suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving
    (by norm_num) (by linarith) ht]
  have hfixed : suzukiRectangularFixedArchChannel 2
      (suzukiCriticalMovingApexLag a + 2 * x) = 0 := by
    rw [suzukiRectangularFixedArchChannel, suzukiCriticalMovingApexLag]
    rw [max_eq_left (by linarith [hx.1])]
    ring
  rw [hfixed, zero_add, suzukiRectangularMovingArchChannel,
    suzukiCriticalMovingApexLag, suzukiCriticalMovingApexHeight,
    tiltedTentFullProfile]
  have hcenter : (4 * a - 4 + 2 * x) / 2 - (2 * a - 2) = x := by ring
  rw [hcenter, max_eq_right (by linarith [abs_le.2 hx])]
  rw [show (4 * a - 4 + 2 * x) / 4 = (a - 1) + (1 / 2 : ℝ) * x by ring,
    Real.exp_add]
  ring

/-- Actual width-two continuum surplus of Suzuki's positive channel. -/
def suzukiCriticalPositiveArchTwoFlankSurplus (a : ℝ) : ℝ :=
  2 * ∫ x : ℝ in (-2 : ℝ)..2,
    (suzukiCriticalMovingApexHeight a -
      suzukiRectangularPositiveArchSampleChannel 2 a
        (suzukiCriticalMovingApexLag a + 2 * x))

/-- Exact connector from the actual Suzuki channel to the universal bilateral surplus law. -/
theorem suzukiCriticalPositiveArchTwoFlankSurplus_eq
    {a : ℝ} (ha : 3 ≤ a) :
    suzukiCriticalPositiveArchTwoFlankSurplus a =
      suzukiCriticalMovingApexHeight a * tiltedTentTwoFlankSurplus (1 / 2) 2 := by
  have hintegral :
      (∫ x : ℝ in (-2 : ℝ)..2,
          (suzukiCriticalMovingApexHeight a -
            suzukiRectangularPositiveArchSampleChannel 2 a
              (suzukiCriticalMovingApexLag a + 2 * x))) =
        ∫ x : ℝ in (-2 : ℝ)..2,
          suzukiCriticalMovingApexHeight a *
            (1 - tiltedTentFullProfile (1 / 2) 2 x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at hx
    change suzukiCriticalMovingApexHeight a -
        suzukiRectangularPositiveArchSampleChannel 2 a
          (suzukiCriticalMovingApexLag a + 2 * x) =
      suzukiCriticalMovingApexHeight a *
        (1 - tiltedTentFullProfile (1 / 2) 2 x)
    rw [suzukiCriticalPositiveArchChannel_eq_apex_mul_tiltedTent ha hx]
    ring
  rw [suzukiCriticalPositiveArchTwoFlankSurplus, hintegral,
    intervalIntegral.integral_const_mul, tiltedTentTwoFlankSurplus]
  ring

/-- Critical Suzuki geometry has strictly more continuum surplus than twice its apex height, the
worst possible charge of a width-two bicausal seam. -/
theorem two_mul_suzukiCriticalMovingApexHeight_lt_twoFlankSurplus
    {a : ℝ} (ha : 3 ≤ a) :
    2 * suzukiCriticalMovingApexHeight a <
      suzukiCriticalPositiveArchTwoFlankSurplus a := by
  rw [suzukiCriticalPositiveArchTwoFlankSurplus_eq ha]
  have hheight : 0 < suzukiCriticalMovingApexHeight a := by
    rw [suzukiCriticalMovingApexHeight]
    positivity
  have hsurplus :=
    mul_lt_mul_of_pos_left tiltedTentTwoFlankSurplus_critical_gt_two hheight
  simpa [mul_comm] using hsurplus

end RHTower
