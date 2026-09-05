import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# A sharp six-endpoint chronological response

Three separated alternating pairs and three nested alternating pairs have different
responses to a moving affine probe. Their combination with coefficients `27` and `1`
has exact unit-variation capacity at the algebraic position `(50 - sqrt 313) / 81`.
The proof reduces arbitrary signed increments to two nonnegative masses and factors
the cubic optimality gap. The rational equal-mass witness already has response `10/9`.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def peakPosition : ℝ := (50 - Real.sqrt 313) / 81

def sixCapacity : ℝ :=
  (27 / 4 : ℝ) * peakPosition * (1 - peakPosition)^2 + peakPosition^2

def sixCost (a b c d e : ℝ) : ℝ := |a| + |b| + |c| + |d| + |e|

def separatedThree (a _b c _d e : ℝ) : ℝ := a * c * e

def rainbowThree (a b c d e : ℝ) : ℝ :=
  (a + b + c + d + e) * (b + c + d) * c

def sixResponse (a b c d e : ℝ) : ℝ :=
  27 * separatedThree a b c d e + rainbowThree a b c d e

theorem peakPosition_bounds : 0 ≤ peakPosition ∧ peakPosition ≤ 5/12 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 313 by positivity)
  have hn := Real.sqrt_nonneg (313 : ℝ)
  unfold peakPosition
  constructor <;> nlinarith

theorem peakPosition_stationary :
    81 * peakPosition^2 - 100 * peakPosition + 27 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 313 by positivity)
  unfold peakPosition
  nlinarith

theorem sixCapacity_nonneg : 0 ≤ sixCapacity := by
  unfold sixCapacity
  have := peakPosition_bounds.1
  positivity

theorem cubic_gap_identity (x y : ℝ) :
    sixCapacity * (|x| + |y|)^3 -
        ((27/4 : ℝ) * |x| * |y|^2 + (|x|+|y|) * |x|^2) =
      (|x| - peakPosition * (|x|+|y|))^2 *
        ((25/2 - 27/2 * peakPosition) * (|x|+|y|) - 27/4 * |x|) := by
  calc
    _ = (|x| - peakPosition * (|x|+|y|))^2 *
        ((25/2 - 27/2 * peakPosition) * (|x|+|y|) - 27/4 * |x|) -
      (|x| - peakPosition * (|x|+|y|)) * (|x|+|y|)^2 *
        (81 * peakPosition^2 - 100 * peakPosition + 27) / 4 := by
      unfold sixCapacity
      ring
    _ = _ := by rw [peakPosition_stationary]; ring

theorem cubic_sharp_bound (x y : ℝ) :
    (27/4 : ℝ) * |x| * |y|^2 + (|x|+|y|) * |x|^2 ≤
      sixCapacity * (|x|+|y|)^3 := by
  have hc := peakPosition_bounds.2
  have h1 : 0 ≤ (23/4 : ℝ) - 27/2 * peakPosition := by linarith
  have h2 : 0 ≤ (25/2 : ℝ) - 27/2 * peakPosition := by linarith
  have hb : 0 ≤ (25/2 - 27/2 * peakPosition) * (|x|+|y|) - 27/4 * |x| := by
    nlinarith [mul_nonneg h1 (abs_nonneg x), mul_nonneg h2 (abs_nonneg y)]
  have hp := mul_nonneg (sq_nonneg (|x| - peakPosition * (|x|+|y|))) hb
  rw [← cubic_gap_identity] at hp
  linarith

theorem six_sharp_bound (a b c d e : ℝ) :
    |sixResponse a b c d e| ≤ sixCapacity * sixCost a b c d e ^ 3 := by
  let t := sixCost a b c d e
  let x := |b| + |c| + |d|
  let p := |a| + |e|
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have ht : 0 ≤ t := by dsimp [t, sixCost]; positivity
  have htotal : t = x + p := by dsimp [t, sixCost, x, p]; ring
  have hmid : |b + c + d| ≤ x :=
    (abs_add_le (b+c) d).trans (add_le_add (abs_add_le b c) le_rfl)
  have hsum : |a+b+c+d+e| ≤ t := by
    dsimp [t, sixCost]
    calc
      _ ≤ |a+b+c+d| + |e| := abs_add_le _ _
      _ ≤ (|a+b+c| + |d|) + |e| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|a+b| + |c|) + |d|) + |e| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl
  have hac : |a| * |e| ≤ p^2 / 4 := by
    dsimp [p]
    nlinarith [sq_nonneg (|a|-|e|)]
  have hcx : |c| ≤ x := by dsimp [x]; linarith [abs_nonneg b, abs_nonneg d]
  calc
    |sixResponse a b c d e| ≤
        27 * |a| * |c| * |e| + t * x * |c| := by
      calc
        _ ≤ |27 * separatedThree a b c d e| + |rainbowThree a b c d e| := abs_add_le _ _
        _ = 27 * |a| * |c| * |e| + |a+b+c+d+e| * |b+c+d| * |c| := by
          simp only [separatedThree, rainbowThree, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ 27 by positivity)]
          ring
        _ ≤ _ := by gcongr
    _ ≤ (27/4 : ℝ) * |c| * p^2 + t * x * |c| := by
      have hh := mul_le_mul_of_nonneg_left hac (show 0 ≤ 27 * |c| by positivity)
      nlinarith
    _ ≤ (27/4 : ℝ) * x * p^2 + t * x^2 := by
      have hfirst := mul_le_mul_of_nonneg_right hcx (show 0 ≤ (27/4 : ℝ)*p^2 by positivity)
      have hsecond := mul_le_mul_of_nonneg_left hcx (mul_nonneg ht hx)
      nlinarith
    _ = (27/4 : ℝ) * |x| * |p|^2 + (|x|+|p|) * |x|^2 := by
      rw [abs_of_nonneg hx, abs_of_nonneg hp, htotal]
    _ ≤ sixCapacity * (|x|+|p|)^3 := cubic_sharp_bound x p
    _ = sixCapacity * sixCost a b c d e ^ 3 := by
      rw [abs_of_nonneg hx, abs_of_nonneg hp, ← htotal]

theorem six_attained :
    sixCost ((1-peakPosition)/2) 0 peakPosition 0 ((1-peakPosition)/2) = 1 ∧
    |sixResponse ((1-peakPosition)/2) 0 peakPosition 0 ((1-peakPosition)/2)| =
      sixCapacity := by
  have hc := peakPosition_bounds
  have he : 0 ≤ (1-peakPosition)/2 := by linarith
  constructor
  · simp only [sixCost, abs_of_nonneg he, abs_of_nonneg hc.1, abs_zero]
    ring
  · have hr : sixResponse ((1-peakPosition)/2) 0 peakPosition 0 ((1-peakPosition)/2) =
        sixCapacity := by unfold sixResponse separatedThree rainbowThree sixCapacity; ring
    rw [hr, abs_of_nonneg sixCapacity_nonneg]

theorem six_rational_witness :
    sixCost (1/3) 0 (1/3) 0 (1/3) = 1 ∧
    sixResponse (1/3) 0 (1/3) 0 (1/3) = 10/9 := by
  constructor
  · simp only [sixCost, abs_of_nonneg (show (0 : ℝ) ≤ 1/3 by positivity), abs_zero]
    ring
  · unfold sixResponse separatedThree rainbowThree
    ring

theorem sixCapacity_gt_one : 1 < sixCapacity := by
  have h := six_sharp_bound (1/3) 0 (1/3) 0 (1/3)
  rw [six_rational_witness.1, six_rational_witness.2,
    abs_of_nonneg (show (0 : ℝ) ≤ 10/9 by positivity)] at h
  nlinarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
