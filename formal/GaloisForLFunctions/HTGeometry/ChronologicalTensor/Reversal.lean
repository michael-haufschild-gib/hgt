import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Curvature

/-!
# Reversal-sensitive chronological response

Each of the normalized separated and rainbow responses has capacity one.
Their difference has monotone capacity exactly one, but a probe reversing its
central increment attains absolute response `28/27` at unit variation cost.
This proves that replacing all signed gaps by monotone gaps can lose information
for a linear combination of diagrams. No signed optimum is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem separated_cubic_gap (x y : ℝ) :
    (x+y)^3 - (27/4 : ℝ)*x*y^2 = (x-y/2)^2*(x+4*y) := by ring

theorem normalized_separated_bound (a b c d e : ℝ) :
    |27*separatedThree a b c d e| ≤ sixCost a b c d e ^ 3 := by
  have h := weightedSix_majorant 27 0 a b c d e
  simp only [weightedSixResponse, zero_mul, add_zero, abs_zero,
    abs_of_nonneg (show (0 : ℝ) ≤ 27 by positivity)] at h
  let x := |b|+|c|+|d|
  let y := |a|+|e|
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hc := mul_nonneg (sq_nonneg (x-y/2)) (show 0 ≤ x+4*y by positivity)
  rw [← separated_cubic_gap] at hc
  have ht : x+y = sixCost a b c d e := by dsimp [x,y,sixCost]; ring
  rw [ht] at hc
  linarith

theorem rainbow_bound (a b c d e : ℝ) :
    |rainbowThree a b c d e| ≤ sixCost a b c d e ^ 3 := by
  have h := weightedSix_majorant 0 1 a b c d e
  simp only [weightedSixResponse, zero_mul, zero_add, one_mul, abs_zero, abs_one,
    zero_div] at h
  let t := sixCost a b c d e
  let x := |b|+|c|+|d|
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxt : x ≤ t := by dsimp [x,t,sixCost]; linarith [abs_nonneg a, abs_nonneg e]
  have ht : 0 ≤ t := hx.trans hxt
  have hh : t*x^2 ≤ t^3 := by
    nlinarith [mul_nonneg ht (sq_nonneg (t-x)),
      mul_nonneg (mul_nonneg ht hx) (sub_nonneg.mpr hxt)]
  exact h.trans hh

def reversalResponse (a b c d e : ℝ) : ℝ :=
  27*separatedThree a b c d e - rainbowThree a b c d e

theorem monotone_reversal_bound (a b c d e : ℝ) :
    |reversalResponse |a| |b| |c| |d| (|e|)| ≤ sixCost a b c d e ^ 3 := by
  have hd := normalized_separated_bound |a| |b| |c| |d| |e|
  have hr := rainbow_bound |a| |b| |c| |d| |e|
  have hd0 : 0 ≤ 27*separatedThree |a| |b| |c| |d| |e| := by
    unfold separatedThree; positivity
  have hr0 : 0 ≤ rainbowThree |a| |b| |c| |d| |e| := by
    unfold rainbowThree; positivity
  have he : sixCost |a| |b| |c| |d| |e| = sixCost a b c d e := by
    simp only [sixCost, abs_abs]
  rw [he, abs_of_nonneg hd0] at hd
  rw [he, abs_of_nonneg hr0] at hr
  unfold reversalResponse
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem monotone_reversal_attained :
    sixCost 0 0 1 0 0 = 1 ∧ |reversalResponse 0 0 1 0 0| = 1 := by
  constructor <;> simp [sixCost, reversalResponse, separatedThree, rainbowThree]

theorem reversal_advantage_witness :
    sixCost (1/3) 0 (-1/3) 0 (1/3) = 1 ∧
    reversalResponse (1/3) 0 (-1/3) 0 (1/3) = -28/27 ∧
    1 < |reversalResponse (1/3) 0 (-1/3) 0 (1/3)| := by
  have hv : reversalResponse (1/3) 0 (-1/3) 0 (1/3) = -28/27 := by
    unfold reversalResponse separatedThree rainbowThree; ring
  refine ⟨?_, hv, ?_⟩
  · simp only [sixCost, abs_of_nonneg (show (0 : ℝ) ≤ 1/3 by positivity),
      abs_of_nonpos (show (-1/3 : ℝ) ≤ 0 by linarith), abs_zero]
    ring
  · rw [hv, abs_of_nonpos (show (-28/27 : ℝ) ≤ 0 by linarith)]
    linarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
