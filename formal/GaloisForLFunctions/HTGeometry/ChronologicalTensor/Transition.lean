import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Curvature

/-!
# Exact transition between concentrated and distributed optimal probes

The unit-capacity plateau for `A * separatedThree + rainbowThree`, with `A ≥ 0`,
ends exactly at `12 + 8 * sqrt 2`. The universal classification is stated with
the generated nonnegative coefficient `|A|`, so no assumption is exposed.
At the threshold a single central jump and a three-jump probe both maximize.
The critical optimality gap is a nonnegative mass times an explicit square.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def criticalWeight : ℝ := 12 + 8 * Real.sqrt 2

theorem criticalWeight_pos : 0 < criticalWeight := by
  unfold criticalWeight
  positivity

theorem critical_gap_identity (x y : ℝ) :
    (x+y)^3 - (criticalWeight/4*x*y^2 + (x+y)*x^2) =
      y*(Real.sqrt 2*x-y)^2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)
  unfold criticalWeight
  calc
    _ = y*(Real.sqrt 2*x-y)^2 + (2-(Real.sqrt 2)^2)*x^2*y := by ring
    _ = _ := by rw [h]; ring

theorem critical_equality_classification (x y : ℝ) :
    (x+y)^3 = criticalWeight/4*x*y^2 + (x+y)*x^2 ↔
      y = 0 ∨ y = Real.sqrt 2*x := by
  rw [← sub_eq_zero, critical_gap_identity, mul_eq_zero, sq_eq_zero_iff, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

theorem critical_cubic_bound (x y : ℝ) :
    criticalWeight/4* |x| * |y|^2 + (|x|+|y|)* |x|^2 ≤ (|x|+|y|)^3 := by
  have h := mul_nonneg (abs_nonneg y) (sq_nonneg (Real.sqrt 2* |x|-|y|))
  rw [← critical_gap_identity] at h
  linarith

theorem critical_sharp_bound (a b c d e : ℝ) :
    |weightedSixResponse criticalWeight 1 a b c d e| ≤ sixCost a b c d e ^ 3 := by
  have h := weightedSix_majorant criticalWeight 1 a b c d e
  rw [abs_of_pos criticalWeight_pos, abs_one, one_mul] at h
  have hc := critical_cubic_bound (|b|+|c|+|d|) (|a|+|e|)
  rw [abs_of_nonneg (show 0 ≤ |b|+|c|+|d| by positivity),
    abs_of_nonneg (show 0 ≤ |a|+|e| by positivity)] at hc
  have ht : |b|+|c|+|d|+(|a|+|e|) = sixCost a b c d e := by
    unfold sixCost; ring
  rw [ht] at hc
  exact h.trans hc

theorem critical_probe_cost :
    sixCost ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2) = 1 := by
  have he := arcEnd_bounds
  have hq : 0 ≤ arcEnd := by linarith
  have hp : 0 ≤ (1-arcEnd)/2 := by linarith
  simp only [sixCost, abs_of_nonneg hp, abs_of_nonneg hq, abs_zero]
  ring

theorem critical_probe_value :
    weightedSixResponse criticalWeight 1 ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2) = 1 := by
  have h := critical_gap_identity arcEnd (1-arcEnd)
  have hz : Real.sqrt 2*arcEnd - (1-arcEnd) = 0 := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)
    unfold arcEnd
    nlinarith
  rw [hz] at h
  unfold weightedSixResponse separatedThree rainbowThree
  nlinarith

theorem critical_two_maximizers :
    (sixCost 0 0 1 0 0 = 1 ∧ weightedSixResponse criticalWeight 1 0 0 1 0 0 = 1) ∧
    (sixCost ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2) = 1 ∧
      weightedSixResponse criticalWeight 1 ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2) = 1) ∧
    arcEnd ≠ 1 := by
  refine ⟨?_, ⟨critical_probe_cost, critical_probe_value⟩, ?_⟩
  · constructor <;> simp [sixCost, weightedSixResponse, separatedThree, rainbowThree]
  · have h := arcEnd_bounds.2
    linarith

theorem critical_weight_classification (A : ℝ) :
    (∀ a b c d e : ℝ,
      |weightedSixResponse |A| 1 a b c d e| ≤ sixCost a b c d e ^ 3) ↔
      |A| ≤ criticalWeight := by
  constructor
  · intro h
    have hp := h ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2)
    rw [critical_probe_cost, one_pow] at hp
    have he := arcEnd_bounds
    have hx : 0 < arcEnd*(1-arcEnd)^2/4 := by
      have hq : 0 < arcEnd := by linarith
      have hh : 0 < 1-arcEnd := by linarith
      positivity
    have hr := critical_probe_value
    have hab := le_abs_self (weightedSixResponse |A| 1 ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2))
    have hdiff : weightedSixResponse |A| 1 ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2) -
        weightedSixResponse criticalWeight 1 ((1-arcEnd)/2) 0 arcEnd 0 ((1-arcEnd)/2) =
          (|A|-criticalWeight)*(arcEnd*(1-arcEnd)^2/4) := by
      unfold weightedSixResponse separatedThree rainbowThree
      ring
    nlinarith
  · intro hA a b c d e
    have h := weightedSix_majorant |A| 1 a b c d e
    rw [abs_abs, abs_one, one_mul] at h
    have hc := critical_cubic_bound (|b|+|c|+|d|) (|a|+|e|)
    rw [abs_of_nonneg (show 0 ≤ |b|+|c|+|d| by positivity),
      abs_of_nonneg (show 0 ≤ |a|+|e| by positivity)] at hc
    have ht : |b|+|c|+|d|+(|a|+|e|) = sixCost a b c d e := by
      unfold sixCost; ring
    rw [ht] at hc
    have hm := mul_le_mul_of_nonneg_right hA
      (show 0 ≤ (|b|+|c|+|d|)*(|a|+|e|)^2/4 by positivity)
    nlinarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
