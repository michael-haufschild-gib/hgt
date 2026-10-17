import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage

open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι : Type*}

/-- A two-coordinate support inequality, with no sign restrictions. -/
theorem origin_pair_support (W A a q : ℝ) :
    W * a + A * q ≤ Real.sqrt (W ^ 2 + A ^ 2) * Real.sqrt (a ^ 2 + q ^ 2) := by
  have h := sphere_weighted_sum_le_sqrt_mul ({()} : Finset Unit) W
    (fun _ => A) (fun _ => q) a (Real.sqrt (a ^ 2 + q ^ 2))
    (Real.sqrt_nonneg _) (by simp [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg q))])
  simpa using h

/-- The exact lower bound for the sum of signed-chain sphere penalties. -/
theorem origin_allocation_cost_lower (s : Finset ι) (a q : ι → ℝ) :
    Real.sqrt ((∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, q i) ^ 2) ≤
      ∑ i ∈ s, Real.sqrt (a i ^ 2 + q i ^ 2) := by
  set W := ∑ i ∈ s, a i
  set A := ∑ i ∈ s, q i
  set S := Real.sqrt (W ^ 2 + A ^ 2)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = W ^ 2 + A ^ 2 := Real.sq_sqrt (by positivity)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ s) => origin_pair_support W A (a i) (q i))
  have heq : (∑ i ∈ s, (W * a i + A * q i)) = W ^ 2 + A ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    dsimp [W, A]
    ring
  rw [heq, ← Finset.mul_sum] at hsum
  change W ^ 2 + A ^ 2 ≤ S * _ at hsum
  rcases eq_or_lt_of_le hS with hz | hp
  · rw [← hz]
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  · apply le_of_mul_le_mul_left (a := S) _ hp
    nlinarith only [hsum, hSsq]

/-- Proportional origin allocation attains the triangle lower bound. -/
theorem origin_allocation_proportional_cost (s : Finset ι) (W : ℝ) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hQ : (∑ i ∈ s, q i) ≠ 0) :
    (∑ i ∈ s, Real.sqrt ((W * (q i / ∑ k ∈ s, q k)) ^ 2 + q i ^ 2)) =
      Real.sqrt (W ^ 2 + (∑ i ∈ s, q i) ^ 2) := by
  set Q := ∑ i ∈ s, q i
  have hQpos : 0 < Q := lt_of_le_of_ne (Finset.sum_nonneg hq) (Ne.symm hQ)
  have hterm (i : ι) (hi : i ∈ s) :
      Real.sqrt ((W * (q i / Q)) ^ 2 + q i ^ 2) =
        q i / Q * Real.sqrt (W ^ 2 + Q ^ 2) := by
    have heq : (W * (q i / Q)) ^ 2 + q i ^ 2 = (q i / Q) ^ 2 * (W ^ 2 + Q ^ 2) := by
      field_simp
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (hq i hi) hQpos.le)]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_div]
  change Q / Q * _ = _
  rw [div_self hQ, one_mul]

/-- The proportional origin allocations use exactly the available origin density. -/
theorem origin_allocation_proportional_sum (s : Finset ι) (W : ℝ) (q : ι → ℝ)
    (hQ : (∑ i ∈ s, q i) ≠ 0) :
    (∑ i ∈ s, W * (q i / ∑ k ∈ s, q k)) = W := by
  rw [← Finset.mul_sum, ← Finset.sum_div, div_self hQ, mul_one]

/-- A probability allocation matched to block sizes, with a fixed zero-mass fallback. -/
def originAllocationShare (n : ℕ) (q : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  if (∑ k, |q k|) = 0 then (if i = 0 then 1 else 0) else |q i| / ∑ k, |q k|

/-- The canonical allocation is a probability vector, including vanishing blocks. -/
theorem originAllocationShare_probability (n : ℕ) (q : Fin (n + 1) → ℝ) :
    (∑ i, originAllocationShare n q i) = 1 ∧ ∀ i, 0 ≤ originAllocationShare n q i := by
  classical
  by_cases hQ : (∑ k, |q k|) = 0
  · constructor
    · simp [originAllocationShare, hQ]
    · intro i
      simp only [originAllocationShare, hQ, ↓reduceIte]
      split_ifs <;> norm_num
  · constructor
    · simp only [originAllocationShare, hQ, ↓reduceIte]
      rw [← Finset.sum_div, div_self hQ]
    · intro i
      simp only [originAllocationShare, hQ, ↓reduceIte]
      exact div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg _)

/-- Canonical origin allocation attains the optimal cost for every block vector,
including the case in which all blocks vanish. -/
theorem originAllocationShare_cost (n : ℕ) (W : ℝ) (q : Fin (n + 1) → ℝ) :
    (∑ i, Real.sqrt ((W * originAllocationShare n q i) ^ 2 + q i ^ 2)) =
      Real.sqrt (W ^ 2 + (∑ i, |q i|) ^ 2) := by
  classical
  by_cases hQ : (∑ k, |q k|) = 0
  · have hzero : ∀ i, q i = 0 := by
      intro i
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun k => |q k|) (fun k _ => abs_nonneg (q k)) (Finset.mem_univ i)
      rw [hQ] at hi
      exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
    rw [Finset.sum_eq_single 0]
    · simp [originAllocationShare, hzero]
    · intro i _ hi
      simp [originAllocationShare, hzero, hi]
    · simp
  · simp only [originAllocationShare, hQ, ↓reduceIte]
    simpa only [sq_abs] using origin_allocation_proportional_cost Finset.univ W
      (fun i => |q i|) (fun i _ => abs_nonneg _) hQ

/-- Exact, attained minimum over all origin allocations of a prescribed total.
The canonical shares are nonnegative even when some or all block sizes vanish. -/
theorem origin_allocation_exact_minimum (n : ℕ) (W : ℝ) (q : Fin (n + 1) → ℝ) :
    (∑ i, W * originAllocationShare n q i) = W ∧
    (∑ i, Real.sqrt ((W * originAllocationShare n q i) ^ 2 + q i ^ 2)) =
      Real.sqrt (W ^ 2 + (∑ i, |q i|) ^ 2) ∧
    ∀ a : Fin (n + 1) → ℝ, (∑ i, a i) = W →
      Real.sqrt (W ^ 2 + (∑ i, |q i|) ^ 2) ≤
        ∑ i, Real.sqrt (a i ^ 2 + q i ^ 2) := by
  refine ⟨?_, originAllocationShare_cost n W q, ?_⟩
  · rw [← Finset.mul_sum, (originAllocationShare_probability n q).1, mul_one]
  · intro a ha
    simpa only [ha, sq_abs] using
      origin_allocation_cost_lower Finset.univ a (fun i => |q i|)

end
end GaloisForLFunctions.BiScaleUncertainty
