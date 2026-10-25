import GaloisForLFunctions.BiarithmeticGeometry.IntrinsicGoldenSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Uniform critical energy of intrinsic point kernels

The centered point kernel cancels the exponential part of the actual
golden cumulative count. Its remaining affine tail has a uniform bound,
while the finite initial segment costs the same inverse norm. Their
weighted square sums give the critical point-kernel energy estimate.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The actual cumulative counting response of a point kernel, centered by its inverse norm. -/
def goldenIntrinsicPointReceiver (r M : ℕ) : ℝ :=
  (if r ≤ M then goldenIntrinsicCount (M - r) else 0) -
    ((5 : ℝ) ^ r)⁻¹ * goldenIntrinsicCount M

/-- The exact affine tail after cancellation of the exponential counting term. -/
theorem goldenIntrinsicPointReceiver_tail (r s : ℕ) :
    goldenIntrinsicPointReceiver r (s + r) =
      -(1 / 4 : ℝ) * (1 - ((5 : ℝ) ^ r)⁻¹) * s +
        (1 / 4 : ℝ) * r * ((5 : ℝ) ^ r)⁻¹ +
        (11 / 16 : ℝ) * (1 - ((5 : ℝ) ^ r)⁻¹) := by
  rw [goldenIntrinsicPointReceiver, if_pos (by omega : r ≤ s + r), Nat.add_sub_cancel,
    goldenIntrinsicCount_eq, goldenIntrinsicCount_eq, pow_add, Nat.cast_add]
  field_simp [pow_ne_zero r (by norm_num : (5 : ℝ) ≠ 0)]
  ring

private theorem intrinsic_point_weight_bounds (r : ℕ) :
    0 ≤ ((5 : ℝ) ^ r)⁻¹ ∧ ((5 : ℝ) ^ r)⁻¹ ≤ 1 ∧
      (r : ℝ) * ((5 : ℝ) ^ r)⁻¹ ≤ 1 := by
  have hp : (r : ℝ) + 1 ≤ (5 : ℝ) ^ r := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith only [ih, Nat.cast_nonneg (α := ℝ) r]
  have hp0 : 0 < (5 : ℝ) ^ r := pow_pos (by norm_num) r
  refine ⟨inv_nonneg.mpr hp0.le, ?_, ?_⟩
  · rw [inv_le_one₀ hp0]
    linarith only [hp, Nat.cast_nonneg (α := ℝ) r]
  · rw [← div_eq_mul_inv, div_le_one hp0]
    linarith only [hp]

/-- The affine tail bound is uniform in the norm of the point kernel. -/
theorem abs_goldenIntrinsicPointReceiver_tail_le (r s : ℕ) :
    |goldenIntrinsicPointReceiver r (s + r)| ≤ (s : ℝ) + 1 := by
  obtain ⟨hw0, hw1, hrw⟩ := intrinsic_point_weight_bounds r
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hslo : 0 ≤ (1 - ((5 : ℝ) ^ r)⁻¹) * (s : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hw1) hs0
  have hshi : (1 - ((5 : ℝ) ^ r)⁻¹) * (s : ℝ) ≤ s := by
    nlinarith only [mul_nonneg hw0 hs0]
  have hr0 : 0 ≤ (r : ℝ) * ((5 : ℝ) ^ r)⁻¹ := mul_nonneg (Nat.cast_nonneg r) hw0
  rw [goldenIntrinsicPointReceiver_tail, abs_le]
  constructor <;> nlinarith only [hw0, hw1, hrw, hs0, hslo, hshi, hr0]

private theorem square_succ_le_four_pow (s : ℕ) : ((s : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ (4 : ℝ) s]
    have hstep : ((s : ℝ) + 1 + 1) ^ 2 ≤ 4 * ((s : ℝ) + 1) ^ 2 := by
      nlinarith only [sq_nonneg (s : ℝ), Nat.cast_nonneg (α := ℝ) s]
    nlinarith only [hstep, ih]

private theorem goldenIntrinsicPointReceiver_tail_energy_le (r s : ℕ) :
    goldenIntrinsicPointReceiver r (s + r) ^ 2 / (5 : ℝ) ^ (s + r) ≤
      ((5 : ℝ) ^ r)⁻¹ * (4 / 5 : ℝ) ^ s := by
  have hsq : goldenIntrinsicPointReceiver r (s + r) ^ 2 ≤ (4 : ℝ) ^ s := by
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (abs_goldenIntrinsicPointReceiver_tail_le r s) 2
    rw [sq_abs] at h
    exact h.trans (square_succ_le_four_pow s)
  calc
    _ ≤ (4 : ℝ) ^ s / (5 : ℝ) ^ (s + r) :=
      div_le_div_of_nonneg_right hsq (pow_nonneg (by norm_num) _)
    _ = _ := by rw [pow_add, div_pow]; field_simp

private theorem summable_goldenIntrinsicPointReceiver_tail_energy (r : ℕ) :
    Summable (fun s : ℕ => goldenIntrinsicPointReceiver r (s + r) ^ 2 / (5 : ℝ) ^ (s + r)) :=
  ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 1)).mul_left (((5 : ℝ) ^ r)⁻¹)).of_nonneg_of_le
      (fun s => by positivity) (goldenIntrinsicPointReceiver_tail_energy_le r)

/-- Every centered intrinsic point kernel has finite total shell square energy. -/
theorem summable_goldenIntrinsicPointReceiver_energy (r : ℕ) :
    Summable (fun M : ℕ => goldenIntrinsicPointReceiver r M ^ 2 / (5 : ℝ) ^ M) :=
  (summable_nat_add_iff r).mp (summable_goldenIntrinsicPointReceiver_tail_energy r)

private theorem goldenIntrinsicPointReceiver_head_energy_le (r : ℕ) :
    (∑ M ∈ range r, goldenIntrinsicPointReceiver r M ^ 2 / (5 : ℝ) ^ M) ≤
      ((5 : ℝ) ^ r)⁻¹ / 4 := by
  have hmajor : (∑ M ∈ range r, goldenIntrinsicPointReceiver r M ^ 2 / (5 : ℝ) ^ M) ≤
      (((5 : ℝ) ^ r)⁻¹) ^ 2 * ∑ M ∈ range r, (5 : ℝ) ^ M := by
    rw [mul_sum]
    apply sum_le_sum
    intro M hM
    rw [goldenIntrinsicPointReceiver, if_neg (by have := mem_range.mp hM; omega),
      zero_sub, neg_sq, mul_pow]
    have hcount := pow_le_pow_left₀ (goldenIntrinsicCount_bounds M).1
      (goldenIntrinsicCount_bounds M).2 2
    calc
      _ ≤ (((5 : ℝ) ^ r)⁻¹) ^ 2 * ((5 : ℝ) ^ M) ^ 2 / (5 : ℝ) ^ M :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcount (sq_nonneg _)) (pow_nonneg (by norm_num) _)
      _ = _ := by field_simp
  have hgeom : (4 : ℝ) * (∑ M ∈ range r, (5 : ℝ) ^ M) = (5 : ℝ) ^ r - 1 := by
    clear hmajor
    induction r with
    | zero => simp only [range_zero, sum_empty, mul_zero, pow_zero, sub_self]
    | succ r ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith only [ih]
  have hsum : (∑ M ∈ range r, (5 : ℝ) ^ M) = ((5 : ℝ) ^ r - 1) / 4 := by
    linarith only [hgeom]
  have he : (((5 : ℝ) ^ r)⁻¹) ^ 2 * (∑ M ∈ range r, (5 : ℝ) ^ M) =
      (((5 : ℝ) ^ r)⁻¹ - (((5 : ℝ) ^ r)⁻¹) ^ 2) / 4 := by
    rw [hsum]
    field_simp [pow_ne_zero r (by norm_num : (5 : ℝ) ≠ 0)]
  rw [he] at hmajor
  nlinarith only [hmajor, sq_nonneg (((5 : ℝ) ^ r)⁻¹)]

/-- The actual intrinsic point-kernel energy is uniformly bounded by six times its inverse norm. -/
theorem tsum_goldenIntrinsicPointReceiver_energy_le (r : ℕ) :
    (∑' M : ℕ, goldenIntrinsicPointReceiver r M ^ 2 / (5 : ℝ) ^ M) ≤
      6 * ((5 : ℝ) ^ r)⁻¹ := by
  have hmajor : Summable (fun s : ℕ => ((5 : ℝ) ^ r)⁻¹ * (4 / 5 : ℝ) ^ s) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by norm_num : (4 / 5 : ℝ) < 1)).mul_left _
  have htail := (summable_goldenIntrinsicPointReceiver_tail_energy r).tsum_le_tsum
    (goldenIntrinsicPointReceiver_tail_energy_le r) hmajor
  have hgeom : (∑' s : ℕ, (4 / 5 : ℝ) ^ s) = 5 := by
    rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by norm_num : (4 / 5 : ℝ) < 1)]
    norm_num
  rw [tsum_mul_left, hgeom] at htail
  rw [← (summable_goldenIntrinsicPointReceiver_energy r).sum_add_tsum_nat_add r]
  have hhead := goldenIntrinsicPointReceiver_head_energy_le r
  have hw0 := (intrinsic_point_weight_bounds r).1
  linarith only [hhead, htail, hw0]

end GaloisForLFunctions.BiarithmeticGeometry

