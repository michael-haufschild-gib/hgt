import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteRootEdge
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The largest Hermite zero at large degree

Summing the positive quotient recurrence over a terminal block gives a lower bound matching
the power-based upper bound. Two elementary order limits yield the sharp squared-edge scale.
-/

/-!
# The asymptotic Hermite edge

Summing the three-term recurrence over a terminal block of positive Hermite ratios gives
the lower bound. Together with the power upper bound it proves that the squared largest
zero divided by degree tends to four, without a spectral or Airy asymptotic input.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- Adjacent Hermite values at the largest zero of degree `N+1`. -/
def hermiteEdgeRatio (N j : ℕ) : ℝ :=
  (hermiteReal (j + 1)).eval (hermiteEdge N) / (hermiteReal j).eval (hermiteEdge N)

theorem hermiteEdgeRatio_pos {N j : ℕ} (hj : j < N) : 0 < hermiteEdgeRatio N j :=
  div_pos (hermite_eval_pos_at_edge (by omega)) (hermite_eval_pos_at_edge (by omega))

@[simp] theorem hermiteEdgeRatio_terminal (N : ℕ) : hermiteEdgeRatio N N = 0 := by
  simp only [hermiteEdgeRatio, hermiteEdge_isRoot, zero_div]

/-- The three-term recurrence expresses the edge through two adjacent positive ratios. -/
theorem hermiteEdgeRatio_recurrence {N j : ℕ} (hj : j < N) :
    hermiteEdge N = hermiteEdgeRatio N (j + 1) + (j + 1 : ℕ) / hermiteEdgeRatio N j := by
  have h0 : (hermiteReal j).eval (hermiteEdge N) ≠ 0 :=
    (hermite_eval_pos_at_edge (by omega : j ≤ N)).ne'
  have h1 : (hermiteReal (j + 1)).eval (hermiteEdge N) ≠ 0 :=
    (hermite_eval_pos_at_edge (by omega : j + 1 ≤ N)).ne'
  have hdiv : (j + 1 : ℕ) / hermiteEdgeRatio N j =
      (j + 1 : ℕ) * (hermiteReal j).eval (hermiteEdge N) /
        (hermiteReal (j + 1)).eval (hermiteEdge N) := by
    unfold hermiteEdgeRatio
    field_simp
  rw [hdiv, hermiteEdgeRatio, ← add_div, eq_div_iff h1]
  have hrec := eval_hermiteReal_add_two j (hermiteEdge N)
  push_cast
  linarith only [hrec]

private theorem sqrt_le_ratio_sum {a b r : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 < r) :
    2 * Real.sqrt a ≤ r + b / r := by
  apply (mul_le_mul_iff_of_pos_right hr).mp
  have hclear : (r + b / r) * r = r ^ 2 + b := by field_simp
  rw [hclear]
  nlinarith only [sq_nonneg (r - Real.sqrt a), Real.sq_sqrt ha, hab]

/-- A block of the quotient recurrence gives a uniform lower bound without a matrix model. -/
theorem hermiteEdge_block_lower (n k : ℕ) :
    2 * k * Real.sqrt (n + 2 : ℕ) ≤ (k + 1 : ℕ) * hermiteEdge (n + k + 1) := by
  have hrec : (k + 1 : ℕ) * hermiteEdge (n + k + 1) =
      ∑ i ∈ Finset.range (k + 1),
        (hermiteEdgeRatio (n + k + 1) (n + i + 1) +
          (n + i + 1 : ℕ) / hermiteEdgeRatio (n + k + 1) (n + i)) := by
    calc
      _ = ∑ _i ∈ Finset.range (k + 1), hermiteEdge (n + k + 1) := by simp
      _ = _ := Finset.sum_congr rfl fun i hi =>
        hermiteEdgeRatio_recurrence (by have := Finset.mem_range.mp hi; omega)
  have hqsum : (∑ i ∈ Finset.range (k + 1), hermiteEdgeRatio (n + k + 1) (n + i + 1)) =
      ∑ i ∈ Finset.range k, hermiteEdgeRatio (n + k + 1) (n + i + 1) := by
    rw [Finset.sum_range_succ, hermiteEdgeRatio_terminal, add_zero]
  have hfsum : (∑ i ∈ Finset.range (k + 1),
      (n + i + 1 : ℕ) / hermiteEdgeRatio (n + k + 1) (n + i)) =
      (∑ i ∈ Finset.range k,
        (n + i + 2 : ℕ) / hermiteEdgeRatio (n + k + 1) (n + i + 1)) +
        (n + 1 : ℕ) / hermiteEdgeRatio (n + k + 1) n := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_assoc, Nat.add_zero]
  rw [Finset.sum_add_distrib, hqsum, hfsum, ← add_assoc, ← Finset.sum_add_distrib] at hrec
  have hterm : ∀ i ∈ Finset.range k, 2 * Real.sqrt (n + 2 : ℕ) ≤
      hermiteEdgeRatio (n + k + 1) (n + i + 1) +
        (n + i + 2 : ℕ) / hermiteEdgeRatio (n + k + 1) (n + i + 1) := by
    intro i hi
    apply sqrt_le_ratio_sum (by positivity)
    · exact_mod_cast (show n + 2 ≤ n + i + 2 by omega)
    · apply hermiteEdgeRatio_pos
      have := Finset.mem_range.mp hi
      omega
  calc
    2 * k * Real.sqrt (n + 2 : ℕ) = ∑ _i ∈ Finset.range k, 2 * Real.sqrt (n + 2 : ℕ) := by
      simp
      ring
    _ ≤ ∑ i ∈ Finset.range k,
        (hermiteEdgeRatio (n + k + 1) (n + i + 1) +
          (n + i + 2 : ℕ) / hermiteEdgeRatio (n + k + 1) (n + i + 1)) :=
      Finset.sum_le_sum hterm
    _ ≤ _ := by
      rw [hrec]
      exact le_add_of_nonneg_right (div_nonneg (by positivity)
        (hermiteEdgeRatio_pos (by omega : n < n + k + 1)).le)

/-- Squaring the block bound retains its exact degree and block-length dependence. -/
theorem hermiteEdge_block_sq_lower (n k : ℕ) :
    4 * (k : ℝ) ^ 2 * (n + 2 : ℕ) ≤ (k + 1 : ℕ) ^ 2 * hermiteEdge (n + k + 1) ^ 2 := by
  have h := mul_self_le_mul_self (by positivity : 0 ≤ 2 * (k : ℝ) * Real.sqrt (n + 2 : ℕ))
    (hermiteEdge_block_lower n k)
  calc
    _ = (2 * (k : ℝ) * Real.sqrt (n + 2 : ℕ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    _ ≤ _ := by simpa only [← pow_two, mul_pow] using h

private def edgeBlockConstant (k : ℕ) : ℝ := 4 * ((k : ℝ) / (k + 1)) ^ 2

private theorem edgeBlockConstant_mul_le (n k : ℕ) :
    edgeBlockConstant k * n ≤ hermiteEdge (n + k + 1) ^ 2 := by
  have hk : 0 < (k + 1 : ℝ) ^ 2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hk).mp
  have hc : edgeBlockConstant k * n * (k + 1 : ℝ) ^ 2 = 4 * (k : ℝ) ^ 2 * n := by
    unfold edgeBlockConstant
    field_simp
  rw [hc, mul_comm (hermiteEdge _ ^ 2)]
  have h := hermiteEdge_block_sq_lower n k
  push_cast at h
  exact (mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) ≤ n + 2) (by positivity)).trans h

private theorem edge_ratio_lower (k j : ℕ) (hj : k + 1 ≤ j) :
    edgeBlockConstant k * (((k : ℝ) + 2) * ((j : ℝ) / (j + 1)) - (k + 1)) ≤
      hermiteEdge j ^ 2 / (j + 1 : ℝ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = n + k + 1 := ⟨j - (k + 1), by omega⟩
  subst j
  have h := div_le_div_of_nonneg_right (edgeBlockConstant_mul_le n k)
    (show (0 : ℝ) ≤ (n + k + 1 : ℕ) + 1 by positivity)
  have hden : ((n + k + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  convert h using 1
  push_cast
  field_simp
  ring

private theorem edge_ratio_upper (j : ℕ) : hermiteEdge j ^ 2 / (j + 1 : ℝ) < 4 := by
  have h := hermiteEdge_lt_two_sqrt j
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (j + 1 : ℕ) by positivity)
  have hsq := mul_self_lt_mul_self (hermiteEdge_nonneg j) h
  apply (div_lt_iff₀ (show 0 < (j + 1 : ℝ) by positivity)).mpr
  push_cast at hs hsq
  nlinarith only [hsq, hs]

/-- The largest probabilists' Hermite zero has squared size asymptotic to four times its degree. -/
theorem tendsto_hermiteEdge_sq_div_degree :
    Tendsto (fun j : ℕ => hermiteEdge j ^ 2 / (j + 1 : ℝ)) atTop (𝓝 4) := by
  have hbase := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hconst : Tendsto edgeBlockConstant atTop (𝓝 4) := by
    simpa only [edgeBlockConstant, one_pow, mul_one] using (hbase.pow 2).const_mul 4
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hconst.eventually_const_lt ha).exists
    have hlow : Tendsto (fun j : ℕ => edgeBlockConstant k *
        (((k : ℝ) + 2) * ((j : ℝ) / (j + 1)) - (k + 1))) atTop (𝓝 (edgeBlockConstant k)) := by
      convert ((hbase.const_mul ((k : ℝ) + 2)).sub_const (k + 1)).const_mul (edgeBlockConstant k) using 1
      congr 1
      ring
    filter_upwards [hlow.eventually_const_lt hk, eventually_ge_atTop (k + 1)] with j hja hj
    exact hja.trans_le (edge_ratio_lower k j hj)
  · intro b hb
    exact Eventually.of_forall fun j => (edge_ratio_upper j).trans hb

/-- The derivative edge has the same asymptotic when divided by the original polynomial degree. -/
theorem tendsto_hermiteEdge_sq_div_successor_degree :
    Tendsto (fun j : ℕ => hermiteEdge j ^ 2 / (j + 2 : ℝ)) atTop (𝓝 4) := by
  have hshift : Tendsto (fun j : ℕ => j + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with j hj
    omega
  have hr : Tendsto (fun j : ℕ => ((j : ℝ) + 1) / (j + 2)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      using (tendsto_natCast_div_add_atTop (1 : ℝ)).comp hshift
  have hp := tendsto_hermiteEdge_sq_div_degree.mul hr
  rw [mul_one] at hp
  refine hp.congr fun j => ?_
  have hden : (j + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The extremizing degree `2m+4` uses the derivative edge of degree `2m+3`. -/
theorem tendsto_even_hermiteEdge_sq_div_degree :
    Tendsto (fun m : ℕ => hermiteEdge (2 * m + 2) ^ 2 / (2 * m + 4 : ℝ)) atTop (𝓝 4) := by
  have hmap : Tendsto (fun m : ℕ => 2 * m + 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with m hm
    omega
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc]
    using tendsto_hermiteEdge_sq_div_successor_degree.comp hmap

/-- In degree `2d`, the squared largest zero of `He_(2d-1)` divided by `2d` tends to four. -/
theorem tendsto_hermiteDerivativeEdge_sq_div_even_degree :
    Tendsto (fun d : ℕ => hermiteEdge (2 * d - 2) ^ 2 / (2 * d : ℝ)) atTop (𝓝 4) := by
  have hmap : Tendsto (fun d : ℕ => 2 * d - 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N + 2)] with d hd
    omega
  apply (tendsto_hermiteEdge_sq_div_successor_degree.comp hmap).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with d hd
  simp only [Function.comp_apply, Nat.cast_sub (by omega : 2 ≤ 2 * d),
    Nat.cast_mul, Nat.cast_ofNat, sub_add_cancel]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
