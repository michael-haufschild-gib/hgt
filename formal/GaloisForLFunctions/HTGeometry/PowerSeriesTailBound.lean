import GaloisForLFunctions.HTGeometry.LatticeTailSums

/-!
# The tail of a `p`-series at a real exponent

For `s > 1` the tail of `∑ (1+k)^{-s}` beyond a band of radius `J` is at most
`(1+J)^{1-s}/(s-1)`.  The proof is a telescoping comparison: Bernoulli's inequality for the real
power `s ≥ 1` gives

`(s-1)·(x+1)^{-s} ≤ x^{1-s} - (x+1)^{1-s}`   for `x ≥ 1`,

and summing the right side collapses.  This is the estimate that replaces the quadratic tail once
the amplitude decay exponent drops below one.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- The telescoping step for a real power above one. -/
theorem rpow_tail_step {s x : ℝ} (hs : 1 < s) (hx : 1 ≤ x) :
    (s - 1) * (x + 1) ^ (-s) ≤ x ^ (1 - s) - (x + 1) ^ (1 - s) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  set y : ℝ := (x + 1) / x with hy
  have hypos : (0 : ℝ) < y := by
    rw [hy]; positivity
  have hyx : (1 : ℝ) + 1 / x = y := by
    rw [hy]; field_simp
  have hber : 1 + s * (1 / x) ≤ y ^ s := by
    have hz : (-1 : ℝ) ≤ 1 / x := by
      have hpos : (0 : ℝ) ≤ 1 / x := by positivity
      linarith
    have h := one_add_mul_self_le_rpow_one_add hz (le_of_lt hs)
    rwa [hyx] at h
  have hsplit : y ^ (s - 1) = y ^ s / y := by
    rw [Real.rpow_sub hypos, Real.rpow_one]
  have hstep : (x + s) / (x + 1) ≤ y ^ (s - 1) := by
    rw [hsplit, le_div_iff₀ hypos]
    have hcalc : (x + s) / (x + 1) * y = 1 + s * (1 / x) := by
      rw [hy]; field_simp
    rw [hcalc]
    exact hber
  have hprod : (x + 1) ^ (1 - s) * (x + 1) ^ (s - 1) = 1 := by
    rw [← Real.rpow_add hx1]
    norm_num
  have hxy : x ^ (1 - s) = (x + 1) ^ (1 - s) * y ^ (s - 1) := by
    rw [hy, Real.div_rpow hx1.le hx0.le, ← mul_div_assoc, hprod,
      show (1 : ℝ) - s = -(s - 1) by ring, Real.rpow_neg hx0.le, one_div]
  have hpospow : (0 : ℝ) < (x + 1) ^ (1 - s) := Real.rpow_pos_of_pos hx1 _
  have hkey : (x + 1) ^ (1 - s) * ((x + s) / (x + 1) - 1)
      ≤ (x + 1) ^ (1 - s) * (y ^ (s - 1) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hstep]) hpospow.le
  have hrhs : (x + 1) ^ (1 - s) * (y ^ (s - 1) - 1) = x ^ (1 - s) - (x + 1) ^ (1 - s) := by
    rw [mul_sub, mul_one, ← hxy]
  have hlhs : (x + s) / (x + 1) - 1 = (s - 1) / (x + 1) := by
    field_simp
    ring
  have hlhs2 : (x + 1) ^ (1 - s) * ((s - 1) / (x + 1)) = (s - 1) * (x + 1) ^ (-s) := by
    rw [show (1 : ℝ) - s = -s + 1 by ring, Real.rpow_add hx1, Real.rpow_one]
    field_simp
  rw [hlhs, hlhs2] at hkey
  linarith [hkey, hrhs]

/-- The telescoped partial sums of the shifted tail. -/
theorem sum_shift_rpow_tail_le {s : ℝ} (hs : 1 < s) (J n : ℕ) :
    ∑ i ∈ Finset.range n, (((J : ℝ) + 1 + (i : ℝ)) + 1) ^ (-s)
      ≤ ((J : ℝ) + 1) ^ (1 - s) / (s - 1) := by
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hstep : ∀ i ∈ Finset.range n,
      (((J : ℝ) + 1 + (i : ℝ)) + 1) ^ (-s)
        ≤ ((((J : ℝ) + 1 + (i : ℝ)) ^ (1 - s)) - (((J : ℝ) + 1 + ((i : ℝ) + 1)) ^ (1 - s)))
            / (s - 1) := by
    intro i _
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hx : (1 : ℝ) ≤ (J : ℝ) + 1 + (i : ℝ) := by linarith
    have hbase := rpow_tail_step hs hx
    rw [le_div_iff₀ hs1]
    have heq : (J : ℝ) + 1 + ((i : ℝ) + 1) = ((J : ℝ) + 1 + (i : ℝ)) + 1 := by ring
    rw [heq]
    linarith [hbase]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_div]
  have htel := Finset.sum_range_sub' (fun i : ℕ => ((J : ℝ) + 1 + (i : ℝ)) ^ (1 - s)) n
  have htel' : ∑ i ∈ Finset.range n,
      ((((J : ℝ) + 1 + (i : ℝ)) ^ (1 - s)) - (((J : ℝ) + 1 + ((i : ℝ) + 1)) ^ (1 - s)))
      = ((J : ℝ) + 1 + ((0 : ℕ) : ℝ)) ^ (1 - s) - ((J : ℝ) + 1 + (n : ℝ)) ^ (1 - s) := by
    rw [← htel]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    push_cast
    ring
  rw [htel']
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfn : (0 : ℝ) ≤ ((J : ℝ) + 1 + (n : ℝ)) ^ (1 - s) :=
    Real.rpow_nonneg (by linarith) _
  have hzero : ((J : ℝ) + 1 + ((0 : ℕ) : ℝ)) = (J : ℝ) + 1 := by norm_num
  rw [hzero, div_le_div_iff₀ hs1 hs1]
  nlinarith [hfn, hs1]

/-- The `p`-series tail outside a band of radius `J`, over `ℕ`. -/
theorem tsum_nat_tail_rpow_le {s : ℝ} (hs : 1 < s) (J : ℕ) :
    ∑' k : ℕ, (if J < k then ENNReal.ofReal ((1 + (k : ℝ)) ^ (-s)) else 0)
      ≤ ENNReal.ofReal (((J : ℝ) + 1) ^ (1 - s) / (s - 1)) := by
  classical
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have hreal : ∑ k ∈ Finset.range n, (if J < k then ENNReal.ofReal ((1 + (k : ℝ)) ^ (-s)) else 0)
      = ENNReal.ofReal (∑ k ∈ Finset.range n,
          (if J < k then (1 + (k : ℝ)) ^ (-s) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : J < k
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk, ENNReal.ofReal_zero]
  rw [hreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hfilter : ∑ k ∈ Finset.range n, (if J < k then (1 + (k : ℝ)) ^ (-s) else 0)
      = ∑ k ∈ (Finset.range n).filter (fun k => J < k), (1 + (k : ℝ)) ^ (-s) := by
    rw [Finset.sum_filter]
  rw [hfilter]
  have hmap : (Finset.range n).filter (fun k => J < k)
      ⊆ (Finset.range n).image (fun i => J + 1 + i) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    refine Finset.mem_image.mpr ⟨k - J - 1, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  have hsub : ∑ k ∈ (Finset.range n).filter (fun k => J < k), (1 + (k : ℝ)) ^ (-s)
      ≤ ∑ k ∈ (Finset.range n).image (fun i => J + 1 + i), (1 + (k : ℝ)) ^ (-s) :=
    Finset.sum_le_sum_of_subset_of_nonneg hmap
      (fun k _ _ => Real.rpow_nonneg (by positivity) (-s))
  refine hsub.trans ?_
  rw [Finset.sum_image (by
    intro a _ b _ h
    simp only [add_right_inj] at h
    exact h)]
  have hcongr : ∀ i ∈ Finset.range n,
      (1 + ((J + 1 + i : ℕ) : ℝ)) ^ (-s) = (((J : ℝ) + 1 + (i : ℝ)) + 1) ^ (-s) := by
    intro i _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr]
  exact sum_shift_rpow_tail_le hs J n

/-- The `p`-series tail outside a band of radius `J`, over `ℤ`. -/
theorem tsum_int_tail_rpow_le {s : ℝ} (hs : 1 < s) (J : ℕ) :
    ∑' j : ℤ, (if J < j.natAbs then
        ENNReal.ofReal ((1 + (j.natAbs : ℝ)) ^ (-s)) else 0)
      ≤ ENNReal.ofReal (2 * (((J : ℝ) + 1) ^ (1 - s) / (s - 1))) := by
  have hstep := tsum_int_natAbs_le
    (fun k : ℕ => if J < k then ENNReal.ofReal ((1 + (k : ℝ)) ^ (-s)) else 0)
  refine hstep.trans ?_
  refine (mul_le_mul_right (tsum_nat_tail_rpow_le hs J) 2).trans (le_of_eq ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]

end GaloisForLFunctions
