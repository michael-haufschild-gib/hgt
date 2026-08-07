import Mathlib.Analysis.MeanInequalities

/-!
# Partial sums of a subunit real power

For `0 < a < 1` the telescoping bound

```text
a n^(a-1) ≤ n^a - (n-1)^a
```

holds by the weighted arithmetic-geometric mean inequality applied to `((n-1)/n, 1)` with weights
`(a, 1-a)`.  Summing gives

```text
∑_{n=1}^{M} n^(a-1) ≤ M^a / a.
```
-/

open Filter Topology
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- The concavity step: `a n^(a-1) ≤ n^a - (n-1)^a` for `0 < a < 1`. -/
theorem rpow_succ_sub_rpow_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    a * ((n : ℝ) + 1) ^ (a - 1) ≤ ((n : ℝ) + 1) ^ a - (n : ℝ) ^ a := by
  have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hu0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hmu : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1)) = (n : ℝ) :=
    mul_div_cancel₀ _ (ne_of_gt hm0)
  have hyoung : ((n : ℝ) / ((n : ℝ) + 1)) ^ a * (1 : ℝ) ^ (1 - a) ≤
      a * ((n : ℝ) / ((n : ℝ) + 1)) + (1 - a) * 1 :=
    Real.geom_mean_le_arith_mean2_weighted ha0.le (by linarith) hu0 zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at hyoung
  have hsplit : (((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1))) ^ a
      = ((n : ℝ) + 1) ^ a * ((n : ℝ) / ((n : ℝ) + 1)) ^ a := Real.mul_rpow hm0.le hu0
  rw [hmu] at hsplit
  have hma : (0 : ℝ) < ((n : ℝ) + 1) ^ a := Real.rpow_pos_of_pos hm0 a
  have hstep : a * (1 - (n : ℝ) / ((n : ℝ) + 1)) ≤ 1 - ((n : ℝ) / ((n : ℝ) + 1)) ^ a := by
    linarith
  have hkey := mul_le_mul_of_nonneg_left hstep hma.le
  have hone : (1 : ℝ) - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
    field_simp
    ring
  have hshift : ((n : ℝ) + 1) ^ (a - 1) = ((n : ℝ) + 1) ^ a / ((n : ℝ) + 1) := by
    rw [Real.rpow_sub hm0, Real.rpow_one]
  have hrhs : ((n : ℝ) + 1) ^ a * (1 - ((n : ℝ) / ((n : ℝ) + 1)) ^ a)
      = ((n : ℝ) + 1) ^ a - (n : ℝ) ^ a := by
    rw [mul_sub, mul_one, ← hsplit]
  rw [hone, hrhs] at hkey
  rw [hshift, show a * (((n : ℝ) + 1) ^ a / ((n : ℝ) + 1))
      = ((n : ℝ) + 1) ^ a * (a * (1 / ((n : ℝ) + 1))) by ring]
  exact hkey

/-- **The partial sums of `n^(a-1)` are bounded by `M^a / a`.** -/
theorem sum_rpow_sub_one_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (M : ℕ) :
    ∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (a - 1) ≤ (M : ℝ) ^ a / a := by
  have htel : ∑ n ∈ Finset.range M, (((n : ℝ) + 1) ^ a - (n : ℝ) ^ a) = (M : ℝ) ^ a := by
    have h := Finset.sum_range_sub (fun k : ℕ => ((k : ℕ) : ℝ) ^ a) M
    have hzero : ((0 : ℕ) : ℝ) ^ a = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (ne_of_gt ha0)]
    rw [hzero, sub_zero] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun n _ => by push_cast; ring
  have hstep : ∑ n ∈ Finset.range M, a * ((n : ℝ) + 1) ^ (a - 1) ≤
      ∑ n ∈ Finset.range M, (((n : ℝ) + 1) ^ a - (n : ℝ) ^ a) :=
    Finset.sum_le_sum fun n _ => rpow_succ_sub_rpow_ge ha0 ha1 n
  rw [htel, ← Finset.mul_sum] at hstep
  rw [le_div_iff₀ ha0]
  linarith [hstep]

end

end HTGeometry
