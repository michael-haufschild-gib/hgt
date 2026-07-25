import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric amplitude dominance

A point at distance `sqrt (p^2 + q^2)` from the origin outgrows one at distance `p` under repeated
powering, whenever `q <> 0`.  Consequently a family of bounds `m * sqrt(p^2+q^2)^n <= K * p^n`,
holding for every `n`, forces `q = 0`.

This is the entire detection mechanism of the real-variable route: at a fixed height `p`, an
off-critical copy sits strictly further from the origin than a critical one, and powering separates
them.
-/

open Filter

namespace HTGeometry

theorem not_forall_mul_pow_le {c m K : ℝ} (hc : 1 < c) (hm : 0 < m)
    (h : ∀ n : ℕ, m * c ^ n ≤ K) : False := by
  have htend : Tendsto (fun n : ℕ => m * c ^ n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hm (tendsto_pow_atTop_atTop_of_one_lt hc)
  obtain ⟨n, hn⟩ := (htend.eventually_ge_atTop (K + 1)).exists
  linarith [h n]

theorem lt_sqrt_sq_add_sq {p q : ℝ} (hp : 0 < p) (hq : q ≠ 0) :
    p < Real.sqrt (p ^ 2 + q ^ 2) := by
  have hq2 : 0 < q ^ 2 := lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 hq))
  have hlt : p ^ 2 < p ^ 2 + q ^ 2 := by linarith
  calc p = Real.sqrt (p ^ 2) := (Real.sqrt_sq hp.le).symm
    _ < Real.sqrt (p ^ 2 + q ^ 2) := by
        exact Real.sqrt_lt_sqrt (by positivity) hlt

/-- **Two-base dominance.**  A geometric sequence of ratio `c` cannot be bounded by one of strictly
smaller ratio `d`, whatever the constants. -/
theorem not_forall_mul_pow_le_pow {c d m K : ℝ} (hd : 0 ≤ d) (hdc : d < c) (hm : 0 < m)
    (h : ∀ n : ℕ, m * c ^ n ≤ K * d ^ n) : False := by
  have hc : 0 < c := lt_of_le_of_lt hd hdc
  have htend : Tendsto (fun n : ℕ => K * (d / c) ^ n) atTop (nhds 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd hc.le)
      ((div_lt_one hc).mpr hdc)
    simpa using hbase.const_mul K
  have hle : ∀ n : ℕ, m ≤ K * (d / c) ^ n := by
    intro n
    have hcn : (0 : ℝ) < c ^ n := pow_pos hc n
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hcn]
    exact h n
  have hzero : m ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hle)
  linarith

/-- **Amplitude dominance.**  If a positive multiple of `sqrt(p^2+q^2)^n` stays below a fixed
multiple of `p^n` for every `n`, the displacement `q` vanishes. -/
theorem eq_zero_of_forall_mul_pow_le {p q m K : ℝ} (hp : 0 < p) (hm : 0 < m)
    (h : ∀ n : ℕ, m * Real.sqrt (p ^ 2 + q ^ 2) ^ n ≤ K * p ^ n) : q = 0 := by
  by_contra hq
  have hlt := lt_sqrt_sq_add_sq hp hq
  have hc : 1 < Real.sqrt (p ^ 2 + q ^ 2) / p := (one_lt_div hp).mpr hlt
  refine not_forall_mul_pow_le hc hm (K := K) ?_
  intro n
  have hpn : (0 : ℝ) < p ^ n := pow_pos hp n
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ hpn]
  exact h n

end HTGeometry
