import Mathlib

/-!
# Rationality of the negative-order polylogarithm values

For `|r| < 1` put

```text
R_m(r) = ∑_{i ≥ 0} i^m r^i .
```

Then `R_0(r) = (1-r)^{-1}` and, for `m ≥ 1`, the binomial shift gives the recurrence

```text
(1 - r) R_m(r) = r · ∑_{t < m} C(m,t) R_t(r).
```

Consequently every `R_m(r)` is a rational function of `r` with rational coefficients, and in
particular `R_m(q)` is **rational** for every rational `q` with `|q| < 1`.  This is the elementary
fact behind the rationality of the Dirichlet densities and prime-log coefficients in the
γ-affine structure of the generalized Stieltjes constants.
-/

open Finset Filter Topology

namespace RHTower

noncomputable section

/-- The `m`-th geometric moment `R_m(r) = ∑_{i ≥ 0} i^m r^i`. -/
def geomMoment (r : ℝ) (m : ℕ) : ℝ := ∑' i : ℕ, (i : ℝ) ^ m * r ^ i

theorem summable_geomMomentTerm {r : ℝ} (hr : |r| < 1) (m : ℕ) :
    Summable (fun i : ℕ => (i : ℝ) ^ m * r ^ i) := by
  refine summable_pow_mul_geometric_of_norm_lt_one m ?_
  rwa [Real.norm_eq_abs]

theorem geomMoment_zero {r : ℝ} (hr : |r| < 1) : geomMoment r 0 = (1 - r)⁻¹ := by
  rw [geomMoment]
  simp only [pow_zero, one_mul]
  exact tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])

/-- **The binomial shift recurrence.** -/
theorem geomMoment_recurrence {r : ℝ} (hr : |r| < 1) {m : ℕ} (hm : 1 ≤ m) :
    (1 - r) * geomMoment r m = r * ∑ t ∈ Finset.range m, (m.choose t : ℝ) * geomMoment r t := by
  have hsum := summable_geomMomentTerm hr m
  have hzero : ((0 : ℕ) : ℝ) ^ m = 0 := by
    rw [Nat.cast_zero]
    exact zero_pow (by omega)
  have hshift : geomMoment r m
      = ∑' i : ℕ, r * ((∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * (i : ℝ) ^ t) * r ^ i) := by
    rw [geomMoment, hsum.tsum_eq_zero_add, hzero, zero_mul, zero_add]
    refine tsum_congr fun i => ?_
    have hbin : (((i : ℕ) : ℝ) + 1) ^ m
        = ∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * (i : ℝ) ^ t := by
      rw [add_pow]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [one_pow, mul_one]
      ring
    push_cast
    rw [hbin, pow_succ]
    ring
  have hswap : (∑' i : ℕ, r * ((∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * (i : ℝ) ^ t)
        * r ^ i))
      = r * ∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * geomMoment r t := by
    rw [tsum_mul_left]
    congr 1
    have hrw : ∀ i : ℕ, (∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * (i : ℝ) ^ t) * r ^ i
        = ∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * ((i : ℝ) ^ t * r ^ i) := by
      intro i
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [show (fun i : ℕ => (∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * (i : ℝ) ^ t) * r ^ i)
        = fun i : ℕ => ∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * ((i : ℝ) ^ t * r ^ i)
      from funext hrw]
    rw [Summable.tsum_finsetSum (fun t _ => (summable_geomMomentTerm hr t).mul_left _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [tsum_mul_left, geomMoment]
  have hkey : geomMoment r m
      = r * ((∑ t ∈ Finset.range m, (m.choose t : ℝ) * geomMoment r t) + geomMoment r m) := by
    conv_lhs => rw [hshift, hswap, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
  linear_combination hkey

theorem exists_rat_geomMoment_le {q : ℚ} (hq : |(q : ℝ)| < 1) :
    ∀ m : ℕ, ∃ c : ℕ → ℚ, ∀ t ≤ m, geomMoment (q : ℝ) t = (c t : ℝ) := by
  have hqlt := abs_lt.mp hq
  have hne : (1 : ℝ) - (q : ℝ) ≠ 0 := by
    intro h
    have hq1 : (q : ℝ) = 1 := by linarith
    linarith [hqlt.2]
  have hneQ : (1 : ℚ) - q ≠ 0 := by
    intro h
    apply hne
    have : ((1 - q : ℚ) : ℝ) = 0 := by rw [h]; norm_num
    push_cast at this
    linarith
  intro m
  induction m with
  | zero =>
    refine ⟨fun _ => 1 / (1 - q), fun t ht => ?_⟩
    have ht0 : t = 0 := by omega
    subst ht0
    rw [geomMoment_zero hq]
    push_cast
    rw [one_div]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨Function.update c (n + 1)
      (q / (1 - q) * ∑ t ∈ Finset.range (n + 1), ((n + 1).choose t : ℚ) * c t), ?_⟩
    intro t ht
    rcases Nat.lt_or_ge t (n + 1) with h | h
    · rw [Function.update_of_ne (by omega)]
      exact hc t (by omega)
    · have htn : t = n + 1 := by omega
      subst htn
      rw [Function.update_self]
      have hrec := geomMoment_recurrence hq (m := n + 1) (by omega)
      have hvals : ∀ t ∈ Finset.range (n + 1),
          ((n + 1).choose t : ℝ) * geomMoment (q : ℝ) t
            = (((n + 1).choose t : ℚ) * c t : ℚ) := by
        intro t ht'
        rw [hc t (by have := Finset.mem_range.mp ht'; omega : t ≤ n)]
        push_cast
        ring
      rw [Finset.sum_congr rfl hvals] at hrec
      rw [← Rat.cast_sum] at hrec
      have hsolve : geomMoment (q : ℝ) (n + 1)
          = (q : ℝ) / (1 - (q : ℝ)) *
            ((∑ t ∈ Finset.range (n + 1), ((n + 1).choose t : ℚ) * c t : ℚ) : ℝ) := by
        field_simp at hrec ⊢
        linarith [hrec]
      rw [hsolve]
      push_cast
      ring

/-- **Rationality of every geometric moment at a rational ratio.** -/
theorem exists_rat_geomMoment {q : ℚ} (hq : |(q : ℝ)| < 1) (m : ℕ) :
    ∃ c : ℚ, geomMoment (q : ℝ) m = (c : ℝ) := by
  obtain ⟨c, hc⟩ := exists_rat_geomMoment_le hq m
  exact ⟨c m, hc m le_rfl⟩

end

end RHTower
