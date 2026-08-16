import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Field

/-!
# The sharp tail of a real power series below the summability threshold

For `q < 0` the mean value theorem applied to `t ↦ t^q` on a unit step gives the two-sided
comparison

`-q·(x+1)^{q-1} ≤ x^q - (x+1)^q ≤ -q·x^{q-1}`,

and summing either side telescopes.  So the tail `∑_{n > N} n^{q-1}` is pinned between
`(N+1)^q/(-q)` and `N^q/(-q)`, hence is asymptotically `N^q/(-q)`.  This is the estimate that
turns a power source into the tail of its harmonic primitive.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The one-step mean value comparison for a negative real power. -/
theorem rpow_unit_step_bounds {q x : ℝ} (hq : q < 0) (hx : 0 < x) :
    -q * (x + 1) ^ (q - 1) ≤ x ^ q - (x + 1) ^ q
      ∧ x ^ q - (x + 1) ^ q ≤ -q * x ^ (q - 1) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ q) (Set.Icc x (x + 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hx ht.1
    exact (Real.continuousAt_rpow_const t q (Or.inl (ne_of_gt ht0))).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo x (x + 1), HasDerivAt (fun t : ℝ => t ^ q) (q * t ^ (q - 1)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hx ht.1
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ q)
    (fun t => q * t ^ (q - 1)) (by linarith : x < x + 1) hcont hderiv
  have hξ0 : (0 : ℝ) < ξ := lt_trans hx hξ.1
  have hval : x ^ q - (x + 1) ^ q = -q * ξ ^ (q - 1) := by
    have hden : (x + 1) - x = 1 := by ring
    rw [hden, div_one] at hslope
    linarith [hslope]
  have hq1 : q - 1 ≤ 0 := by linarith
  have hqpos : (0 : ℝ) < -q := by linarith
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hξ0 hξ.2.le hq1) hqpos.le
  · rw [hval]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hξ.1.le hq1) hqpos.le

/-- The shifted power tail is summable below the threshold. -/
theorem summable_shift_rpow {q : ℝ} (hq : q < 0) (N : ℕ) :
    Summable fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1) := by
  have hbase : Summable fun n : ℕ => ((n : ℝ)) ^ (q - 1) := by
    have hiff : Summable fun n : ℕ => (((n : ℝ)) ^ (1 - q))⁻¹ :=
      Real.summable_nat_rpow_inv.2 (by linarith)
    refine hiff.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
      simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [← Real.rpow_neg hn0.le]
      congr 1
      ring
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (q - 1)) (N + 1)).2 hbase
  refine hshift.congr fun k => ?_
  congr 1
  push_cast
  ring

/-- **The tail is at most `N^q/(-q)`.** -/
theorem tsum_shift_rpow_le {q : ℝ} (hq : q < 0) {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1) ≤ (N : ℝ) ^ q / (-q) := by
  have hqpos : (0 : ℝ) < -q := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hstep : ∀ k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1)
      ≤ (((N : ℝ) + (k : ℝ)) ^ q - ((N : ℝ) + ((k : ℝ) + 1)) ^ q) / (-q) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hx : (0 : ℝ) < (N : ℝ) + (k : ℝ) := by linarith
    have hlow := (rpow_unit_step_bounds hq hx).1
    have hcast : (N : ℝ) + (k : ℝ) + 1 = (N : ℝ) + 1 + (k : ℝ) := by ring
    have hcast2 : (N : ℝ) + ((k : ℝ) + 1) = (N : ℝ) + 1 + (k : ℝ) := by ring
    rw [hcast] at hlow
    rw [hcast2, le_div_iff₀ hqpos]
    linarith [hlow]
  have hpartial : ∀ M : ℕ, ∑ k ∈ Finset.range M, ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1)
      ≤ (N : ℝ) ^ q / (-q) := by
    intro M
    refine (Finset.sum_le_sum fun k _ => hstep k).trans ?_
    rw [← Finset.sum_div]
    have htel := Finset.sum_range_sub' (fun k : ℕ => ((N : ℝ) + (k : ℝ)) ^ q) M
    have htel' : ∑ k ∈ Finset.range M,
        (((N : ℝ) + (k : ℝ)) ^ q - ((N : ℝ) + ((k : ℝ) + 1)) ^ q)
        = ((N : ℝ) + ((0 : ℕ) : ℝ)) ^ q - ((N : ℝ) + (M : ℝ)) ^ q := by
      rw [← htel]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      push_cast
      ring
    rw [htel']
    have hMnn : (0 : ℝ) ≤ ((N : ℝ) + (M : ℝ)) ^ q := by
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      exact Real.rpow_nonneg (by linarith) _
    rw [div_le_div_iff₀ hqpos hqpos]
    push_cast
    rw [add_zero]
    nlinarith [hMnn, hqpos]
  refine le_of_tendsto (summable_shift_rpow hq N).hasSum.tendsto_sum_nat ?_
  exact Eventually.of_forall hpartial

/-- **The tail is at least `(N+1)^q/(-q)`.** -/
theorem tsum_shift_rpow_ge {q : ℝ} (hq : q < 0) (N : ℕ) :
    ((N : ℝ) + 1) ^ q / (-q) ≤ ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1) := by
  have hqpos : (0 : ℝ) < -q := by linarith
  have hstep : ∀ k : ℕ,
      (((N : ℝ) + 1 + (k : ℝ)) ^ q - ((N : ℝ) + 1 + ((k : ℝ) + 1)) ^ q) / (-q)
        ≤ ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hx : (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by linarith
    have hup := (rpow_unit_step_bounds hq hx).2
    have hcast : (N : ℝ) + 1 + (k : ℝ) + 1 = (N : ℝ) + 1 + ((k : ℝ) + 1) := by ring
    rw [hcast] at hup
    rw [div_le_iff₀ hqpos]
    linarith [hup]
  have hlimL := (summable_shift_rpow hq N).hasSum.tendsto_sum_nat
  have htail : Tendsto (fun M : ℕ => ((N : ℝ) + 1 + (M : ℝ)) ^ q) atTop (𝓝 0) := by
    have hbase : Tendsto (fun M : ℕ => (N : ℝ) + 1 + (M : ℝ)) atTop atTop := by
      refine tendsto_atTop_add_const_left _ _ ?_
      exact tendsto_natCast_atTop_atTop
    have := (tendsto_rpow_neg_atTop (y := -q) hqpos).comp hbase
    simpa [neg_neg, Function.comp_def] using this
  have hlimR : Tendsto (fun M : ℕ =>
      (((N : ℝ) + 1) ^ q - ((N : ℝ) + 1 + (M : ℝ)) ^ q) / (-q)) atTop
      (𝓝 (((N : ℝ) + 1) ^ q / (-q))) := by
    have := ((tendsto_const_nhds (x := ((N : ℝ) + 1) ^ q) (f := atTop (α := ℕ))).sub
      htail).div_const (-q)
    simpa using this
  refine le_of_tendsto_of_tendsto' hlimR hlimL fun M => ?_
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun k _ => hstep k)
  rw [← Finset.sum_div]
  congr 1
  have htel := Finset.sum_range_sub' (fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ q) M
  rw [show ((N : ℝ) + 1) ^ q = ((N : ℝ) + 1 + ((0 : ℕ) : ℝ)) ^ q by norm_num, ← htel]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

/-- **The sharp tail asymptotic.**  `N^{-q}·∑_{n > N} n^{q-1} → 1/(-q)`. -/
theorem tendsto_tsum_shift_rpow {q : ℝ} (hq : q < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-q) * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (q - 1))
      atTop (𝓝 (1 / (-q))) := by
  have hqpos : (0 : ℝ) < -q := by linarith
  have hlow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-q) * (((N : ℝ) + 1) ^ q / (-q))) atTop
      (𝓝 (1 / (-q))) := by
    have hratio : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / (N : ℝ)) ^ q) atTop (𝓝 1) := by
      have hbase : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
        have h : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat)
        rw [add_zero] at h
        refine h.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        field_simp
      have hcont : ContinuousAt (fun x : ℝ => x ^ q) 1 :=
        Real.continuousAt_rpow_const 1 q (Or.inl one_ne_zero)
      have := hcont.tendsto.comp hbase
      simpa [Real.one_rpow, Function.comp_def] using this
    have hmain : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / (N : ℝ)) ^ q / (-q)) atTop
        (𝓝 (1 / (-q))) := hratio.div_const (-q)
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [Real.div_rpow (by linarith) hN0.le, Real.rpow_neg hN0.le]
    have hne : ((N : ℝ) ^ q) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hN0 q)
    field_simp
  have hhigh : Tendsto (fun N : ℕ => (N : ℝ) ^ (-q) * ((N : ℝ) ^ q / (-q))) atTop
      (𝓝 (1 / (-q))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [← mul_div_assoc, ← Real.rpow_add hN0]
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact mul_le_mul_of_nonneg_left (tsum_shift_rpow_ge hq N)
      (Real.rpow_nonneg hN0.le _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact mul_le_mul_of_nonneg_left (tsum_shift_rpow_le hq hN)
      (Real.rpow_nonneg hN0.le _)

end GaloisForLFunctions.HTGeometry
