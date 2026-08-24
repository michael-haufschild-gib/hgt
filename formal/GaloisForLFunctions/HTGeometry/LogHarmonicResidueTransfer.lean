import GaloisForLFunctions.HTGeometry.MonotoneRiemannSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Log-harmonic partial sums and squared-log residue transfer

The critical weight `log(n+1)/(n+1)` has cumulative mass asymptotic to
`(1/2) log²(N+1)`. Consequently any pointwise law `a_n ~ R log(n)/n` transfers to
the exact partial-sum law `sum_{n<N} a_n ~ (R/2) log² N`.
-/

open Filter Finset MeasureTheory intervalIntegral Asymptotics

namespace GaloisForLFunctions

noncomputable section

def logHarmonicWeight (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)

private theorem intervalIntegral_log_div_id {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, Real.log x / x) =
      Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Real.log y ^ 2 / 2)
        (Real.log x / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    have h := (Real.hasDerivAt_log hx0).pow 2 |>.div_const 2
    refine h.congr_deriv ?_
    simp [div_eq_mul_inv]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / x)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    exact (Real.continuousAt_log hx0).div continuousAt_id hx0 |>.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private theorem abs_logHarmonicTail_sub_integral_le (N : ℕ) :
    |(∑ i ∈ Finset.range N, Real.log (3 + (i : ℝ)) / (3 + (i : ℝ))) -
        ∫ x in (3 : ℝ)..3 + N, Real.log x / x| ≤ Real.log 3 / 3 := by
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x)
      (Set.Icc 3 (3 + (N : ℝ))) := by
    exact Real.log_div_self_antitoneOn.mono (fun x hx =>
      Real.exp_one_lt_three.le.trans hx.1)
  have h := HTGeometry.abs_sum_sub_integral_le_of_antitoneOn hanti
  have hnonneg : 0 ≤ Real.log (3 + (N : ℝ)) / (3 + (N : ℝ)) := by
    exact div_nonneg (Real.log_nonneg (by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith)) (by positivity)
  simpa only [Nat.cast_ofNat] using h.trans (sub_le_self _ hnonneg)

private theorem tendsto_log_three_add_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (3 + (N : ℝ))) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  exact Filter.tendsto_atTop_add_const_left atTop 3 tendsto_natCast_atTop_atTop

private theorem tendsto_log_three_add_nat_sq_atTop :
    Tendsto (fun N : ℕ => Real.log (3 + (N : ℝ)) ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [tendsto_log_three_add_nat_atTop.eventually
      (eventually_ge_atTop (max 1 B))] with N hN
  have hN1 : 1 ≤ Real.log (3 + (N : ℝ)) := (le_max_left _ _).trans hN
  have hNB : B ≤ Real.log (3 + (N : ℝ)) := (le_max_right _ _).trans hN
  nlinarith [sq_nonneg (Real.log (3 + (N : ℝ)))]

theorem tendsto_logHarmonicTail_div_logSq :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, Real.log (3 + (i : ℝ)) / (3 + (i : ℝ))) /
        (Real.log (3 + (N : ℝ)) ^ 2)) atTop (nhds (1 / 2 : ℝ)) := by
  let I : ℕ → ℝ := fun N =>
    Real.log (3 + (N : ℝ)) ^ 2 / 2 - Real.log 3 ^ 2 / 2
  have hmain : Tendsto (fun N : ℕ => I N /
      Real.log (3 + (N : ℝ)) ^ 2) atTop (nhds (1 / 2 : ℝ)) := by
    have hsmall := tendsto_log_three_add_nat_sq_atTop.const_div_atTop
      (Real.log 3 ^ 2 / 2)
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hsmall
    have hfinal : Tendsto (fun N : ℕ => I N /
        Real.log (3 + (N : ℝ)) ^ 2) atTop
        (nhds ((1 / 2 : ℝ) - 0)) := by
      apply h.congr'
      filter_upwards [] with N
      have hlog : Real.log (3 + (N : ℝ)) ≠ 0 := by
        exact (Real.log_pos (by
          have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith)).ne'
      simp only [I]
      field_simp [hlog]
    simpa using hfinal
  have herr : Tendsto (fun N : ℕ =>
      ((∑ i ∈ Finset.range N, Real.log (3 + (i : ℝ)) / (3 + (i : ℝ))) - I N) /
        (Real.log (3 + (N : ℝ)) ^ 2)) atTop (nhds 0) := by
    have hmajor := tendsto_log_three_add_nat_sq_atTop.const_div_atTop (Real.log 3 / 3)
    refine squeeze_zero_norm' ?_ hmajor
    filter_upwards [] with N
    have hden : 0 < Real.log (3 + (N : ℝ)) ^ 2 :=
      pow_pos (Real.log_pos (by
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)) 2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    simp only [I]
    rw [← intervalIntegral_log_div_id (by norm_num : (0 : ℝ) < 3) (by norm_num)]
    exact abs_logHarmonicTail_sub_integral_le N
  have h := hmain.add herr
  have hfinal : Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, Real.log (3 + (i : ℝ)) / (3 + (i : ℝ))) /
        Real.log (3 + (N : ℝ)) ^ 2) atTop
        (nhds ((1 / 2 : ℝ) + 0)) := by
    apply h.congr'
    filter_upwards [] with N
    have hden : Real.log (3 + (N : ℝ)) ^ 2 ≠ 0 :=
      (pow_pos (Real.log_pos (by
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)) 2).ne'
    field_simp [hden] <;> ring
  simpa using hfinal

theorem tendsto_logHarmonicWeight_partialSum_div_logSq :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, logHarmonicWeight n) /
        (Real.log ((N : ℝ) + 1) ^ 2)) atTop (nhds (1 / 2 : ℝ)) := by
  apply (Filter.tendsto_add_atTop_iff_nat 2).mp
  have htail : Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, Real.log (3 + (i : ℝ)) / (3 + (i : ℝ))) /
        Real.log (((N + 2 : ℕ) : ℝ) + 1) ^ 2) atTop (nhds (1 / 2 : ℝ)) := by
    convert tendsto_logHarmonicTail_div_logSq using 1 <;>
      norm_num [Nat.cast_add] <;> ring
  have hdenTop : Tendsto (fun N : ℕ =>
      Real.log (((N + 2 : ℕ) : ℝ) + 1) ^ 2) atTop atTop := by
    convert tendsto_log_three_add_nat_sq_atTop using 1 <;>
      norm_num [Nat.cast_add] <;> ring
  have hfinite := hdenTop.const_div_atTop (Real.log 2 / 2)
  have htotal := hfinite.add htail
  have hfinal : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range (N + 2), logHarmonicWeight n) /
        Real.log (((N + 2 : ℕ) : ℝ) + 1) ^ 2) atTop
        (nhds (0 + (1 / 2 : ℝ))) := by
    apply htotal.congr'
    filter_upwards [] with N
    have hsum : (∑ n ∈ Finset.range (N + 2), logHarmonicWeight n) =
        Real.log 2 / 2 +
          ∑ i ∈ Finset.range N, Real.log (3 + (i : ℝ)) / (3 + (i : ℝ)) := by
      rw [show N + 2 = 2 + N by omega, Finset.sum_range_add]
      have hhead : (∑ n ∈ Finset.range 2, logHarmonicWeight n) =
          Real.log 2 / 2 := by
        norm_num [Finset.sum_range_succ, logHarmonicWeight]
      rw [hhead]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      have harg : ((((2 + i : ℕ) : ℕ) : ℝ) + 1) =
          3 + (i : ℝ) := by
        push_cast
        ring
      simp only [logHarmonicWeight]
      rw [harg]
    rw [hsum]
    ring
  simpa using hfinal

theorem logHarmonicWeight_nonneg (n : ℕ) : 0 ≤ logHarmonicWeight n := by
  apply div_nonneg
  · apply Real.log_nonneg
    norm_num
  · positivity

theorem tendsto_log_natCast_succ_sq_atTop :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 1 B))] with N hN
  have hN1 : 1 ≤ Real.log ((N : ℝ) + 1) := (le_max_left _ _).trans hN
  have hNB : B ≤ Real.log ((N : ℝ) + 1) := (le_max_right _ _).trans hN
  nlinarith [sq_nonneg (Real.log ((N : ℝ) + 1))]

theorem tendsto_logHarmonicWeight_partialSum_atTop :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, logHarmonicWeight n)
      atTop atTop := by
  have hproduct := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    tendsto_logHarmonicWeight_partialSum_div_logSq
    tendsto_log_natCast_succ_sq_atTop
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hlog : Real.log ((N : ℝ) + 1) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast Nat.succ_lt_succ hN
  field_simp [hlog]

/-- A pointwise `R log(n)/n` law has partial sums asymptotic to `(R/2) log² N`. -/
theorem tendsto_logSquaredResidue_of_div_logHarmonicWeight_tendsto
    {a : ℕ → ℝ} {R : ℝ}
    (ha : Tendsto (fun n : ℕ => a n / logHarmonicWeight n)
      atTop (nhds R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) /
      (Real.log ((N : ℝ) + 1) ^ 2)) atTop (nhds (R / 2)) := by
  let d : ℕ → ℝ := fun n => if n = 0 then 0 else
    a n - R * logHarmonicWeight n
  have hdo : d =o[atTop] logHarmonicWeight := by
    apply (isLittleO_iff_tendsto (fun n hzero => by
      by_cases hn : n = 0
      · simp [d, hn]
      · exfalso
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hlog : 0 < Real.log ((n : ℝ) + 1) := by
          apply Real.log_pos
          exact_mod_cast Nat.succ_lt_succ hnpos
        exact (div_pos hlog (by positivity)).ne' hzero)).2
    have he : Tendsto (fun n : ℕ => a n / logHarmonicWeight n - R)
        atTop (nhds 0) := tendsto_sub_nhds_zero_iff.mpr ha
    apply he.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hw : logHarmonicWeight n ≠ 0 := by
      apply (div_pos ?_ (by positivity)).ne'
      apply Real.log_pos
      exact_mod_cast Nat.succ_lt_succ hn
    simp only [d, if_neg (Nat.ne_of_gt hn)]
    field_simp [hw]
  have hsum := hdo.sum_range logHarmonicWeight_nonneg
    tendsto_logHarmonicWeight_partialSum_atTop
  have hratio : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, d n) /
        (∑ n ∈ Finset.range N, logHarmonicWeight n))
      atTop (nhds 0) := hsum.tendsto_div_nhds_zero
  have herrProduct := hratio.mul
    tendsto_logHarmonicWeight_partialSum_div_logSq
  have herr : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, d n) /
        Real.log ((N : ℝ) + 1) ^ 2) atTop (nhds 0) := by
    simpa only [zero_mul] using herrProduct.congr' (by
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hlog : Real.log ((N : ℝ) + 1) ≠ 0 := by
        apply (Real.log_pos ?_).ne'
        exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt hN)
      have hweight : (∑ n ∈ Finset.range N, logHarmonicWeight n) ≠ 0 := by
        have hterm : 0 < logHarmonicWeight 1 := by
          rw [logHarmonicWeight]
          positivity
        have hmem : 1 ∈ Finset.range N := Finset.mem_range.mpr hN
        exact ne_of_gt (Finset.sum_pos' (fun n _ => logHarmonicWeight_nonneg n)
          ⟨1, hmem, hterm⟩)
      field_simp [hlog, hweight])
  have hmain :=
    tendsto_logHarmonicWeight_partialSum_div_logSq.const_mul R
  have hprefix := tendsto_log_natCast_succ_sq_atTop.const_div_atTop (a 0)
  have htotal := (hmain.add herr).add hprefix
  have hfinal : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, a n) /
        Real.log ((N : ℝ) + 1) ^ 2) atTop
        (nhds ((R * (1 / 2) + 0) + 0)) := by
    apply htotal.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hlog : Real.log ((N : ℝ) + 1) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast Nat.succ_lt_succ hN
    have hsum : (∑ n ∈ Finset.range N, a n) =
        a 0 + R * (∑ n ∈ Finset.range N, logHarmonicWeight n) +
          ∑ n ∈ Finset.range N, d n := by
      have hpoint : ∀ n : ℕ, a n =
          (if n = 0 then a 0 else 0) + R * logHarmonicWeight n + d n := by
        intro n
        by_cases hn0 : n = 0
        · subst n
          simp [d, logHarmonicWeight]
        · simp [d, hn0]
      calc
        (∑ n ∈ Finset.range N, a n) =
            ∑ n ∈ Finset.range N,
              ((if n = 0 then a 0 else 0) +
                R * logHarmonicWeight n + d n) := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact hpoint n
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
          have hzeroMem : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
          simp [hzeroMem]
    rw [hsum]
    field_simp [hlog]
    ring
  convert hfinal using 1 <;> ring

end

end GaloisForLFunctions

