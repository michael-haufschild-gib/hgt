import GaloisForLFunctions.RHTower.ZetaPartialSumStrip

/-!
# The Dirichlet series as a Mellin transform of its partial sums

For bounded coefficients and `Re s > 1`, improper Abel summation against `t ↦ t^(-s)` gives

`L(f, s) = s ∫_1^∞ S_f(⌊t⌋₊) t^(-s-1) dt`,   `S_f(m) = ∑_{k ≤ m} f(k)`.

This is the sharp Perron kernel: the weight attached to the vertical line is `1/s`, decaying like
`1/|t|`, in contrast with a smoothed cutoff whose kernel is a Mellin transform of the smoothing profile.
The identity is exact — no truncation error and no smoothing — and it holds for every bounded
coefficient sequence.
-/

open Complex Filter MeasureTheory Set Asymptotics Topology

noncomputable section

namespace RHTower.Sieve

variable {f : ℕ → ℂ}

/-- The trivial size of a partial sum of bounded coefficients vanishing at zero. -/
theorem norm_sum_Icc_zero_le (hf0 : f 0 = 0) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 0 n, f k‖ ≤ (n : ℝ) := by
  have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp), hf0, zero_add]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun k _ => hbdd k) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

/-- **The Mellin bridge.**  For `Re s > 1` the Dirichlet series of a bounded coefficient sequence is
`s` times the Mellin transform of its partial-sum function. -/
theorem LSeries_eq_mul_integral_sum_Icc (hf0 : f 0 = 0) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries f s
      = s * ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) * ((t : ℝ) : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hsn : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t :=
    fun t ht => RHTower.differentiableAt_ofReal_cpow_neg hsn
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))
  have hf_int : LocallyIntegrableOn (deriv fun x : ℝ => (x : ℂ) ^ (-s)) (Ici (1 : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Ici (1 : ℝ)) := by
      intro t ht
      have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
      exact ContinuousAt.continuousWithinAt
        (continuousAt_const.mul
          (Complex.continuousAt_ofReal_cpow_const t (-s - 1) (Or.inr htne)))
    refine (hcont.congr fun t ht => ?_).locallyIntegrableOn measurableSet_Ici
    exact RHTower.deriv_ofReal_cpow_neg hsn (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))
  have h_lim : Tendsto
      (fun n : ℕ => (fun x : ℝ => (x : ℂ) ^ (-s)) (n : ℝ) * ∑ k ∈ Finset.Icc 0 n, f k)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) ?_
    · show ‖((n : ℝ) : ℂ) ^ (-s) * ∑ k ∈ Finset.Icc 0 n, f k‖ ≤ (n : ℝ) ^ (1 - s.re)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 : ∑ k ∈ Finset.Icc 0 0, f k = 0 := by simp [hf0]
        rw [h0, mul_zero, norm_zero, Nat.cast_zero,
          Real.zero_rpow (by intro h; linarith [h ▸ (by linarith : (0:ℝ) < s.re - 1)])]
      · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
        have hb := norm_sum_Icc_zero_le hf0 hbdd n
        have hpow : (0 : ℝ) < (n : ℝ) ^ (-s).re := Real.rpow_pos_of_pos hn0 _
        have hval : (n : ℝ) ^ (-s).re * (n : ℝ) = (n : ℝ) ^ (1 - s.re) := by
          rw [show (-s).re = -s.re from Complex.neg_re s, ← Real.rpow_one (n : ℝ),
            ← Real.rpow_add hn0]
          ring_nf
        calc (n : ℝ) ^ (-s).re * ‖∑ k ∈ Finset.Icc 0 n, f k‖
            ≤ (n : ℝ) ^ (-s).re * (n : ℝ) := mul_le_mul_of_nonneg_left hb hpow.le
          _ = (n : ℝ) ^ (1 - s.re) := hval
    · have hpos : (0 : ℝ) < s.re - 1 := by linarith
      have h := (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
      refine h.congr fun n => ?_
      show ((n : ℝ)) ^ (-(s.re - 1)) = ((n : ℝ)) ^ (1 - s.re)
      rw [show -(s.re - 1) = 1 - s.re by ring]
  have hg_dom : (fun t : ℝ =>
        deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k)
      =O[atTop] (fun t : ℝ => t ^ (-s.re)) := by
    refine IsBigO.of_bound ‖s‖ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
    rw [RHTower.deriv_ofReal_cpow_neg hsn ht0.ne', norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0, norm_neg,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hb := (norm_sum_Icc_zero_le hf0 hbdd ⌊t⌋₊).trans hfloor
    have hpow : (0 : ℝ) < t ^ (-s - 1).re := Real.rpow_pos_of_pos ht0 _
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [Complex.sub_re, Complex.neg_re]
    have hval : t ^ (-s - 1).re * t = t ^ (-s.re) := by
      rw [hre, ← Real.rpow_one t, ← Real.rpow_add ht0]
      ring_nf
    calc ‖s‖ * t ^ (-s - 1).re * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k‖
        ≤ ‖s‖ * t ^ (-s - 1).re * t :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ‖s‖ * (t ^ (-s - 1).re * t) := by ring
      _ = ‖s‖ * t ^ (-s.re) := by rw [hval]
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-s.re)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := f)
    (f := fun x : ℝ => (x : ℂ) ^ (-s)) hf0 hf_diff hf_int h_lim hg_dom hg_int
  have hpartial : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (fun x : ℝ => (x : ℂ) ^ (-s)) (k : ℝ) * f k)
      atTop (𝓝 (LSeries f s)) := by
    have hsum : LSeriesSummable f s :=
      LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => hbdd n) hs
    have h := hsum.hasSum.tendsto_sum_nat
    have hshift := h.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr fun n => ?_
    show (∑ i ∈ Finset.range (n + 1), LSeries.term f s i)
        = ∑ k ∈ Finset.Icc 0 n, ((k : ℝ) : ℂ) ^ (-s) * f k
    rw [show Finset.range (n + 1) = Finset.Icc 0 n by
      ext k
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [LSeries.term_def, if_pos rfl, hf0, mul_zero]
    · have hk0 : (k : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      rw [LSeries.term_def, if_neg (by omega : k ≠ 0), Complex.ofReal_natCast,
        Complex.cpow_neg, div_eq_mul_inv, mul_comm]
  have hval := tendsto_nhds_unique hpartial habel
  have hderiv : (∫ t in Ioi (1 : ℝ),
        deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k)
      = -s * ∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) * ((t : ℝ) : ℂ) ^ (-s - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [RHTower.deriv_ofReal_cpow_neg hsn (ne_of_gt (lt_trans zero_lt_one ht))]
    ring
  rw [hval, hderiv]
  ring

end RHTower.Sieve

end
