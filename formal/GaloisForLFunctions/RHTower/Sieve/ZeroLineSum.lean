import GaloisForLFunctions.RHTower.Sieve.ZeroLinePower

/-!
# The zero-line exponential sum

Comparing `∑_{n ≤ N} n^{iv}` with `∫ x^{iv} dx` gives

`‖∑_{n ≤ N} n^{iv}‖ ≤ (N + 2)/‖1 + iv‖ + |v| (1 + log N)`.

The integral part telescopes through the antiderivative of `ZeroLinePower.lean`, and each correction
`n^{iv} - ∫_n^{n+1} x^{iv} dx` is at most `|v|/n` because the phase exponential is `1`-Lipschitz and
`log(x/n) ≤ 1/n` on `[n, n+1]`.  The corrections sum to a harmonic series.

This is the far-field estimate the mean value theorem needs: for a frequency difference `v` with
`1 ≪ |v| ≪ N / log N` the bound is far below the trivial `N` of `DirichletTrivial.lean`, so the Gram
row of a separated family is dominated by its diagonal.  The two competing terms are the reason a
mean value theorem carries both `N` and a term growing in the number of frequencies.
-/

namespace RHTower.Sieve

open Finset

/-- The fundamental theorem of calculus for the zero-line power. -/
theorem integral_zpow0_eq (v : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, zpow0 v x = Zpow0 v b - Zpow0 v a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
    (intervalIntegrable_zpow0 v ha hab)
  rw [Set.uIcc_of_le hab] at hx
  exact hasDerivAt_Zpow0 v (lt_of_lt_of_le ha hx.1)

/-- The zero-line power varies by at most `|v|/k` across a unit step. -/
theorem norm_zpow0_sub_le (v : ℝ) {k x : ℝ} (hk : 1 ≤ k) (hkx : k ≤ x) (hxk : x ≤ k + 1) :
    ‖zpow0 v k - zpow0 v x‖ ≤ |v| / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  rw [zpow0_eq, zpow0_eq]
  refine le_trans (norm_exp_phase_sub_le _ _) ?_
  have hdiff : v * Real.log k - v * Real.log x = -(v * (Real.log x - Real.log k)) := by ring
  rw [hdiff, abs_neg, abs_mul]
  have hlognn : 0 ≤ Real.log x - Real.log k := by
    have := Real.log_le_log hk0 hkx
    linarith
  rw [abs_of_nonneg hlognn]
  have hlog : Real.log x - Real.log k ≤ 1 / k := by
    have hlogdiv : Real.log x - Real.log k = Real.log (x / k) := by
      rw [Real.log_div hx0.ne' hk0.ne']
    rw [hlogdiv]
    have h1 : Real.log (x / k) ≤ x / k - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : x / k - 1 ≤ 1 / k := by
      rw [sub_le_iff_le_add, div_le_iff₀ hk0]
      have hexp : (1 / k + 1) * k = 1 + k := by field_simp
      rw [hexp]
      linarith
    linarith
  calc |v| * (Real.log x - Real.log k) ≤ |v| * (1 / k) :=
        mul_le_mul_of_nonneg_left hlog (abs_nonneg v)
    _ = |v| / k := by ring

/-- The Euler–Maclaurin correction at a single step. -/
theorem norm_zpow0_sub_integral_le (v : ℝ) {k : ℝ} (hk : 1 ≤ k) :
    ‖zpow0 v k - (Zpow0 v (k + 1) - Zpow0 v k)‖ ≤ |v| / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hkk1 : k ≤ k + 1 := by linarith
  have hII : IntervalIntegrable (zpow0 v) MeasureTheory.volume k (k + 1) :=
    intervalIntegrable_zpow0 v hk0 hkk1
  rw [← integral_zpow0_eq v hk0 hkk1]
  have hconst : ∫ _x in k..(k + 1), zpow0 v k = zpow0 v k := by
    rw [intervalIntegral.integral_const]
    simp
  have hsub : zpow0 v k - ∫ x in k..(k + 1), zpow0 v x
      = ∫ x in k..(k + 1), (zpow0 v k - zpow0 v x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hII, hconst]
  rw [hsub]
  have hnormII : IntervalIntegrable (fun x => ‖zpow0 v k - zpow0 v x‖)
      MeasureTheory.volume k (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.sub ((continuousOn_zpow0 v).mono ?_)).norm
    rw [Set.uIcc_of_le hkk1]
    exact fun x hx => lt_of_lt_of_le hk0 hx.1
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hkk1) ?_
  calc ∫ x in k..(k + 1), ‖zpow0 v k - zpow0 v x‖
      ≤ ∫ _x in k..(k + 1), (|v| / k) := by
        apply intervalIntegral.integral_mono_on hkk1 hnormII intervalIntegrable_const
        intro x hx
        exact norm_zpow0_sub_le v hk hx.1 hx.2
    _ = |v| / k := by
        rw [intervalIntegral.integral_const]
        simp

/-- **The zero-line exponential sum.** -/
theorem norm_sum_zpow0_le (v : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, zpow0 v ((n : ℝ) + 1)‖
      ≤ ((N : ℝ) + 2) / ‖(1 : ℂ) + (v : ℂ) * Complex.I‖ + |v| * (1 + Real.log N) := by
  have hdecomp : ∀ n : ℕ, zpow0 v ((n : ℝ) + 1)
      = (Zpow0 v ((n : ℝ) + 1 + 1) - Zpow0 v ((n : ℝ) + 1))
        + (zpow0 v ((n : ℝ) + 1) - (Zpow0 v ((n : ℝ) + 1 + 1) - Zpow0 v ((n : ℝ) + 1))) :=
    fun n => by ring
  rw [Finset.sum_congr rfl (fun n _ => hdecomp n), Finset.sum_add_distrib]
  refine le_trans (norm_add_le _ _) ?_
  have htele : ∑ n ∈ Finset.range N, (Zpow0 v ((n : ℝ) + 1 + 1) - Zpow0 v ((n : ℝ) + 1))
      = Zpow0 v ((N : ℝ) + 1) - Zpow0 v 1 := by
    have hsr := Finset.sum_range_sub (fun n : ℕ => Zpow0 v ((n : ℝ) + 1)) N
    calc ∑ n ∈ Finset.range N, (Zpow0 v ((n : ℝ) + 1 + 1) - Zpow0 v ((n : ℝ) + 1))
        = ∑ n ∈ Finset.range N, (Zpow0 v (((n + 1 : ℕ) : ℝ) + 1) - Zpow0 v ((n : ℝ) + 1)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          push_cast
          ring_nf
      _ = Zpow0 v ((N : ℝ) + 1) - Zpow0 v 1 := by simpa using hsr
  rw [htele]
  have hT : ‖Zpow0 v ((N : ℝ) + 1) - Zpow0 v 1‖
      ≤ ((N : ℝ) + 2) / ‖(1 : ℂ) + (v : ℂ) * Complex.I‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_Zpow0 v (by positivity), norm_Zpow0 v one_pos]
    have heq : ((N : ℝ) + 1) / ‖(1 : ℂ) + (v : ℂ) * Complex.I‖
        + 1 / ‖(1 : ℂ) + (v : ℂ) * Complex.I‖
        = ((N : ℝ) + 2) / ‖(1 : ℂ) + (v : ℂ) * Complex.I‖ := by
      rw [← add_div]
      congr 1
      ring
    linarith [heq]
  have hcorr : ‖∑ n ∈ Finset.range N,
      (zpow0 v ((n : ℝ) + 1) - (Zpow0 v ((n : ℝ) + 1 + 1) - Zpow0 v ((n : ℝ) + 1)))‖
      ≤ |v| * (1 + Real.log N) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.range N,
        ‖zpow0 v ((n : ℝ) + 1) - (Zpow0 v ((n : ℝ) + 1 + 1) - Zpow0 v ((n : ℝ) + 1))‖
          ≤ |v| / ((n : ℝ) + 1) := by
      intro n _
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      exact norm_zpow0_sub_integral_le v hn
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : ∑ n ∈ Finset.range N, |v| / ((n : ℝ) + 1)
        = |v| * ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hsum, ← sum_Icc_one_div_eq_sum_range]
    exact mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) (abs_nonneg v)
  linarith [hT, hcorr]

end RHTower.Sieve
