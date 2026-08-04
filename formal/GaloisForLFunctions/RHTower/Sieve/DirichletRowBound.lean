import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The Gram row of a Dirichlet polynomial

`DirichletRow.lean` reduces the Halász–Montgomery frame to the size of `∑_{n ≤ N} n^{iu}` at a
nonzero frequency.  Euler–Maclaurin gives it: with `g(x) = x^{iu}` and antiderivative
`G(x) = x^{1+iu}/(1+iu)`, the telescoped integral part is `‖G(N+1) − G(1)‖ ≤ (N+2)/‖1+iu‖`, and each
correction is controlled by `‖g'‖ = |u|/x`, so

    ‖∑_{n ≤ N} n^{iu}‖ ≤ (N + 2)/|u| + |u|·(1 + log N).

Both terms are needed: the first is small when `|u|` is large, the second when `|u|` is small, and
their balance at `|u| ≍ √N` is what makes the Gram rows of `dirRow` small away from the diagonal.

The argument is the one of `HTGeometry/DirichletLinePartialSum.lean` at the abscissa `0` instead of
`-1`; there the antiderivative is bounded, here it grows like `x`, which is the whole difference
between a bounded partial sum and one of size `N/|u|`.
-/

namespace RHTower.Sieve

open Finset

/-- The unimodular row entry `x^{iu}`. -/
noncomputable def rowPow (u : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((u * Complex.I) * (Real.log x : ℂ))

/-- Its antiderivative `x^{1+iu}/(1+iu)`. -/
noncomputable def rowAnti (u : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (((1 : ℂ) + u * Complex.I) * (Real.log x : ℂ)) / ((1 : ℂ) + u * Complex.I)

theorem one_add_mul_I_ne_zero (u : ℝ) : ((1 : ℂ) + u * Complex.I) ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) + (u : ℂ) * Complex.I).re = 1 := by simp
  rw [h] at hre
  simp at hre

theorem norm_rowPow (u : ℝ) (x : ℝ) : ‖rowPow u x‖ = 1 := by
  rw [rowPow, Complex.norm_exp]
  have hre : (((u : ℂ) * Complex.I) * (Real.log x : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

theorem norm_rowAnti (u : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖rowAnti u x‖ = x / ‖(1 : ℂ) + u * Complex.I‖ := by
  rw [rowAnti, norm_div, Complex.norm_exp]
  have hre : ((((1 : ℂ) + (u : ℂ) * Complex.I)) * (Real.log x : ℂ)).re = Real.log x := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hre, Real.exp_log hx]

theorem hasDerivAt_rowPow (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rowPow u) (rowPow u x * ((u : ℂ) * Complex.I) / x) x := by
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hg := (hlog.const_mul ((u : ℂ) * Complex.I)).cexp
  change HasDerivAt
    (fun y : ℝ => Complex.exp (((u : ℂ) * Complex.I) * (Real.log y : ℂ)))
    (Complex.exp (((u : ℂ) * Complex.I) * (Real.log x : ℂ)) * ((u : ℂ) * Complex.I) / x) x
  apply hg.congr_deriv
  rw [Complex.ofReal_inv]
  ring

theorem hasDerivAt_rowAnti (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rowAnti u) (rowPow u x) x := by
  have hw : ((1 : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := one_add_mul_I_ne_zero u
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hG := ((hlog.const_mul ((1 : ℂ) + (u : ℂ) * Complex.I)).cexp).div_const
    ((1 : ℂ) + (u : ℂ) * Complex.I)
  change HasDerivAt
    (fun y : ℝ =>
      Complex.exp (((1 : ℂ) + (u : ℂ) * Complex.I) * (Real.log y : ℂ))
        / ((1 : ℂ) + (u : ℂ) * Complex.I))
    (Complex.exp (((u : ℂ) * Complex.I) * (Real.log x : ℂ))) x
  apply hG.congr_deriv
  have hxc : ((x : ℂ)) ≠ 0 := by exact_mod_cast hx.ne'
  have hexp : Complex.exp ((Real.log x : ℂ)) = (x : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hx]
  have hsplit : ((1 : ℂ) + (u : ℂ) * Complex.I) * (Real.log x : ℂ)
      = (Real.log x : ℂ) + ((u : ℂ) * Complex.I) * (Real.log x : ℂ) := by ring
  rw [hsplit, Complex.exp_add, hexp, Complex.ofReal_inv]
  field_simp

theorem continuousOn_rowPow (u : ℝ) : ContinuousOn (rowPow u) (Set.Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun x : ℝ => (Real.log x : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx))
  exact (hlog.const_mul ((u : ℂ) * Complex.I)).cexp

theorem intervalIntegrable_rowPow (u : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (rowPow u) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_rowPow u).mono
  rw [Set.uIcc_of_le hab]
  exact fun x hx => lt_of_lt_of_le ha hx.1

theorem integral_rowPow (u : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, rowPow u x = rowAnti u b - rowAnti u a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_rowAnti u (lt_of_lt_of_le ha hx.1)
  · exact intervalIntegrable_rowPow u ha hab

/-- The one-step variation of the row entry. -/
theorem rowPow_diff_le (u : ℝ) {k x : ℝ} (hk : 1 ≤ k) (hx : x ∈ Set.Icc k (k + 1)) :
    ‖rowPow u k - rowPow u x‖ ≤ |u| / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  set C := |u| / k with hC
  have hconv : Convex ℝ (Set.Icc k (k + 1)) := convex_Icc _ _
  have hderiv : ∀ y ∈ Set.Icc k (k + 1), HasDerivWithinAt (rowPow u)
      (rowPow u y * ((u : ℂ) * Complex.I) / y) (Set.Icc k (k + 1)) y := by
    intro y hy
    exact (hasDerivAt_rowPow u (by simp only [Set.mem_Icc] at hy; linarith [hy.1])).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Icc k (k + 1), ‖rowPow u y * ((u : ℂ) * Complex.I) / y‖ ≤ C := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    rw [norm_div, norm_mul, norm_rowPow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
      one_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, hC]
    gcongr
    exact hy.1
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hconv
    (Set.left_mem_Icc.mpr (by linarith : k ≤ k + 1)) hx
  rw [norm_sub_rev]
  refine le_trans hmvt ?_
  have hxk : ‖x - k‖ ≤ 1 := by
    simp only [Set.mem_Icc] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  calc C * ‖x - k‖ ≤ C * 1 := by
        apply mul_le_mul_of_nonneg_left hxk
        rw [hC]
        positivity
    _ = C := mul_one C

/-- The one-step Euler–Maclaurin correction. -/
theorem rowCorr_bound (u : ℝ) {k : ℝ} (hk : 1 ≤ k) :
    ‖rowPow u k - ∫ x in k..(k + 1), rowPow u x‖ ≤ |u| / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hkk1 : k ≤ k + 1 := by linarith
  have hII : IntervalIntegrable (rowPow u) MeasureTheory.volume k (k + 1) :=
    intervalIntegrable_rowPow u hk0 hkk1
  have hconst : ∫ _x in k..(k + 1), rowPow u k = rowPow u k := by
    rw [intervalIntegral.integral_const]; simp
  have hnormII : IntervalIntegrable (fun x => ‖rowPow u k - rowPow u x‖)
      MeasureTheory.volume k (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.sub ((continuousOn_rowPow u).mono ?_)).norm
    rw [Set.uIcc_of_le hkk1]
    exact fun x hx => lt_of_lt_of_le hk0 hx.1
  have hsub : rowPow u k - ∫ x in k..(k + 1), rowPow u x
      = ∫ x in k..(k + 1), (rowPow u k - rowPow u x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hII, hconst]
  rw [hsub]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hkk1) ?_
  calc ∫ x in k..(k + 1), ‖rowPow u k - rowPow u x‖
      ≤ ∫ _x in k..(k + 1), (|u| / k) := by
        apply intervalIntegral.integral_mono_on hkk1 hnormII intervalIntegrable_const
        intro x hx
        exact rowPow_diff_le u hk hx
    _ = |u| / k := by rw [intervalIntegral.integral_const]; simp

/-- The modulus of `1 + iu` dominates `|u|`. -/
theorem abs_le_norm_one_add_mul_I (u : ℝ) : |u| ≤ ‖(1 : ℂ) + u * Complex.I‖ := by
  have him : ((1 : ℂ) + (u : ℂ) * Complex.I).im = u := by simp
  have h := Complex.abs_im_le_norm ((1 : ℂ) + (u : ℂ) * Complex.I)
  rwa [him] at h

/-- **The Gram row bound.**  The partial sums of `n^{iu}` at a nonzero frequency. -/
theorem norm_sum_rowPow_le {u : ℝ} (hu : u ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, rowPow u ((n : ℝ) + 1)‖
      ≤ ((N : ℝ) + 2) / |u| + |u| * (1 + Real.log N) := by
  classical
  have hu0 : (0 : ℝ) < |u| := abs_pos.2 hu
  have hw : (0 : ℝ) < ‖(1 : ℂ) + u * Complex.I‖ :=
    lt_of_lt_of_le hu0 (abs_le_norm_one_add_mul_I u)
  have hdecomp : ∀ n : ℕ, rowPow u ((n : ℝ) + 1)
      = (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1))
        + (rowPow u ((n : ℝ) + 1) - (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1))) :=
    fun n => by ring
  rw [Finset.sum_congr rfl (fun n _ => hdecomp n), Finset.sum_add_distrib]
  have htele : ∑ n ∈ Finset.range N, (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1))
      = rowAnti u ((N : ℝ) + 1) - rowAnti u 1 := by
    induction N with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  rw [htele]
  have hmain : ‖rowAnti u ((N : ℝ) + 1) - rowAnti u 1‖ ≤ ((N : ℝ) + 2) / |u| := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_rowAnti u (by positivity : (0 : ℝ) < (N : ℝ) + 1),
      norm_rowAnti u (by norm_num : (0 : ℝ) < (1 : ℝ))]
    have hsum : ((N : ℝ) + 1) / ‖(1 : ℂ) + u * Complex.I‖ + 1 / ‖(1 : ℂ) + u * Complex.I‖
        = ((N : ℝ) + 2) / ‖(1 : ℂ) + u * Complex.I‖ := by
      field_simp
      ring
    rw [hsum]
    exact div_le_div_of_nonneg_left (by positivity) hu0 (abs_le_norm_one_add_mul_I u)
  have hcorr : ‖∑ n ∈ Finset.range N,
      (rowPow u ((n : ℝ) + 1) - (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1)))‖
      ≤ |u| * (1 + Real.log N) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.range N,
        ‖rowPow u ((n : ℝ) + 1) - (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1))‖
          ≤ |u| * (1 / ((n : ℝ) + 1)) := by
      intro n _
      have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hint := integral_rowPow u (a := (n : ℝ) + 1) (b := (n : ℝ) + 1 + 1)
        (by positivity) (by linarith)
      rw [← hint]
      have := rowCorr_bound u (k := (n : ℝ) + 1) hk
      calc ‖rowPow u ((n : ℝ) + 1) - ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 1 + 1), rowPow u x‖
          ≤ |u| / ((n : ℝ) + 1) := this
        _ = |u| * (1 / ((n : ℝ) + 1)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hu0.le
    rw [← sum_Icc_one_div_eq_sum_range N]
    exact sum_Icc_one_div_le_one_add_log N
  calc ‖(rowAnti u ((N : ℝ) + 1) - rowAnti u 1)
        + ∑ n ∈ Finset.range N,
          (rowPow u ((n : ℝ) + 1) - (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1)))‖
      ≤ ‖rowAnti u ((N : ℝ) + 1) - rowAnti u 1‖
        + ‖∑ n ∈ Finset.range N,
          (rowPow u ((n : ℝ) + 1)
            - (rowAnti u ((n : ℝ) + 1 + 1) - rowAnti u ((n : ℝ) + 1)))‖ := norm_add_le _ _
    _ ≤ ((N : ℝ) + 2) / |u| + |u| * (1 + Real.log N) := by linarith

end RHTower.Sieve
