import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# Hadamard positivity inside the critical strip

`Re (ξ'/ξ)(s) ≥ 0` for every `Re s > ½` is an exact receiver for the Riemann Hypothesis.  The
corpus proves it unconditionally on `Re s ≥ 1`.  Here it is pushed into the strip with the same
constant as the zero-free region:

```text
1 - 1/(58 log(4(|Im s| + 1))) ≤ Re s   →   0 ≤ Re (ξ'/ξ)(s).
```

The reflection-paired resolvent term of a copy `ρ = β + iγ` has numerator
`2(x(x² - a²) + x(t² + γ²) - 2 a t γ)` with `x = Re s - ½`, `a = β - ½`, `t = Im s`.  Two regimes
cover every copy.

* `log|γ| ≤ log(4(|Im s| + 1))`: the zero-free region gives `|a| ≤ ½ - 1/(58 log|γ|) ≤ x`, and the
  numerator is `[(x-a)(t+γ)² + (x+a)(t-γ)²]/2 + x(x²-a²) ≥ 0` termwise.
* `log|γ| > log(4(|Im s| + 1))`: the region is too weak there, but then `|γ| > 4(|Im s| + 1)`, and
  the quadratic distance term `x γ²` dominates: `(t² + γ²)/4 - |t||γ| ≥ 4` while
  `x(x² - a²) ≥ -1/8`.

No zero counting and no analytic input are used; only the zero-free region and the exact algebra of
the reflected pair.
-/

open Complex

namespace RHTower

noncomputable section

/-! ### The two numerator inequalities -/

/-- Near regime: the displacement of the zero is at most the displacement of the test point. -/
theorem pairedNumerator_nonneg_near {x t a g : ℝ} (hx : 0 < x) (ha : |a| ≤ x) :
    0 ≤ x * (x ^ 2 - a ^ 2) + x * (t ^ 2 + g ^ 2) - 2 * a * t * g := by
  have h1 : -x ≤ a := neg_le_of_abs_le ha
  have h2 : a ≤ x := le_of_abs_le ha
  have hid : 2 * (x * (x ^ 2 - a ^ 2) + x * (t ^ 2 + g ^ 2) - 2 * a * t * g)
      = 2 * x * (x ^ 2 - a ^ 2) + (x - a) * (t + g) ^ 2 + (x + a) * (t - g) ^ 2 := by ring
  have hsq : 0 ≤ x ^ 2 - a ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - a) (by linarith : (0 : ℝ) ≤ x + a)]
  have h3 : 0 ≤ 2 * x * (x ^ 2 - a ^ 2) :=
    mul_nonneg (by linarith) hsq
  have h4 : 0 ≤ (x - a) * (t + g) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h5 : 0 ≤ (x + a) * (t - g) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hsum : 0 ≤ 2 * (x * (x ^ 2 - a ^ 2) + x * (t ^ 2 + g ^ 2) - 2 * a * t * g) := by
    rw [hid]; linarith
  linarith

/-- Far regime: the ordinate exceeds the square of the test height, so the quadratic distance term
dominates whatever the displacement of the zero. -/
theorem pairedNumerator_nonneg_far {x t a g : ℝ}
    (hx1 : 1 / 4 ≤ x) (hx2 : x ≤ 1 / 2) (ha : |a| ≤ 1 / 2)
    (hg : 4 * (|t| + 1) ≤ |g|) :
    0 ≤ x * (x ^ 2 - a ^ 2) + x * (t ^ 2 + g ^ 2) - 2 * a * t * g := by
  have hT : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hGnn : (0 : ℝ) ≤ |g| := abs_nonneg g
  have hG16 : (4 : ℝ) ≤ |g| := by linarith
  have hcross : 2 * a * t * g ≤ |t| * |g| := by
    have h1 : 2 * a * t * g ≤ |2 * a * t * g| := le_abs_self _
    have habs : |2 * a * t * g| = 2 * |a| * (|t| * |g|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      ring
    rw [habs] at h1
    have h2 : 2 * |a| ≤ 1 := by linarith
    nlinarith [h1, h2, mul_nonneg hT hGnn, abs_nonneg a]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hg2 : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs a, abs_nonneg a, ha]
  have hkey : (1 : ℝ) / 8 ≤ (|t| ^ 2 + |g| ^ 2) / 4 - |t| * |g| := by
    nlinarith [hT, hG16, hg, sq_nonneg (|t|),
      mul_le_mul_of_nonneg_left hg hGnn]
  have hTG : (0 : ℝ) ≤ |t| ^ 2 + |g| ^ 2 := by positivity
  have hstep1 : (|t| ^ 2 + |g| ^ 2) / 4 ≤ x * (|t| ^ 2 + |g| ^ 2) := by nlinarith [hx1, hTG]
  have hstep2 : -(1 / 8 : ℝ) ≤ x * (x ^ 2 - a ^ 2) := by
    nlinarith [hx1, hx2, ha2, sq_nonneg x]
  have hrw : x * (t ^ 2 + g ^ 2) = x * (|t| ^ 2 + |g| ^ 2) := by rw [ht2, hg2]
  linarith [hcross, hkey, hstep1, hstep2, hrw]

/-! ### The paired resolvent term -/

theorem normSq_sub_copy (s : ℂ) (q : XiZeroCopy) :
    normSq (s - (q.1 : ℂ)) = (s.re - (q.1 : ℂ).re) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2 := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem normSq_sub_reflect (s : ℂ) (q : XiZeroCopy) :
    normSq (s - (1 - (q.1 : ℂ)))
      = (s.re - (1 - (q.1 : ℂ).re)) ^ 2 + (s.im + (q.1 : ℂ).im) ^ 2 := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im]
  simp only [Complex.one_re, Complex.one_im]
  ring

/-- **The paired resolvent term is nonnegative once its explicit numerator is.** -/
theorem xiPairedResolventTerm_nonneg_of_numerator {s : ℂ} {q : XiZeroCopy}
    (hA : (0 : ℝ) < normSq (s - (q.1 : ℂ))) (hB : (0 : ℝ) < normSq (s - (1 - (q.1 : ℂ))))
    (hN : 0 ≤ (s.re - 1 / 2) * ((s.re - 1 / 2) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2)
            + (s.re - 1 / 2) * (s.im ^ 2 + ((q.1 : ℂ).im) ^ 2)
            - 2 * ((q.1 : ℂ).re - 1 / 2) * s.im * ((q.1 : ℂ).im)) :
    0 ≤ xiPairedResolventTerm s q := by
  unfold xiPairedResolventTerm
  rw [div_add_div _ _ (ne_of_gt hA) (ne_of_gt hB)]
  refine div_nonneg ?_ (by positivity)
  rw [normSq_sub_copy, normSq_sub_reflect]
  nlinarith [hN]

/-! ### The zero-free region in displacement form -/

/-- Every divisor copy is a zero of `ζ` in the open strip. -/
theorem riemannZeta_eq_zero_of_xiZeroCopy (q : XiZeroCopy) : riemannZeta (q.1 : ℂ) = 0 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hne : (q.1 : ℂ) ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  exact (xi_eq_zero_iff h0 hne).mp (xi_eq_zero_of_mem_divisor_support q.1)

/-- **The zero-free region as a bound on the displacement of a copy.** -/
theorem abs_re_sub_half_le_of_xiZeroCopy (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - 1 / 58 / Real.log |(q.1 : ℂ).im| := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hz := riemannZeta_eq_zero_of_xiZeroCopy q
  have hup := re_le_one_sub_of_zeta_zero h0 h1 hz
  have hlo := one_div_le_re_of_zeta_zero h0 h1 hz
  rw [abs_le]
  constructor <;> linarith

/-- Copies have ordinate at least four, so their logarithm is positive. -/
theorem one_lt_log_abs_im_of_xiZeroCopy (q : XiZeroCopy) : 1 < Real.log |(q.1 : ℂ).im| := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hz := riemannZeta_eq_zero_of_xiZeroCopy q
  have h4 := four_le_abs_im_of_zeta_zero h0 h1 hz
  have hlog4 : 1 < Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    rw [h2]
    linarith
  exact lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4)

/-! ### Hadamard positivity in the zero-free region -/

/-- **`Re (ξ'/ξ) ≥ 0` on `Re s ≥ 1 - 1/(116 log(|Im s| + 4))`.**  The exact Hadamard receiver for
the Riemann Hypothesis, pushed into the critical strip by the width of the zero-free region. -/
theorem re_logDeriv_xi_nonneg_of_zeroFree {s : ℂ}
    (hs : 1 - 1 / 58 / Real.log (4 * (|s.im| + 1)) ≤ s.re) :
    0 ≤ (logDeriv xi s).re := by
  set L : ℝ := Real.log (4 * (|s.im| + 1)) with hLdef
  have hlog4 : 1 < Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    rw [h2]
    linarith
  have hL1 : 1 < L := by
    refine lt_of_lt_of_le hlog4 ?_
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hL0 : 0 < L := by linarith
  have hsmall : 1 / 58 / L < 1 / 4 := by
    rw [div_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL1]
  have hx4 : (1 : ℝ) / 4 ≤ s.re - 1 / 2 := by linarith
  have hxpos : 0 < s.re - 1 / 2 := by linarith
  -- `ξ` does not vanish in the region
  have hsne : xi s ≠ 0 := by
    intro hzero
    rcases le_or_gt 1 s.re with hge | hlt
    · exact xi_ne_zero_of_one_le_re hge hzero
    · have h0 : 0 < s.re := by linarith
      have hne1 : s ≠ 1 := by
        intro h
        rw [h] at hlt
        simp at hlt
      have hz : riemannZeta s = 0 := (xi_eq_zero_iff h0 hne1).mp hzero
      have h4 := four_le_abs_im_of_zeta_zero h0 hlt hz
      have hup := re_le_one_sub_of_zeta_zero h0 hlt hz
      have hlogpos : 1 < Real.log |s.im| :=
        lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4)
      have hcmp : Real.log |s.im| < L := by
        have hmono : Real.log |s.im| < L :=
          Real.log_lt_log (by linarith) (by linarith [abs_nonneg s.im])
        exact hmono
      have h1 : 1 / 58 / L < 1 / 58 / Real.log |s.im| := by
        rw [div_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hcmp, hL0, hlogpos]
      linarith
  -- every paired resolvent term is nonnegative
  have hterm : ∀ q : XiZeroCopy, 0 ≤ xiPairedResolventTerm s q := by
    intro q
    obtain ⟨hb0, hb1⟩ := xi_divisor_support_re_mem_open_unit q.1
    have hxiq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
    have hA : (0 : ℝ) < normSq (s - (q.1 : ℂ)) := by
      refine Complex.normSq_pos.mpr (sub_ne_zero.mpr ?_)
      intro h
      rw [h] at hsne
      exact hsne hxiq
    have hB : (0 : ℝ) < normSq (s - (1 - (q.1 : ℂ))) := by
      refine Complex.normSq_pos.mpr (sub_ne_zero.mpr ?_)
      intro h
      rw [h] at hsne
      exact hsne (by rw [xi_one_sub]; exact hxiq)
    refine xiPairedResolventTerm_nonneg_of_numerator hA hB ?_
    have habs : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    rcases le_or_gt (1 / 2 : ℝ) (s.re - 1 / 2) with hbig | hlt
    · exact pairedNumerator_nonneg_near hxpos (le_trans habs hbig)
    rcases le_or_gt (Real.log |(q.1 : ℂ).im|) L with hnear | hfar
    · refine pairedNumerator_nonneg_near hxpos ?_
      have hglog := one_lt_log_abs_im_of_xiZeroCopy q
      have hzf := abs_re_sub_half_le_of_xiZeroCopy q
      have hcmp : 1 / 58 / L ≤ 1 / 58 / Real.log |(q.1 : ℂ).im| := by
        rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hnear, hL0, hglog]
      linarith
    · refine pairedNumerator_nonneg_far hx4 (le_of_lt hlt) habs ?_
      by_contra hcon
      push Not at hcon
      have hg4 : (4 : ℝ) ≤ |(q.1 : ℂ).im| :=
        four_le_abs_im_of_zeta_zero hb0 hb1 (riemannZeta_eq_zero_of_xiZeroCopy q)
      have hgpos : 0 < |(q.1 : ℂ).im| := by linarith
      have hmono : Real.log |(q.1 : ℂ).im| ≤ Real.log (4 * (|s.im| + 1)) :=
        Real.log_le_log hgpos (le_of_lt hcon)
      rw [← hLdef] at hmono
      linarith
  have htwice := two_mul_re_logDeriv_xi_eq_tsum_paired hsne
  have hsum : 0 ≤ ∑' q : XiZeroCopy, xiPairedResolventTerm s q := tsum_nonneg hterm
  linarith

end

end RHTower
