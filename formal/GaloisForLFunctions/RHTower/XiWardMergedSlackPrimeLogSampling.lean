import GaloisForLFunctions.RHTower.XiWardZeroFreeMarginPrimeLogSampling

/-!
# Merged slack: the relaxed budget survives prime-log sampling

Inside a detection window the continued Ward response exceeds the four-unit
budget by twice the zero-free margin, while the margin itself varies
log-slowly along the edge.  Hence the sampled Euler-edge law remains
RH-complete even after the four-unit budget is relaxed pointwise by the full
margin at the sampled node: on any detection cover, and in particular on the
prime-log sample family, the criterion

`∀ t ∈ S, |r(1/2+it)|² ≤ 4 + m(t)`

is exactly RH.  The discrete criterion is therefore robust to a margin-sized
evaluation error at every node.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

theorem xiWardZeroFreeMargin_le_inv1024 (y : ℝ) :
    xiWardZeroFreeMargin y ≤ 1 / 1024 := by
  have hlog : (2 : ℝ) ≤ Real.log (|y| + 9) := by
    have := two_lt_log_of_nine_le (x := |y| + 9) (by linarith [abs_nonneg y])
    linarith
  have hpow : (512 : ℝ) ≤ Real.log (|y| + 9) ^ (9 : ℕ) := by
    calc (512 : ℝ) = 2 ^ (9 : ℕ) := by norm_num
      _ ≤ Real.log (|y| + 9) ^ (9 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) hlog 9
  have hC := xiWardZeroFreeMarginC_le_half
  have hCpos := xiWardZeroFreeMarginC_pos
  unfold xiWardZeroFreeMargin
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/-- Log-slow variation of the margin: moving the edge height by at most one
loses at most a factor of two. -/
theorem xiWardZeroFreeMargin_close_le_two_mul {t b : ℝ} (h : |t + b| ≤ 1) :
    xiWardZeroFreeMargin t ≤ 2 * xiWardZeroFreeMargin b := by
  have hb : |b| ≤ |t| + 1 := by
    calc |b| = |(t + b) + -t| := by congr 1; ring
      _ ≤ |t + b| + |-t| := abs_add_le _ _
      _ = |t + b| + |t| := by rw [abs_neg]
      _ ≤ |t| + 1 := by linarith
  have hLt : (2 : ℝ) ≤ Real.log (|t| + 9) := by
    have := two_lt_log_of_nine_le (x := |t| + 9) (by linarith [abs_nonneg t])
    linarith
  -- `log(|b|+9) ≤ (17/16)·log(|t|+9)`
  have hquot : Real.log (|b| + 9) ≤ Real.log (|t| + 9) + 1 / 8 := by
    have h1 : Real.log (|b| + 9) ≤ Real.log ((|t| + 9) * (10 / 9)) := by
      apply Real.log_le_log (by linarith [abs_nonneg b])
      nlinarith [abs_nonneg t]
    have h2 : Real.log ((|t| + 9) * (10 / 9)) =
        Real.log (|t| + 9) + Real.log (10 / 9) := by
      rw [Real.log_mul (by linarith [abs_nonneg t]) (by norm_num)]
    have h3 : Real.log (10 / 9) ≤ 1 / 8 := by
      have h4 : (10 / 9 : ℝ) ≤ Real.exp (1 / 8) := by
        have h5 := Real.add_one_le_exp ((1 : ℝ) / 8)
        linarith
      have h6 := Real.log_le_log (by norm_num : (0 : ℝ) < 10 / 9) h4
      rwa [Real.log_exp] at h6
    linarith [h1, h2 ▸ h1, h3]
  have hratio : Real.log (|b| + 9) ≤ (17 / 16) * Real.log (|t| + 9) := by
    nlinarith [hquot, hLt]
  have hLb : (0 : ℝ) ≤ Real.log (|b| + 9) := by
    linarith [one_lt_log_abs_add_nine b]
  have hpow : Real.log (|b| + 9) ^ (9 : ℕ) ≤
      2 * Real.log (|t| + 9) ^ (9 : ℕ) := by
    calc Real.log (|b| + 9) ^ (9 : ℕ)
        ≤ ((17 / 16) * Real.log (|t| + 9)) ^ (9 : ℕ) :=
          pow_le_pow_left₀ hLb hratio 9
      _ = (17 / 16 : ℝ) ^ (9 : ℕ) * Real.log (|t| + 9) ^ (9 : ℕ) := by
          rw [mul_pow]
      _ ≤ 2 * Real.log (|t| + 9) ^ (9 : ℕ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          norm_num
  have hLtpow : (0 : ℝ) < Real.log (|t| + 9) ^ (9 : ℕ) :=
    pow_pos (by linarith) 9
  have hLbpow : (0 : ℝ) < Real.log (|b| + 9) ^ (9 : ℕ) :=
    pow_pos (by linarith [one_lt_log_abs_add_nine b]) 9
  unfold xiWardZeroFreeMargin
  rw [show (2 : ℝ) * (xiWardZeroFreeMarginC / Real.log (|b| + 9) ^ (9 : ℕ)) =
      2 * xiWardZeroFreeMarginC / Real.log (|b| + 9) ^ (9 : ℕ) from
    (mul_div_assoc _ _ _).symm]
  rw [div_le_div_iff₀ hLtpow hLbpow]
  nlinarith [mul_le_mul_of_nonneg_left hpow xiWardZeroFreeMarginC_pos.le]

/-- Inside a detection window the selected pair response exceeds the four-unit
level by half the margin. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_half
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ 2 ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    2 + xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2 <
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  set lam := xiRightCenteredZero q.1
  set w : ℂ := (1 / 2 : ℂ) + I * (t : ℂ) with hwdef
  set m : ℝ := xiWardZeroFreeMargin lam.im with hmdef
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hm0 : 0 < m := xiWardZeroFreeMargin_pos lam.im
  have hm1024 : m ≤ 1 / 1024 := xiWardZeroFreeMargin_le_inv1024 lam.im
  have hM : lam.re ≤ 1 / 2 - m := xiRightCenteredZero_re_le_half_sub_margin q.1
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) lam :=
    xiRightCenteredZero_conj q.1
  have hwre : w.re = 1 / 2 := by
    rw [hwdef]
    norm_num [Complex.add_re, Complex.mul_re]
  have hwim : w.im = t := by
    rw [hwdef]
    norm_num [Complex.add_im, Complex.mul_im]
  have hzre : (w + lam).re = lam.re + 1 / 2 := by
    rw [Complex.add_re, hwre]
    ring
  have hzim : (w + lam).im = t + lam.im := by
    rw [Complex.add_im, hwim]
  have hznormSq : Complex.normSq (w + lam) =
      (lam.re + 1 / 2) ^ 2 + (t + lam.im) ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hdenpos : 0 < (lam.re + 1 / 2) ^ 2 + (t + lam.im) ^ 2 := by
    nlinarith [sq_nonneg (t + lam.im)]
  -- the first inverse dominates `(2 + m/2)/2` after clearing denominators
  have hfirst : (2 + m / 2) / 2 ≤ ((w + lam)⁻¹).re := by
    rw [Complex.inv_re, hzre, hznormSq, div_le_div_iff₀ (by norm_num) hdenpos]
    nlinarith [ht, hM, ha.le, hm0.le, hm1024, sq_nonneg (t + lam.im),
      mul_nonneg ha.le (by linarith : (0 : ℝ) ≤ 1 / 2 - m - lam.re),
      mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - m - lam.re),
      mul_nonneg ha.le hm0.le,
      mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ m / 2 - (t + lam.im) ^ 2),
      mul_le_mul_of_nonneg_left hm1024 hm0.le]
  have hother : 0 < (w + (starRingEnd ℂ) lam).re := by
    rw [Complex.add_re, hwre, Complex.conj_re]
    linarith
  have hiother : 0 < ((w + (starRingEnd ℂ) lam)⁻¹).re :=
    re_inv_pos_of_re_pos hother
  rw [xiAntiCausalWardSchwarzPairResponse, hconj]
  rw [show (2 : ℂ) * ((w + lam)⁻¹ + (w + (starRingEnd ℂ) lam)⁻¹) =
    2 * (w + lam)⁻¹ + 2 * (w + (starRingEnd ℂ) lam)⁻¹ by ring]
  rw [Complex.add_re]
  have h2a : (2 * (w + lam)⁻¹).re = 2 * ((w + lam)⁻¹).re := by
    norm_num [Complex.mul_re]
  have h2b : (2 * (w + (starRingEnd ℂ) lam)⁻¹).re =
      2 * ((w + (starRingEnd ℂ) lam)⁻¹).re := by
    norm_num [Complex.mul_re]
  rw [h2a, h2b]
  linarith [hfirst, hiother]

/-- Inside a detection window the continued response exceeds the four-unit
budget by twice the margin. -/
theorem normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ 2 ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    4 + 2 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im <
      Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hm0 := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hpair :=
    re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_half q ht
  have hfull := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
  have hre : 2 + xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2 <
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
    lt_of_lt_of_le hpair hfull
  have hsq := Complex.re_sq_le_normSq
    (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))
  nlinarith [hre, hsq, hm0]

/-! ## The merged slack sampled law -/

/-- The Euler-edge scalar law sampled on `S` with the budget relaxed pointwise
by the zero-free margin. -/
def ContinuedXiWardMergedSlackSampledScalarLaw (S : Set ℝ) : Prop :=
  ∀ t ∈ S,
    Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) ≤
      4 + xiWardZeroFreeMargin t

theorem continuedXiWardMergedSlackSampledScalarLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Set ℝ) :
    ContinuedXiWardMergedSlackSampledScalarLaw S := by
  intro t _
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw,
    Complex.normSq_zero]
  have := xiWardZeroFreeMargin_pos t
  linarith

theorem riemannHypothesis_of_continuedXiWardMergedSlackSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S)
    (hlaw : ContinuedXiWardMergedSlackSampledScalarLaw S) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im
  have hm0 := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hm1024 :=
    xiWardZeroFreeMargin_le_inv1024 (xiRightCenteredZero q.1).im
  have hclose : |t + (xiRightCenteredZero q.1).im| ≤ 1 := by
    have h1 : (t + (xiRightCenteredZero q.1).im) ^ 2 ≤ 1 := by
      nlinarith [htwin]
    nlinarith [sq_abs (t + (xiRightCenteredZero q.1).im),
      abs_nonneg (t + (xiRightCenteredZero q.1).im),
      sq_nonneg (|t + (xiRightCenteredZero q.1).im| - 1)]
  have hvar : xiWardZeroFreeMargin t ≤
      2 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im :=
    xiWardZeroFreeMargin_close_le_two_mul hclose
  have hgt :=
    normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add q htwin
  have hle := hlaw t htS
  linarith

/-- **Merged slack sampled completeness law.**  On every detection cover the
margin-relaxed sampled four-unit law is exactly RH: the discrete criterion is
robust to a margin-sized error at every node. -/
theorem riemannHypothesis_iff_continuedXiWardMergedSlackSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S) :
    RiemannHypothesis ↔ ContinuedXiWardMergedSlackSampledScalarLaw S :=
  ⟨fun hRH =>
    continuedXiWardMergedSlackSampledScalarLaw_of_riemannHypothesis hRH S,
    riemannHypothesis_of_continuedXiWardMergedSlackSampledScalarLaw hcov⟩

/-- **Prime-log merged slack completeness.**  Past an explicit cutoff, RH is
equivalent to the margin-relaxed four-unit law sampled only on the signed prime
logarithms and one finite grid. -/
theorem exists_cutoff_riemannHypothesis_iff_primeLogMergedSlackScalarLaw :
    ∃ y₁ : ℝ, 3 ≤ y₁ ∧ ∀ Y : ℝ, y₁ ≤ Y →
      (RiemannHypothesis ↔
        ContinuedXiWardMergedSlackSampledScalarLaw
          (xiWardPrimeLogSampleSet Y)) := by
  obtain ⟨y₁, hy₁3, hcov⟩ := exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  exact ⟨y₁, hy₁3, fun Y hY =>
    riemannHypothesis_iff_continuedXiWardMergedSlackSampledScalarLaw
      (hcov Y hY)⟩

end

end RHTower
