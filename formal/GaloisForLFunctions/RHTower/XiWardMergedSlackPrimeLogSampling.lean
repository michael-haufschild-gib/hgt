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

/-- Source allowance retaining the actual detection-window displacement rather than replacing it
by one unit.  Its coefficient relative to `xiWardZeroFreeMargin t` tends to three. -/
def xiWardRefinedSampleSlack (t : ℝ) : ℝ :=
  3 * xiWardZeroFreeMarginC /
    (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ)

/-- Sharp uniform coefficient for the first Lorentzian detector kernel under
`m ≤ 1/1024` and squared displacement at most `m/2`. -/
def xiWardSharpRealSlackCoefficient : ℝ := 1046528 / 1047041

theorem xiWardSharpRealSlackCoefficient_pos :
    0 < xiWardSharpRealSlackCoefficient := by
  norm_num [xiWardSharpRealSlackCoefficient]

/-- Refined source allowance for the real channel.  Its coefficient relative
to the local margin tends to the sharp detector coefficient above. -/
def xiWardRefinedRealSampleSlack (t : ℝ) : ℝ :=
  xiWardSharpRealSlackCoefficient * xiWardZeroFreeMarginC /
    (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ)

/-- Margin proxy transported exactly across the `1/405` detector displacement. -/
def xiWardRefinedMarginProxy (t : ℝ) : ℝ :=
  xiWardZeroFreeMarginC /
    (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ)

/-- Exact excess of the worst first Lorentzian detector kernel at margin `m`. -/
def xiWardDetectorRealExcess (m : ℝ) : ℝ :=
  m * (1 - 2 * m) / (1 - 3 * m / 2 + m ^ (2 : ℕ))

/-- Adaptive real-channel allowance retaining the exact transported detector excess. -/
def xiWardAdaptiveRealSampleSlack (t : ℝ) : ℝ :=
  xiWardDetectorRealExcess (xiWardRefinedMarginProxy t)

theorem xiWardRefinedSampleSlack_pos (t : ℝ) : 0 < xiWardRefinedSampleSlack t := by
  have hlog := one_lt_log_abs_add_nine t
  unfold xiWardRefinedSampleSlack
  exact div_pos (mul_pos (by norm_num) xiWardZeroFreeMarginC_pos)
    (pow_pos (by linarith) 9)

theorem xiWardRefinedRealSampleSlack_pos (t : ℝ) :
    0 < xiWardRefinedRealSampleSlack t := by
  have hlog := one_lt_log_abs_add_nine t
  unfold xiWardRefinedRealSampleSlack
  exact div_pos
    (mul_pos xiWardSharpRealSlackCoefficient_pos xiWardZeroFreeMarginC_pos)
    (pow_pos (by linarith) 9)

theorem xiWardRefinedMarginProxy_pos (t : ℝ) :
    0 < xiWardRefinedMarginProxy t := by
  have hlog := one_lt_log_abs_add_nine t
  unfold xiWardRefinedMarginProxy
  exact div_pos xiWardZeroFreeMarginC_pos (pow_pos (by linarith) 9)

theorem xiWardDetectorRealExcess_den_pos {m : ℝ}
    (hm : m ≤ 1 / 1024) :
    0 < 1 - 3 * m / 2 + m ^ (2 : ℕ) := by
  nlinarith [sq_nonneg m]

/-- Exact detector excess is monotone throughout the admissible margin interval. -/
theorem xiWardDetectorRealExcess_mono {r b : ℝ} (hr0 : 0 ≤ r) (hrb : r ≤ b)
    (hb : b ≤ 1 / 1024) :
    xiWardDetectorRealExcess r ≤ xiWardDetectorRealExcess b := by
  have hb0 : 0 ≤ b := hr0.trans hrb
  have hrmax : r ≤ 1 / 1024 := hrb.trans hb
  have hDr := xiWardDetectorRealExcess_den_pos hrmax
  have hDb := xiWardDetectorRealExcess_den_pos hb
  have hP : 0 ≤ 1 - 2 * b - 2 * r + 2 * b * r := by
    nlinarith [mul_nonneg hb0 hr0]
  have hfactor :
      b * (1 - 2 * b) * (1 - 3 * r / 2 + r ^ (2 : ℕ)) -
          r * (1 - 2 * r) * (1 - 3 * b / 2 + b ^ (2 : ℕ)) =
        (b - r) * (1 - 2 * b - 2 * r + 2 * b * r) := by ring
  unfold xiWardDetectorRealExcess
  rw [div_le_div_iff₀ hDr hDb]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrb) hP]

/-- The true Ward detection window is narrower than `1/45`; the earlier unit displacement was a
deliberately coarse compatibility bound. -/
theorem abs_add_le_one_over_fortyFive_of_xiWard_marginWindow {t b : ℝ}
    (ht : (t + b) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin b / 2) :
    |t + b| ≤ 1 / 45 := by
  have hm := xiWardZeroFreeMargin_le_inv1024 b
  have hd : (t + b) ^ (2 : ℕ) ≤ 1 / 2048 := by nlinarith
  nlinarith [sq_abs (t + b), abs_nonneg (t + b),
    sq_nonneg (|t + b| - 1 / 45)]

/-- Refined log variation across a genuine Ward detection window. -/
theorem log_abs_add_nine_le_refined_of_xiWard_marginWindow {t b : ℝ}
    (ht : (t + b) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin b / 2) :
    Real.log (|b| + 9) ≤ Real.log (|t| + 9) + 1 / 405 := by
  have hdist := abs_add_le_one_over_fortyFive_of_xiWard_marginWindow ht
  have hb : |b| ≤ |t| + 1 / 45 := by
    calc
      |b| = |(t + b) + -t| := by congr 1; ring
      _ ≤ |t + b| + |-t| := abs_add_le _ _
      _ = |t + b| + |t| := by rw [abs_neg]
      _ ≤ |t| + 1 / 45 := by linarith
  have harg : |b| + 9 ≤ (|t| + 9) * (406 / 405) := by
    nlinarith [abs_nonneg t]
  have hlogarg : Real.log (|b| + 9) ≤
      Real.log ((|t| + 9) * (406 / 405)) :=
    Real.log_le_log (by linarith [abs_nonneg b]) harg
  have hmul : Real.log ((|t| + 9) * (406 / 405)) =
      Real.log (|t| + 9) + Real.log (406 / 405) := by
    rw [Real.log_mul (by linarith [abs_nonneg t]) (by norm_num)]
  have hsmall : Real.log (406 / 405) ≤ 1 / 405 := by
    have hexp : (406 / 405 : ℝ) ≤ Real.exp (1 / 405) := by
      have := Real.add_one_le_exp ((1 : ℝ) / 405)
      linarith
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 406 / 405) hexp
    rwa [Real.log_exp] at hlog
  linarith

/-- At any detector-selected node, refined sampled slack stays below the strict three-margin
off-line excess at the zero height. -/
theorem xiWardRefinedSampleSlack_le_three_mul_margin_of_marginWindow
    {t b : ℝ} (ht : (t + b) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin b / 2) :
    xiWardRefinedSampleSlack t ≤ 3 * xiWardZeroFreeMargin b := by
  have hlog := log_abs_add_nine_le_refined_of_xiWard_marginWindow ht
  have hLt : 0 < Real.log (|t| + 9) + 1 / 405 := by
    have := one_lt_log_abs_add_nine t
    linarith
  have hLb : 0 < Real.log (|b| + 9) := by
    linarith [one_lt_log_abs_add_nine b]
  have hpow : Real.log (|b| + 9) ^ (9 : ℕ) ≤
      (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ) :=
    pow_le_pow_left₀ hLb.le hlog 9
  unfold xiWardRefinedSampleSlack xiWardZeroFreeMargin
  rw [show 3 * (xiWardZeroFreeMarginC / Real.log (|b| + 9) ^ (9 : ℕ)) =
      3 * xiWardZeroFreeMarginC / Real.log (|b| + 9) ^ (9 : ℕ) by ring]
  rw [div_le_div_iff₀ (pow_pos hLt 9) (pow_pos hLb 9)]
  exact mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (by norm_num) xiWardZeroFreeMarginC_pos.le)

/-- Detector-window transfer for the sharp real-channel allowance. -/
theorem xiWardRefinedRealSampleSlack_le_coefficient_mul_margin_of_marginWindow
    {t b : ℝ} (ht : (t + b) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin b / 2) :
    xiWardRefinedRealSampleSlack t ≤
      xiWardSharpRealSlackCoefficient * xiWardZeroFreeMargin b := by
  have h := xiWardRefinedSampleSlack_le_three_mul_margin_of_marginWindow ht
  have hc : 0 ≤ xiWardSharpRealSlackCoefficient / 3 := by
    exact div_nonneg xiWardSharpRealSlackCoefficient_pos.le (by norm_num)
  calc
    xiWardRefinedRealSampleSlack t =
        (xiWardSharpRealSlackCoefficient / 3) * xiWardRefinedSampleSlack t := by
      unfold xiWardRefinedRealSampleSlack xiWardRefinedSampleSlack
      ring
    _ ≤ (xiWardSharpRealSlackCoefficient / 3) *
        (3 * xiWardZeroFreeMargin b) :=
      mul_le_mul_of_nonneg_left h hc
    _ = xiWardSharpRealSlackCoefficient * xiWardZeroFreeMargin b := by ring

/-- The refined proxy itself stays below the true zero-height margin in every
detector window. -/
theorem xiWardRefinedMarginProxy_le_margin_of_marginWindow
    {t b : ℝ} (ht : (t + b) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin b / 2) :
    xiWardRefinedMarginProxy t ≤ xiWardZeroFreeMargin b := by
  have h := xiWardRefinedSampleSlack_le_three_mul_margin_of_marginWindow ht
  have heq : xiWardRefinedSampleSlack t = 3 * xiWardRefinedMarginProxy t := by
    unfold xiWardRefinedSampleSlack xiWardRefinedMarginProxy
    ring
  rw [heq] at h
  nlinarith

theorem xiWardRefinedMarginProxy_le_inv1024 (t : ℝ) :
    xiWardRefinedMarginProxy t ≤ 1 / 1024 := by
  have ht : ((-t) + t) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin t / 2 := by
    nlinarith [xiWardZeroFreeMargin_pos t]
  have h := xiWardRefinedMarginProxy_le_margin_of_marginWindow ht
  rw [show xiWardRefinedMarginProxy (-t) = xiWardRefinedMarginProxy t by
    simp [xiWardRefinedMarginProxy]] at h
  exact h.trans (xiWardZeroFreeMargin_le_inv1024 t)

/-- Adaptive allowance transfers without replacing the actual margin by its
global maximum. -/
theorem xiWardAdaptiveRealSampleSlack_le_detectorExcess_of_marginWindow
    {t b : ℝ} (ht : (t + b) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin b / 2) :
    xiWardAdaptiveRealSampleSlack t ≤
      xiWardDetectorRealExcess (xiWardZeroFreeMargin b) := by
  exact xiWardDetectorRealExcess_mono (xiWardRefinedMarginProxy_pos t).le
    (xiWardRefinedMarginProxy_le_margin_of_marginWindow ht)
    (xiWardZeroFreeMargin_le_inv1024 b)

theorem xiWardDetectorRealExcess_pos {m : ℝ} (hm0 : 0 < m)
    (hm : m ≤ 1 / 1024) : 0 < xiWardDetectorRealExcess m := by
  unfold xiWardDetectorRealExcess
  exact div_pos (mul_pos hm0 (by nlinarith))
    (xiWardDetectorRealExcess_den_pos hm)

theorem xiWardAdaptiveRealSampleSlack_pos (t : ℝ) :
    0 < xiWardAdaptiveRealSampleSlack t := by
  exact xiWardDetectorRealExcess_pos (xiWardRefinedMarginProxy_pos t)
    (xiWardRefinedMarginProxy_le_inv1024 t)

/-- The earlier fixed coefficient is the worst-margin specialization of the
adaptive exact excess. -/
theorem xiWardSharpRealSlackCoefficient_mul_le_detectorRealExcess
    {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1 / 1024) :
    xiWardSharpRealSlackCoefficient * m ≤ xiWardDetectorRealExcess m := by
  have hD := xiWardDetectorRealExcess_den_pos hm
  unfold xiWardSharpRealSlackCoefficient xiWardDetectorRealExcess
  rw [le_div_iff₀ hD]
  nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm)]

theorem xiWardRefinedRealSampleSlack_le_adaptive (t : ℝ) :
    xiWardRefinedRealSampleSlack t ≤ xiWardAdaptiveRealSampleSlack t := by
  have h := xiWardSharpRealSlackCoefficient_mul_le_detectorRealExcess
    (xiWardRefinedMarginProxy_pos t).le (xiWardRefinedMarginProxy_le_inv1024 t)
  calc
    xiWardRefinedRealSampleSlack t =
        xiWardSharpRealSlackCoefficient * xiWardRefinedMarginProxy t := by
      unfold xiWardRefinedRealSampleSlack xiWardRefinedMarginProxy
      ring
    _ ≤ xiWardDetectorRealExcess (xiWardRefinedMarginProxy t) := h
    _ = xiWardAdaptiveRealSampleSlack t := rfl

/-- The sharp real-channel allowance is strictly larger than one quarter of
the refined norm-square allowance used by the first real reduction. -/
theorem refinedSampleSlack_div_four_lt_refinedRealSampleSlack (t : ℝ) :
    xiWardRefinedSampleSlack t / 4 < xiWardRefinedRealSampleSlack t := by
  have hA : 0 < xiWardZeroFreeMarginC /
      (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ) := by
    have hlog := one_lt_log_abs_add_nine t
    exact div_pos xiWardZeroFreeMarginC_pos (pow_pos (by linarith) 9)
  unfold xiWardRefinedSampleSlack xiWardRefinedRealSampleSlack
  rw [show (3 * xiWardZeroFreeMarginC /
        (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ)) / 4 =
      (3 / 4 : ℝ) * (xiWardZeroFreeMarginC /
        (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ)) by ring]
  rw [show xiWardSharpRealSlackCoefficient * xiWardZeroFreeMarginC /
        (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ) =
      xiWardSharpRealSlackCoefficient * (xiWardZeroFreeMarginC /
        (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ)) by ring]
  apply mul_lt_mul_of_pos_right _ hA
  norm_num [xiWardSharpRealSlackCoefficient]

/-- The refined source allowance is pointwise strictly larger than the previous three-halves
margin allowance. -/
theorem threeHalves_mul_xiWardZeroFreeMargin_lt_refinedSampleSlack (t : ℝ) :
    (3 / 2 : ℝ) * xiWardZeroFreeMargin t < xiWardRefinedSampleSlack t := by
  have hL : 2 ≤ Real.log (|t| + 9) := by
    have := two_lt_log_of_nine_le (x := |t| + 9) (by linarith [abs_nonneg t])
    linarith
  have hLpos : 0 < Real.log (|t| + 9) := by linarith
  have hApos : 0 < Real.log (|t| + 9) + 1 / 405 := by linarith
  have hA : Real.log (|t| + 9) + 1 / 405 ≤
      (811 / 810 : ℝ) * Real.log (|t| + 9) := by
    nlinarith
  have hpow : (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ) <
      2 * Real.log (|t| + 9) ^ (9 : ℕ) := by
    calc
      (Real.log (|t| + 9) + 1 / 405) ^ (9 : ℕ) ≤
          ((811 / 810 : ℝ) * Real.log (|t| + 9)) ^ (9 : ℕ) :=
        pow_le_pow_left₀ hApos.le hA 9
      _ = (811 / 810 : ℝ) ^ (9 : ℕ) *
          Real.log (|t| + 9) ^ (9 : ℕ) := by rw [mul_pow]
      _ < 2 * Real.log (|t| + 9) ^ (9 : ℕ) := by
        apply mul_lt_mul_of_pos_right (by norm_num)
        positivity
  unfold xiWardRefinedSampleSlack xiWardZeroFreeMargin
  rw [show (3 / 2 : ℝ) *
      (xiWardZeroFreeMarginC / Real.log (|t| + 9) ^ (9 : ℕ)) =
      ((3 / 2 : ℝ) * xiWardZeroFreeMarginC) /
        Real.log (|t| + 9) ^ (9 : ℕ) by ring]
  rw [div_lt_div_iff₀ (pow_pos hLpos 9) (pow_pos hApos 9)]
  nlinarith [xiWardZeroFreeMarginC_pos]

/-- Exact adaptive real-channel detector bound.  The first kernel attains the
rational function `xiWardDetectorRealExcess`; the positive conjugate kernel
makes the complete pair inequality strict. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_detectorExcess
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    2 + xiWardDetectorRealExcess
        (xiWardZeroFreeMargin (xiRightCenteredZero q.1).im) <
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  set lam := xiRightCenteredZero q.1
  set w : ℂ := (1 / 2 : ℂ) + I * (t : ℂ) with hwdef
  set m : ℝ := xiWardZeroFreeMargin lam.im with hmdef
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hm0 : 0 < m := xiWardZeroFreeMargin_pos lam.im
  have hm1024 : m ≤ 1 / 1024 := xiWardZeroFreeMargin_le_inv1024 lam.im
  have hD : 0 < 1 - 3 * m / 2 + m ^ (2 : ℕ) :=
    xiWardDetectorRealExcess_den_pos hm1024
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
      (lam.re + 1 / 2) ^ (2 : ℕ) + (t + lam.im) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hdenpos : 0 < (lam.re + 1 / 2) ^ (2 : ℕ) + (t + lam.im) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (t + lam.im)]
  have hfirst : (1 - m) / (1 - 3 * m / 2 + m ^ (2 : ℕ)) ≤ ((w + lam)⁻¹).re := by
    rw [Complex.inv_re, hzre, hznormSq, div_le_div_iff₀ hD hdenpos]
    nlinarith [ht, hM, ha.le, hm0.le, hm1024, sq_nonneg (t + lam.im),
      mul_nonneg ha.le (by linarith : (0 : ℝ) ≤ 1 / 2 - m - lam.re),
      mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - m - lam.re),
      mul_nonneg ha.le hm0.le,
      mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ m / 2 - (t + lam.im) ^ (2 : ℕ)),
      mul_le_mul_of_nonneg_left hm1024 hm0.le]
  have hid : 2 * ((1 - m) / (1 - 3 * m / 2 + m ^ (2 : ℕ))) =
      2 + xiWardDetectorRealExcess m := by
    have hcancel :
        (2 * (1 - 3 * m / 2 + m ^ (2 : ℕ))) / (1 - 3 * m / 2 + m ^ (2 : ℕ)) = 2 := by
      simpa [mul_comm] using mul_div_cancel_left₀ 2 (ne_of_gt hD)
    unfold xiWardDetectorRealExcess
    calc
      2 * ((1 - m) / (1 - 3 * m / 2 + m ^ (2 : ℕ))) =
          (2 * (1 - m)) / (1 - 3 * m / 2 + m ^ (2 : ℕ)) := by ring
      _ = (2 * (1 - 3 * m / 2 + m ^ (2 : ℕ)) + m * (1 - 2 * m)) /
          (1 - 3 * m / 2 + m ^ (2 : ℕ)) := by ring
      _ = 2 + m * (1 - 2 * m) / (1 - 3 * m / 2 + m ^ (2 : ℕ)) := by
        rw [add_div, hcancel]
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
  dsimp [m]
  rw [← hid]
  nlinarith

/-- Uniform sharp-coefficient compatibility form, derived from the exact
adaptive excess rather than reproving detector geometry. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_sharp
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    2 + xiWardSharpRealSlackCoefficient *
        xiWardZeroFreeMargin (xiRightCenteredZero q.1).im <
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  have hexact :=
    re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_detectorExcess
      q ht
  have hm0 := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hcoef := xiWardSharpRealSlackCoefficient_mul_le_detectorRealExcess
    hm0.le (xiWardZeroFreeMargin_le_inv1024 (xiRightCenteredZero q.1).im)
  linarith

/-- Compatibility form retaining the earlier three-quarters detector API. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_three_quarters
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    2 + 3 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 4 <
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  have hstrong :=
    re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_sharp q ht
  have hm0 := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hc : (3 / 4 : ℝ) < xiWardSharpRealSlackCoefficient := by
    norm_num [xiWardSharpRealSlackCoefficient]
  nlinarith

/-- Compatibility form of the detection-window pair lower bound. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_half
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    2 + xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2 <
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  have hstrong :=
    re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_three_quarters q ht
  have hm0 := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  linarith

/-- Inside a detection window the continued response exceeds the four-unit
budget by twice the margin. -/
theorem normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
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

/-- The sharpened detection-window estimate leaves three full margin units
above the four-unit budget. -/
theorem normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add_three
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    4 + 3 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im <
      Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hm0 := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hpair :=
    re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_three_quarters q ht
  have hfull := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
  have hre : 2 + 3 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 4 <
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
    have h1 : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤ 1 := by
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

/-- The sampled Ward scalar law with a three-halves local-margin allowance.  It
is strictly weaker than the full-margin law while retaining the same detector. -/
def ContinuedXiWardThreeHalvesSlackSampledScalarLaw (S : Set ℝ) : Prop :=
  ∀ t ∈ S,
    Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) ≤
      4 + (3 / 2 : ℝ) * xiWardZeroFreeMargin t

theorem continuedXiWardThreeHalvesSlackSampledScalarLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Set ℝ) :
    ContinuedXiWardThreeHalvesSlackSampledScalarLaw S := by
  intro t _
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw,
    Complex.normSq_zero]
  have := xiWardZeroFreeMargin_pos t
  linarith

theorem riemannHypothesis_of_continuedXiWardThreeHalvesSlackSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S)
    (hlaw : ContinuedXiWardThreeHalvesSlackSampledScalarLaw S) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im
  have hclose : |t + (xiRightCenteredZero q.1).im| ≤ 1 := by
    have hbound :=
      xiWardZeroFreeMargin_le_inv1024 (xiRightCenteredZero q.1).im
    have h1 : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤ 1 := by
      nlinarith [htwin]
    nlinarith [sq_abs (t + (xiRightCenteredZero q.1).im),
      abs_nonneg (t + (xiRightCenteredZero q.1).im),
      sq_nonneg (|t + (xiRightCenteredZero q.1).im| - 1)]
  have hvar : xiWardZeroFreeMargin t ≤
      2 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im :=
    xiWardZeroFreeMargin_close_le_two_mul hclose
  have hgt :=
    normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add_three q htwin
  have hle := hlaw t htS
  linarith

/-- **Three-halves-slack sampled completeness law.**  The same detection cover
still decides RH after enlarging every sampled budget by three halves of its
local zero-free margin. -/
theorem riemannHypothesis_iff_continuedXiWardThreeHalvesSlackSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S) :
    RiemannHypothesis ↔ ContinuedXiWardThreeHalvesSlackSampledScalarLaw S :=
  ⟨fun hRH =>
    continuedXiWardThreeHalvesSlackSampledScalarLaw_of_riemannHypothesis hRH S,
    riemannHypothesis_of_continuedXiWardThreeHalvesSlackSampledScalarLaw hcov⟩

/-- The weakest sampled Ward scalar law currently available: the allowance keeps the exact
`1/405` log displacement forced by a genuine detection window and approaches three margin units
at large height. -/
def ContinuedXiWardRefinedSlackSampledScalarLaw (S : Set ℝ) : Prop :=
  ∀ t ∈ S,
    Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) ≤
      4 + xiWardRefinedSampleSlack t

theorem continuedXiWardRefinedSlackSampledScalarLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Set ℝ) :
    ContinuedXiWardRefinedSlackSampledScalarLaw S := by
  intro t _
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw,
    Complex.normSq_zero]
  linarith [xiWardRefinedSampleSlack_pos t]

theorem riemannHypothesis_of_continuedXiWardRefinedSlackSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S)
    (hlaw : ContinuedXiWardRefinedSlackSampledScalarLaw S) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im
  have hslack :=
    xiWardRefinedSampleSlack_le_three_mul_margin_of_marginWindow htwin
  have hgt :=
    normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add_three q htwin
  have hle := hlaw t htS
  linarith

/-- The previous three-halves law implies the refined law pointwise; the latter has a strictly
larger allowance at every sample. -/
theorem continuedXiWardThreeHalvesSlackSampledScalarLaw_implies_refinedSlack
    {S : Set ℝ} (h : ContinuedXiWardThreeHalvesSlackSampledScalarLaw S) :
    ContinuedXiWardRefinedSlackSampledScalarLaw S := by
  intro t ht
  exact (h t ht).trans (by
    simpa [add_comm] using add_le_add_left
      (threeHalves_mul_xiWardZeroFreeMargin_lt_refinedSampleSlack t).le 4)

/-- **Refined-slack sampled completeness law.**  Exact detector variation permits a pointwise
allowance asymptotic to three margin units while the same detection cover still decides RH. -/
theorem riemannHypothesis_iff_continuedXiWardRefinedSlackSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S) :
    RiemannHypothesis ↔ ContinuedXiWardRefinedSlackSampledScalarLaw S :=
  ⟨fun hRH =>
    continuedXiWardRefinedSlackSampledScalarLaw_of_riemannHypothesis hRH S,
    riemannHypothesis_of_continuedXiWardRefinedSlackSampledScalarLaw hcov⟩

/-! ## Real-channel reduction -/

/-- The source-facing form of the refined sampled endpoint.  Only the real
Herglotz channel must stay below the two-unit detector threshold; no estimate
of the independent imaginary channel is required. -/
def ContinuedXiWardRefinedSlackSampledRealLaw (S : Set ℝ) : Prop :=
  ∀ t ∈ S,
    (continuedXiAntiCausalWardResponse
      ((1 / 2 : ℂ) + I * (t : ℂ))).re ≤
        2 + xiWardAdaptiveRealSampleSlack t

theorem continuedXiWardRefinedSlackSampledRealLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Set ℝ) :
    ContinuedXiWardRefinedSlackSampledRealLaw S := by
  intro t _
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw]
  norm_num
  nlinarith [xiWardAdaptiveRealSampleSlack_pos t]

theorem riemannHypothesis_of_continuedXiWardRefinedSlackSampledRealLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S)
    (hlaw : ContinuedXiWardRefinedSlackSampledRealLaw S) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im
  have hslack :=
    xiWardAdaptiveRealSampleSlack_le_detectorExcess_of_marginWindow htwin
  have hpair :=
    re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_detectorExcess
      q htwin
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hfull := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
  have hle := hlaw t htS
  linarith

/-- The refined norm-square law implies the real-channel law pointwise.  The
converse need not hold without controlling the independent odd channel. -/
theorem continuedXiWardRefinedSlackSampledScalarLaw_implies_realLaw
    {S : Set ℝ} (h : ContinuedXiWardRefinedSlackSampledScalarLaw S) :
    ContinuedXiWardRefinedSlackSampledRealLaw S := by
  intro t ht
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hre := re_continuedXiAntiCausalWardResponse_nonneg hw
  have hsq := Complex.re_sq_le_normSq
    (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))
  have hnorm := h t ht
  have hcompare := refinedSampleSlack_div_four_lt_refinedRealSampleSlack t
  have hadaptive := xiWardRefinedRealSampleSlack_le_adaptive t
  nlinarith [xiWardRefinedSampleSlack_pos t]

/-- **Real-channel sampled completeness.**  On a detection cover, the
refined two-unit real-part ceiling is exactly RH and is a strictly lower source
burden than the corresponding complex norm-square ceiling. -/
theorem riemannHypothesis_iff_continuedXiWardRefinedSlackSampledRealLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S) :
    RiemannHypothesis ↔ ContinuedXiWardRefinedSlackSampledRealLaw S :=
  ⟨fun hRH =>
    continuedXiWardRefinedSlackSampledRealLaw_of_riemannHypothesis hRH S,
    riemannHypothesis_of_continuedXiWardRefinedSlackSampledRealLaw hcov⟩

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
