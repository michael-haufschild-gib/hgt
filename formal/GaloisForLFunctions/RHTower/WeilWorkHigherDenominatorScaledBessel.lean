import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBesselBoundary

/-!
# Uniform spatial derivatives of the logarithmically normalized Bessel kernel

Writing the scale derivatives relative to the scale cancels the frequency from
the bounds. These are the actual first and second derivatives, not assumed
majorants for a formal Fourier series. The inversion application supplies the
positive scale and its bounded relative derivatives on each compact test support.
-/

noncomputable section

open RHTower.BesselKZero

namespace RHTower.WeilHigherDenominator

def scaledKLog (c : ℝ → ℝ) (k y x : ℝ) : ℝ :=
  kMoment 0 (k * y * c x) / Real.log y

def scaledKLogD (c c' : ℝ → ℝ) (k y x : ℝ) : ℝ :=
  -(k * y * c' x) * kMoment 1 (k * y * c x) / Real.log y

def scaledKLogDD (c c' c'' : ℝ → ℝ) (k y x : ℝ) : ℝ :=
  ((k * y * c' x) ^ 2 * kMoment 2 (k * y * c x) -
    k * y * c'' x * kMoment 1 (k * y * c x)) / Real.log y

theorem hasDerivAt_scaledKLog {c c' : ℝ → ℝ} {k y x : ℝ}
    (hk : 0 < k) (hy : 0 < y) (hc : 0 < c x) (hd : HasDerivAt c (c' x) x) :
    HasDerivAt (scaledKLog c k y) (scaledKLogD c c' k y x) x := by
  have hr := mul_pos (mul_pos hk hy) hc
  refine (((hasDerivAt_kMoment 0 hr).comp x (hd.const_mul (k * y))).div_const
    (Real.log y)).congr_deriv ?_
  dsimp [scaledKLogD]
  ring

theorem hasDerivAt_scaledKLogD {c c' c'' : ℝ → ℝ} {k y x : ℝ}
    (hk : 0 < k) (hy : 0 < y) (hc : 0 < c x)
    (hd : HasDerivAt c (c' x) x) (hd' : HasDerivAt c' (c'' x) x) :
    HasDerivAt (scaledKLogD c c' k y) (scaledKLogDD c c' c'' k y x) x := by
  have hr := mul_pos (mul_pos hk hy) hc
  have hK := (hasDerivAt_kMoment 1 hr).comp x (hd.const_mul (k * y))
  refine ((((hd'.const_mul (k * y)).neg).mul hK).div_const (Real.log y)).congr_deriv ?_
  dsimp [scaledKLogDD]
  ring

/-- The zeroth derivative has a frequency-independent bound above a positive base scale. -/
theorem abs_scaledKLog_le {c : ℝ → ℝ} {k y x c₀ : ℝ}
    (hc₀ : 0 < c₀) (hy : 0 < y) (hk : 1 ≤ k) (hc : c₀ ≤ c x)
    (hsmall : c₀ * y ≤ 1) (hlog : Real.log y ≤ -1) :
    |scaledKLog c k y x| ≤ kMoment 0 1 + |Real.log c₀| + 1 := by
  apply kMoment_zero_div_log_bound hc₀ hy hsmall hlog
  calc
    c₀ * y ≤ c x * y := mul_le_mul_of_nonneg_right hc hy.le
    _ ≤ (k * c x) * y := mul_le_mul_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right hk (hc₀.le.trans hc)) hy.le
    _ = k * y * c x := by ring

/-- One spatial derivative only costs the relative derivative of the scale. -/
theorem abs_scaledKLogD_le {c c' : ℝ → ℝ} {k y x : ℝ}
    (hk : 0 < k) (hy : 0 < y) (hc : 0 < c x) (hlog : Real.log y ≤ -1) :
    |scaledKLogD c c' k y x| ≤ |c' x / c x| := by
  have hr := mul_pos (mul_pos hk hy) hc
  have hM := (kMoment_one_mul_bounds hr).2
  have hM0 := mul_nonneg hr.le (kMoment_nonneg 1 (k * y * c x))
  have hlogabs : 1 ≤ |Real.log y| := by
    rw [abs_of_nonpos (by linarith : Real.log y ≤ 0)]
    linarith
  have he : -(k * y * c' x) * kMoment 1 (k * y * c x) =
      -(c' x / c x) * ((k * y * c x) * kMoment 1 (k * y * c x)) := by
    field_simp [hc.ne']
  rw [scaledKLogD, he, abs_div, abs_mul, abs_neg, abs_of_nonneg hM0]
  calc
    |c' x / c x| * (k * y * c x * kMoment 1 (k * y * c x)) / |Real.log y| ≤
        |c' x / c x| / |Real.log y| :=
      div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left hM (abs_nonneg (c' x / c x))) (abs_nonneg _)
    _ ≤ |c' x / c x| := div_le_self (abs_nonneg _) hlogabs

/-- Two spatial derivatives cost only the first two relative scale derivatives. -/
theorem abs_scaledKLogDD_le {c c' c'' : ℝ → ℝ} {k y x : ℝ}
    (hk : 0 < k) (hy : 0 < y) (hc : 0 < c x) (hlog : Real.log y ≤ -1) :
    |scaledKLogDD c c' c'' k y x| ≤
      (c' x / c x) ^ 2 * (2 + 2 * Real.exp 1 * kMoment 0 1) + |c'' x / c x| := by
  let r := k * y * c x
  have hr : 0 < r := mul_pos (mul_pos hk hy) hc
  have h₁ := (kMoment_one_mul_bounds hr).2
  have h₂ := sq_mul_kMoment_two_le hr
  have h₁0 : 0 ≤ r * kMoment 1 r := mul_nonneg hr.le (kMoment_nonneg 1 r)
  have h₂0 : 0 ≤ r ^ 2 * kMoment 2 r := mul_nonneg (sq_nonneg r) (kMoment_nonneg 2 r)
  have hlogabs : 1 ≤ |Real.log y| := by
    rw [abs_of_nonpos (by linarith : Real.log y ≤ 0)]
    linarith
  have he : (k * y * c' x) ^ 2 * kMoment 2 r - k * y * c'' x * kMoment 1 r =
      (c' x / c x) ^ 2 * (r ^ 2 * kMoment 2 r) - (c'' x / c x) * (r * kMoment 1 r) := by
    dsimp only [r]
    field_simp [hc.ne']
  change |((k * y * c' x) ^ 2 * kMoment 2 r - k * y * c'' x * kMoment 1 r) / Real.log y| ≤ _
  rw [abs_div, he]
  calc
    |(c' x / c x) ^ 2 * (r ^ 2 * kMoment 2 r) - (c'' x / c x) * (r * kMoment 1 r)| /
        |Real.log y| ≤
        |(c' x / c x) ^ 2 * (r ^ 2 * kMoment 2 r) - (c'' x / c x) * (r * kMoment 1 r)| :=
      div_le_self (abs_nonneg _) hlogabs
    _ ≤ |(c' x / c x) ^ 2 * (r ^ 2 * kMoment 2 r)| +
        |(c'' x / c x) * (r * kMoment 1 r)| := abs_sub _ _
    _ = (c' x / c x) ^ 2 * (r ^ 2 * kMoment 2 r) +
        |c'' x / c x| * (r * kMoment 1 r) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg h₂0,
        abs_mul, abs_of_nonneg h₁0]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h₂ (sq_nonneg _))
      (by simpa using mul_le_mul_of_nonneg_left h₁ (abs_nonneg (c'' x / c x)))

end RHTower.WeilHigherDenominator
