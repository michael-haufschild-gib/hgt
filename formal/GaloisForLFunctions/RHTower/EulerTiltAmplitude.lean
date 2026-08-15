import GaloisForLFunctions.RHTower.EulerTiltCharacteristic
import GaloisForLFunctions.RHTower.EulerTiltEscape

/-!
# The all-cumulant Euler-edge amplitude

At the source-faithful tilt and the escape frequency the oscillatory prime defect is bounded, so
the parity–energy characteristic function has logarithmic modulus `-2 log ℓ + O(1)`:

```text
|E e^{i(πN - t* E)}| = ℓ^{-2} e^{O(1)}.
```

This is the exact all-cumulant amplitude of the Euler edge: it is only logarithmically small, not
Gaussian-small.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The escape frequency of the saddle tilt at aperture parameter `L`. -/
def saddleFrequency (L : ℝ) : ℝ :=
  eulerTiltEscapeFrequency (1 + saddleTilt L) (cofinalAperture L)

theorem tendsto_saddleFrequency_mul_apertureLog :
    Tendsto (fun L : ℝ => saddleFrequency L * apertureLog L) atTop (nhds (2 * Real.pi)) :=
  tendsto_escapeFrequency_mul_apertureLog

theorem tendsto_saddleFrequency : Tendsto saddleFrequency atTop (nhds 0) := by
  have hmul := tendsto_saddleFrequency_mul_apertureLog
  have hquot := hmul.div_atTop tendsto_apertureLog
  refine hquot.congr' ?_
  filter_upwards [tendsto_apertureLog.eventually_gt_atTop 1] with L hℓ
  have hℓ0 : apertureLog L ≠ 0 := by
    intro h
    rw [h] at hℓ
    linarith
  field_simp

/-- Numerical comparison used to make the split point large. -/
theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [h, Real.exp_pos 1, hsq]

/-- The quadratic head of the defect is bounded once the split point is `e^{1/t}`. -/
theorem quadraticHead_le {t Z : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hZ2 : 2 ≤ Z) (hlogZ : Real.log Z = 1 / t) :
    t ^ 2 / 2 * primeLogSqSumLE Z ≤ 1 / 4 + mertensLogSqConst + Real.log 2 ^ 2 / 2 := by
  have hlogsq := abs_primeLogSqSumLE_sub_le hZ2
  have hMnn : 0 ≤ mertensLogSqConst := mertensLogSqConst_nonneg
  have hb := abs_le.mp hlogsq
  have hupper : primeLogSqSumLE Z
      ≤ Real.log Z ^ 2 / 2 + mertensLogSqConst * (1 + Real.log Z) + Real.log 2 ^ 2 / 2 := by
    linarith [hb.2]
  have hstep := mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
  refine le_trans hstep ?_
  rw [hlogZ]
  have hval : t ^ 2 / 2 * ((1 / t) ^ 2 / 2 + mertensLogSqConst * (1 + 1 / t)
      + Real.log 2 ^ 2 / 2)
      = 1 / 4 + mertensLogSqConst * (t ^ 2 / 2 + t / 2) + t ^ 2 * Real.log 2 ^ 2 / 4 := by
    field_simp
    ring
  rw [hval]
  have hfac : t ^ 2 / 2 + t / 2 ≤ 1 := by nlinarith [ht0, ht1]
  have h1 : mertensLogSqConst * (t ^ 2 / 2 + t / 2) ≤ mertensLogSqConst := by
    have := mul_le_mul_of_nonneg_left hfac hMnn
    linarith [this]
  have hsq : t ^ 2 ≤ 2 := by nlinarith [ht0, ht1]
  have h2 : t ^ 2 * Real.log 2 ^ 2 / 4 ≤ Real.log 2 ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log 2))
    linarith [this]
  linarith

/-- Mertens' second theorem bounds the harmonic tail by the logarithm of the resonance ratio. -/
theorem harmonicTail_le {t Y Z : ℝ} (ht0 : 0 < t) (hY : Real.exp 2 ≤ Y)
    (hZexp2 : Real.exp 2 ≤ Z) (hlogZ : Real.log Z = 1 / t) :
    Sieve.mertensS ⌊Y⌋₊ - Sieve.mertensS ⌊Z⌋₊
      ≤ Real.log (t * Real.log Y) + 3 + 4 * Sieve.mertensFirstConst := by
  have hexp2 := seven_lt_exp_two
  have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hY
  have hZ7 : (7 : ℝ) < Z := lt_of_lt_of_le hexp2 hZexp2
  have hlogY : (2 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 2) hY
    rwa [Real.log_exp] at h
  have hfloorY2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Y))
  have hfloorZ2 : 2 ≤ ⌊Z⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Z))
  have hfloorY6 : (6 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Y))
    exact_mod_cast h
  have hfloorZ6 : (6 : ℝ) ≤ ((⌊Z⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊Z⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Z))
    exact_mod_cast h
  have hexp1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogfloorY : (1 : ℝ) ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ ((⌊Y⌋₊ : ℕ) : ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hlogfloorZ : (1 : ℝ) ≤ Real.log ((⌊Z⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ ((⌊Z⌋₊ : ℕ) : ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hmY := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloorY2)
  have hmZ := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloorZ2)
  have hfY := abs_le.mp (abs_logLog_floor_sub_le hY)
  have hfZ := abs_le.mp (abs_logLog_floor_sub_le hZexp2)
  have hC1 : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have := Sieve.mertensFirstConst_nonneg
    linarith
  have hdivY : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊Y⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hC1, hlogfloorY]
  have hdivZ : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊Z⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hC1, hlogfloorZ]
  have hlogratio : Real.log (Real.log Y) - Real.log (Real.log Z) = Real.log (t * Real.log Y) := by
    rw [hlogZ, Real.log_div one_ne_zero (ne_of_gt ht0), Real.log_one,
      Real.log_mul (ne_of_gt ht0) (by linarith : Real.log Y ≠ 0)]
    ring
  linarith [hmY.2, hmZ.1, hfY.1, hfY.2, hfZ.1, hfZ.2, hdivY, hdivZ, hlogratio]

/-- **The oscillatory defect is bounded by the resonance ratio.** -/
theorem abs_primeCosineDefect_le_const {σ t Y : ℝ} (hσ : 1 ≤ σ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hY : Real.exp 2 ≤ Y) (htY : 1 ≤ t * Real.log Y) :
    |primeCosineDefect σ t Y|
      ≤ (1 / 4 + mertensLogSqConst + Real.log 2 ^ 2 / 2)
        + 2 * (Real.log (t * Real.log Y) + 3 + 4 * Sieve.mertensFirstConst) := by
  have hexp2 := seven_lt_exp_two
  have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hY
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = Real.exp (1 / t) := ⟨_, rfl⟩
  have hinvt : (2 : ℝ) ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    linarith
  have hlogZ : Real.log Z = 1 / t := by rw [hZdef]; exact Real.log_exp _
  have hZexp2 : Real.exp 2 ≤ Z := by rw [hZdef]; exact Real.exp_le_exp.mpr hinvt
  have hZ7 : (7 : ℝ) < Z := lt_of_lt_of_le hexp2 hZexp2
  have hZ2 : (2 : ℝ) ≤ Z := by linarith
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZY : Z ≤ Y := by
    have hle : Real.log Z ≤ Real.log Y := by
      rw [hlogZ, div_le_iff₀ ht0]
      linarith [htY]
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hZ0, Real.exp_log hY0] at h
  have hsplit := abs_primeCosineDefect_le hσ ht0 hZ2 hZY
  have hhead := quadraticHead_le ht0 ht1 hZ2 hlogZ
  have htail := harmonicTail_le ht0 hY hZexp2 hlogZ
  linarith [hsplit, hhead, htail]

/-- **The oscillatory defect at the escape frequency is bounded.** -/
theorem exists_bound_primeCosineDefect :
    ∃ C : ℝ, ∀ᶠ L in atTop,
      |primeCosineDefect (1 + saddleTilt L) (saddleFrequency L) (cofinalAperture L)| ≤ C := by
  have hfreq := tendsto_saddleFrequency
  have hmul := tendsto_saddleFrequency_mul_apertureLog
  have hlogmul : Tendsto (fun L : ℝ => Real.log (saddleFrequency L * apertureLog L)) atTop
      (nhds (Real.log (2 * Real.pi))) := by
    have hcont : ContinuousAt Real.log (2 * Real.pi) :=
      Real.continuousAt_log (by positivity)
    exact hcont.tendsto.comp hmul
  refine ⟨(1 / 4 + mertensLogSqConst + Real.log 2 ^ 2 / 2)
    + 2 * ((Real.log (2 * Real.pi) + 1) + 3 + 4 * Sieve.mertensFirstConst), ?_⟩
  filter_upwards [hfreq.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hmul.eventually (lt_mem_nhds (show (1 : ℝ) < 2 * Real.pi by
      have := Real.pi_gt_three; linarith)),
    hlogmul.eventually (gt_mem_nhds (show Real.log (2 * Real.pi) < Real.log (2 * Real.pi) + 1 by
      linarith)),
    tendsto_cofinalAperture.eventually_ge_atTop (Real.exp 2),
    eventually_saddleTilt_spec] with L hsmall hres hlogres hY hspec
  obtain ⟨hmem, _, _⟩ := hspec
  have hσ : (1 : ℝ) ≤ 1 + saddleTilt L := by linarith [hmem.1]
  have hfreqpos : 0 < saddleFrequency L := by
    by_contra hcon
    rw [not_lt] at hcon
    have hℓpos : 0 < apertureLog L := by
      have h := Real.log_pos (show (1 : ℝ) < cofinalAperture L by
        have hexp2 : (1 : ℝ) < Real.exp 2 := by
          have := Real.add_one_le_exp (2 : ℝ)
          linarith
        linarith)
      exact h
    nlinarith [hres, hcon, hℓpos]
  have hlogY : apertureLog L = Real.log (cofinalAperture L) := rfl
  have hres' : 1 ≤ saddleFrequency L * Real.log (cofinalAperture L) := by
    rw [← hlogY]
    linarith
  have hbound := abs_primeCosineDefect_le_const (σ := 1 + saddleTilt L)
    (t := saddleFrequency L) (Y := cofinalAperture L) hσ hfreqpos hsmall.le hY hres'
  rw [← hlogY] at hbound
  refine le_trans hbound ?_
  linarith [hlogres]

/-- **(14) The all-cumulant Euler-edge amplitude.**  At the source-faithful tilt and the escape
frequency the parity–energy characteristic function has logarithmic modulus `-2 log ℓ + O(1)`,
i.e. `|Φ| = ℓ^{-2} e^{O(1)}`: the Euler edge is only logarithmically small, never Gaussian-small. -/
theorem exists_bound_log_norm_eulerTiltCharacteristic :
    ∃ C : ℝ, ∀ᶠ L in atTop,
      |Real.log ‖eulerTiltCharacteristic (1 + saddleTilt L) (saddleFrequency L)
            (cofinalAperture L)‖
          + 2 * Real.log (apertureLog L)| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_primeCosineDefect
  have hδℓ := tendsto_saddleTilt_mul_apertureLog
  have hδ := tendsto_saddleTilt
  have hδW : Tendsto (fun L : ℝ => saddleTilt L * (mertensPrimeWindowBound + 1)) atTop (nhds 0) := by
    have := hδ.mul_const (mertensPrimeWindowBound + 1)
    simpa using this
  refine ⟨405 / 2 * invSquareTailConst + C₀ + 2 * (eulerTiltMassConst + 1), ?_⟩
  filter_upwards [hC₀,
    hδℓ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hδW.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    tendsto_cofinalAperture.eventually_ge_atTop (Real.exp 2),
    eventually_saddleTilt_spec] with L hdefect hδℓL hδWL hY hspec
  obtain ⟨hmem, _, _⟩ := hspec
  have hδ0 : 0 ≤ saddleTilt L := le_of_lt hmem.1
  have hbound := abs_log_norm_add_two_logLog_le (δ := saddleTilt L)
    (t := saddleFrequency L) (Y := cofinalAperture L) hδ0 hY
  have hlogY : apertureLog L = Real.log (cofinalAperture L) := rfl
  rw [← hlogY] at hbound
  refine le_trans hbound ?_
  have hcorr : saddleTilt L * (apertureLog L + (mertensPrimeWindowBound + 1)) ≤ 1 := by
    have hexpand : saddleTilt L * (apertureLog L + (mertensPrimeWindowBound + 1))
        = saddleTilt L * apertureLog L + saddleTilt L * (mertensPrimeWindowBound + 1) := by ring
    rw [hexpand]
    linarith
  linarith [hdefect, hcorr]

end

end RHTower
