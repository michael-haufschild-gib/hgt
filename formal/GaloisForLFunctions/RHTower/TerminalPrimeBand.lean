import GaloisForLFunctions.RHTower.EulerTiltAmplitude

/-!
# The terminal prime band

The harmonic mass of the top logarithmic band `Y/(log Y)^K < p ≤ Y` is

```text
∑_{Y/ℓ^K < p ≤ Y} 1/p = O(K log ℓ / ℓ),      ℓ = log Y,
```

so it vanishes in the cofinal limit.  Escape variance at the Euler edge is therefore carried
across all logarithmic prime scales, never by the terminal band alone.  The proof is Mertens'
second theorem in sharp form at both endpoints, where the two Meissel–Mertens constants cancel.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The harmonic mass of the terminal band `Y/(log Y)^K < p ≤ Y`. -/
def terminalBandMass (K Y : ℝ) : ℝ :=
  Sieve.mertensS ⌊Y⌋₊ - Sieve.mertensS ⌊Y / Real.log Y ^ K⌋₊

theorem log_terminalSplit {K Y : ℝ} (hY : (1 : ℝ) < Y) :
    Real.log (Y / Real.log Y ^ K) = Real.log Y - K * Real.log (Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlog : (0 : ℝ) < Real.log Y := Real.log_pos hY
  have hpow : (0 : ℝ) < Real.log Y ^ K := Real.rpow_pos_of_pos hlog _
  rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hpow), Real.log_rpow hlog]

theorem terminalSplit_le {K Y : ℝ} (hK : 0 ≤ K) (hY : Real.exp 1 ≤ Y) :
    Y / Real.log Y ^ K ≤ Y := by
  have hY1 : (1 : ℝ) < Y := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlog : (1 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 1) hY
    rwa [Real.log_exp] at h
  have hpow : (1 : ℝ) ≤ Real.log Y ^ K := Real.one_le_rpow hlog hK
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hY0, hpow]

theorem terminalBandMass_nonneg {K Y : ℝ} (hK : 0 ≤ K) (hY : Real.exp 1 ≤ Y) :
    0 ≤ terminalBandMass K Y := by
  rw [terminalBandMass, mertensS_sub_eq_sum_sdiff (terminalSplit_le hK hY)]
  refine Finset.sum_nonneg fun p hp => ?_
  have hpmem : p ∈ Nat.primesLE ⌊Y⌋₊ := (Finset.mem_sdiff.mp hp).1
  have hprime := Nat.prime_of_mem_primesLE hpmem
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  positivity

/-- A ratio bound for logarithms: if `A ≤ B + u` and both are at least `ℓ/2`, then the logarithmic
gap is at most `2u/ℓ`. -/
theorem log_sub_log_le_of_le_add {A B u l : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
    (hA : l / 2 ≤ A) (hB : l / 2 ≤ B) (hAB : A ≤ B + u) :
    Real.log A - Real.log B ≤ 2 * u / l := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hdiff : Real.log A - Real.log B = Real.log (A / B) := (Real.log_div (ne_of_gt hA0) (ne_of_gt hB0)).symm
  have hle := Real.log_le_sub_one_of_pos (show (0:ℝ) < A / B by positivity)
  have hquot : A / B - 1 ≤ 2 * u / l := by
    rw [div_sub_one (ne_of_gt hB0), div_le_div_iff₀ hB0 hl]
    nlinarith [hAB, hB, hu, hl]
  rw [hdiff]
  linarith

/-- **The terminal band carries `O(K log ℓ / ℓ)` harmonic mass.** -/
theorem terminalBandMass_le {K Y : ℝ} (hK : 0 ≤ K) (hY : Real.exp 2 ≤ Y)
    (hband : K * Real.log (Real.log Y) + Real.log 2 ≤ Real.log Y / 2) :
    terminalBandMass K Y
      ≤ (2 * K * Real.log (Real.log Y) + 2 * Real.log 2
          + 4 * (2 * Sieve.mertensFirstConst + 1 / 2)) / Real.log Y := by
  have hexp2 := seven_lt_exp_two
  have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hY1 : (1 : ℝ) < Y := by linarith
  have hℓ : (2 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 2) hY
    rwa [Real.log_exp] at h
  have hℓ0 : (0 : ℝ) < Real.log Y := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hu0 : 0 ≤ K * Real.log (Real.log Y) := by
    have : 0 ≤ Real.log (Real.log Y) := Real.log_nonneg (by linarith)
    positivity
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = Y / Real.log Y ^ K := ⟨_, rfl⟩
  have hlogZ : Real.log Z = Real.log Y - K * Real.log (Real.log Y) := by
    rw [hZdef]; exact log_terminalSplit hY1
  have hlogZlow : Real.log Y / 2 + Real.log 2 ≤ Real.log Z := by
    rw [hlogZ]; linarith
  have hZpos : (0 : ℝ) < Z := by
    rw [hZdef]
    have hpow : (0 : ℝ) < Real.log Y ^ K := Real.rpow_pos_of_pos hℓ0 _
    positivity
  have hZ2 : (2 : ℝ) ≤ Z := by
    have hle : Real.log 2 ≤ Real.log Z := by linarith
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_log hZpos] at h
  have hexp1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hZY : Z ≤ Y := by rw [hZdef]; exact terminalSplit_le hK (by linarith)
  -- floor comparisons
  have hfloorY2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Y))
  have hfloorZ2 : 2 ≤ ⌊Z⌋₊ := Nat.le_floor (by exact_mod_cast hZ2)
  have hfloorYle : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hfloorZle : ((⌊Z⌋₊ : ℕ) : ℝ) ≤ Z := Nat.floor_le hZpos.le
  have hfloorYlow : Y / 2 ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one Y
    linarith
  have hfloorZlow : Z / 2 ≤ ((⌊Z⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one Z
    linarith
  have hfloorYpos : (0 : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := by linarith
  have hfloorZpos : (0 : ℝ) < ((⌊Z⌋₊ : ℕ) : ℝ) := by linarith
  have hlogfloorY : Real.log Y - Real.log 2 ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < Y / 2) hfloorYlow
    rwa [Real.log_div (ne_of_gt hY0) (by norm_num)] at h
  have hlogfloorZ : Real.log Z - Real.log 2 ≤ Real.log ((⌊Z⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < Z / 2) hfloorZlow
    rwa [Real.log_div (ne_of_gt hZpos) (by norm_num)] at h
  have hlogfloorYup : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y :=
    Real.log_le_log hfloorYpos hfloorYle
  have hhalfY : Real.log Y / 2 ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have hlog2le : Real.log 2 ≤ Real.log Y / 2 := by linarith
    linarith
  have hhalfZ : Real.log Y / 2 ≤ Real.log ((⌊Z⌋₊ : ℕ) : ℝ) := by linarith
  -- the two Mertens error terms
  have hC1 : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have := Sieve.mertensFirstConst_nonneg
    linarith
  have hmY := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloorY2)
  have hmZ := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloorZ2)
  have hdivY : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊Y⌋₊ : ℕ) : ℝ)
      ≤ 2 * (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log Y := by
    rw [div_le_div_iff₀ (by linarith) hℓ0]
    nlinarith [hC1, hhalfY]
  have hdivZ : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊Z⌋₊ : ℕ) : ℝ)
      ≤ 2 * (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log Y := by
    rw [div_le_div_iff₀ (by linarith) hℓ0]
    nlinarith [hC1, hhalfZ]
  -- the logarithmic ratio
  have hratio : Sieve.logLog ⌊Y⌋₊ - Sieve.logLog ⌊Z⌋₊
      ≤ (2 * K * Real.log (Real.log Y) + 2 * Real.log 2) / Real.log Y := by
    have hnum : Real.log ((⌊Y⌋₊ : ℕ) : ℝ)
        ≤ Real.log ((⌊Z⌋₊ : ℕ) : ℝ) + (K * Real.log (Real.log Y) + Real.log 2) := by
      linarith [hlogfloorYup, hlogfloorZ, hlogZ]
    have hstep := log_sub_log_le_of_le_add (l := Real.log Y)
      (u := K * Real.log (Real.log Y) + Real.log 2) hℓ0 (by linarith) hhalfY hhalfZ hnum
    have hval : 2 * (K * Real.log (Real.log Y) + Real.log 2) / Real.log Y
        = (2 * K * Real.log (Real.log Y) + 2 * Real.log 2) / Real.log Y := by
      rw [show 2 * (K * Real.log (Real.log Y) + Real.log 2)
        = 2 * K * Real.log (Real.log Y) + 2 * Real.log 2 by ring]
    rw [Sieve.logLog, Sieve.logLog, ← hval]
    exact hstep
  rw [terminalBandMass, ← hZdef]
  have hfinalsplit : (2 * K * Real.log (Real.log Y) + 2 * Real.log 2
      + 4 * (2 * Sieve.mertensFirstConst + 1 / 2)) / Real.log Y
      = (2 * K * Real.log (Real.log Y) + 2 * Real.log 2) / Real.log Y
        + (2 * (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log Y
          + 2 * (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log Y) := by
    field_simp
    ring
  rw [hfinalsplit]
  linarith [hmY.2, hmZ.1, hdivY, hdivZ, hratio]

/-- **The terminal band is asymptotically negligible.** -/
theorem tendsto_terminalBandMass {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun Y : ℝ => terminalBandMass K Y) atTop (nhds 0) := by
  have hloglog : Tendsto (fun Y : ℝ => Real.log (Real.log Y) / Real.log Y) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun Y : ℝ => (Real.log Y)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hmaj : Tendsto (fun Y : ℝ => (2 * K * Real.log (Real.log Y) + 2 * Real.log 2
      + 4 * (2 * Sieve.mertensFirstConst + 1 / 2)) / Real.log Y) atTop (nhds 0) := by
    have h1 := hloglog.const_mul (2 * K)
    have h2 := hinv.const_mul (2 * Real.log 2 + 4 * (2 * Sieve.mertensFirstConst + 1 / 2))
    have h := h1.add h2
    rw [mul_zero, mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hℓ0 : (0 : ℝ) < Real.log Y := Real.log_pos hY
    field_simp
    ring
  -- the band condition eventually holds
  have hcond : ∀ᶠ Y : ℝ in atTop,
      K * Real.log (Real.log Y) + Real.log 2 ≤ Real.log Y / 2 := by
    have hquot : Tendsto (fun Y : ℝ => K * (Real.log (Real.log Y) / Real.log Y)
        + Real.log 2 * (Real.log Y)⁻¹) atTop (nhds 0) := by
      have h1 := hloglog.const_mul K
      have h2 := hinv.const_mul (Real.log 2)
      have h := h1.add h2
      rw [mul_zero, mul_zero, add_zero] at h
      exact h
    filter_upwards [hquot.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)),
      eventually_ge_atTop (Real.exp 2)] with Y hY hYexp
    have hexp2 := seven_lt_exp_two
    have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hYexp
    have hℓ0 : (0 : ℝ) < Real.log Y := Real.log_pos (by linarith)
    have hval : K * (Real.log (Real.log Y) / Real.log Y) + Real.log 2 * (Real.log Y)⁻¹
        = (K * Real.log (Real.log Y) + Real.log 2) / Real.log Y := by
      field_simp
    rw [hval] at hY
    have hlt := (div_lt_iff₀ hℓ0).mp hY
    linarith
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with Y hY
    exact terminalBandMass_nonneg hK hY
  · filter_upwards [hcond, eventually_ge_atTop (Real.exp 2)] with Y hcondY hY
    exact terminalBandMass_le hK hY hcondY

end

end RHTower
