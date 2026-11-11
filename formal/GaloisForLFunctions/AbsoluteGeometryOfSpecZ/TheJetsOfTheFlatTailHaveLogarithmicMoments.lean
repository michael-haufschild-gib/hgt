import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRemainderOfThePrimeNumberTheoremHasLogarithmicMomentsOnATail

/-!
# The jets of the flat tail have logarithmic moments

The row of the flat tail at the degree point `n` is the remainder of the prime number theorem at
`N/n` plus the archimedean part

`J_N(n) = H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π`   (`jetRow`),

the jets of the tail and the counterterm. In the coordinate `t = n/N` it is
`a(t) = −½ log(1 − t²) − log 2π` (`archRow`) up to `1/(N−n) + 2/n`
(`abs_jetRow_sub_archRow_le`; `log M + γ ≤ H_M ≤ log M + γ + 1/M`). This file proves, for `j ≥ 1`,

`(1/N) Σ_{n ≤ N} log^j(N/n) J_N(n) → σ_j = ∫_0^1 log^j(1/t) a(t) dt`

(`tendsto_sum_logTail_mul_jetRow`). The profile `log^j(1/t) log(1 − t²)` is bounded and continuous
on `(0, 1]`: near `1` it is at most `2 |(1 − t) log(1 − t)|`, near `0` at most `t log^j(1/t) ≤ j!`.
The error sums to `O(log^{j+1} N)` because `log(N/n) ≤ (N − n)/n`.
-/

open Finset Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (chebyshev tailRow)

/-! ### The row and its profile -/

/-- The archimedean part of the row of the flat tail at the degree point `n`. -/
def jetRow (N n : ℕ) : ℝ :=
  harm N - (harm (N - n) + harm (N + n)) / 2 + 3 / (4 * (n : ℝ)) - Real.log (2 * Real.pi)

/-- The row of the flat tail: the remainder of the prime number theorem plus the jets. -/
theorem tailRow_eq (N n : ℕ) :
    tailRow N n = ((N : ℝ) / n - chebyshev (N / n)) + jetRow N n := by
  rw [tailRow, jetRow]
  ring

/-- The archimedean part of the row in the coordinate of the tail:
`a(t) = −½ log(1 − t²) − log 2π`. -/
def archRow (t : ℝ) : ℝ := -(1 / 2) * Real.log (1 - t ^ 2) - Real.log (2 * Real.pi)

/-- The moment `σ_j = ∫_0^1 log^j(1/t) a(t) dt`. -/
def archMoment (j : ℕ) : ℝ := ∫ t in Set.Ioc 0 1, logPow j t * archRow t

/-- `log^{i+1}(1/t) log(1 − t²)`. -/
def logSqProfile (i : ℕ) (t : ℝ) : ℝ := logPow (i + 1) t * Real.log (1 - t ^ 2)

/-! ### Elementary bounds -/

/-- `log M + γ ≤ H_M ≤ log M + γ + 1/M`. -/
theorem harm_sub_log_mem {M : ℕ} (hM : 1 ≤ M) :
    Real.log M + Real.eulerMascheroniConstant ≤ harm M ∧
      harm M ≤ Real.log M + Real.eulerMascheroniConstant + 1 / M := by
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant M
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' M
  rw [Real.eulerMascheroniSeq] at h1
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at h2
  rw [harm_eq_harmonic]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : Real.log ((M : ℝ) + 1) ≤ Real.log M + 1 / M := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < M + 1) hM0)
    rw [Real.log_div (by positivity) hM0.ne'] at h
    have e : ((M : ℝ) + 1) / M - 1 = 1 / M := by
      field_simp
      ring
    linarith
  constructor <;> linarith

theorem log_one_div_le {t : ℝ} (ht : 0 < t) : Real.log (1 / t) ≤ (1 - t) / t := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr ht)
  have e : 1 / t - 1 = (1 - t) / t := by field_simp
  linarith

theorem neg_log_one_sub_sq_mem {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ -Real.log (1 - t ^ 2) ∧ -Real.log (1 - t ^ 2) ≤ -Real.log (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 + t := by linarith
  have e : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
  have h3 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have h5 : Real.log (1 - t ^ 2) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  have h6 : Real.log (1 - t ^ 2) = Real.log (1 - t) + Real.log (1 + t) := by
    rw [e, Real.log_mul h1.ne' h2.ne']
  constructor <;> linarith

theorem neg_log_one_sub_le {x : ℝ} (hx1 : x < 1) : -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
    field_simp
    ring
  linarith

theorem mul_neg_log_le_one {x : ℝ} (hx0 : 0 < x) : x * -Real.log x ≤ 1 := by
  have h := Real.one_sub_inv_le_log_of_pos hx0
  have h' : -Real.log x ≤ x⁻¹ - 1 := by linarith
  calc x * -Real.log x ≤ x * (x⁻¹ - 1) := mul_le_mul_of_nonneg_left h' hx0.le
    _ = 1 - x := by field_simp
    _ ≤ 1 := by linarith

/-- `t log^j(1/t) ≤ j!` on `(0, 1]`. -/
theorem mul_logPow_le_factorial (j : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    t * logPow j t ≤ j.factorial := by
  have hL := log_one_div_nonneg ht
  have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h := Real.pow_div_factorial_le_exp (Real.log (1 / t)) hL j
  rw [Real.exp_log (one_div_pos.mpr ht.1), div_le_iff₀ hfac] at h
  rw [logPow]
  calc t * Real.log (1 / t) ^ j ≤ t * (1 / t * j.factorial) :=
        mul_le_mul_of_nonneg_left h ht.1.le
    _ = j.factorial := by
        have := ht.1.ne'
        field_simp

/-! ### The profile `log^{i+1}(1/t) log(1 − t²)` is bounded and continuous on `(0, 1]` -/

theorem logSqProfile_one (i : ℕ) : logSqProfile i 1 = 0 := by
  simp [logSqProfile, logPow]

theorem abs_logSqProfile_le_near_one (i : ℕ) {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    |logSqProfile i t| ≤ 2 * |(1 - t) * Real.log (1 - t)| := by
  have ht0 : 0 < t := by linarith
  have hx : 0 < 1 - t := by linarith
  have hmem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
  have hL0 := log_one_div_nonneg hmem
  have hL1 : Real.log (1 / t) ≤ 2 * (1 - t) := by
    refine (log_one_div_le ht0).trans ?_
    rw [div_le_iff₀ ht0]
    nlinarith [mul_nonneg hx.le (by linarith : (0 : ℝ) ≤ 2 * t - 1)]
  have hL2 : Real.log (1 / t) ≤ 1 := by linarith
  have hpow : logPow (i + 1) t ≤ Real.log (1 / t) :=
    pow_le_of_le_one hL0 hL2 (Nat.succ_ne_zero i)
  obtain ⟨h1, h2⟩ := neg_log_one_sub_sq_mem ht0.le ht1
  have hlogx : Real.log (1 - t) ≤ 0 := Real.log_nonpos hx.le (by linarith)
  rw [logSqProfile, abs_mul, abs_of_nonneg (logPow_nonneg (i + 1) hmem),
    abs_of_nonpos (by linarith : Real.log (1 - t ^ 2) ≤ 0), abs_mul, abs_of_pos hx,
    abs_of_nonpos hlogx]
  calc logPow (i + 1) t * -Real.log (1 - t ^ 2)
      ≤ Real.log (1 / t) * -Real.log (1 - t) := mul_le_mul hpow h2 h1 hL0
    _ ≤ 2 * (1 - t) * -Real.log (1 - t) := mul_le_mul_of_nonneg_right hL1 (by linarith)
    _ = 2 * ((1 - t) * -Real.log (1 - t)) := by ring

theorem abs_logSqProfile_le_near_zero (i : ℕ) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    |logSqProfile i t| ≤ (i + 1).factorial := by
  have hmem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, by linarith⟩
  obtain ⟨h1, -⟩ := neg_log_one_sub_sq_mem ht0.le (by linarith)
  have hsq1 : t ^ 2 < 1 := by nlinarith
  have hsq : -Real.log (1 - t ^ 2) ≤ t := by
    refine (neg_log_one_sub_le hsq1).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg ht0.le (by nlinarith : (0 : ℝ) ≤ 1 - t ^ 2 - t)]
  rw [logSqProfile, abs_mul, abs_of_nonneg (logPow_nonneg (i + 1) hmem),
    abs_of_nonpos (by linarith : Real.log (1 - t ^ 2) ≤ 0)]
  calc logPow (i + 1) t * -Real.log (1 - t ^ 2) ≤ logPow (i + 1) t * t :=
        mul_le_mul_of_nonneg_left hsq (logPow_nonneg _ hmem)
    _ = t * logPow (i + 1) t := mul_comm _ _
    _ ≤ (i + 1).factorial := mul_logPow_le_factorial (i + 1) hmem

theorem abs_logSqProfile_le (i : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    |logSqProfile i t| ≤ (i + 1).factorial + 2 := by
  have hfac : (0 : ℝ) ≤ (i + 1).factorial := by positivity
  rcases le_total t (1 / 2) with h | h
  · linarith [abs_logSqProfile_le_near_zero i ht.1 h]
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, logSqProfile_one, abs_zero]
      linarith
    · have hb := abs_logSqProfile_le_near_one i h h1
      have hx : 0 < 1 - t := by linarith
      have hlogx : Real.log (1 - t) ≤ 0 := Real.log_nonpos hx.le (by linarith [ht.1])
      have h4 := mul_neg_log_le_one hx
      rw [abs_mul, abs_of_pos hx, abs_of_nonpos hlogx] at hb
      linarith

theorem continuousOn_logSqProfile (i : ℕ) : ContinuousOn (logSqProfile i) (Set.Ioc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · -- at the endpoint the profile tends to its value `0`
    rw [h1, ContinuousWithinAt, logSqProfile_one]
    have hψ : Tendsto (fun t : ℝ => 2 * |(1 - t) * Real.log (1 - t)|) (𝓝[Set.Ioc 0 1] 1)
        (𝓝 0) := by
      have hc : Continuous fun t : ℝ => 2 * |(1 - t) * Real.log (1 - t)| :=
        continuous_const.mul
          (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).abs
      have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioc 0 1))
      simpa using h
    refine squeeze_zero_norm' ?_ hψ
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with s hs1 hs2
    rw [Real.norm_eq_abs]
    rcases eq_or_lt_of_le hs1.2 with h | h
    · rw [h, logSqProfile_one, abs_zero]
      positivity
    · exact abs_logSqProfile_le_near_one i (le_of_lt hs2) h
  · refine ContinuousAt.continuousWithinAt ?_
    have h0 : 0 < 1 - t ^ 2 := by nlinarith [ht.1]
    show ContinuousAt (fun t : ℝ => Real.log (1 / t) ^ (i + 1) * Real.log (1 - t ^ 2)) t
    refine ContinuousAt.mul (ContinuousAt.pow ?_ _) ?_
    · exact (Real.continuousAt_log (one_div_pos.mpr ht.1).ne').comp
        (continuousAt_const.div continuousAt_id ht.1.ne')
    · exact (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2).continuousAt.log h0.ne'

/-- **The archimedean profile against a logarithm of positive degree has convergent Riemann
sums.** -/
theorem riemannOn_logPow_mul_archRow (i : ℕ) :
    RiemannOn (fun t => logPow (i + 1) t * archRow t) := by
  have h1 : RiemannOn (logSqProfile i) :=
    riemannOn_of_continuousOn_of_bounded (continuousOn_logSqProfile i)
      fun t ht => abs_logSqProfile_le i ht
  have h2 : RiemannOn (logPow (i + 1)) :=
    riemannOn_of_antitoneOn (antitoneOn_logPow _) (fun t ht => logPow_nonneg _ ht)
      (integrableOn_logPow _)
  refine ((h1.const_mul (-(1 / 2))).sub (h2.const_mul (Real.log (2 * Real.pi)))).congr
    fun t _ => ?_
  rw [archRow, logSqProfile]
  ring

theorem measurable_archRow : Measurable archRow :=
  (measurable_const.mul (Real.measurable_log.comp
    (measurable_const.sub (measurable_id.pow_const 2)))).sub measurable_const

/-- The archimedean profile is integrable on `(0, 1]` against every logarithmic profile. -/
theorem integrableOn_logPow_mul_archRow (j : ℕ) :
    IntegrableOn (fun t => logPow j t * archRow t) (Set.Ioc 0 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- degree zero: `log(1 − t²) = log(1 − t) + log(1 + t)` off the endpoint
    have h1 : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume 0 1 := by
      have h := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
      simpa using h
    have h2 : IntervalIntegrable (fun t : ℝ => Real.log (1 + t)) volume 0 1 :=
      ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht =>
        ((Real.continuousAt_log (by linarith [ht.1] : (1 : ℝ) + t ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)).continuousWithinAt
    have h3 : IntegrableOn (fun t : ℝ => -(1 / 2) * (Real.log (1 - t) + Real.log (1 + t)) -
        Real.log (2 * Real.pi)) (Set.Ioc 0 1) :=
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (h1.add h2)).const_mul
        (-(1 / 2))).sub (integrableOn_const (C := Real.log (2 * Real.pi)) (by simp))
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at h3 ⊢
    refine h3.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have e : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
    show -(1 / 2) * (Real.log (1 - t) + Real.log (1 + t)) - Real.log (2 * Real.pi) =
      logPow 0 t * archRow t
    rw [logPow, pow_zero, one_mul, archRow, e,
      Real.log_mul (x := 1 - t) (y := 1 + t) (by linarith [ht.2] : (0 : ℝ) < 1 - t).ne'
        (by linarith [ht.1] : (0 : ℝ) < 1 + t).ne']
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact (riemannOn_logPow_mul_archRow i).1

/-! ### The row against the profile -/

/-- **The jets of the tail are the archimedean profile** up to `1/(N − n) + 2/n`. -/
theorem abs_jetRow_sub_archRow_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    |jetRow N n - archRow ((n : ℝ) / N)| ≤ 1 / ((N : ℝ) - n) + 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (n : ℝ) < N := by exact_mod_cast hnN
  have hd : (0 : ℝ) < (N : ℝ) - n := by linarith
  obtain ⟨a1, a2⟩ := harm_sub_log_mem (by omega : 1 ≤ N)
  obtain ⟨b1, b2⟩ := harm_sub_log_mem (by omega : 1 ≤ N - n)
  obtain ⟨c1, c2⟩ := harm_sub_log_mem (by omega : 1 ≤ N + n)
  rw [Nat.cast_sub hnN.le] at b1 b2
  rw [Nat.cast_add] at c1 c2
  have harch : archRow ((n : ℝ) / N) = Real.log N - Real.log ((N : ℝ) - n) / 2 -
      Real.log ((N : ℝ) + n) / 2 - Real.log (2 * Real.pi) := by
    have e : 1 - ((n : ℝ) / N) ^ 2 = ((N : ℝ) - n) * ((N : ℝ) + n) / (N : ℝ) ^ 2 := by
      field_simp
      ring
    rw [archRow, e, Real.log_div (by positivity) (by positivity),
      Real.log_mul hd.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have h1 : 1 / ((N : ℝ) + n) ≤ 1 / ((N : ℝ) - n) := one_div_le_one_div_of_le hd (by linarith)
  have h2 : 1 / (N : ℝ) ≤ 1 / n := one_div_le_one_div_of_le hn0 hlt.le
  have h3 : 3 / (4 * (n : ℝ)) = 3 / 4 * (1 / n) := by
    field_simp
  have h4 : 2 / (n : ℝ) = 2 * (1 / n) := by ring
  have h5 : (0 : ℝ) ≤ 1 / n := by positivity
  have h6 : (0 : ℝ) ≤ 1 / ((N : ℝ) + n) := by positivity
  rw [jetRow, harch, abs_le]
  constructor <;> linarith

theorem tendsto_pow_log_div_natCast (p : ℕ) :
    Tendsto (fun N : ℕ => Real.log N ^ p / (N : ℝ)) atTop (𝓝 0) :=
  (Real.isLittleO_pow_log_id_atTop (n := p)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop

/-- **The jets of the flat tail have logarithmic moments**:
`(1/N) Σ_{n ≤ N} log^{i+1}(N/n) J_N(n) → σ_{i+1}`. -/
theorem tendsto_sum_logTail_mul_jetRow (i : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, logTail (i + 1) N n * jetRow N n) / N) atTop
      (𝓝 (archMoment (i + 1))) := by
  have hmain := (riemannOn_logPow_mul_archRow i).2
  -- the row against its profile, term by term
  have hterm : ∀ N n : ℕ, n ∈ Finset.Icc 1 N →
      |logTail (i + 1) N n * jetRow N n - logPow (i + 1) ((n : ℝ) / N) * archRow ((n : ℝ) / N)| ≤
        (Real.log N ^ i + 2 * Real.log N ^ (i + 1)) * (1 / (n : ℝ)) := by
    intro N n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hn1.trans hn2
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hprof : logPow (i + 1) ((n : ℝ) / N) = logTail (i + 1) N n := by
      rw [logPow, one_div_div, logTail]
    rw [hprof, ← mul_sub, abs_mul]
    rcases eq_or_lt_of_le hn2 with h | h
    · rw [h, logTail_self (Nat.succ_ne_zero i), abs_zero, zero_mul]
      positivity
    · have hlt : (n : ℝ) < N := by exact_mod_cast h
      have hd : (0 : ℝ) < (N : ℝ) - n := by linarith
      have hℓ0 : 0 ≤ Real.log ((N : ℝ) / n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
      have hℓN : Real.log ((N : ℝ) / n) ≤ Real.log N :=
        Real.log_le_log (by positivity) (div_le_self (by linarith) (by exact_mod_cast hn1))
      have hℓd : Real.log ((N : ℝ) / n) ≤ ((N : ℝ) - n) / n := by
        have h' := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < N) hn0)
        have e : (N : ℝ) / n - 1 = ((N : ℝ) - n) / n := by field_simp
        linarith
      have hjet := abs_jetRow_sub_archRow_le hn1 h
      have hpi : Real.log ((N : ℝ) / n) ^ i ≤ Real.log N ^ i := pow_le_pow_left₀ hℓ0 hℓN i
      have hpi1 : Real.log ((N : ℝ) / n) ^ (i + 1) ≤ Real.log N ^ (i + 1) :=
        pow_le_pow_left₀ hℓ0 hℓN (i + 1)
      have hfirst : Real.log ((N : ℝ) / n) ^ (i + 1) * (1 / ((N : ℝ) - n)) ≤
          Real.log N ^ i * (1 / (n : ℝ)) := by
        have h1 : Real.log ((N : ℝ) / n) * (1 / ((N : ℝ) - n)) ≤ 1 / (n : ℝ) := by
          calc Real.log ((N : ℝ) / n) * (1 / ((N : ℝ) - n))
              ≤ ((N : ℝ) - n) / n * (1 / ((N : ℝ) - n)) :=
                mul_le_mul_of_nonneg_right hℓd (by positivity)
            _ = 1 / (n : ℝ) := by field_simp
        calc Real.log ((N : ℝ) / n) ^ (i + 1) * (1 / ((N : ℝ) - n))
            = Real.log ((N : ℝ) / n) ^ i * (Real.log ((N : ℝ) / n) * (1 / ((N : ℝ) - n))) := by
              ring
          _ ≤ Real.log N ^ i * (1 / (n : ℝ)) :=
              mul_le_mul hpi h1 (by positivity) (by positivity)
      rw [logTail, abs_of_nonneg (pow_nonneg hℓ0 _)]
      calc Real.log ((N : ℝ) / n) ^ (i + 1) * |jetRow N n - archRow ((n : ℝ) / N)|
          ≤ Real.log ((N : ℝ) / n) ^ (i + 1) * (1 / ((N : ℝ) - n) + 2 / n) :=
            mul_le_mul_of_nonneg_left hjet (pow_nonneg hℓ0 _)
        _ = Real.log ((N : ℝ) / n) ^ (i + 1) * (1 / ((N : ℝ) - n)) +
              2 * Real.log ((N : ℝ) / n) ^ (i + 1) * (1 / (n : ℝ)) := by ring
        _ ≤ Real.log N ^ i * (1 / (n : ℝ)) + 2 * Real.log N ^ (i + 1) * (1 / (n : ℝ)) :=
            add_le_add hfirst (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpi1 (by norm_num)) (by positivity))
        _ = (Real.log N ^ i + 2 * Real.log N ^ (i + 1)) * (1 / (n : ℝ)) := by ring
  -- the error per degree point
  have herr : ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, logTail (i + 1) N n * jetRow N n) / N -
        tailRiemannSum (fun t => logPow (i + 1) t * archRow t) N| ≤
        (Real.log N ^ i + 2 * Real.log N ^ (i + 1)) * (1 + Real.log N) / N := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    rw [tailRiemannSum, ← sub_div, abs_div, abs_of_pos hN0, ← Finset.sum_sub_distrib]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (hterm N)).trans ?_)
    rw [← Finset.mul_sum, HodgeTheoryOfAFixedPart.sum_Icc_one_div, harm_eq_harmonic]
    exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)
  have hzero : Tendsto (fun N : ℕ =>
      (Real.log N ^ i + 2 * Real.log N ^ (i + 1)) * (1 + Real.log N) / N) atTop (𝓝 0) := by
    have h := ((tendsto_pow_log_div_natCast i).add
      ((tendsto_pow_log_div_natCast (i + 1)).const_mul 3)).add
      ((tendsto_pow_log_div_natCast (i + 2)).const_mul 2)
    rw [mul_zero, mul_zero, add_zero, add_zero] at h
    refine h.congr fun N => ?_
    ring
  have hdiff : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, logTail (i + 1) N n * jetRow N n) / N -
        tailRiemannSum (fun t => logPow (i + 1) t * archRow t) N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact herr N hN
  have h := hmain.add hdiff
  rw [add_zero] at h
  refine h.congr fun N => ?_
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
