import GaloisForLFunctions.RHTower.DeningerPeriodizationFundamentalBound
import GaloisForLFunctions.RHTower.DeningerPeriodizationSmooth

/-!
# The all-prime Floquet energy

For a source cochain `h` and a prime `q` put `L_q = log q` and

`E_q(h) = q^{-2} ∫_0^{L_q} ‖Per_{L_q} h(t)‖² dt`,   `E(h) = ∑_q E_q(h)`.

The period-uniform bound gives `‖Per_{L_q}h‖ ≤ 5 q_{1,0}(h)` on the fundamental interval, so
`E_q(h) ≤ 25 q_{1,0}(h)² · (log q)/q²`, and `∑_n (log n)/n²` converges by comparison with
`∑ n^{-3/2}`.  Hence the energy is finite, and the same bound makes it locally Lipschitz, hence
continuous, for the Meyer topology.

* `deningerLogDivSq_summable` : **`∑_n (log n)/n²` converges.**
* `deningerFloquetTerm_le` : **the period-uniform term bound.**
* `deningerFloquetTerm_summable` : **the all-prime energy converges.**
* `deningerFloquetEnergy` : **`E(h)`.**
* `deningerFloquetEnergy_le` : **`E(h) ≤ C q_{1,0}(h)²`.**
-/

namespace RHTower

open SchwartzMap MeasureTheory

noncomputable section

/-! ## The arithmetic weight is summable -/

/-- `log n ≤ 2√n`. -/
theorem deningerLog_le_two_sqrt (n : ℕ) : Real.log n ≤ 2 * Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt h0.le]
      ring
    have hle : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 h0)
    rw [hs]
    linarith

/-- The arithmetic weight is dominated by `2 n^{-3/2}`. -/
theorem deningerLogDivSq_le (n : ℕ) :
    Real.log n / (n : ℝ) ^ 2 ≤ 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt h0.le
    have hspos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 h0
    have hsplit : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt n := by
      rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
        Real.rpow_add_of_nonneg h0.le zero_le_one (by norm_num), Real.rpow_one]
    rw [hsplit]
    rw [div_le_iff₀ (by positivity), mul_comm (2 : ℝ), mul_assoc, one_div,
      inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have hlog := deningerLog_le_two_sqrt n
    have hstep : Real.log n * ((n : ℝ) * Real.sqrt n)
        ≤ (2 * Real.sqrt n) * ((n : ℝ) * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    have heq : (2 * Real.sqrt n) * ((n : ℝ) * Real.sqrt n) = 2 * (n : ℝ) ^ 2 := by
      linear_combination (2 * (n : ℝ)) * hsq
    linarith

/-- **`∑_n (log n)/n²` converges.** -/
theorem deningerLogDivSq_summable : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ 2 := by
  have hcomp : Summable fun n : ℕ => 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    refine Summable.mul_left 2 ?_
    rw [Real.summable_one_div_nat_rpow]
    norm_num
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => deningerLogDivSq_le n) hcomp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have := Real.log_nonneg h1
    positivity

/-! ## The Floquet terms -/

/-- The `q`-th all-prime Floquet term `q^{-2}∫_0^{log q}‖Per_{log q}h‖²`. -/
def deningerFloquetTerm (h : DeningerExpSchwartz) (q : ℕ) : ℝ :=
  ((q : ℝ) ^ 2)⁻¹ * ∫ t in (0 : ℝ)..Real.log q,
    ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ 2

/-- The periodization is continuous for a positive period. -/
theorem deningerPeriodizationSum_continuous {h : DeningerExpSchwartz} {L : ℝ} (hL : 0 < L) :
    Continuous (deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L) :=
  (deningerPeriodizationSum_contDiff h.2 hL).continuous

theorem deningerFloquetTerm_nonneg (h : DeningerExpSchwartz) {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ deningerFloquetTerm h q := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  refine mul_nonneg (by positivity) ?_
  exact intervalIntegral.integral_nonneg hlog fun u _ => by positivity

/-- **The period-uniform term bound.** -/
theorem deningerFloquetTerm_le (h : DeningerExpSchwartz) {q : ℕ} (hq : 2 ≤ q) :
    deningerFloquetTerm h q
      ≤ 25 * deningerMeyerSeminormFun 1 0 h ^ 2 * (Real.log q / (q : ℝ) ^ 2) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hqR
  have hLpos : 0 < Real.log q := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hcont := deningerPeriodizationSum_continuous (h := h) hLpos
  have hint : IntervalIntegrable
      (fun t => ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ 2)
      volume 0 (Real.log q) := (hcont.norm.pow 2).intervalIntegrable _ _
  have hconstint : IntervalIntegrable
      (fun _ : ℝ => (5 * deningerMeyerSeminormFun 1 0 h) ^ 2) volume 0 (Real.log q) :=
    intervalIntegrable_const
  have hbound : ∫ t in (0 : ℝ)..Real.log q,
      ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ 2
      ≤ Real.log q * (5 * deningerMeyerSeminormFun 1 0 h) ^ 2 := by
    have hmono := intervalIntegral.integral_mono_on hLpos.le hint hconstint (fun t ht => ?_)
    · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
      exact hmono
    · have hpt := deningerPeriodizationSum_norm_le_period (h := h) hL ht.1 ht.2
      have hnn : (0 : ℝ) ≤ ‖deningerPeriodizationSum
        ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t‖ := norm_nonneg _
      nlinarith [deningerMeyerSeminormFun_nonneg 1 0 h]
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  calc deningerFloquetTerm h q
      ≤ ((q : ℝ) ^ 2)⁻¹ * (Real.log q * (5 * deningerMeyerSeminormFun 1 0 h) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 25 * deningerMeyerSeminormFun 1 0 h ^ 2 * (Real.log q / (q : ℝ) ^ 2) := by
        field_simp
        ring

/-- **The all-prime energy converges.** -/
theorem deningerFloquetTerm_summable (h : DeningerExpSchwartz) :
    Summable fun q : Nat.Primes => deningerFloquetTerm h (q : ℕ) := by
  have hmaj : Summable fun q : Nat.Primes =>
      25 * deningerMeyerSeminormFun 1 0 h ^ 2 * (Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ 2) := by
    refine (deningerLogDivSq_summable.mul_left
      (25 * deningerMeyerSeminormFun 1 0 h ^ 2)).comp_injective ?_
    exact Nat.Primes.coe_nat_injective
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hmaj
  · exact deningerFloquetTerm_nonneg h (q.2.one_lt.le)
  · exact deningerFloquetTerm_le h q.2.two_le

/-- **The all-prime Floquet energy.** -/
def deningerFloquetEnergy (h : DeningerExpSchwartz) : ℝ :=
  ∑' q : Nat.Primes, deningerFloquetTerm h (q : ℕ)

theorem deningerFloquetEnergy_nonneg (h : DeningerExpSchwartz) : 0 ≤ deningerFloquetEnergy h :=
  tsum_nonneg fun q => deningerFloquetTerm_nonneg h q.2.one_lt.le

/-- **The energy is dominated by the order-zero Meyer seminorm.** -/
theorem deningerFloquetEnergy_le (h : DeningerExpSchwartz) :
    deningerFloquetEnergy h
      ≤ 25 * deningerMeyerSeminormFun 1 0 h ^ 2
        * ∑' q : Nat.Primes, Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ 2 := by
  have hmajsum : Summable fun q : Nat.Primes => Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ 2 :=
    deningerLogDivSq_summable.comp_injective Nat.Primes.coe_nat_injective
  rw [deningerFloquetEnergy, ← tsum_mul_left]
  exact (deningerFloquetTerm_summable h).tsum_le_tsum
    (fun q => deningerFloquetTerm_le h q.2.two_le)
    (hmajsum.mul_left (25 * deningerMeyerSeminormFun 1 0 h ^ 2))

end

end RHTower
