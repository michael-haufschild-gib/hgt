import GaloisForLFunctions.RHTower.DeningerAllPrimeFloquetEnergy
import GaloisForLFunctions.RHTower.DeningerGreenSumSource
import GaloisForLFunctions.RHTower.DeningerMeyerTopology

/-!
# The all-prime Floquet energy is continuous

Periodization is additive, so the difference of two traces is the trace of the difference, and
`| ‖u‖² - ‖v‖² | ≤ ‖u-v‖(‖u‖+‖v‖)`.  The period-uniform bound then makes the energy locally
Lipschitz for the order-zero Meyer seminorm:

`|E(h) - E(k)| ≤ 25 C q_{1,0}(h-k) (q_{1,0}(h) + q_{1,0}(k))`,   `C = ∑_q (log q)/q²`,

and hence continuous for the Meyer topology.

* `deningerPrimeLogWeight` : the arithmetic constant `∑_q (log q)/q²`.
* `deningerFloquetTerm_sub_le` : the termwise Lipschitz bound.
* `deningerFloquetEnergy_sub_le` : **the Lipschitz bound.**
* `deningerFloquetEnergy_continuous` : **the energy is continuous.**
-/

namespace RHTower

open SchwartzMap MeasureTheory Filter Topology

noncomputable section

/-- The arithmetic constant `∑_q (log q)/q²`. -/
def deningerPrimeLogWeight : ℝ := ∑' q : Nat.Primes, Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ (2 : ℕ)

theorem deningerPrimeLogWeight_summable :
    Summable fun q : Nat.Primes => Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ (2 : ℕ) :=
  deningerLogDivSq_summable.comp_injective Nat.Primes.coe_nat_injective

theorem deningerPrimeLogWeight_nonneg : 0 ≤ deningerPrimeLogWeight := by
  refine tsum_nonneg fun q => ?_
  have h1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.2.one_lt.le
  have := Real.log_nonneg h1
  positivity

/-- The elementary quadratic estimate `| ‖u‖² - ‖v‖² | ≤ ‖u-v‖(‖u‖+‖v‖)`. -/
theorem normSq_sub_normSq_le (u v : ℂ) : |‖u‖ ^ (2 : ℕ) - ‖v‖ ^ (2 : ℕ)| ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have hfac : ‖u‖ ^ (2 : ℕ) - ‖v‖ ^ (2 : ℕ) = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [hfac, abs_mul]
  have habs : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
  have hsum : |‖u‖ + ‖v‖| = ‖u‖ + ‖v‖ := abs_of_nonneg (by positivity)
  rw [hsum]
  exact mul_le_mul_of_nonneg_right habs (by positivity)

/-- **The termwise Lipschitz bound.** -/
theorem deningerFloquetTerm_sub_le (h k : DeningerExpSchwartz) {q : ℕ} (hq : 2 ≤ q) :
    |deningerFloquetTerm h q - deningerFloquetTerm k q|
      ≤ 25 * (deningerMeyerSeminormFun 1 0 (h - k)
          * (deningerMeyerSeminormFun 1 0 h + deningerMeyerSeminormFun 1 0 k))
        * (Real.log q / (q : ℝ) ^ (2 : ℕ)) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hqR
  have hLpos : 0 < Real.log q := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set Sh := deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) with hSh
  set Sk := deningerPeriodizationSum ((k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) with hSk
  have hcontH : Continuous Sh := deningerPeriodizationSum_continuous (h := h) hLpos
  have hcontK : Continuous Sk := deningerPeriodizationSum_continuous (h := k) hLpos
  have hintH : IntervalIntegrable (fun t => ‖Sh t‖ ^ (2 : ℕ)) volume 0 (Real.log q) :=
    (hcontH.norm.pow 2).intervalIntegrable _ _
  have hintK : IntervalIntegrable (fun t => ‖Sk t‖ ^ (2 : ℕ)) volume 0 (Real.log q) :=
    (hcontK.norm.pow 2).intervalIntegrable _ _
  -- the pointwise bound
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) (Real.log q),
      ‖‖Sh t‖ ^ (2 : ℕ) - ‖Sk t‖ ^ (2 : ℕ)‖
        ≤ 5 * deningerMeyerSeminormFun 1 0 (h - k)
          * (5 * deningerMeyerSeminormFun 1 0 h + 5 * deningerMeyerSeminormFun 1 0 k) := by
    intro t ht
    rw [Set.uIoc_of_le hLpos.le] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have htL : t ≤ Real.log q := ht.2
    have hdiff : Sh t - Sk t
        = deningerPeriodizationSum (((h - k : DeningerExpSchwartz) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) (Real.log q) t := by
      rw [hSh, hSk]
      exact (deningerPeriodizationSum_sub h.2 k.2 hLpos t).symm
    have hbd : ‖Sh t - Sk t‖ ≤ 5 * deningerMeyerSeminormFun 1 0 (h - k) := by
      rw [hdiff]
      exact deningerPeriodizationSum_norm_le_period (h := h - k) hL ht0 htL
    have hbh : ‖Sh t‖ ≤ 5 * deningerMeyerSeminormFun 1 0 h :=
      deningerPeriodizationSum_norm_le_period (h := h) hL ht0 htL
    have hbk : ‖Sk t‖ ≤ 5 * deningerMeyerSeminormFun 1 0 k :=
      deningerPeriodizationSum_norm_le_period (h := k) hL ht0 htL
    have hquad := normSq_sub_normSq_le (Sh t) (Sk t)
    rw [Real.norm_eq_abs]
    refine hquad.trans ?_
    have hnn : (0 : ℝ) ≤ ‖Sh t‖ + ‖Sk t‖ := by positivity
    have hnnk : (0 : ℝ) ≤ 5 * deningerMeyerSeminormFun 1 0 (h - k) := by
      have := deningerMeyerSeminormFun_nonneg 1 0 (h - k)
      linarith
    exact mul_le_mul hbd (by linarith) hnn hnnk
  -- integrate
  have hintsub : (∫ t in (0 : ℝ)..Real.log q, ‖Sh t‖ ^ (2 : ℕ))
      - ∫ t in (0 : ℝ)..Real.log q, ‖Sk t‖ ^ (2 : ℕ)
      = ∫ t in (0 : ℝ)..Real.log q, (‖Sh t‖ ^ (2 : ℕ) - ‖Sk t‖ ^ (2 : ℕ)) :=
    (intervalIntegral.integral_sub hintH hintK).symm
  have hnormint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    (a := (0 : ℝ)) (b := Real.log q)
  have habsdiff : |(∫ t in (0 : ℝ)..Real.log q, ‖Sh t‖ ^ (2 : ℕ))
      - ∫ t in (0 : ℝ)..Real.log q, ‖Sk t‖ ^ (2 : ℕ)|
      ≤ (5 * deningerMeyerSeminormFun 1 0 (h - k)
        * (5 * deningerMeyerSeminormFun 1 0 h + 5 * deningerMeyerSeminormFun 1 0 k))
        * Real.log q := by
    rw [hintsub]
    have habsval : |Real.log q - 0| = Real.log q := by
      rw [sub_zero, abs_of_nonneg hLpos.le]
    rw [Real.norm_eq_abs, habsval] at hnormint
    exact hnormint
  -- assemble
  rw [deningerFloquetTerm, deningerFloquetTerm, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((q : ℝ) ^ (2 : ℕ))⁻¹)]
  have hstep := mul_le_mul_of_nonneg_left habsdiff
    (by positivity : (0 : ℝ) ≤ ((q : ℝ) ^ (2 : ℕ))⁻¹)
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The Lipschitz bound for the all-prime energy.** -/
theorem deningerFloquetEnergy_sub_le (h k : DeningerExpSchwartz) :
    |deningerFloquetEnergy h - deningerFloquetEnergy k|
      ≤ 25 * (deningerMeyerSeminormFun 1 0 (h - k)
          * (deningerMeyerSeminormFun 1 0 h + deningerMeyerSeminormFun 1 0 k))
        * deningerPrimeLogWeight := by
  have hsh := deningerFloquetTerm_summable h
  have hsk := deningerFloquetTerm_summable k
  have hmaj : Summable fun q : Nat.Primes =>
      25 * (deningerMeyerSeminormFun 1 0 (h - k)
        * (deningerMeyerSeminormFun 1 0 h + deningerMeyerSeminormFun 1 0 k))
      * (Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ (2 : ℕ)) :=
    deningerPrimeLogWeight_summable.mul_left _
  have hsub : Summable fun q : Nat.Primes =>
      deningerFloquetTerm h (q : ℕ) - deningerFloquetTerm k (q : ℕ) := hsh.sub hsk
  rw [deningerFloquetEnergy, deningerFloquetEnergy, ← hsh.tsum_sub hsk, ← Real.norm_eq_abs]
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hmaj
    rw [Real.norm_eq_abs]
    exact deningerFloquetTerm_sub_le h k q.2.two_le
  · rw [deningerPrimeLogWeight, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun q => ?_) ?_ hmaj
    · rw [Real.norm_eq_abs]
      exact deningerFloquetTerm_sub_le h k q.2.two_le
    · refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hmaj
      rw [Real.norm_eq_abs]
      exact deningerFloquetTerm_sub_le h k q.2.two_le

/-- **The all-prime Floquet energy is continuous** for the Meyer topology. -/
theorem deningerFloquetEnergy_continuous :
    Continuous fun x : DeningerMeyerSource =>
      deningerFloquetEnergy (DeningerMeyerSource.toSource x) := by
  set F : DeningerMeyerSource → ℝ := fun x =>
    deningerFloquetEnergy (DeningerMeyerSource.toSource x) with hF
  have hsem : Continuous fun x : DeningerMeyerSource => DeningerMeyerSource.seminorms (1, 0) x :=
    DeningerMeyerSource.withSeminorms.continuous_seminorm (1, 0)
  refine continuous_iff_continuousAt.2 fun c => ?_
  set G : DeningerMeyerSource → ℝ := fun x =>
    25 * (DeningerMeyerSource.seminorms (1, 0) (x - c)
      * (DeningerMeyerSource.seminorms (1, 0) x + DeningerMeyerSource.seminorms (1, 0) c))
    * deningerPrimeLogWeight with hG
  have hGcont : Continuous G := by
    refine (Continuous.mul (Continuous.mul continuous_const ?_) continuous_const)
    exact (hsem.comp (continuous_id.sub continuous_const)).mul (hsem.add continuous_const)
  have hbound : ∀ x : DeningerMeyerSource, ‖F x - F c‖ ≤ G x := by
    intro x
    have hb := deningerFloquetEnergy_sub_le (DeningerMeyerSource.toSource x)
      (DeningerMeyerSource.toSource c)
    have hsub : DeningerMeyerSource.toSource x - DeningerMeyerSource.toSource c
        = DeningerMeyerSource.toSource (x - c) := (map_sub _ _ _).symm
    rw [hsub] at hb
    rw [Real.norm_eq_abs, hF, hG]
    simpa using hb
  have hGzero : G c = 0 := by
    have hzero : DeningerMeyerSource.seminorms (1, 0) (c - c) = 0 := by
      rw [sub_self, map_zero]
    show 25 * (DeningerMeyerSource.seminorms (1, 0) (c - c)
      * (DeningerMeyerSource.seminorms (1, 0) c + DeningerMeyerSource.seminorms (1, 0) c))
      * deningerPrimeLogWeight = 0
    rw [hzero]
    ring
  have hGtend : Tendsto G (𝓝 c) (𝓝 0) := by
    have := hGcont.continuousAt (x := c)
    rwa [ContinuousAt, hGzero] at this
  have hdiff : Tendsto (fun x => F x - F c) (𝓝 c) (𝓝 0) :=
    squeeze_zero_norm hbound hGtend
  have := hdiff.add_const (F c)
  simpa [ContinuousAt] using this

end

end RHTower
