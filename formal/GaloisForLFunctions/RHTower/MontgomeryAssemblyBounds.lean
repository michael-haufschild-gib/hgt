import GaloisForLFunctions.RHTower.MontgomeryPrimeAmpMoments
import GaloisForLFunctions.RHTower.MontgomeryPairFormTruncation
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Assembly bounds for the pair-correlation mean square

The zero side of Montgomery's lemma is `Σ_ρ 2x^ρ/((ρ−a_t)(ρ−b_t)) = primeSide + E`, with
`‖Σ_ρ …‖² = 4x ‖S(x,t)‖²`.  This module records the elementary inequalities used to compare
`∫_0^T ‖S‖²` with the prime-side mean square:

* `‖P + E‖² ≤ (1+δ)‖P‖² + (1+1/δ)‖E‖²` and `‖P‖² − (1+1/δ)‖E‖² ≤ (1+δ)‖P+E‖²`, integrated;
* `∫_0^T ‖E‖² ≤ 96 x² + 3 T (C + log(T+4))²/x + 1536/x⁴`;
* `∫_0^T ‖S‖² = (1/(4x)) ∫_0^T ‖P + E‖²`.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

/-! ## The `δ`-inequalities -/

theorem normSq_add_le_delta (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + 1 / δ) * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hamgm : 2 * ‖a‖ * ‖b‖ ≤ δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ := by
    rw [← sub_nonneg]
    have : δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ - 2 * ‖a‖ * ‖b‖ = (δ * ‖a‖ - ‖b‖) ^ 2 / δ := by
      field_simp; ring
    rw [this]; positivity
  have : (1 + 1 / δ) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / δ := by ring
  nlinarith

theorem normSq_add_ge_delta (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖a‖ ^ 2 - (1 + 1 / δ) * ‖b‖ ^ 2 ≤ (1 + δ) * ‖a + b‖ ^ 2 := by
  have h : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    have := norm_add_le (a + b) (-b); simpa using this
  have hab := norm_nonneg (a + b)
  have hb := norm_nonneg b
  have hsq : ‖a‖ ^ 2 ≤ (‖a + b‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hamgm : 2 * ‖a + b‖ * ‖b‖ ≤ δ * ‖a + b‖ ^ 2 + ‖b‖ ^ 2 / δ := by
    rw [← sub_nonneg]
    have : δ * ‖a + b‖ ^ 2 + ‖b‖ ^ 2 / δ - 2 * ‖a + b‖ * ‖b‖ = (δ * ‖a + b‖ - ‖b‖) ^ 2 / δ := by
      field_simp; ring
    rw [this]; positivity
  have : (1 + 1 / δ) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / δ := by ring
  nlinarith

/-! ## Continuity and the basic identity -/

/-- `E = −2√x · S − P` pointwise. -/
theorem montgomeryRemainder_eq {x : ℝ} (hx : 1 < x) (t : ℝ) :
    montgomeryRemainder x t
      = -2 * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * lorentzZeroSumAll x t - primeSide x t := by
  have h1 := tsum_montgomeryZeroTerm_eq hx.le t
  have h2 := tsum_montgomeryZeroTerm_eq_primeSide_add_remainder hx t
  rw [← h1, h2]; ring

theorem continuousOn_montgomeryRemainder {x : ℝ} (hx : 1 < x) (T : ℝ) :
    ContinuousOn (montgomeryRemainder x) (Icc 0 T) := by
  have : montgomeryRemainder x = fun t =>
      -2 * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * lorentzZeroSumAll x t - primeSide x t :=
    funext (montgomeryRemainder_eq hx)
  rw [this]
  exact (continuousOn_const.mul (continuousOn_lorentzZeroSumAll hx.le T)).sub
    (continuous_primeSide hx.le).continuousOn

/-- `∫_0^T ‖S‖² = (1/(4x)) ∫_0^T ‖P + E‖²`. -/
theorem integral_normSq_lorentzZeroSumAll_eq {x : ℝ} (hx : 1 < x) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll x t‖ ^ 2
      = (1 / (4 * x)) * ∫ t in (0 : ℝ)..T, ‖primeSide x t + montgomeryRemainder x t‖ ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have h1 := normSq_tsum_montgomeryZeroTerm hx.le t
  have h2 := tsum_montgomeryZeroTerm_eq_primeSide_add_remainder hx t
  rw [h2] at h1
  have hx0 : (0 : ℝ) < x := by linarith
  rw [h1]; field_simp

/-- The set-integral over `Icc 0 T` of `‖S‖²` is the interval integral. -/
theorem setIntegral_Icc_normSq_lorentzZeroSumAll {x T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Icc 0 T, ‖lorentzZeroSumAll x t‖ ^ 2 = ∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll x t‖ ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hT]

/-! ## The integrated `δ`-inequalities -/

theorem integral_normSq_add_le_delta {x : ℝ} (hx : 1 < x) {T : ℝ} (hT : 0 ≤ T) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in (0 : ℝ)..T, ‖primeSide x t + montgomeryRemainder x t‖ ^ 2
      ≤ (1 + δ) * (∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2)
        + (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x t‖ ^ 2 := by
  have hP : IntervalIntegrable (fun t => ‖primeSide x t‖ ^ 2) volume 0 T :=
    ((continuous_primeSide hx.le).norm.pow 2).intervalIntegrable _ _
  have hE : IntervalIntegrable (fun t => ‖montgomeryRemainder x t‖ ^ 2) volume 0 T :=
    (((continuousOn_montgomeryRemainder hx T).norm.pow 2).mono
      (by rw [uIcc_of_le hT])).intervalIntegrable
  have hPE : IntervalIntegrable (fun t => ‖primeSide x t + montgomeryRemainder x t‖ ^ 2) volume 0 T :=
    ((((continuous_primeSide hx.le).continuousOn.add
      (continuousOn_montgomeryRemainder hx T)).norm.pow 2).mono
      (by rw [uIcc_of_le hT])).intervalIntegrable
  calc ∫ t in (0 : ℝ)..T, ‖primeSide x t + montgomeryRemainder x t‖ ^ 2
      ≤ ∫ t in (0 : ℝ)..T, ((1 + δ) * ‖primeSide x t‖ ^ 2
          + (1 + 1 / δ) * ‖montgomeryRemainder x t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hT hPE ((hP.const_mul _).add (hE.const_mul _))
          fun t _ => normSq_add_le_delta _ _ hδ
    _ = _ := by
        rw [intervalIntegral.integral_add (hP.const_mul _) (hE.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem integral_normSq_add_ge_delta {x : ℝ} (hx : 1 < x) {T : ℝ} (hT : 0 ≤ T) {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2)
        - (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x t‖ ^ 2
      ≤ (1 + δ) * ∫ t in (0 : ℝ)..T, ‖primeSide x t + montgomeryRemainder x t‖ ^ 2 := by
  have hP : IntervalIntegrable (fun t => ‖primeSide x t‖ ^ 2) volume 0 T :=
    ((continuous_primeSide hx.le).norm.pow 2).intervalIntegrable _ _
  have hE : IntervalIntegrable (fun t => ‖montgomeryRemainder x t‖ ^ 2) volume 0 T :=
    (((continuousOn_montgomeryRemainder hx T).norm.pow 2).mono
      (by rw [uIcc_of_le hT])).intervalIntegrable
  have hPE : IntervalIntegrable (fun t => ‖primeSide x t + montgomeryRemainder x t‖ ^ 2) volume 0 T :=
    ((((continuous_primeSide hx.le).continuousOn.add
      (continuousOn_montgomeryRemainder hx T)).norm.pow 2).mono
      (by rw [uIcc_of_le hT])).intervalIntegrable
  calc (∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2)
        - (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x t‖ ^ 2
      = ∫ t in (0 : ℝ)..T, (‖primeSide x t‖ ^ 2
          - (1 + 1 / δ) * ‖montgomeryRemainder x t‖ ^ 2) := by
        rw [intervalIntegral.integral_sub hP (hE.const_mul _), intervalIntegral.integral_const_mul]
    _ ≤ ∫ t in (0 : ℝ)..T, (1 + δ) * ‖primeSide x t + montgomeryRemainder x t‖ ^ 2 :=
        intervalIntegral.integral_mono_on hT (hP.sub (hE.const_mul _)) (hPE.const_mul _)
          fun t _ => normSq_add_ge_delta _ _ hδ
    _ = _ := intervalIntegral.integral_const_mul _ _

/-! ## The remainder energy -/

theorem integral_inv_one_add_sq_le (T : ℝ) :
    ∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2) ≤ 2 := by
  rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
  have := Real.arctan_lt_pi_div_two T
  have := Real.pi_lt_four
  linarith

/-- The pointwise bound `‖E‖² ≤ 3 (a² + b² + c²)` with the three explicit pieces, for `t ≥ 0`. -/
theorem normSq_montgomeryRemainder_le {x : ℝ} (hx : 1 < x) {t : ℝ} (ht : 0 ≤ t) :
    ‖montgomeryRemainder x t‖ ^ 2
      ≤ 3 * ((16 * x ^ 2) * (1 / (1 + t ^ 2))
        + (1 / x) * (xbBlockConstant + Real.log (t + 4)) ^ 2
        + (256 / x ^ 4) * (1 / (1 + t ^ 2))) := by
  have h := norm_montgomeryRemainder_le hx t
  rw [abs_of_nonneg ht] at h
  set a := 4 * x / (1 + t ^ 2) with ha
  set b := x ^ (-(1 / 2 : ℝ)) * (xbBlockConstant + Real.log (t + 4)) with hb
  set c := 16 * (x ^ 2)⁻¹ / (1 + t) with hc
  have hx0 : 0 < x := by linarith
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by
    have := xbBlockConstant_nonneg
    have : 0 ≤ Real.log (t + 4) := Real.log_nonneg (by linarith)
    positivity
  have hc0 : 0 ≤ c := by positivity
  have hsq : ‖montgomeryRemainder x t‖ ^ 2 ≤ (a + b + c) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcs : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have ha2 : a ^ 2 ≤ (16 * x ^ 2) * (1 / (1 + t ^ 2)) := by
    rw [ha, div_pow, mul_pow]
    have h1 : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : (1 + t ^ 2) ^ 2 ≥ 1 + t ^ 2 := by nlinarith
    calc (4 : ℝ) ^ 2 * x ^ 2 = 16 * x ^ 2 := by norm_num
      _ = 16 * x ^ 2 * (1 / (1 + t ^ 2)) * (1 + t ^ 2) := by field_simp
      _ ≤ 16 * x ^ 2 * (1 / (1 + t ^ 2)) * (1 + t ^ 2) ^ 2 := by gcongr
  have hb2 : b ^ 2 = (1 / x) * (xbBlockConstant + Real.log (t + 4)) ^ 2 := by
    have hsq : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [hb, mul_pow, hsq, Real.rpow_neg_one]; ring
  have hc2 : c ^ 2 ≤ (256 / x ^ 4) * (1 / (1 + t ^ 2)) := by
    have h1 : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    have hpos : 0 < 1 + t := by linarith
    have : c ^ 2 = (256 / x ^ 4) * (1 / (1 + t) ^ 2) := by
      rw [hc]; field_simp; ring
    rw [this]
    gcongr
  nlinarith

/-- **The remainder energy** `∫_0^T ‖E‖² ≤ 96 x² + 3 T (C + log(T+4))²/x + 1536/x⁴`. -/
theorem integral_normSq_montgomeryRemainder_le {x : ℝ} (hx : 1 < x) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x t‖ ^ 2
      ≤ 96 * x ^ 2 + 3 * T * (xbBlockConstant + Real.log (T + 4)) ^ 2 / x + 1536 / x ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hE : IntervalIntegrable (fun t => ‖montgomeryRemainder x t‖ ^ 2) volume 0 T :=
    (((continuousOn_montgomeryRemainder hx T).norm.pow 2).mono
      (by rw [uIcc_of_le hT])).intervalIntegrable
  have hmaj : IntervalIntegrable (fun t : ℝ => 3 * ((16 * x ^ 2) * (1 / (1 + t ^ 2))
      + (1 / x) * (xbBlockConstant + Real.log (T + 4)) ^ 2
      + (256 / x ^ 4) * (1 / (1 + t ^ 2)))) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop (disch := intro t; positivity)
  have hlogT : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hC := xbBlockConstant_nonneg
  have hpt : ∀ t ∈ Icc (0 : ℝ) T, ‖montgomeryRemainder x t‖ ^ 2
      ≤ 3 * ((16 * x ^ 2) * (1 / (1 + t ^ 2))
        + (1 / x) * (xbBlockConstant + Real.log (T + 4)) ^ 2
        + (256 / x ^ 4) * (1 / (1 + t ^ 2))) := by
    intro t ht
    refine (normSq_montgomeryRemainder_le hx ht.1).trans ?_
    have hlog : Real.log (t + 4) ≤ Real.log (T + 4) := Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
    have hlt : 0 ≤ Real.log (t + 4) := Real.log_nonneg (by linarith [ht.1])
    have : (xbBlockConstant + Real.log (t + 4)) ^ 2 ≤ (xbBlockConstant + Real.log (T + 4)) ^ 2 := by
      gcongr
    have h1 : 0 ≤ (16 * x ^ 2) * (1 / (1 + t ^ 2)) := by positivity
    have h3 : 0 ≤ (256 / x ^ 4) * (1 / (1 + t ^ 2)) := by positivity
    have h2 : (1 / x) * (xbBlockConstant + Real.log (t + 4)) ^ 2
        ≤ (1 / x) * (xbBlockConstant + Real.log (T + 4)) ^ 2 := by gcongr
    linarith
  refine (intervalIntegral.integral_mono_on hT hE hmaj hpt).trans ?_
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / (1 + t ^ 2)) volume 0 T :=
    (by fun_prop (disch := intro t; positivity) : Continuous fun t : ℝ => 1 / (1 + t ^ 2)).intervalIntegrable _ _
  have hI := integral_inv_one_add_sq_le T
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2) :=
    intervalIntegral.integral_nonneg hT fun t _ => by positivity
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((hint1.const_mul _).add (by apply Continuous.intervalIntegrable; fun_prop)) (hint1.const_mul _),
    intervalIntegral.integral_add (hint1.const_mul _) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have h16 : 0 ≤ 16 * x ^ 2 := by positivity
  have h256 : 0 ≤ 256 / x ^ 4 := by positivity
  have e1 : 16 * x ^ 2 * ∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2) ≤ 16 * x ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hI h16
  have e3 : 256 / x ^ 4 * ∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2) ≤ 256 / x ^ 4 * 2 :=
    mul_le_mul_of_nonneg_left hI h256
  have e2 : 1 / x * (T * (xbBlockConstant + Real.log (T + 4)) ^ 2)
      = T * (xbBlockConstant + Real.log (T + 4)) ^ 2 / x := by ring
  rw [e2]
  rw [intervalIntegral.integral_const_mul]
  set I := ∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2) with hIdef
  set A := (xbBlockConstant + Real.log (T + 4)) ^ 2 with hAdef
  have hkey : 3 * ((16 * x ^ 2 * I) + T * A / x + 256 / x ^ 4 * I)
      ≤ 96 * x ^ 2 + 3 * T * A / x + 1536 / x ^ 4 := by
    have h1 : 16 * x ^ 2 * I ≤ 32 * x ^ 2 := by
      have := e1; rw [show (16 : ℝ) * x ^ 2 * 2 = 32 * x ^ 2 by ring] at this; exact this
    have h3 : 256 / x ^ 4 * I ≤ 512 / x ^ 4 := by
      have := e3; rw [show (256 : ℝ) / x ^ 4 * 2 = 512 / x ^ 4 by ring] at this; exact this
    have : 3 * T * A / x = 3 * (T * A / x) := by ring
    rw [this]
    have : (1536 : ℝ) / x ^ 4 = 3 * (512 / x ^ 4) := by ring
    rw [this]
    linarith
  exact hkey

end RHTower
