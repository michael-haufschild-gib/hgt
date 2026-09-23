import GaloisForLFunctions.RHTower.ThetaRelativeErrorMass

/-!
# The prime log-square sum

Abel summation of the Chebyshev function against the weight `log t / t` gives Mertens' second
moment

```text
∑_{2 < p ≤ Y} (log p)² / p = (log Y)²/2 + O(log Y),
```

with an explicit constant: the boundary terms are `O(log Y)` by the relative prime-number-theorem
error bound, and the remainder integral is controlled by the absolute relative-error mass.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- The prime log-square sum over the window `(2, Y]`. -/
def primeLogSqSumIoc (Y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊, (if k.Prime then Real.log k ^ (2 : ℕ) / (k : ℝ) else 0)

theorem hasDerivAt_logDivId {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log s / s) ((1 - Real.log t) / t ^ (2 : ℕ)) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht
  have h := hlog.div (hasDerivAt_id t) ht
  refine h.congr_deriv ?_
  simp only [id_eq]
  field_simp

theorem continuousOn_logDivIdDeriv (Y : ℝ) :
    ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ (2 : ℕ)) (Icc 2 Y) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht2
    linarith
  refine ContinuousAt.continuousWithinAt ?_
  exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div
    (continuousAt_id.pow 2) (by positivity)

theorem integrableOn_logDivIdDeriv (Y : ℝ) :
    IntegrableOn (deriv fun s : ℝ => Real.log s / s) (Icc 2 Y) := by
  refine (continuousOn_logDivIdDeriv Y).integrableOn_Icc.congr_fun (fun t ht => ?_)
    measurableSet_Icc
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht2
    linarith
  exact ((hasDerivAt_logDivId ht0).deriv).symm

/-- **Abel summation of the prime log-square sum.** -/
theorem primeLogSqSumIoc_eq {Y : ℝ} (hY : 2 ≤ Y) :
    primeLogSqSumIoc Y
      = Real.log Y / Y * Chebyshev.theta Y - Real.log 2 / 2 * Chebyshev.theta 2
        - ∫ t in (2 : ℝ)..Y, (1 - Real.log t) / t ^ (2 : ℕ) * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) primeLogWeight_primeRpowAbelSummation
    (f := fun s : ℝ => Real.log s / s) (a := (2 : ℝ)) (b := Y) (by norm_num) hY
    (fun t ht => (hasDerivAt_logDivId (by
      have h2 : (2 : ℝ) ≤ t := ht.1
      intro h
      rw [h] at h2
      linarith)).differentiableAt)
    (integrableOn_logDivIdDeriv Y)
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  have hint : (∫ t in Ioc (2 : ℝ) Y, deriv (fun s : ℝ => Real.log s / s) t * Chebyshev.theta t)
      = ∫ t in (2 : ℝ)..Y, (1 - Real.log t) / t ^ (2 : ℕ) * Chebyshev.theta t := by
    rw [intervalIntegral.integral_of_le hY]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht2 : (2 : ℝ) < t := ht.1
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht2
      linarith
    rw [(hasDerivAt_logDivId ht0).deriv]
  rw [primeLogSqSumIoc, ← hint, ← habel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [primeLogWeight_primeRpowAbelSummation]
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp]
    ring
  · rw [if_neg hp, if_neg hp, mul_zero]

/-! ## The second-moment law -/

theorem abs_theta_two_le : |Chebyshev.theta 2| ≤ 2 * (Real.log 4 + 2) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hval : Chebyshev.theta 2 = 2 * (1 + thetaError 2) := theta_eq_mul_thetaError h2
  have habs : |thetaError 2| ≤ Real.log 4 + 1 := abs_thetaError_le le_rfl
  have hbound := abs_le.mp habs
  rw [hval, abs_le]
  constructor
  · nlinarith [hbound.1, hbound.2]
  · nlinarith [hbound.1, hbound.2]

/-- The uniform constant of the prime log-square law. -/
def mertensLogSqConst : ℝ :=
  1 + 2 * (Real.log 4 + 2) + (Real.log 4 + 1) + thetaRelMass

theorem mertensLogSqConst_nonneg : 0 ≤ mertensLogSqConst := by
  have h1 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 := thetaRelMass_nonneg
  rw [mertensLogSqConst]
  linarith

theorem integral_one_sub_log_div_id {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, (1 - Real.log t) / t)
      = (Real.log Y - Real.log Y ^ (2 : ℕ) / 2) - (Real.log 2 - Real.log 2 ^ (2 : ℕ) / 2) := by
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) Y,
      HasDerivAt (fun s : ℝ => Real.log s - Real.log s ^ (2 : ℕ) / 2) ((1 - Real.log t) / t) t := by
    intro t ht
    rw [uIcc_of_le hY] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht2
      linarith
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have hsq : HasDerivAt (fun s : ℝ => Real.log s ^ (2 : ℕ) / 2) (Real.log t * t⁻¹) t := by
      have h := (hlog.pow 2).div_const 2
      refine h.congr_deriv ?_
      push_cast
      ring
    have h := hlog.sub hsq
    refine h.congr_deriv ?_
    field_simp
  have hcont : IntervalIntegrable (fun t : ℝ => (1 - Real.log t) / t) volume 2 Y := by
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    rw [uIcc_of_le hY] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht2
      linarith
    exact ((continuousAt_const.sub (Real.continuousAt_log ht0)).div
      continuousAt_id ht0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]

theorem integral_abs_thetaError_div_le {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, |thetaError t| / t) ≤ thetaRelMass := by
  have hint : IntervalIntegrable (fun t : ℝ => |thetaError t| / t) volume 2 Y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
    exact integrableOn_abs_thetaError_div_id.mono_set Ioc_subset_Ioi_self
  rw [intervalIntegral.integral_of_le hY]
  refine setIntegral_mono_set integrableOn_abs_thetaError_div_id ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
    positivity
  · exact Filter.Eventually.of_forall fun t ht => Ioc_subset_Ioi_self ht

/-- **Mertens' second-moment law.**  `∑_{2 < p ≤ Y} (log p)²/p = (log Y)²/2 + O(log Y)`. -/
theorem abs_primeLogSqSumIoc_sub_le {Y : ℝ} (hY : 2 ≤ Y) :
    |primeLogSqSumIoc Y - Real.log Y ^ (2 : ℕ) / 2| ≤ mertensLogSqConst * (1 + Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have habel := primeLogSqSumIoc_eq hY
  -- the boundary term
  have hbdry : Real.log Y / Y * Chebyshev.theta Y = Real.log Y * (1 + thetaError Y) := by
    rw [theta_eq_mul_thetaError hY0]
    field_simp
  -- the main integral
  have hsplit : (∫ t in (2 : ℝ)..Y, (1 - Real.log t) / t ^ (2 : ℕ) * Chebyshev.theta t)
      = (∫ t in (2 : ℝ)..Y, (1 - Real.log t) / t)
        + ∫ t in (2 : ℝ)..Y, (1 - Real.log t) * thetaError t / t := by
    have hpt : ∀ t ∈ uIcc (2 : ℝ) Y, (1 - Real.log t) / t ^ (2 : ℕ) * Chebyshev.theta t
        = (1 - Real.log t) / t + (1 - Real.log t) * thetaError t / t := by
      intro t ht
      rw [uIcc_of_le hY] at ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have ht0 : (0 : ℝ) < t := by linarith
      rw [theta_eq_mul_thetaError ht0]
      field_simp
    have hI1 : IntervalIntegrable (fun t : ℝ => (1 - Real.log t) / t) volume 2 Y := by
      refine ContinuousOn.intervalIntegrable ?_
      intro t ht
      rw [uIcc_of_le hY] at ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have ht0 : t ≠ 0 := by
        intro h
        rw [h] at ht2
        linarith
      exact ((continuousAt_const.sub (Real.continuousAt_log ht0)).div
        continuousAt_id ht0).continuousWithinAt
    have hI2 : IntervalIntegrable (fun t : ℝ => (1 - Real.log t) * thetaError t / t) volume 2 Y := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
      have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t) (Icc 2 Y) := by
        intro t ht
        have ht2 : (2 : ℝ) ≤ t := ht.1
        have ht0 : t ≠ 0 := by
          intro h
          rw [h] at ht2
          linarith
        exact ((continuousAt_const.sub (Real.continuousAt_log ht0)).div
          continuousAt_id ht0).continuousWithinAt
      have hprod := ((integrableOn_thetaError Y).mul_continuousOn hcont isCompact_Icc)
      refine (hprod.mono_set Ioc_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
      have ht2 : (2 : ℝ) < t := ht.1
      have ht0 : (0 : ℝ) < t := by linarith
      field_simp
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hI1 hI2]
  rw [hsplit, integral_one_sub_log_div_id hY] at habel
  -- bound each piece
  have hthetaY : |thetaError Y| ≤ Real.log 4 + 1 := abs_thetaError_le hY
  have hthetaTwo : |Chebyshev.theta 2| ≤ 2 * (Real.log 4 + 2) := abs_theta_two_le
  have hrem : |∫ t in (2 : ℝ)..Y, (1 - Real.log t) * thetaError t / t|
      ≤ (1 + Real.log Y) * thetaRelMass := by
    have hint : IntervalIntegrable (fun t : ℝ => (1 - Real.log t) * thetaError t / t) volume 2 Y := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
      have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t) (Icc 2 Y) := by
        intro t ht
        have ht2 : (2 : ℝ) ≤ t := ht.1
        have ht0 : t ≠ 0 := by
          intro h
          rw [h] at ht2
          linarith
        exact ((continuousAt_const.sub (Real.continuousAt_log ht0)).div
          continuousAt_id ht0).continuousWithinAt
      have hprod := ((integrableOn_thetaError Y).mul_continuousOn hcont isCompact_Icc)
      refine (hprod.mono_set Ioc_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
      have ht2 : (2 : ℝ) < t := ht.1
      have ht0 : (0 : ℝ) < t := by linarith
      field_simp
    have habs : |∫ t in (2 : ℝ)..Y, (1 - Real.log t) * thetaError t / t|
        ≤ ∫ t in (2 : ℝ)..Y, |(1 - Real.log t) * thetaError t / t| :=
      intervalIntegral.abs_integral_le_integral_abs hY
    have hpt : ∀ t ∈ Ioc (2 : ℝ) Y, |(1 - Real.log t) * thetaError t / t|
        ≤ (1 + Real.log Y) * (|thetaError t| / t) := by
      intro t ht
      have ht2 : (2 : ℝ) < t := ht.1
      have htY : t ≤ Y := ht.2
      have ht0 : (0 : ℝ) < t := by linarith
      have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have hlogle : Real.log t ≤ Real.log Y := Real.log_le_log ht0 htY
      have hfac : |1 - Real.log t| ≤ 1 + Real.log Y := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_div, abs_mul, abs_of_pos ht0, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      refine mul_le_mul_of_nonneg_right hfac ?_ |>.trans_eq ?_
      · positivity
      · ring
    have hmono : (∫ t in (2 : ℝ)..Y, |(1 - Real.log t) * thetaError t / t|)
        ≤ ∫ t in (2 : ℝ)..Y, (1 + Real.log Y) * (|thetaError t| / t) := by
      refine intervalIntegral.integral_mono_on hY hint.abs ?_ (fun t ht => ?_)
      · have hbase : IntervalIntegrable (fun t : ℝ => |thetaError t| / t) volume 2 Y := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
          exact integrableOn_abs_thetaError_div_id.mono_set Ioc_subset_Ioi_self
        exact hbase.const_mul _
      · rcases eq_or_lt_of_le ht.1 with heq | hlt
        · rw [← heq]
          have h2 : (0 : ℝ) < 2 := by norm_num
          have : |1 - Real.log 2| ≤ 1 + Real.log Y := by
            have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            have hlogle : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
            rw [abs_le]
            constructor <;> linarith
          rw [abs_div, abs_mul, abs_of_pos h2, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
          refine mul_le_mul_of_nonneg_right this ?_ |>.trans_eq ?_
          · positivity
          · ring
        · exact hpt t ⟨hlt, ht.2⟩
    rw [intervalIntegral.integral_const_mul] at hmono
    have hbase := integral_abs_thetaError_div_le hY
    have hcoef : (0 : ℝ) ≤ 1 + Real.log Y := by linarith
    calc |∫ t in (2 : ℝ)..Y, (1 - Real.log t) * thetaError t / t|
        ≤ ∫ t in (2 : ℝ)..Y, |(1 - Real.log t) * thetaError t / t| := habs
      _ ≤ (1 + Real.log Y) * ∫ t in (2 : ℝ)..Y, |thetaError t| / t := hmono
      _ ≤ (1 + Real.log Y) * thetaRelMass := mul_le_mul_of_nonneg_left hbase hcoef
  -- assemble
  rw [hbdry] at habel
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hb1 := abs_le.mp hthetaY
  have hb2 := abs_le.mp hthetaTwo
  have hb3 := abs_le.mp hrem
  have hmass := thetaRelMass_nonneg
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [mertensLogSqConst, abs_le]
  constructor
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hlogY, hlog2, hlog2le, hmass, hlog4]
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hlogY, hlog2, hlog2le, hmass, hlog4]

end

end RHTower
