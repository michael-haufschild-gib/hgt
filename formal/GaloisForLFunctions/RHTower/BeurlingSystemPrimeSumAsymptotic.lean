import GaloisForLFunctions.RHTower.BeurlingSystemPartialSummation
import GaloisForLFunctions.HTGeometry.LogWeightedRpowIntegral

/-!
# The generalized prime power sum

If a discrete Beurling system satisfies the prime number theorem `π_P(X) log X / X → 1`, then for
every positive exponent

```text
∑_{2 < |p| ≤ X} |p|^(a-1) ~ X^a/(a log X).
```

Abel summation converts the sum into the counting function; writing `π_P(t) = (t/log t)(1 + E(t))`
with `E → 0`, the main term is `(1-a)` times the logarithmic power integral, the boundary term
contributes `a`, and the `E`-weighted remainder is of smaller order because its kernel is exactly
`t^(a-1)/log t`.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

namespace BeurlingSystem

variable {B : BeurlingSystem}

/-- The relative error in the generalized prime number theorem. -/
noncomputable def pntError (B : BeurlingSystem) (t : ℝ) : ℝ :=
  (B.primeCount t : ℝ) * Real.log t / t - 1

theorem primeCount_eq_mul (B : BeurlingSystem) {t : ℝ} (ht : 1 < t) :
    (B.primeCount t : ℝ) = t / Real.log t * (1 + B.pntError t) := by
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; linarith
  have hone : (1 : ℝ) + B.pntError t = (B.primeCount t : ℝ) * Real.log t / t := by
    rw [pntError]; ring
  rw [hone]
  field_simp

theorem tendsto_pntError (hpnt : B.HasPrimePNT) : Tendsto B.pntError atTop (nhds 0) := by
  have h : Tendsto (fun X : ℝ => (B.primeCount X : ℝ) * Real.log X / X - 1) atTop
      (nhds (1 - 1)) := hpnt.sub_const 1
  rw [sub_self] at h
  exact h

theorem measurable_pntError (hdisc : B.IsDiscrete) : Measurable B.pntError := by
  have h : Measurable fun t : ℝ => (B.primeCount t : ℝ) := (monotone_primeCount hdisc).measurable
  exact ((h.mul Real.measurable_log).div measurable_id).sub measurable_const

theorem integrableOn_pntError (hdisc : B.IsDiscrete) (x : ℝ) :
    IntegrableOn B.pntError (Icc 2 x) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_pntError hdisc).aestronglyMeasurable
    (M := (B.primeCount x : ℝ) * Real.log x / 2 + 1) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have htx : t ≤ x := ht.2
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogtx : Real.log t ≤ Real.log x := Real.log_le_log ht0 htx
  have hlogx0 : (0 : ℝ) ≤ Real.log x := hlogt.le.trans hlogtx
  have hpi : (B.primeCount t : ℝ) ≤ (B.primeCount x : ℝ) :=
    Nat.cast_le.mpr (primeCount_mono hdisc htx)
  have hnum : (B.primeCount t : ℝ) * Real.log t ≤ (B.primeCount x : ℝ) * Real.log x :=
    mul_le_mul hpi hlogtx hlogt.le (Nat.cast_nonneg _)
  have hPX : (0 : ℝ) ≤ (B.primeCount x : ℝ) * Real.log x := mul_nonneg (Nat.cast_nonneg _) hlogx0
  have hmain : (B.primeCount t : ℝ) * Real.log t / t ≤ (B.primeCount x : ℝ) * Real.log x / 2 := by
    rw [div_le_div_iff₀ ht0 (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hnum, ht2, hPX]
  have hnonneg : (0 : ℝ) ≤ (B.primeCount t : ℝ) * Real.log t / t := by positivity
  rw [pntError, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem intervalIntegrable_pntError_mul (hdisc : B.IsDiscrete) {a x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => B.pntError t * (t ^ (a - 1) / Real.log t)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact ((integrableOn_pntError hdisc x).mul_continuousOn
    (fun t ht => (HTGeometry.continuousAt_rpowDivLog (a := a) ht.1).continuousWithinAt)
    isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- The generalized prime power sum over the window `(2, X]`. -/
noncomputable def primeRpowSum (hdisc : B.IsDiscrete) (a X : ℝ) : ℝ :=
  ∑ p ∈ (finite_primeWindow hdisc 2 X).toFinset, B.labelNorm p ^ (a - 1)

/-- Abel summation splits the prime power sum into a boundary term, the logarithmic power
integral, and an error-weighted remainder. -/
theorem primeRpowSum_eq (hdisc : B.IsDiscrete) {a X : ℝ} (hX : 2 ≤ X) :
    primeRpowSum hdisc a X
      = (B.primeCount X : ℝ) * X ^ (a - 1) - (B.primeCount 2 : ℝ) * (2 : ℝ) ^ (a - 1)
        - (a - 1) * HTGeometry.logRpowIntegral a X
        - (a - 1) * ∫ t in (2 : ℝ)..X, B.pntError t * (t ^ (a - 1) / Real.log t) := by
  have hderiv : ∀ t ∈ Icc (2 : ℝ) X,
      HasDerivAt (fun s : ℝ => s ^ (a - 1)) ((a - 1) * t ^ (a - 2)) t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht2; linarith
    have h := Real.hasDerivAt_rpow_const (x := t) (p := a - 1) (Or.inl ht0)
    rwa [show a - 1 - 1 = a - 2 by ring] at h
  have hint : IntervalIntegrable (fun t : ℝ => (a - 1) * t ^ (a - 2)) volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hX]
    have hc : ContinuousOn (fun t : ℝ => t ^ (a - 2)) (Icc 2 X) :=
      ContinuousOn.rpow_const continuous_id.continuousOn fun t ht => Or.inl (by
        have h2 : (2 : ℝ) ≤ t := ht.1
        intro h
        rw [h] at h2
        linarith)
    exact continuousOn_const.mul hc
  have habel := sum_primeWindow_eq_sub_sub_integral hdisc hX hderiv hint
  have hpt : ∀ t ∈ uIcc (2 : ℝ) X, ((a - 1) * t ^ (a - 2)) * (B.primeCount t : ℝ)
      = (a - 1) * (t ^ (a - 1) / Real.log t)
        + (a - 1) * (B.pntError t * (t ^ (a - 1) / Real.log t)) := by
    intro t ht
    rw [uIcc_of_le hX] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    have hrp : t ^ (a - 2) * t = t ^ (a - 1) := by
      nth_rewrite 2 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0, show a - 2 + 1 = a - 1 by ring]
    have hshift : ((a - 1) * t ^ (a - 2)) * (t / Real.log t * (1 + B.pntError t))
        = (a - 1) * ((t ^ (a - 2) * t) / Real.log t) * (1 + B.pntError t) := by
      field_simp
    rw [primeCount_eq_mul B (by linarith : (1 : ℝ) < t), hshift, hrp]
    ring
  have hI1 : IntervalIntegrable (fun t : ℝ => (a - 1) * (t ^ (a - 1) / Real.log t)) volume 2 X :=
    (HTGeometry.intervalIntegrable_rpowDivLog a le_rfl hX).const_mul _
  have hI2 : IntervalIntegrable
      (fun t : ℝ => (a - 1) * (B.pntError t * (t ^ (a - 1) / Real.log t))) volume 2 X :=
    (intervalIntegrable_pntError_mul hdisc hX).const_mul _
  have hsplit : (∫ t in (2 : ℝ)..X, ((a - 1) * t ^ (a - 2)) * (B.primeCount t : ℝ))
      = (a - 1) * HTGeometry.logRpowIntegral a X
        + (a - 1) * ∫ t in (2 : ℝ)..X, B.pntError t * (t ^ (a - 1) / Real.log t) := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hI1 hI2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      HTGeometry.logRpowIntegral]
  rw [primeRpowSum, habel, hsplit]
  ring

/-- **The generalized prime power sum is asymptotic to `X^a/(a log X)`.** -/
theorem tendsto_primeRpowSum (hdisc : B.IsDiscrete) (hpnt : B.HasPrimePNT) {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun X : ℝ => primeRpowSum hdisc a X * (a * Real.log X) / X ^ a) atTop (nhds 1) := by
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
  have hT1 : Tendsto
      (fun X : ℝ => (B.primeCount X : ℝ) * X ^ (a - 1) * (a * Real.log X) / X ^ a) atTop
      (nhds a) := by
    have h : Tendsto (fun X : ℝ => a * ((B.primeCount X : ℝ) * Real.log X / X)) atTop
        (nhds (a * 1)) := hpnt.const_mul a
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hXa : X ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hX a)
    have hsub : X ^ (a - 1) = X ^ a / X := by rw [Real.rpow_sub hX, Real.rpow_one]
    rw [hsub]
    field_simp
  have hT2 : Tendsto
      (fun X : ℝ => (B.primeCount 2 : ℝ) * (2 : ℝ) ^ (a - 1) * (a * Real.log X) / X ^ a) atTop
      (nhds 0) := by
    have h := hlogdiv.const_mul ((B.primeCount 2 : ℝ) * (2 : ℝ) ^ (a - 1) * a)
    rw [mul_zero] at h
    refine h.congr fun X => ?_
    ring
  have hT3 : Tendsto
      (fun X : ℝ => (a - 1) * HTGeometry.logRpowIntegral a X * (a * Real.log X) / X ^ a) atTop
      (nhds (a - 1)) := by
    have h := (HTGeometry.tendsto_logRpowIntegral ha0).const_mul (a - 1)
    rw [mul_one] at h
    refine h.congr fun X => ?_
    ring
  have hT4 : Tendsto (fun X : ℝ =>
      (a - 1) * (∫ t in (2 : ℝ)..X, B.pntError t * (t ^ (a - 1) / Real.log t))
        * (a * Real.log X) / X ^ a) atTop (nhds 0) := by
    have hrem := HTGeometry.tendsto_logKernelRemainder ha0 zero_le_one (tendsto_pntError hpnt)
      (K := fun t : ℝ => t ^ (a - 1) / Real.log t)
      (fun t ht => le_of_eq (by
        have h0 : (0 : ℝ) < t := by linarith
        have hl : 0 < Real.log t := Real.log_pos (by linarith)
        rw [one_mul]
        exact abs_of_nonneg (by positivity)))
      (fun x hx => intervalIntegrable_pntError_mul hdisc hx)
    have h := hrem.const_mul (a - 1)
    rw [mul_zero] at h
    refine h.congr fun X => ?_
    ring
  have hsum : Tendsto (fun X : ℝ =>
      (B.primeCount X : ℝ) * X ^ (a - 1) * (a * Real.log X) / X ^ a
        - (B.primeCount 2 : ℝ) * (2 : ℝ) ^ (a - 1) * (a * Real.log X) / X ^ a
        - ((a - 1) * HTGeometry.logRpowIntegral a X * (a * Real.log X) / X ^ a
          + (a - 1) * (∫ t in (2 : ℝ)..X, B.pntError t * (t ^ (a - 1) / Real.log t))
            * (a * Real.log X) / X ^ a)) atTop (nhds (a - 0 - ((a - 1) + 0))) :=
    (hT1.sub hT2).sub (hT3.add hT4)
  rw [show a - 0 - ((a - 1) + 0) = 1 by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  rw [primeRpowSum_eq hdisc hX]
  ring

end BeurlingSystem

end RHTower
