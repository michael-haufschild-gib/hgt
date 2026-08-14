import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic

/-!
# Absolute mass of the relative prime-number-theorem error

The prime number theorem with the square-root-logarithmic error term makes the relative error
`θ(t)/t - 1` decay faster than any power of `1/log t`.  In particular

```text
∫_2^∞ |θ(t)/t - 1| dt/t < ∞,
```

which is the uniform ingredient needed for tilted prime sums `∑_{p ≤ Y} p^{-1-δ} log p` with a
moving tilt `δ`: the Abel remainder is bounded by this one absolute mass, uniformly in `δ ≥ 0`.
-/

open Filter Topology Set MeasureTheory intervalIntegral Asymptotics

namespace RHTower

noncomputable section

/-! ## The logarithmic majorant -/

/-- `1/(t (log t)²)` is integrable on `(e, ∞)`, with primitive `-1/log t`. -/
theorem integrableOn_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Ioi (Real.exp 1)) := by
  have hcont : ContinuousWithinAt (fun t : ℝ => -(Real.log t)⁻¹) (Ici (Real.exp 1))
      (Real.exp 1) := by
    have hlog : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h : ContinuousAt (fun t : ℝ => -(Real.log t)⁻¹) (Real.exp 1) := by
      refine ContinuousAt.neg (ContinuousAt.inv₀ ?_ ?_)
      · exact Real.continuousAt_log (ne_of_gt hpos)
      · rw [hlog]
        norm_num
    exact h.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (Real.exp 1),
      HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
    intro x hx
    have hx1 : Real.exp 1 < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans (Real.exp_pos 1) hx1
    have hlog1 : (1 : ℝ) < Real.log x := by
      have h := Real.log_lt_log (Real.exp_pos 1) hx1
      rwa [Real.log_exp] at h
    have hlogne : Real.log x ≠ 0 := by linarith
    have hbase : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx0)
    have hinv := hbase.inv hlogne
    have hneg := hinv.neg
    refine hneg.congr_deriv ?_
    field_simp
  have hnonneg : ∀ x ∈ Ioi (Real.exp 1), (0 : ℝ) ≤ (x * Real.log x ^ 2)⁻¹ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans (Real.exp_pos 1) hx
    positivity
  have hlim : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (nhds 0) := by
    have h : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa using h.neg
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim

/-! ## The relative error decays faster than `(log t)^{-2}` -/

theorem exp_neg_le_inv_sq {c v : ℝ} (hc : 0 < c) (hv : 0 < v) :
    Real.exp (-c * Real.sqrt v) ≤ 256 / (c ^ 4 * v ^ 2) := by
  have hsqrt : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hx : 0 < c * Real.sqrt v := mul_pos hc hsqrt
  have hquarter : (1 : ℝ) + c * Real.sqrt v / 4 ≤ Real.exp (c * Real.sqrt v / 4) := by
    have := Real.add_one_le_exp (c * Real.sqrt v / 4)
    linarith
  have hbase : (0 : ℝ) ≤ 1 + c * Real.sqrt v / 4 := by positivity
  have hpow : ((1 : ℝ) + c * Real.sqrt v / 4) ^ 4 ≤ Real.exp (c * Real.sqrt v / 4) ^ 4 :=
    pow_le_pow_left₀ hbase hquarter 4
  have hexp4 : Real.exp (c * Real.sqrt v / 4) ^ 4 = Real.exp (c * Real.sqrt v) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  have hlow : c ^ 4 * v ^ 2 / 256 ≤ Real.exp (c * Real.sqrt v) := by
    have hchain : (c * Real.sqrt v / 4) ^ 4 ≤ ((1 : ℝ) + c * Real.sqrt v / 4) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hval : (c * Real.sqrt v / 4) ^ 4 = c ^ 4 * v ^ 2 / 256 := by
      have : (c * Real.sqrt v) ^ 4 = c ^ 4 * (Real.sqrt v ^ 2) ^ 2 := by ring
      rw [div_pow, this, hsq]
      norm_num
    rw [← hval, ← hexp4]
    linarith [hchain, hpow]
  have hexppos : (0 : ℝ) < Real.exp (c * Real.sqrt v) := Real.exp_pos _
  have hcv : (0 : ℝ) < c ^ 4 * v ^ 2 := by positivity
  rw [neg_mul, Real.exp_neg,
    inv_le_comm₀ hexppos (by positivity : (0 : ℝ) < 256 / (c ^ 4 * v ^ 2)), inv_div]
  exact hlow

/-- **The relative error of the prime number theorem is `O((log t)^{-2})`.** -/
theorem exists_abs_thetaError_le :
    ∃ C > 0, ∃ T ≥ Real.exp 1, ∀ t ≥ T, |thetaError t| ≤ C * (Real.log t ^ 2)⁻¹ := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  rw [Filter.eventually_atTop] at hC
  obtain ⟨T₀, hT₀⟩ := hC
  refine ⟨256 * (|C| + 1) / c ^ 4, by positivity,
    max (max T₀ (Real.exp 1)) (Real.exp 1), le_max_right _ _, fun t ht => ?_⟩
  have hT : T₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have hE : Real.exp 1 ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 1) hE
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) hE
    rwa [Real.log_exp] at h
  have hlogpos : (0 : ℝ) < Real.log t := by linarith
  have hbound := hT₀ t hT
  have habs : |Chebyshev.theta t - t| ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := by
    have hpos : (0 : ℝ) ≤ t * Real.exp (-c * Real.sqrt (Real.log t)) := by positivity
    have h := hbound
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at h
    have hCle : C ≤ |C| := le_abs_self C
    have hmul : C * (t * Real.exp (-c * Real.sqrt (Real.log t)))
        ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
      mul_le_mul_of_nonneg_right hCle hpos
    have hval : |(Chebyshev.theta - (id : ℝ → ℝ)) t| = |Chebyshev.theta t - t| := by
      simp [Pi.sub_apply]
    rw [hval] at h
    linarith
  have hrel : |thetaError t| = |Chebyshev.theta t - t| / t := by
    have hval : thetaError t = (Chebyshev.theta t - t) / t := by
      rw [thetaError]
      field_simp
    rw [hval, abs_div, abs_of_pos ht0]
  rw [hrel]
  have hexp := exp_neg_le_inv_sq hc0 hlogpos
  have hstep : |Chebyshev.theta t - t| / t ≤ |C| * Real.exp (-c * Real.sqrt (Real.log t)) := by
    rw [div_le_iff₀ ht0]
    calc |Chebyshev.theta t - t| ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := habs
      _ = |C| * Real.exp (-c * Real.sqrt (Real.log t)) * t := by ring
  have hfinal : |C| * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ 256 * (|C| + 1) / c ^ 4 * (Real.log t ^ 2)⁻¹ := by
    have hCabs : (0 : ℝ) ≤ |C| := abs_nonneg C
    have hmul : |C| * Real.exp (-c * Real.sqrt (Real.log t))
        ≤ |C| * (256 / (c ^ 4 * Real.log t ^ 2)) := mul_le_mul_of_nonneg_left hexp hCabs
    have hlogsq : (0 : ℝ) < Real.log t ^ 2 := by positivity
    have hc4 : (0 : ℝ) < c ^ 4 := by positivity
    have hrw : |C| * (256 / (c ^ 4 * Real.log t ^ 2))
        = 256 * |C| / c ^ 4 * (Real.log t ^ 2)⁻¹ := by
      field_simp
    have hle : 256 * |C| / c ^ 4 * (Real.log t ^ 2)⁻¹
        ≤ 256 * (|C| + 1) / c ^ 4 * (Real.log t ^ 2)⁻¹ := by
      have hcoef : 256 * |C| / c ^ 4 ≤ 256 * (|C| + 1) / c ^ 4 := by
        apply div_le_div_of_nonneg_right _ hc4.le
        linarith
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    rw [hrw] at hmul
    linarith
  linarith

/-! ## The absolute relative-error mass -/

theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

/-- The relative error has finite absolute logarithmic mass. -/
theorem integrableOn_abs_thetaError_div_id :
    IntegrableOn (fun t : ℝ => |thetaError t| / t) (Ioi 2) := by
  obtain ⟨C, hC0, T, hT, hbound⟩ := exists_abs_thetaError_le
  have hT2 : (2 : ℝ) ≤ T := le_trans two_lt_exp_one.le hT
  have hmeas : Measurable fun t : ℝ => |thetaError t| / t :=
    measurable_thetaError.abs.div measurable_id
  -- the compact part
  have hEabs : IntegrableOn (fun t : ℝ => |thetaError t|) (Icc 2 T) :=
    (integrableOn_thetaError T).abs
  have hcompactIcc : IntegrableOn (fun t : ℝ => |thetaError t| / t) (Icc 2 T) := by
    refine Integrable.mono' (hEabs.const_mul (1 / 2)) hmeas.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ ht0]
    have habs : 0 ≤ |thetaError t| := abs_nonneg _
    nlinarith [habs, ht2]
  have hcompact : IntegrableOn (fun t : ℝ => |thetaError t| / t) (Ioc 2 T) :=
    hcompactIcc.mono_set Ioc_subset_Icc_self
  -- the tail
  have hmaj : IntegrableOn (fun t : ℝ => C * (t * Real.log t ^ 2)⁻¹) (Ioi T) :=
    (integrableOn_inv_mul_log_sq.mono_set (Ioi_subset_Ioi hT)).const_mul C
  have htail : IntegrableOn (fun t : ℝ => |thetaError t| / t) (Ioi T) := by
    refine Integrable.mono' hmaj hmeas.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have htT : T ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) < t := by
      have : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT2
      linarith
    have hlogpos : (0 : ℝ) < Real.log t := by
      have hE : Real.exp 1 ≤ t := le_trans hT htT
      have h := Real.log_le_log (Real.exp_pos 1) hE
      rw [Real.log_exp] at h
      linarith
    have hb := hbound t htT
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hstep : |thetaError t| / t ≤ C * (Real.log t ^ 2)⁻¹ / t := by
      exact div_le_div_of_nonneg_right hb ht0.le
    have hval : C * (Real.log t ^ 2)⁻¹ / t = C * (t * Real.log t ^ 2)⁻¹ := by
      field_simp
    rw [← hval]
    exact hstep
  have hunion := hcompact.union htail
  rwa [Ioc_union_Ioi_eq_Ioi hT2] at hunion

/-- The total absolute logarithmic mass of the relative error. -/
def thetaRelMass : ℝ := ∫ t in Ioi (2 : ℝ), |thetaError t| / t

theorem thetaRelMass_nonneg : 0 ≤ thetaRelMass := by
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
  positivity

/-- **The Abel remainder of a tilted prime sum is bounded by one absolute mass**, uniformly in the
tilt `δ ≥ 0` and the aperture `x`. -/
theorem abs_integral_thetaError_mul_rpow_le {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, thetaError t * t ^ (-δ - 1)| ≤ thetaRelMass := by
  have hint : IntervalIntegrable (fun t : ℝ => thetaError t * t ^ (-δ - 1)) volume 2 x := by
    have h := intervalIntegrable_thetaError_mul (a := -δ) hx
    simpa using h
  have habs : |∫ t in (2 : ℝ)..x, thetaError t * t ^ (-δ - 1)|
      ≤ ∫ t in (2 : ℝ)..x, |thetaError t * t ^ (-δ - 1)| := by
    have h := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun t : ℝ => thetaError t * t ^ (-δ - 1)) (a := (2 : ℝ)) (b := x) hx
    exact h
  have hmono : (∫ t in (2 : ℝ)..x, |thetaError t * t ^ (-δ - 1)|)
      ≤ ∫ t in Ioi (2 : ℝ), |thetaError t| / t := by
    have hset : (∫ t in (2 : ℝ)..x, |thetaError t * t ^ (-δ - 1)|)
        = ∫ t in Ioc (2 : ℝ) x, |thetaError t * t ^ (-δ - 1)| := by
      rw [intervalIntegral.integral_of_le hx]
    rw [hset]
    have hf : IntegrableOn (fun t : ℝ => |thetaError t * t ^ (-δ - 1)|) (Ioc 2 x) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hint).abs
    have hg : IntegrableOn (fun t : ℝ => |thetaError t| / t) (Ioc 2 x) :=
      integrableOn_abs_thetaError_div_id.mono_set Ioc_subset_Ioi_self
    have hle : (∫ t in Ioc (2 : ℝ) x, |thetaError t * t ^ (-δ - 1)|)
        ≤ ∫ t in Ioc (2 : ℝ) x, |thetaError t| / t := by
      refine setIntegral_mono_on hf hg measurableSet_Ioc (fun t ht => ?_)
      have ht2 : (2 : ℝ) < t := ht.1
      have ht0 : (0 : ℝ) < t := by linarith
      have ht1 : (1 : ℝ) ≤ t := by linarith
      have hrp : t ^ (-δ - 1) ≤ t⁻¹ := by
        have hle : t ^ (-δ - 1) ≤ t ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
        rwa [Real.rpow_neg_one] at hle
      have hrp0 : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
      rw [abs_mul, abs_of_pos hrp0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrp (abs_nonneg _)
    refine le_trans hle ?_
    refine setIntegral_mono_set integrableOn_abs_thetaError_div_id ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
      positivity
    · exact Filter.Eventually.of_forall fun t ht => Ioc_subset_Ioi_self ht
  exact le_trans habs hmono

end

end RHTower
