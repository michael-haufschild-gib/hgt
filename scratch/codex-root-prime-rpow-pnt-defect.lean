import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.RHTower.RouteETerminalPrimeStieltjesTransport

noncomputable section
open Set MeasureTheory intervalIntegral
namespace RHTower

private theorem logRpowIntegral_eq_boundary_sub_deriv {a x : ℝ} (hx : 2 ≤ x) :
    HTGeometry.logRpowIntegral a x =
      rpowDivLog a x * x - rpowDivLog a 2 * 2 -
        ∫ t in Ioc (2 : ℝ) x, deriv (rpowDivLog a) t * t := by
  have hwderiv : ∀ t ∈ uIcc (2 : ℝ) x,
      HasDerivAt (rpowDivLog a) (deriv (rpowDivLog a) t) t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := (uIcc_of_le hx ▸ ht).1
    have hd := hasDerivAt_rpowDivLog (a := a) ht2
    simpa only [hd.deriv] using hd
  have hwint : IntervalIntegrable (rpowDivLog a) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    have hc : ContinuousOn (rpowDivLog a) (Icc 2 x) := by
      intro t ht
      exact (hwderiv t (by simpa [uIcc_of_le hx] using ht)).continuousAt.continuousWithinAt
    exact hc.integrableOn_Icc
  have hdint : IntervalIntegrable (deriv (rpowDivLog a)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact integrableOn_derivRpowDivLog hx
  have hidint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 2 x :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ : ℝ => 1)
    (v := rpowDivLog a) (v' := deriv (rpowDivLog a))
    (fun _ _ => hasDerivAt_id _) hwderiv hidint hdint
  have hmain : HTGeometry.logRpowIntegral a x =
      ∫ t in (2 : ℝ)..x, rpowDivLog a t := by
    rfl
  rw [hmain]
  have hprod : (∫ t in (2 : ℝ)..x, t * deriv (rpowDivLog a) t) =
      x * rpowDivLog a x - 2 * rpowDivLog a 2 -
        ∫ t in (2 : ℝ)..x, rpowDivLog a t := by
    simpa only [one_mul] using hibp
  have hset : (∫ t in Ioc (2 : ℝ) x, deriv (rpowDivLog a) t * t) =
      ∫ t in (2 : ℝ)..x, t * deriv (rpowDivLog a) t := by
    rw [← intervalIntegral.integral_of_le hx]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hset, hprod]
  ring

/-- Exact prime-power weighted PNT defect. The weight may grow; no sign or
decay assumption on its exponent is needed. -/
theorem primeRpowSumIoc_sub_logRpowIntegral_eq_thetaError
    {a x : ℝ} (hx : 2 ≤ x) :
    primeRpowSumIoc a x - HTGeometry.logRpowIntegral a x =
      rpowDivLog a x * (Chebyshev.theta x - x) -
        rpowDivLog a 2 * (Chebyshev.theta 2 - 2) -
          ∫ t in Ioc (2 : ℝ) x,
            deriv (rpowDivLog a) t * (Chebyshev.theta t - t) := by
  have hderivCont : ContinuousOn (deriv (rpowDivLog a)) (Icc 2 x) := by
    have hc : ContinuousOn (derivRpowDivLog a) (Icc 2 x) := fun t ht =>
      (continuousAt_derivRpowDivLog (a := a) ht.1).continuousWithinAt
    refine hc.congr ?_
    intro t ht
    exact (deriv_rpowDivLog (a := a) ht.1)
  have htheta : IntegrableOn Chebyshev.theta (Icc 2 x) :=
    MonotoneOn.integrableOn_isCompact isCompact_Icc (Chebyshev.theta_mono.monotoneOn _)
  have hid : IntegrableOn (fun t : ℝ => t) (Icc 2 x) :=
    continuous_id.continuousOn.integrableOn_Icc
  have herr : IntegrableOn (fun t : ℝ => Chebyshev.theta t - t) (Icc 2 x) :=
    htheta.sub hid
  have hmulId : IntegrableOn
      (fun t : ℝ => deriv (rpowDivLog a) t * t) (Icc 2 x) :=
    hid.mul_continuousOn hderivCont isCompact_Icc |>.congr_fun
      (fun t _ => by ring) measurableSet_Icc
  have hmulErr : IntegrableOn
      (fun t : ℝ => deriv (rpowDivLog a) t * (Chebyshev.theta t - t))
      (Icc 2 x) :=
    herr.mul_continuousOn hderivCont isCompact_Icc |>.congr_fun
      (fun t _ => by ring) measurableSet_Icc
  have hsplit : (∫ t in Ioc (2 : ℝ) x,
      deriv (rpowDivLog a) t * Chebyshev.theta t) =
      (∫ t in Ioc (2 : ℝ) x, deriv (rpowDivLog a) t * t) +
        ∫ t in Ioc (2 : ℝ) x,
          deriv (rpowDivLog a) t * (Chebyshev.theta t - t) := by
    rw [← MeasureTheory.integral_add
      (hmulId.mono_set Ioc_subset_Icc_self)
      (hmulErr.mono_set Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    ring
  rw [primeRpowSumIoc_eq hx,
    logRpowIntegral_eq_boundary_sub_deriv hx, hsplit]
  ring

/-- The exact error localizes to every growing prime interval. -/
theorem primeRpowSumIoc_diff_sub_logRpowIntegral_diff_eq_thetaError
    {a u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (primeRpowSumIoc a v - primeRpowSumIoc a u) -
        (HTGeometry.logRpowIntegral a v - HTGeometry.logRpowIntegral a u) =
      rpowDivLog a v * (Chebyshev.theta v - v) -
        rpowDivLog a u * (Chebyshev.theta u - u) -
          ∫ t in Ioc u v,
            deriv (rpowDivLog a) t * (Chebyshev.theta t - t) := by
  have hv : 2 ≤ v := hu.trans huv
  have hdc : ContinuousOn (deriv (rpowDivLog a)) (Icc 2 v) := by
    have hc : ContinuousOn (derivRpowDivLog a) (Icc 2 v) := fun t ht =>
      (continuousAt_derivRpowDivLog (a := a) ht.1).continuousWithinAt
    refine hc.congr ?_
    intro t ht
    exact deriv_rpowDivLog ht.1
  have htheta : IntegrableOn Chebyshev.theta (Icc 2 v) :=
    MonotoneOn.integrableOn_isCompact isCompact_Icc (Chebyshev.theta_mono.monotoneOn _)
  have herr : IntegrableOn (fun t : ℝ => Chebyshev.theta t - t) (Icc 2 v) :=
    htheta.sub (continuous_id.continuousOn.integrableOn_Icc)
  have hint : IntegrableOn
      (fun t : ℝ => deriv (rpowDivLog a) t * (Chebyshev.theta t - t))
      (Icc 2 v) :=
    herr.mul_continuousOn hdc isCompact_Icc |>.congr_fun
      (fun t _ => by ring) measurableSet_Icc
  have hint₁ : IntervalIntegrable
      (fun t : ℝ => deriv (rpowDivLog a) t * (Chebyshev.theta t - t)) volume 2 u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu]
    exact hint.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans huv⟩)
  have hint₂ : IntervalIntegrable
      (fun t : ℝ => deriv (rpowDivLog a) t * (Chebyshev.theta t - t)) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    exact hint.mono_set (fun t ht => ⟨hu.trans ht.1.le, ht.2⟩)
  have hsplit :
      (∫ t in Ioc (2 : ℝ) v,
        deriv (rpowDivLog a) t * (Chebyshev.theta t - t)) =
      (∫ t in Ioc (2 : ℝ) u,
        deriv (rpowDivLog a) t * (Chebyshev.theta t - t)) +
      ∫ t in Ioc u v,
        deriv (rpowDivLog a) t * (Chebyshev.theta t - t) := by
    rw [← intervalIntegral.integral_of_le hv,
      ← intervalIntegral.integral_of_le hu,
      ← intervalIntegral.integral_of_le huv]
    exact (intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂).symm
  calc
    _ = (primeRpowSumIoc a v - HTGeometry.logRpowIntegral a v) -
        (primeRpowSumIoc a u - HTGeometry.logRpowIntegral a u) := by ring
    _ = (rpowDivLog a v * (Chebyshev.theta v - v) -
        rpowDivLog a 2 * (Chebyshev.theta 2 - 2) -
          ∫ t in Ioc (2 : ℝ) v,
            deriv (rpowDivLog a) t * (Chebyshev.theta t - t)) -
        (rpowDivLog a u * (Chebyshev.theta u - u) -
        rpowDivLog a 2 * (Chebyshev.theta 2 - 2) -
          ∫ t in Ioc (2 : ℝ) u,
            deriv (rpowDivLog a) t * (Chebyshev.theta t - t)) := by
      rw [primeRpowSumIoc_sub_logRpowIntegral_eq_thetaError hv,
        primeRpowSumIoc_sub_logRpowIntegral_eq_thetaError hu]
    _ = _ := by rw [hsplit]; ring

/-- Quantitative finite-band transfer in terms of the actual Chebyshev error,
with both endpoints retained. -/
theorem abs_primeRpowSumIoc_diff_sub_logRpowIntegral_diff_le
    {a u v W D E : ℝ} (hu : 2 ≤ u) (huv : u ≤ v)
    (hW : ∀ t ∈ Icc u v, |rpowDivLog a t| ≤ W)
    (hD : ∀ t ∈ Icc u v, |deriv (rpowDivLog a) t| ≤ D)
    (hE : ∀ t ∈ Icc u v, |Chebyshev.theta t - t| ≤ E) :
    |(primeRpowSumIoc a v - primeRpowSumIoc a u) -
        (HTGeometry.logRpowIntegral a v - HTGeometry.logRpowIntegral a u)| ≤
      2 * W * E + (v - u) * D * E := by
  have hu_mem : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have hv_mem : v ∈ Icc u v := ⟨huv, le_rfl⟩
  have hint :
      |∫ t in Ioc u v,
          deriv (rpowDivLog a) t * (Chebyshev.theta t - t)| ≤
        D * E * (v - u) := by
    rw [← intervalIntegral.integral_of_le huv, ← Real.norm_eq_abs,
      show v - u = |v - u| by rw [abs_of_nonneg (sub_nonneg.mpr huv)]]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le huv] at ht
    have ht' : t ∈ Icc u v := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hD t ht') (hE t ht') (abs_nonneg _)
      (le_trans (abs_nonneg _) (hD t ht'))
  rw [primeRpowSumIoc_diff_sub_logRpowIntegral_diff_eq_thetaError hu huv]
  have htermv :
      |rpowDivLog a v * (Chebyshev.theta v - v)| ≤ W * E := by
    rw [abs_mul]
    exact mul_le_mul (hW v hv_mem) (hE v hv_mem) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hW v hv_mem))
  have htermu :
      |rpowDivLog a u * (Chebyshev.theta u - u)| ≤ W * E := by
    rw [abs_mul]
    exact mul_le_mul (hW u hu_mem) (hE u hu_mem) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hW u hu_mem))
  have htri1 := abs_sub
    (rpowDivLog a v * (Chebyshev.theta v - v) -
      rpowDivLog a u * (Chebyshev.theta u - u))
    (∫ t in Ioc u v,
      deriv (rpowDivLog a) t * (Chebyshev.theta t - t))
  have htri2 := abs_sub
    (rpowDivLog a v * (Chebyshev.theta v - v))
    (rpowDivLog a u * (Chebyshev.theta u - u))
  nlinarith

private theorem rpowPrimeAbelWeight_terminalBand_le {a X t : ℝ}
    (ha : 1 ≤ a) (hL : 4 ≤ Real.log X)
    (ht : t ∈ Icc (X / Real.exp 1) X) :
    |rpowDivLog a t| ≤ 2 * X ^ (a - 1) / Real.log X := by
  have hone := routeETerminal_band_one_lt hL ht
  have ht0 : 0 ≤ t := le_trans (by norm_num) hone.2.le
  have hX0 : 0 ≤ X := ht0.trans ht.2
  have hlogt : 0 < Real.log t := Real.log_pos hone.2
  have hlogX : 0 < Real.log X := by linarith
  have hpow : t ^ (a - 1) ≤ X ^ (a - 1) :=
    Real.rpow_le_rpow ht0 ht.2 (by linarith)
  have hlog := routeETerminal_band_log_lower hL ht
  have hnum0 : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht0 _
  have hden0 : 0 < Real.log X / 2 := by positivity
  have hfrac : t ^ (a - 1) / Real.log t ≤
      X ^ (a - 1) / (Real.log X / 2) := by
    apply div_le_div₀
    · positivity
    · exact hpow
    · exact hden0
    · exact hlog
  have hweight : 0 ≤ rpowDivLog a t := by
    dsimp [rpowDivLog]
    positivity
  rw [abs_of_nonneg hweight]
  change t ^ (a - 1) / Real.log t ≤ _
  calc
    _ ≤ X ^ (a - 1) / (Real.log X / 2) := hfrac
    _ = _ := by field_simp

private theorem rpowPrimeAbelDeriv_terminalBand_le {a X t : ℝ}
    (ha : 1 ≤ a) (hL : 4 ≤ Real.log X)
    (ht : t ∈ Icc (X / Real.exp 1) X) :
    |deriv (rpowDivLog a) t| ≤
      abelKernelConst a *
        (2 * X ^ (a - 1) / Real.log X) /
          (X / Real.exp 1) := by
  have hone := routeETerminal_band_one_lt hL ht
  have hu0 : 0 < X / Real.exp 1 := lt_trans zero_lt_one hone.1
  have ht0 : 0 < t := lt_trans zero_lt_one hone.2
  have hW := rpowPrimeAbelWeight_terminalBand_le ha hL ht
  have hC : 0 ≤ abelKernelConst a := abelKernelConst_nonneg _
  have hW0 : 0 ≤ 2 * X ^ (a - 1) / Real.log X := by
    have hX0 : 0 ≤ X := (lt_of_lt_of_le hu0 (ht.1.trans ht.2)).le
    have hL0 : 0 < Real.log X := by linarith
    positivity
  have ht2 : 2 ≤ t := by
    have hlogu : Real.log (X / Real.exp 1) = Real.log X - 1 := by
      have hX0 : 0 < X := lt_of_lt_of_le hu0 (ht.1.trans ht.2)
      rw [Real.log_div hX0.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)]
    have hu2 : 2 ≤ X / Real.exp 1 :=
      (Real.log_le_log_iff (by norm_num) hu0).mp (by rw [hlogu]; linarith)
    exact hu2.trans ht.1
  have hkernel := abs_abelKernel_le (a := a) (t := t) ht2
  change |abelKernel a t| ≤
    abelKernelConst a * rpowDivLog a t at hkernel
  have hW' : rpowDivLog a t ≤
      2 * X ^ (a - 1) / Real.log X :=
    (le_abs_self _).trans hW
  rw [abelKernel, ← deriv_rpowDivLog ht2] at hkernel
  rw [abs_mul, abs_of_pos ht0] at hkernel
  have hbound : t * |deriv (rpowDivLog a) t| ≤
      abelKernelConst a *
        (2 * X ^ (a - 1) / Real.log X) :=
    hkernel.trans (mul_le_mul_of_nonneg_left hW' hC)
  calc
    |deriv (rpowDivLog a) t| ≤
        abelKernelConst a *
          (2 * X ^ (a - 1) / Real.log X) / t :=
      (le_div_iff₀ ht0).2 (by simpa [mul_comm] using hbound)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC hW0) hu0 ht.1

/-- Strong PNT transfer for every nondecreasing prime-power weight on a moving band. -/
theorem exists_primeRpowWeighted_terminalBand_exp_bound :
    ∃ c > 0, ∃ K > 0, ∀ᶠ X : ℝ in Filter.atTop,
      ∀ a u v : ℝ, 1 ≤ a → u ∈ Icc (X / Real.exp 1) X →
        v ∈ Icc (X / Real.exp 1) X → u ≤ v →
      |(primeRpowSumIoc a v -
          primeRpowSumIoc a u) -
        (HTGeometry.logRpowIntegral a v -
          HTGeometry.logRpowIntegral a u)| ≤
        (2 + Real.exp 1 * abelKernelConst a) *
          (2 * X ^ (a - 1) / Real.log X) *
            (K * X * Real.exp (-c * Real.sqrt (Real.log X))) := by
  obtain ⟨c, hc, K, hK, htheta⟩ := exists_chebyshevTheta_terminalBand_exp_bound
  refine ⟨c / 2, by positivity, K, hK, ?_⟩
  filter_upwards [htheta, Real.tendsto_log_atTop.eventually_ge_atTop 4,
    Filter.eventually_ge_atTop (2 * Real.exp 1)] with X hthetaX hL hXlarge
  intro a u v ha hu hv huv
  have hX0 : 0 < X := by nlinarith [Real.exp_pos (1 : ℝ)]
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase2 : 2 ≤ X / Real.exp 1 :=
    (le_div_iff₀ he0).mpr hXlarge
  have hu2 : 2 ≤ u := hbase2.trans hu.1
  let base : ℝ := X / Real.exp 1
  let W : ℝ := 2 * X ^ (a - 1) / Real.log X
  let D : ℝ := abelKernelConst a * W / base
  let E : ℝ := K * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))
  have hW0 : 0 ≤ W := by
    dsimp [W]
    positivity
  have hD0 : 0 ≤ D := by
    have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase2
    exact div_nonneg
      (mul_nonneg (abelKernelConst_nonneg _) hW0) hbase0.le
  have hE0 : 0 ≤ E := by
    dsimp [E]
    positivity
  have hfinite := abs_primeRpowSumIoc_diff_sub_logRpowIntegral_diff_le
    (a := a) (u := u) (v := v) (W := W) (D := D) (E := E)
    hu2 huv
    (fun t ht => by
      simpa [W] using rpowPrimeAbelWeight_terminalBand_le ha hL
        (show t ∈ Icc (X / Real.exp 1) X from ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩))
    (fun t ht => by
      simpa [D, W, base] using rpowPrimeAbelDeriv_terminalBand_le ha hL
        (show t ∈ Icc (X / Real.exp 1) X from ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩))
    (fun t ht => by
      simpa [E] using hthetaX t
        (show t ∈ Icc (X / Real.exp 1) X from ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩))
  have hlen : v - u ≤ X := by
    have hu0 : 0 ≤ u := le_trans (by norm_num) hu2
    linarith [hv.2]
  have hXD : X * D = Real.exp 1 * abelKernelConst a * W := by
    dsimp [D, base]
    field_simp
  have hbound :
      |(primeRpowSumIoc a v - primeRpowSumIoc a u) -
        (HTGeometry.logRpowIntegral a v -
          HTGeometry.logRpowIntegral a u)| ≤
        (2 + Real.exp 1 * abelKernelConst a) * W * E := by
    calc
      _ ≤ 2 * W * E + (v - u) * D * E := hfinite
      _ ≤ 2 * W * E + X * D * E := by
        gcongr
      _ = _ := by rw [hXD]; ring
  simpa [W, E] using hbound

end RHTower
