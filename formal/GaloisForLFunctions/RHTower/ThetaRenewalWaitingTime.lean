import GaloisForLFunctions.RHTower.ThetaRenewalSeamGerm

/-!
# The theta renewal waiting-time law

The weighted increment `v = e^{at} ν/c = 2π e^{3t/2} M₁(e^t)/c` differentiates to the literal
completed-theta source: `v'(2x) = -e^{x/2} k(x)/(2c) < 0`.  Hence `v` is strictly decreasing from
`v(0) = a`.

With `w̃(t) = e^{at} t Q(t)` the Volterra law becomes `w̃ = τv + v ⋆ w̃`, and the Leibniz rule gives
`w̃' = v + τv' + a w̃ + v' ⋆ w̃`.  The function `M(t) = 1 - e^{-at} - tQ(t) = 1 - s(t)` therefore has
`M'(t) = e^{-at} [a - v(t) - t v'(t) - (v' ⋆ w̃)(t)] > 0` for `t > 0`; it is even and real-analytic,
`M(0) = 0` and `M(t) → 1`.  The measure `μ(dt) = M'(t) dt` on `(0, ∞)` is a probability law with
survival function `μ((t, ∞)) = s(t) = e^{-at} + tQ(t)` and distribution function
`μ([0, t]) = M(t)`, so the rate `ρ = (1 - e^{-at})/t - Q` and the odd boundary kernel `W` are
`μ([0,t])/t` and `μ((t,∞))/t`.  Integration by parts against `s ≤ 2e^{-at}` gives finite
exponential moments `∫ e^{σt} μ(dt) < ∞` for every `σ < a`.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The physical source is the exit rate of the renewal density -/

/-- `k(x) = e^{x/2} (4π² y² M₂(y) - 6π y M₁(y))` with `y = e^{2x}`. -/
theorem thetaCuspFullSource_eq_thetaMoment (x : ℝ) :
    thetaCuspFullSource x = Real.exp (x / 2) *
      (4 * Real.pi ^ 2 * Real.exp (2 * x) ^ 2 * thetaMoment 2 (Real.exp (2 * x)) -
        6 * Real.pi * Real.exp (2 * x) * thetaMoment 1 (Real.exp (2 * x))) := by
  have hs := summable_thetaCuspSourceTerm x
  have hy := Real.exp_pos (2 * x)
  have h1 := summable_thetaMoment_terms 1 hy
  have h2 := summable_thetaMoment_terms 2 hy
  have hzero : thetaCuspSourceTerm x 0 = 0 := by simp [thetaCuspSourceTerm, thetaCuspSeed]
  rw [thetaCuspFullSource, hs.tsum_eq_zero_add, hzero, zero_add, thetaMoment, thetaMoment,
    ← tsum_mul_left, ← tsum_mul_left, ← (h2.mul_left _).tsum_sub (h1.mul_left _),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hE : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  simp only [thetaCuspSourceTerm, thetaCuspSeed, hE]
  push_cast
  rw [show -Real.pi * (((n : ℝ) + 1) * Real.exp x) ^ 2 =
    -(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp x ^ 2) by ring]
  ring

/-- `v(t) = 2π e^{3t/2} M₁(e^t)/c`. -/
theorem thetaRenewalDensity_eq_thetaMoment (t : ℝ) :
    thetaRenewalDensity t =
      2 * Real.pi * Real.exp (3 / 2 * t) * thetaMoment 1 (Real.exp t) / Θ 1 := by
  rw [thetaRenewalDensity, thetaRenewalIncrement, show Real.exp (3 / 2 * t) =
    Real.exp (t / 4) * Real.exp (5 / 4 * t) by rw [← Real.exp_add]; ring_nf]
  ring

theorem hasDerivAt_thetaRenewalDensity (t : ℝ) :
    HasDerivAt thetaRenewalDensity
      (2 * Real.pi * Real.exp (3 / 2 * t) * (3 / 2 * thetaMoment 1 (Real.exp t) -
        Real.pi * Real.exp t * thetaMoment 2 (Real.exp t)) / Θ 1) t := by
  have h1 : HasDerivAt (fun t => Real.exp (3 / 2 * t)) (Real.exp (3 / 2 * t) * (3 / 2)) t := by
    simpa using ((hasDerivAt_id t).const_mul (3 / 2 : ℝ)).exp
  have h2 : HasDerivAt (fun t => thetaMoment 1 (Real.exp t))
      (-(Real.pi * thetaMoment 2 (Real.exp t)) * Real.exp t) t :=
    (hasDerivAt_thetaMoment 1 (Real.exp_pos t)).comp t (Real.hasDerivAt_exp t)
  have h := ((h1.const_mul (2 * Real.pi)).fun_mul h2).div_const (Θ 1)
  rw [show thetaRenewalDensity = fun t =>
    2 * Real.pi * Real.exp (3 / 2 * t) * thetaMoment 1 (Real.exp t) / Θ 1 from
      funext thetaRenewalDensity_eq_thetaMoment]
  exact h.congr_deriv (by ring)

/-- **The source identity (18).** `v'(2x) = -e^{x/2} k(x)/(2c)`. -/
theorem hasDerivAt_thetaRenewalDensity_two_mul (x : ℝ) :
    HasDerivAt thetaRenewalDensity
      (-(Real.exp (x / 2) * thetaCuspFullSource x / (2 * Θ 1))) (2 * x) := by
  have hc := thetaSeam_pos
  refine (hasDerivAt_thetaRenewalDensity (2 * x)).congr_deriv ?_
  rw [thetaCuspFullSource_eq_thetaMoment]
  have hu2 : Real.exp (2 * x) = Real.exp (x / 2) ^ 4 := by rw [← Real.exp_nat_mul]; ring_nf
  have hu3 : Real.exp (3 / 2 * (2 * x)) = Real.exp (x / 2) ^ 6 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hu2, hu3]
  field_simp
  ring

/-- The renewal density is strictly decreasing: `v' < 0` everywhere. -/
theorem deriv_thetaRenewalDensity_neg (t : ℝ) : deriv thetaRenewalDensity t < 0 := by
  have h := hasDerivAt_thetaRenewalDensity_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  rw [h.deriv, neg_lt_zero]
  exact div_pos (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos _))
    (mul_pos two_pos thetaSeam_pos)

theorem contDiff_thetaRenewalDensity : ContDiff ℝ ∞ thetaRenewalDensity := by
  have h : thetaRenewalDensity = fun t => Real.exp (t / 4) * thetaRenewalIncrement t / Θ 1 := rfl
  rw [h]
  exact ((Real.contDiff_exp.comp (contDiff_id.div_const 4)).mul
    contDiff_thetaRenewalIncrement).div_const _

theorem hasDerivAt_thetaRenewalDensity_deriv (t : ℝ) :
    HasDerivAt thetaRenewalDensity (deriv thetaRenewalDensity t) t :=
  (contDiff_thetaRenewalDensity.differentiable (by simp) t).hasDerivAt

theorem continuous_deriv_thetaRenewalDensity : Continuous (deriv thetaRenewalDensity) :=
  contDiff_thetaRenewalDensity.continuous_deriv (by simp)

theorem strictAnti_thetaRenewalDensity : StrictAnti thetaRenewalDensity :=
  strictAnti_of_hasDerivAt_neg hasDerivAt_thetaRenewalDensity_deriv deriv_thetaRenewalDensity_neg

/-- `v(t) < a` for `t > 0`. -/
theorem thetaRenewalDensity_lt_quarter {t : ℝ} (ht : 0 < t) : thetaRenewalDensity t < 1 / 4 := by
  rw [← thetaRenewalDensity_zero]; exact strictAnti_thetaRenewalDensity ht

/-! ## The weighted Volterra law and the waiting-time density -/

/-- The weighted moment kernel `w̃(t) = e^{at} t Q(t)`. -/
def thetaRenewalWeightedMoment (t : ℝ) : ℝ := Real.exp (t / 4) * thetaRenewalMomentKernel t

theorem continuous_thetaRenewalWeightedMoment : Continuous thetaRenewalWeightedMoment := by
  have := continuous_thetaRenewalMomentKernel
  unfold thetaRenewalWeightedMoment; fun_prop

theorem thetaRenewalWeightedMoment_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ thetaRenewalWeightedMoment t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [thetaRenewalWeightedMoment, thetaRenewalMomentKernel]
  · exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg ht.le (thetaRenewalLogKernel_pos ht).le)

/-- **Weighted Volterra law.** `w̃ = τ v + v ⋆ w̃`. -/
theorem thetaRenewalWeightedMoment_law (t : ℝ) :
    thetaRenewalWeightedMoment t =
      t * thetaRenewalDensity t + volterraConv thetaRenewalDensity thetaRenewalWeightedMoment t := by
  have hc := thetaSeam_pos
  have hlaw := thetaRenewal_volterra_law t
  have hconv := exp_mul_volterraConv (1 / 4) thetaRenewalIncrement
    (fun s => s * thetaRenewalLogKernel s) t
  have hv : thetaRenewalDensity = fun s => (1 / Θ 1) * (Real.exp (1 / 4 * s) * thetaRenewalIncrement s) := by
    funext s; rw [thetaRenewalDensity]; ring_nf
  have hw : thetaRenewalWeightedMoment = fun s => Real.exp (1 / 4 * s) * (s * thetaRenewalLogKernel s) := by
    funext s; rw [thetaRenewalWeightedMoment, thetaRenewalMomentKernel]; ring_nf
  rw [hv, hw, volterraConv_smul_left, ← hconv]
  simp only
  field_simp
  linear_combination hlaw

/-- `w̃' = v + τ v' + a w̃ + v' ⋆ w̃`. -/
theorem hasDerivAt_thetaRenewalWeightedMoment (t : ℝ) :
    HasDerivAt thetaRenewalWeightedMoment
      (thetaRenewalDensity t + t * deriv thetaRenewalDensity t +
        thetaRenewalWeightedMoment t / 4 +
          volterraConv (deriv thetaRenewalDensity) thetaRenewalWeightedMoment t) t := by
  have hfun : thetaRenewalWeightedMoment = fun t =>
      t * thetaRenewalDensity t + volterraConv thetaRenewalDensity thetaRenewalWeightedMoment t :=
    funext thetaRenewalWeightedMoment_law
  have h1 := (hasDerivAt_id' t).fun_mul (hasDerivAt_thetaRenewalDensity_deriv t)
  have h2 := hasDerivAt_volterraConv hasDerivAt_thetaRenewalDensity_deriv
    continuous_deriv_thetaRenewalDensity continuous_thetaRenewalWeightedMoment t
  rw [thetaRenewalDensity_zero] at h2
  have h := h1.fun_add h2
  rw [← hfun] at h
  refine h.congr_deriv ?_
  ring

/-- The universal pole kernel `B(t) = (1 - e^{-at})/t`. -/
def thetaWaitingPole (t : ℝ) : ℝ := (1 - Real.exp (-(t / 4))) / t

/-- The waiting-time rate `ρ = B - Q`. -/
def thetaWaitingRate (t : ℝ) : ℝ := thetaWaitingPole t - thetaRenewalLogKernel t

/-- The waiting-time distribution function `M(t) = 1 - e^{-at} - t Q(t) = 1 - s(t)`. -/
def thetaWaitingCDF (t : ℝ) : ℝ := 1 - thetaRenewalReflectionProfile t

theorem thetaWaitingCDF_eq (t : ℝ) :
    thetaWaitingCDF t = 1 - Real.exp (-(t / 4)) - t * thetaRenewalLogKernel t := by
  simp only [thetaWaitingCDF, thetaRenewalReflectionProfile, thetaRenewalMomentKernel]; ring

theorem thetaWaitingCDF_eq_mul_rate {t : ℝ} (ht : t ≠ 0) :
    thetaWaitingCDF t = t * thetaWaitingRate t := by
  rw [thetaWaitingCDF_eq, thetaWaitingRate, thetaWaitingPole]
  field_simp

theorem thetaWaitingCDF_zero : thetaWaitingCDF 0 = 0 := by simp [thetaWaitingCDF_eq]

/-- `M` is even. -/
theorem thetaWaitingCDF_neg (t : ℝ) : thetaWaitingCDF (-t) = thetaWaitingCDF t := by
  simp only [thetaWaitingCDF, thetaRenewalReflectionProfile_neg]

/-- `ρ` is odd. -/
theorem thetaWaitingRate_neg {t : ℝ} (ht : t ≠ 0) : thetaWaitingRate (-t) = -thetaWaitingRate t := by
  have h1 := thetaWaitingCDF_eq_mul_rate ht
  have h2 := thetaWaitingCDF_eq_mul_rate (neg_ne_zero.mpr ht)
  rw [thetaWaitingCDF_neg, h1] at h2
  have := mul_left_cancel₀ ht (by linarith : t * thetaWaitingRate t = t * -thetaWaitingRate (-t))
  linarith

theorem analyticAt_thetaWaitingCDF (t : ℝ) : AnalyticAt ℝ thetaWaitingCDF t := by
  have hQ := analyticAt_thetaRenewalLogKernel t
  have he : AnalyticAt ℝ (fun t : ℝ => Real.exp (-(t / 4))) t := by fun_prop
  have h : thetaWaitingCDF = fun t => 1 - Real.exp (-(t / 4)) - t * thetaRenewalLogKernel t :=
    funext thetaWaitingCDF_eq
  rw [h]
  exact (analyticAt_const.sub he).sub (analyticAt_id.mul hQ)

theorem contDiff_thetaWaitingCDF : ContDiff ℝ ∞ thetaWaitingCDF :=
  AnalyticOnNhd.contDiff fun t _ => analyticAt_thetaWaitingCDF t

/-- `M'` is odd. -/
theorem deriv_thetaWaitingCDF_neg (t : ℝ) :
    deriv thetaWaitingCDF (-t) = -deriv thetaWaitingCDF t := by
  have h := deriv_comp_neg thetaWaitingCDF t
  rw [show (fun x => thetaWaitingCDF (-x)) = thetaWaitingCDF from funext thetaWaitingCDF_neg] at h
  linarith

/-- **The waiting-time density (12).** `M'(t) = e^{-at} [a - v(t) - t v'(t) - (v' ⋆ w̃)(t)]`. -/
theorem hasDerivAt_thetaWaitingCDF (t : ℝ) :
    HasDerivAt thetaWaitingCDF (Real.exp (-(t / 4)) * (1 / 4 - thetaRenewalDensity t -
      t * deriv thetaRenewalDensity t -
        volterraConv (deriv thetaRenewalDensity) thetaRenewalWeightedMoment t)) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(t / 4))) (Real.exp (-(t / 4)) * (-(1 / 4))) t := by
    simpa using (((hasDerivAt_id t).div_const 4).neg).exp
  have hfun : thetaWaitingCDF = fun t =>
      1 - Real.exp (-(t / 4)) - Real.exp (-(t / 4)) * thetaRenewalWeightedMoment t := by
    funext t
    rw [thetaWaitingCDF_eq, thetaRenewalWeightedMoment, thetaRenewalMomentKernel, ← mul_assoc,
      ← Real.exp_add]
    simp
  rw [hfun]
  refine (((hasDerivAt_const t (1 : ℝ)).fun_sub he).fun_sub
    (he.fun_mul (hasDerivAt_thetaRenewalWeightedMoment t))).congr_deriv ?_
  ring

/-- `M' > 0` on `(0, ∞)`. -/
theorem deriv_thetaWaitingCDF_pos {t : ℝ} (ht : 0 < t) : 0 < deriv thetaWaitingCDF t := by
  rw [(hasDerivAt_thetaWaitingCDF t).deriv]
  refine mul_pos (Real.exp_pos _) ?_
  have h1 := thetaRenewalDensity_lt_quarter ht
  have h2 : 0 < -(t * deriv thetaRenewalDensity t) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg ht (deriv_thetaRenewalDensity_neg t))
  have h3 : volterraConv (deriv thetaRenewalDensity) thetaRenewalWeightedMoment t ≤ 0 := by
    rw [volterraConv, ← neg_nonneg, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_nonneg ht.le fun s hs => ?_
    rw [neg_nonneg]
    exact mul_nonpos_of_nonpos_of_nonneg (deriv_thetaRenewalDensity_neg _).le
      (thetaRenewalWeightedMoment_nonneg hs.1)
  linarith

/-- `M` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_thetaWaitingCDF : StrictMonoOn thetaWaitingCDF (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) contDiff_thetaWaitingCDF.continuous.continuousOn
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact deriv_thetaWaitingCDF_pos hx

theorem tendsto_mul_thetaRenewalLogKernel_atTop :
    Tendsto (fun t => t * thetaRenewalLogKernel t) atTop (𝓝 0) := by
  have hβ : 0 < Real.pi - 3 / 2 := by linarith [Real.pi_gt_three]
  have hlim : Tendsto (fun t : ℝ => Real.exp (-((Real.pi - 3 / 2) * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hβ))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact mul_nonneg ht.le (thetaRenewalLogKernel_pos ht).le
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hQ := thetaRenewalLogKernel_le ht
    have he : 0 ≤ Real.exp (-(t / 4)) := (Real.exp_pos _).le
    calc t * thetaRenewalLogKernel t
        ≤ t * (Real.exp (-((Real.pi - 3 / 2) * t)) * (1 - Real.exp (-(t / 4))) / t) :=
          mul_le_mul_of_nonneg_left hQ ht.le
      _ = Real.exp (-((Real.pi - 3 / 2) * t)) * (1 - Real.exp (-(t / 4))) := by field_simp
      _ ≤ Real.exp (-((Real.pi - 3 / 2) * t)) := by
          nlinarith [Real.exp_pos (-((Real.pi - 3 / 2) * t))]

/-- `M(t) → 1`. -/
theorem tendsto_thetaWaitingCDF_atTop : Tendsto thetaWaitingCDF atTop (𝓝 1) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-(t / 4))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const four_pos))
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).sub tendsto_mul_thetaRenewalLogKernel_atTop
  simp only [sub_zero] at h
  exact h.congr fun t => (thetaWaitingCDF_eq t).symm

/-- **Rate bound (10).** `ρ(t) ≥ (1 - e^{-βt}) B(t) > 0` for `t > 0`. -/
theorem thetaWaitingRate_ge {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-((Real.pi - 3 / 2) * t))) * thetaWaitingPole t ≤ thetaWaitingRate t := by
  have hQ := thetaRenewalLogKernel_le ht
  rw [thetaWaitingRate, thetaWaitingPole]
  rw [mul_div_assoc] at hQ
  nlinarith

theorem thetaWaitingPole_pos {t : ℝ} (ht : 0 < t) : 0 < thetaWaitingPole t :=
  div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) ht

theorem thetaWaitingRate_pos {t : ℝ} (ht : 0 < t) : 0 < thetaWaitingRate t := by
  have hβ : 0 < Real.pi - 3 / 2 := by linarith [Real.pi_gt_three]
  refine lt_of_lt_of_le (mul_pos ?_ (thetaWaitingPole_pos ht)) (thetaWaitingRate_ge ht)
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))

/-- **Survival tail bound.** `s(t) ≤ e^{-at} + e^{-βt}(1 - e^{-at})`. -/
theorem thetaRenewalReflectionProfile_le {t : ℝ} (ht : 0 < t) :
    thetaRenewalReflectionProfile t ≤
      Real.exp (-(t / 4)) + Real.exp (-((Real.pi - 3 / 2) * t)) * (1 - Real.exp (-(t / 4))) := by
  have hQ := thetaRenewalLogKernel_le ht
  simp only [thetaRenewalReflectionProfile, thetaRenewalMomentKernel]
  have : t * thetaRenewalLogKernel t ≤
      Real.exp (-((Real.pi - 3 / 2) * t)) * (1 - Real.exp (-(t / 4))) := by
    calc t * thetaRenewalLogKernel t
        ≤ t * (Real.exp (-((Real.pi - 3 / 2) * t)) * (1 - Real.exp (-(t / 4))) / t) :=
          mul_le_mul_of_nonneg_left hQ ht.le
      _ = _ := by field_simp
  linarith

theorem thetaRenewalReflectionProfile_zero : thetaRenewalReflectionProfile 0 = 1 := by
  simp [thetaRenewalReflectionProfile, thetaRenewalMomentKernel]

theorem thetaRenewalReflectionProfile_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < thetaRenewalReflectionProfile t := by
  simp only [thetaRenewalReflectionProfile, thetaRenewalMomentKernel]
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · exact add_pos (Real.exp_pos _) (mul_pos ht (thetaRenewalLogKernel_pos ht))

/-- `s(t) ≤ 2 e^{-at}` on `t ≥ 0`. -/
theorem thetaRenewalReflectionProfile_le_two_mul {t : ℝ} (ht : 0 ≤ t) :
    thetaRenewalReflectionProfile t ≤ 2 * Real.exp (-(t / 4)) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [thetaRenewalReflectionProfile_zero]; simp
  · have h := thetaRenewalReflectionProfile_le ht
    have h1 : Real.exp (-((Real.pi - 3 / 2) * t)) ≤ Real.exp (-(t / 4)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    have h2 : 0 ≤ 1 - Real.exp (-(t / 4)) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    have h3 : 1 - Real.exp (-(t / 4)) ≤ 1 := by linarith [Real.exp_pos (-(t / 4))]
    nlinarith [Real.exp_pos (-((Real.pi - 3 / 2) * t))]

theorem deriv_thetaWaitingCDF_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ deriv thetaWaitingCDF t := by
  rcases ht.eq_or_lt with rfl | ht
  · have := deriv_thetaWaitingCDF_neg 0
    rw [neg_zero] at this
    linarith
  · exact (deriv_thetaWaitingCDF_pos ht).le

theorem hasDerivAt_thetaWaitingCDF_deriv (t : ℝ) :
    HasDerivAt thetaWaitingCDF (deriv thetaWaitingCDF t) t :=
  (contDiff_thetaWaitingCDF.differentiable (by simp) t).hasDerivAt

theorem continuous_deriv_thetaWaitingCDF : Continuous (deriv thetaWaitingCDF) :=
  contDiff_thetaWaitingCDF.continuous_deriv (by simp)

/-! ## The waiting-time law as a probability measure -/

/-- The source-defined waiting-time law `μ(dt) = M'(t) dt` on `(0, ∞)`. -/
def thetaWaitingTimeLaw : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (deriv thetaWaitingCDF t)

theorem integrableOn_deriv_thetaWaitingCDF {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (deriv thetaWaitingCDF) (Ioi t) :=
  integrableOn_Ioi_deriv_of_nonneg contDiff_thetaWaitingCDF.continuous.continuousWithinAt
    (fun x _ => hasDerivAt_thetaWaitingCDF_deriv x)
    (fun _ hx => deriv_thetaWaitingCDF_nonneg (ht.trans (le_of_lt hx)))
    tendsto_thetaWaitingCDF_atTop

theorem integral_Ioi_deriv_thetaWaitingCDF {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in Ioi t, deriv thetaWaitingCDF x = thetaRenewalReflectionProfile t := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg contDiff_thetaWaitingCDF.continuous.continuousWithinAt
    (fun x _ => hasDerivAt_thetaWaitingCDF_deriv x)
    (fun _ hx => deriv_thetaWaitingCDF_nonneg (ht.trans (le_of_lt hx)))
    tendsto_thetaWaitingCDF_atTop]
  simp [thetaWaitingCDF]

/-- **Survival function.** `μ((t, ∞)) = s(t)` for `t ≥ 0`. -/
theorem thetaWaitingTimeLaw_Ioi {t : ℝ} (ht : 0 ≤ t) :
    thetaWaitingTimeLaw (Ioi t) = ENNReal.ofReal (thetaRenewalReflectionProfile t) := by
  rw [thetaWaitingTimeLaw, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left ht,
    ← integral_Ioi_deriv_thetaWaitingCDF ht, ofReal_integral_eq_lintegral_ofReal
      (integrableOn_deriv_thetaWaitingCDF ht)]
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
    deriv_thetaWaitingCDF_nonneg (ht.trans (le_of_lt hx)))

instance isProbabilityMeasure_thetaWaitingTimeLaw : IsProbabilityMeasure thetaWaitingTimeLaw := by
  constructor
  have h := thetaWaitingTimeLaw_Ioi le_rfl
  rw [thetaRenewalReflectionProfile_zero, ENNReal.ofReal_one] at h
  rw [← h, thetaWaitingTimeLaw, withDensity_apply _ MeasurableSet.univ,
    withDensity_apply _ measurableSet_Ioi, Measure.restrict_univ,
    Measure.restrict_restrict measurableSet_Ioi, inter_self]

/-- **Distribution function.** `μ([0, t]) = M(t)` for `t ≥ 0`. -/
theorem thetaWaitingTimeLaw_Icc {t : ℝ} (ht : 0 ≤ t) :
    thetaWaitingTimeLaw (Icc 0 t) = ENNReal.ofReal (thetaWaitingCDF t) := by
  have hset : Icc 0 t ∩ Ioi 0 = Ioc 0 t := by
    ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
  have hint : ∫ x in Ioc 0 t, deriv thetaWaitingCDF x = thetaWaitingCDF t := by
    rw [← intervalIntegral.integral_of_le ht, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_thetaWaitingCDF_deriv x)
      (continuous_deriv_thetaWaitingCDF.intervalIntegrable _ _), thetaWaitingCDF_zero, sub_zero]
  rw [thetaWaitingTimeLaw, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, hset, ← hint, ofReal_integral_eq_lintegral_ofReal
      (continuous_deriv_thetaWaitingCDF.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx =>
    deriv_thetaWaitingCDF_nonneg hx.1.le)

/-- **The odd kernels as waiting-time ratios (11).** `ρ(t) = μ([0,t])/t` and
`W(t) = μ((t,∞))/t` for `t > 0`. -/
theorem thetaWaitingRate_eq_measure {t : ℝ} (ht : 0 < t) :
    thetaWaitingRate t = (thetaWaitingTimeLaw (Icc 0 t)).toReal / t := by
  have hM : 0 ≤ thetaWaitingCDF t := by
    rw [thetaWaitingCDF_eq_mul_rate ht.ne']; exact mul_nonneg ht.le (thetaWaitingRate_pos ht).le
  rw [thetaWaitingTimeLaw_Icc ht.le, ENNReal.toReal_ofReal hM, thetaWaitingCDF_eq_mul_rate ht.ne']
  field_simp

theorem thetaRenewalOddKernel_eq_measure {t : ℝ} (ht : 0 < t) :
    thetaRenewalOddKernel t = (thetaWaitingTimeLaw (Ioi t)).toReal / t := by
  rw [thetaWaitingTimeLaw_Ioi ht.le, ENNReal.toReal_ofReal (thetaRenewalReflectionProfile_pos ht.le).le,
    thetaRenewalOddKernel, thetaRenewalReflectionProfile, thetaRenewalMomentKernel]
  field_simp

/-- **Exponential moments.** `∫₀^∞ e^{σt} M'(t) dt < ∞` for every `σ < a`. -/
theorem integrableOn_exp_mul_deriv_thetaWaitingCDF {σ : ℝ} (hσ : σ < 1 / 4) :
    IntegrableOn (fun t => Real.exp (σ * t) * deriv thetaWaitingCDF t) (Ioi 0) := by
  set c := σ - 1 / 4 with hcdef
  have hc : c < 0 := by linarith
  have hM' := continuous_deriv_thetaWaitingCDF
  have hcont : Continuous fun t => Real.exp (σ * t) * deriv thetaWaitingCDF t := by fun_prop
  have hy := continuous_thetaRenewalReflectionProfile
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (1 + |σ| * (2 / -c)) 0
    (fun T => hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) tendsto_id ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  have hnorm : ∫ t in (0 : ℝ)..id T, ‖Real.exp (σ * t) * deriv thetaWaitingCDF t‖ =
      ∫ t in (0 : ℝ)..T, Real.exp (σ * t) * deriv thetaWaitingCDF t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht : t ∈ Icc 0 T := by simpa [uIcc_of_le hT] using ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (deriv_thetaWaitingCDF_nonneg ht.1))]
  rw [hnorm]
  have hv : ∀ x, HasDerivAt (fun t => -thetaRenewalReflectionProfile t)
      (deriv thetaWaitingCDF x) x := by
    intro x
    have h := (hasDerivAt_thetaWaitingCDF_deriv x).sub_const 1
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [thetaWaitingCDF]
  have hu : ∀ x, HasDerivAt (fun t => Real.exp (σ * t)) (σ * Real.exp (σ * x)) x := by
    intro x
    have := ((hasDerivAt_id x).const_mul σ).exp
    simpa [mul_comm] using this
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
    (fun x _ => hu x) (fun x _ => hv x) ((by fun_prop : Continuous fun t =>
      σ * Real.exp (σ * t)).intervalIntegrable _ _) (hM'.intervalIntegrable _ _)
  rw [hparts]
  simp only [mul_zero, Real.exp_zero, thetaRenewalReflectionProfile_zero, one_mul]
  have hI : ∫ x in (0 : ℝ)..T, σ * Real.exp (σ * x) * -thetaRenewalReflectionProfile x =
      -(σ * ∫ x in (0 : ℝ)..T, Real.exp (σ * x) * thetaRenewalReflectionProfile x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hI]
  have hJ0 : 0 ≤ ∫ x in (0 : ℝ)..T, Real.exp (σ * x) * thetaRenewalReflectionProfile x :=
    intervalIntegral.integral_nonneg hT fun x hx =>
      mul_nonneg (Real.exp_pos _).le (thetaRenewalReflectionProfile_pos hx.1).le
  have hJ : ∫ x in (0 : ℝ)..T, Real.exp (σ * x) * thetaRenewalReflectionProfile x ≤ 2 / -c := by
    have hle := intervalIntegral.integral_mono_on (μ := volume) hT
      ((by fun_prop : Continuous fun x => Real.exp (σ * x) *
        thetaRenewalReflectionProfile x).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x => 2 * Real.exp (c * x)).intervalIntegrable 0 T)
      (fun x hx => by
        have h1 := thetaRenewalReflectionProfile_le_two_mul hx.1
        calc Real.exp (σ * x) * thetaRenewalReflectionProfile x
            ≤ Real.exp (σ * x) * (2 * Real.exp (-(x / 4))) :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = 2 * Real.exp (c * x) := by
              rw [hcdef, show (σ - 1 / 4) * x = σ * x + -(x / 4) by ring, Real.exp_add]; ring)
    have hF : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun x => 2 * Real.exp (c * x) / c)
        (2 * Real.exp (c * x)) x := by
      intro x _
      have := (((hasDerivAt_id x).const_mul c).exp.const_mul 2).div_const c
      refine this.congr_deriv ?_
      have hc0 : c ≠ 0 := hc.ne
      simp only [id]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous fun x => 2 * Real.exp (c * x)).intervalIntegrable _ _)] at hle
    have hexp : 0 < Real.exp (c * T) := Real.exp_pos _
    have hexp1 : Real.exp (c * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have key : 2 * Real.exp (c * T) / c - 2 * Real.exp (c * 0) / c =
        (2 - 2 * Real.exp (c * T)) / (-c) := by
      rw [mul_zero, Real.exp_zero]; field_simp; ring
    rw [key] at hle
    refine hle.trans ?_
    gcongr
    · linarith
    · linarith
  have hsT : 0 ≤ Real.exp (σ * T) * thetaRenewalReflectionProfile T :=
    mul_nonneg (Real.exp_pos _).le (thetaRenewalReflectionProfile_pos hT).le
  have hσJ : σ * ∫ x in (0 : ℝ)..T, Real.exp (σ * x) * thetaRenewalReflectionProfile x ≤
      |σ| * (2 / -c) :=
    (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hJ0]; exact
      mul_le_mul_of_nonneg_left hJ (abs_nonneg _))
  linarith

theorem lintegral_exp_mul_thetaWaitingTimeLaw_lt_top {σ : ℝ} (hσ : σ < 1 / 4) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (σ * t)) ∂thetaWaitingTimeLaw < ⊤ := by
  rw [thetaWaitingTimeLaw, lintegral_withDensity_eq_lintegral_mul _
    continuous_deriv_thetaWaitingCDF.measurable.ennreal_ofReal
    (by fun_prop : Continuous fun t : ℝ => Real.exp (σ * t)).measurable.ennreal_ofReal]
  have heq : ∫⁻ t in Ioi 0, ((fun t => ENNReal.ofReal (deriv thetaWaitingCDF t)) *
      fun t => ENNReal.ofReal (Real.exp (σ * t))) t =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (σ * t) * deriv thetaWaitingCDF t) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (deriv_thetaWaitingCDF_nonneg (le_of_lt ht)), mul_comm]
  rw [heq]
  exact (integrableOn_exp_mul_deriv_thetaWaitingCDF hσ).lintegral_lt_top

end RHTower
