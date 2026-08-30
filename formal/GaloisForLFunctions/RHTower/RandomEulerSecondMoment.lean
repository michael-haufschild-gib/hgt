import GaloisForLFunctions.RHTower.RandomEulerObservableFactor
import GaloisForLFunctions.RHTower.RandomEulerObservableAbscissa
import GaloisForLFunctions.HTGeometry.GutzmerIdentity
import GaloisForLFunctions.HTGeometry.SzegoRadialMean
import GaloisForLFunctions.HTGeometry.HardyTaylorCoefficient

/-!
# The exact second moment of one random Euler factor

The logarithmic Euler factor `-log (1 - r e^{2πix})` has Taylor coefficients `1/k`, so Gutzmer's
identity computes its circle mean square exactly as `∑_{k ≥ 1} r^{2k}/k²`.  This is the local factor
of the total second moment `V(σ)` of the random Euler observable.
-/

namespace GaloisForLFunctions.RHTower

open Complex GaloisForLFunctions.HTGeometry

noncomputable section

theorem hasSum_negLogOneSub {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (1 / (n : ℂ)) * z ^ n) (negLogOneSub z) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have hfun : (fun n : ℕ => (1 / (n : ℂ)) * z ^ n) = fun n : ℕ => z ^ n / (n : ℂ) := by
    funext n
    field_simp
  rw [hfun, negLogOneSub]
  exact h

/-- The Taylor series of the logarithmic Euler factor on the unit disc. -/
theorem hasFPowerSeriesOnBall_negLogOneSub :
    HasFPowerSeriesOnBall negLogOneSub
      (FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => 1 / (n : ℂ))) 0 1 := by
  refine ⟨?_, by norm_num, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ 1 (fun n => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm]
    have hb : ‖(1 : ℂ) / (n : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      by_cases h : n = 0
      · subst h
        norm_num
      · rw [Complex.norm_natCast, div_le_one_iff]
        left
        constructor
        · exact_mod_cast Nat.pos_of_ne_zero h
        · exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    simpa using hb
  · intro y hy
    have hy1 : ‖y‖ < 1 := by
      have h2 : ‖y‖ₑ < 1 := by simpa using hy
      rw [← ofReal_norm, show (1 : ENNReal) = ENNReal.ofReal 1 from by simp] at h2
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp h2
    have h := hasSum_negLogOneSub hy1
    rw [zero_add]
    refine h.congr_fun ?_
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

theorem cauchyPowerSeries_negLogOneSub_coeff (k : ℕ) :
    (cauchyPowerSeries negLogOneSub 0 (1 / 2 : NNReal)).coeff k = 1 / (k : ℂ) := by
  have hfac := hasFPowerSeriesOnBall_negLogOneSub.factorial_smul (1 : ℂ) k
  have hp : HasFPowerSeriesOnBall negLogOneSub
      (cauchyPowerSeries negLogOneSub 0 (1 / 2 : NNReal)) 0 (1 / 2 : NNReal) := by
    refine hasFPowerSeriesOnBall_of_analyticOnNhd_ball ?_ (by norm_num) (by norm_num)
    intro z hz
    refine (hasFPowerSeriesOnBall_negLogOneSub.analyticOnNhd) z ?_
    have hz' : ‖z‖ < 1 := by simpa using hz
    have h2 : ‖z‖ₑ < 1 := by
      rw [← ofReal_norm, show (1 : ENNReal) = ENNReal.ofReal 1 from by simp]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hz'
    simpa using h2
  have hfac2 := hp.factorial_smul (1 : ℂ) k
  rw [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] at hfac
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at hfac hfac2
  have : (k.factorial : ℂ) * (cauchyPowerSeries negLogOneSub 0 (1 / 2 : NNReal)).coeff k
      = (k.factorial : ℂ) * (1 / (k : ℂ)) := by
    have h1 : (k.factorial : ℂ) • (cauchyPowerSeries negLogOneSub 0 (1 / 2 : NNReal)).coeff k
        = iteratedDeriv k negLogOneSub 0 := by
      simpa using hfac2
    have h2 : (k.factorial : ℂ) • ((1 : ℂ) / (k : ℂ)) = iteratedDeriv k negLogOneSub 0 := by
      simpa using hfac
    rw [← smul_eq_mul, ← smul_eq_mul, h1, h2]
  have hfacne : ((k.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr k.factorial_ne_zero
  exact mul_left_cancel₀ hfacne this

theorem analyticOnNhd_negLogOneSub : AnalyticOnNhd ℂ negLogOneSub (Metric.ball 0 1) := by
  intro z hz
  refine hasFPowerSeriesOnBall_negLogOneSub.analyticOnNhd z ?_
  have hz' : ‖z‖ < 1 := by simpa using hz
  have h2 : ‖z‖ₑ < 1 := by
    rw [← ofReal_norm, show (1 : ENNReal) = ENNReal.ofReal 1 from by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hz'
  simpa using h2

/-- **The exact circle mean square of the logarithmic Euler factor.** -/
theorem hasSum_circleMeanSq_negLogOneSub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (1 / (k : ℝ)) ^ 2 * r ^ (2 * k))
      (circleMeanSq negLogOneSub r) := by
  have h := hasSum_circleMeanSq analyticOnNhd_negLogOneSub (R₀ := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) hr0 hr1
  refine h.congr_fun ?_
  intro k
  rw [cauchyPowerSeries_negLogOneSub_coeff]
  congr 1
  rw [norm_div, norm_one, Complex.norm_natCast]

theorem randomEulerLogFactor_eq_circleMap (r x : ℝ) :
    randomEulerLogFactor r x = negLogOneSub (circleMap 0 r (2 * Real.pi * x)) := by
  rw [randomEulerLogFactor, negLogOneSub, circleMap, zero_add]

/-- **The second moment of one Euler factor as a circle mean.** -/
theorem intervalIntegral_normSq_randomEulerLogFactor (r : ℝ) :
    ∫ x in (0 : ℝ)..1, ‖randomEulerLogFactor r x‖ ^ 2 = circleMeanSq negLogOneSub r := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hcv := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun θ => ‖negLogOneSub (circleMap 0 r θ)‖ ^ 2) hpi
  rw [mul_zero, mul_one] at hcv
  calc ∫ x in (0 : ℝ)..1, ‖randomEulerLogFactor r x‖ ^ 2
      = ∫ x in (0 : ℝ)..1, ‖negLogOneSub (circleMap 0 r (2 * Real.pi * x))‖ ^ 2 := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [randomEulerLogFactor_eq_circleMap]
    _ = (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖negLogOneSub (circleMap 0 r θ)‖ ^ 2 := hcv
    _ = circleMeanSq negLogOneSub r := by
        rw [circleMeanSq, smul_eq_mul]

/-- **The exact second moment of one Euler factor.** -/
theorem hasSum_intervalIntegral_normSq_randomEulerLogFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (1 / (k : ℝ)) ^ 2 * r ^ (2 * k))
      (∫ x in (0 : ℝ)..1, ‖randomEulerLogFactor r x‖ ^ 2) := by
  rw [intervalIntegral_normSq_randomEulerLogFactor]
  exact hasSum_circleMeanSq_negLogOneSub hr0 hr1

/-! ### The real part carries half the second moment -/

theorem integral_sq_randomEulerLogFactor {r : ℝ} (hr : |r| < 1) :
    ∫ x in (0 : ℝ)..1, (randomEulerLogFactor r x) ^ 2 = 0 := by
  have hdiff : ∀ z : ℂ, ‖z‖ ≤ |r| → DifferentiableAt ℂ (fun w => (negLogOneSub w) ^ 2) z := by
    intro z hz
    exact ((differentiableAt_negLogOneSub (lt_of_le_of_lt hz hr)).pow 2)
  have hcont : ContinuousOn (fun w => (negLogOneSub w) ^ 2) (Metric.closedBall (0 : ℂ) |r|) := by
    intro z hz
    refine ((hdiff z ?_).continuousAt).continuousWithinAt
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hball : ∀ z ∈ Metric.ball (0 : ℂ) |r| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w => (negLogOneSub w) ^ 2) z := by
    intro z hz
    refine hdiff z (le_of_lt ?_)
    simpa [Metric.mem_ball, dist_eq_norm] using hz.1
  have hmv : Real.circleAverage (fun w => (negLogOneSub w) ^ 2) 0 r
      = (negLogOneSub 0) ^ 2 :=
    circleAverage_of_differentiable_on_off_countable Set.countable_empty hcont hball
  have hzero : (negLogOneSub 0) ^ 2 = 0 := by simp [negLogOneSub]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hchange := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun θ => (negLogOneSub (circleMap 0 r θ)) ^ 2) hpi
  calc ∫ x in (0 : ℝ)..1, (randomEulerLogFactor r x) ^ 2
      = ∫ x in (0 : ℝ)..1, (negLogOneSub (circleMap 0 r (2 * Real.pi * x))) ^ 2 := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [randomEulerLogFactor_eq_circleMap]
    _ = (2 * Real.pi)⁻¹ • ∫ θ in (2 * Real.pi * 0)..(2 * Real.pi * 1),
          (negLogOneSub (circleMap 0 r θ)) ^ 2 := hchange
    _ = Real.circleAverage (fun w => (negLogOneSub w) ^ 2) 0 r := by
        rw [Real.circleAverage]
        norm_num
    _ = 0 := by rw [hmv, hzero]

theorem re_sq_eq (w : ℂ) : (w.re) ^ 2 = (‖w‖ ^ 2 + (w ^ 2).re) / 2 := by
  have hnorm : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w), Complex.normSq_apply]
    ring
  have hsq : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [hnorm, hsq]
  ring

theorem continuous_randomEulerLogFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun x : ℝ => randomEulerLogFactor r x) := by
  have hcirc : Continuous (fun x : ℝ => circleMap 0 r (2 * Real.pi * x)) :=
    (continuous_circleMap 0 r).comp (by fun_prop)
  have hne : ∀ x : ℝ, ‖circleMap 0 r (2 * Real.pi * x)‖ < 1 := by
    intro x
    rw [norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  have hcomp : Continuous (fun x : ℝ => negLogOneSub (circleMap 0 r (2 * Real.pi * x))) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact ContinuousAt.comp (f := fun y : ℝ => circleMap 0 r (2 * Real.pi * y))
      (g := negLogOneSub) ((differentiableAt_negLogOneSub (hne x)).continuousAt)
      (hcirc.continuousAt (x := x))
  refine hcomp.congr fun x => ?_
  rw [randomEulerLogFactor_eq_circleMap]

/-- **The real part of one Euler factor carries exactly half the second moment.** -/
theorem hasSum_intervalIntegral_reSq_randomEulerLogFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (1 / 2 : ℝ) * ((1 / (k : ℝ)) ^ 2 * r ^ (2 * k)))
      (∫ x in (0 : ℝ)..1, ((randomEulerLogFactor r x).re) ^ 2) := by
  have hcont := continuous_randomEulerLogFactor hr0 hr1
  have hnorm : Continuous (fun x : ℝ => ‖randomEulerLogFactor r x‖ ^ 2) :=
    (hcont.norm.pow 2)
  have hsq : Continuous (fun x : ℝ => (randomEulerLogFactor r x) ^ 2) := hcont.pow 2
  have hre : Continuous (fun x : ℝ => ((randomEulerLogFactor r x) ^ 2).re) :=
    Complex.continuous_re.comp hsq
  have hsplit : ∫ x in (0 : ℝ)..1, ((randomEulerLogFactor r x).re) ^ 2
      = (1 / 2 : ℝ) * ((∫ x in (0 : ℝ)..1, ‖randomEulerLogFactor r x‖ ^ 2)
        + ∫ x in (0 : ℝ)..1, ((randomEulerLogFactor r x) ^ 2).re) := by
    rw [← intervalIntegral.integral_add (hnorm.intervalIntegrable 0 1)
        (hre.intervalIntegrable 0 1),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [re_sq_eq]
    ring
  have hzero : ∫ x in (0 : ℝ)..1, ((randomEulerLogFactor r x) ^ 2).re = 0 := by
    have habs : |r| < 1 := by rwa [abs_of_nonneg hr0]
    have h := integral_sq_randomEulerLogFactor habs
    have hre' : ∫ x in (0 : ℝ)..1, ((randomEulerLogFactor r x) ^ 2).re
        = (∫ x in (0 : ℝ)..1, (randomEulerLogFactor r x) ^ 2).re := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have hint : MeasureTheory.Integrable (fun x : ℝ => (randomEulerLogFactor r x) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        (hsq.integrableOn_Ioc (a := 0) (b := 1))
      simpa using (Complex.reCLM.integral_comp_comm hint)
    rw [hre', h, Complex.zero_re]
  rw [hsplit, hzero, add_zero]
  exact (hasSum_intervalIntegral_normSq_randomEulerLogFactor hr0 hr1).mul_left (1 / 2)

/-! ### The total second moment -/

/-- The local second moment of one Euler factor at abscissa `σ`. -/
noncomputable def eulerLocalSecondMoment (σ : ℝ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, ((p : ℝ) ^ (-σ)) ^ (2 * k) * (1 / (k : ℝ)) ^ 2

theorem eulerLocalSecondMoment_eq_integral {σ : ℝ} {p : ℕ} (hp : p.Prime) (hσ : 0 < σ) :
    eulerLocalSecondMoment σ p
      = ∫ x in (0 : ℝ)..1, ‖randomEulerLogFactor ((p : ℝ) ^ (-σ)) x‖ ^ 2 := by
  have hp2 : (2 : ℕ) ≤ p := hp.two_le
  have hr0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) :=
    le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _)
  have hr1 : ((p : ℝ) ^ (-σ)) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
    exact_mod_cast hp.one_lt
  have h := hasSum_intervalIntegral_normSq_randomEulerLogFactor hr0 hr1
  rw [eulerLocalSecondMoment]
  refine (HasSum.tsum_eq ?_)
  refine h.congr_fun ?_
  intro k
  ring

/-- **The real part carries half of the local second moment.** -/
theorem intervalIntegral_reSq_eq_half {σ : ℝ} {p : ℕ} (hp : p.Prime) (hσ : 0 < σ) :
    ∫ x in (0 : ℝ)..1, ((randomEulerLogFactor ((p : ℝ) ^ (-σ)) x).re) ^ 2
      = (1 / 2 : ℝ) * eulerLocalSecondMoment σ p := by
  have hr0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) :=
    le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _)
  have hr1 : ((p : ℝ) ^ (-σ)) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
    exact_mod_cast hp.one_lt
  have h := hasSum_intervalIntegral_reSq_randomEulerLogFactor hr0 hr1
  have h2 : HasSum (fun k : ℕ => (1 / 2 : ℝ) * (((p : ℝ) ^ (-σ)) ^ (2 * k) * (1 / (k : ℝ)) ^ 2))
      (∫ x in (0 : ℝ)..1, ((randomEulerLogFactor ((p : ℝ) ^ (-σ)) x).re) ^ 2) := by
    refine h.congr_fun ?_
    intro k
    ring
  rw [h2.tsum_eq.symm, eulerLocalSecondMoment, ← tsum_mul_left]

theorem eulerLocalSecondMoment_nonneg (σ : ℝ) (p : ℕ) : 0 ≤ eulerLocalSecondMoment σ p := by
  rw [eulerLocalSecondMoment]
  refine tsum_nonneg fun k => ?_
  positivity

theorem eulerLocalSecondMoment_le {σ : ℝ} {p : ℕ} (hp : p.Prime) (hσ : 0 < σ) :
    eulerLocalSecondMoment σ p
      ≤ (1 - ((2 : ℝ) ^ (-σ)) ^ 2)⁻¹ * ((p : ℝ) ^ (-σ)) ^ 2 := by
  set r : ℝ := (p : ℝ) ^ (-σ) with hrdef
  set ρ : ℝ := (2 : ℝ) ^ (-σ) with hρdef
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  have hrρ : r ≤ ρ := prime_rpow_neg_le_rho hσ hp
  have hρ1 : ρ < 1 := randomEulerRho_lt_one hσ
  have hρ0 : (0 : ℝ) < ρ := randomEulerRho_pos σ
  have hr1 : r < 1 := lt_of_le_of_lt hrρ hρ1
  have hden : (0 : ℝ) < 1 - ρ ^ 2 := by nlinarith
  have hdenr : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
  have hgeom : HasSum (fun k : ℕ => (r ^ 2) ^ k) (1 - r ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one (by positivity) (by nlinarith)
  have hterm : ∀ k : ℕ, r ^ (2 * k) * (1 / (k : ℝ)) ^ 2 ≤ (r ^ 2) ^ k := by
    intro k
    rw [pow_mul]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      norm_num
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hle : (1 / (k : ℝ)) ^ 2 ≤ 1 := by
        rw [div_pow, one_pow, div_le_one (by positivity)]
        nlinarith
      nlinarith [pow_nonneg (le_of_lt (by positivity : (0 : ℝ) < r ^ 2)) k]
  have hsummable : Summable (fun k : ℕ => r ^ (2 * k) * (1 / (k : ℝ)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hterm hgeom.summable
  -- split off the vanishing `k = 0` term and compare with the geometric tail
  have hzero : r ^ (2 * 0) * (1 / ((0 : ℕ) : ℝ)) ^ 2 = 0 := by norm_num
  have hsplit : eulerLocalSecondMoment σ p
      = ∑' k : ℕ, r ^ (2 * (k + 1)) * (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [eulerLocalSecondMoment, Summable.tsum_eq_zero_add hsummable, hzero, zero_add]
  have hshift : ∀ k : ℕ, r ^ (2 * (k + 1)) * (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ r ^ 2 * (r ^ 2) ^ k := by
    intro k
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hle : (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow, div_le_one (by positivity)]
      nlinarith
    have hpow : r ^ (2 * (k + 1)) = r ^ 2 * (r ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    rw [hpow]
    exact mul_le_of_le_one_right (by positivity) hle
  have hsummable' : Summable (fun k : ℕ => r ^ (2 * (k + 1)) * (1 / ((k + 1 : ℕ) : ℝ)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) hshift ?_
    exact hgeom.summable.mul_left (r ^ 2)
  have hbound : eulerLocalSecondMoment σ p ≤ r ^ 2 * (1 - r ^ 2)⁻¹ := by
    rw [hsplit, ← hgeom.tsum_eq, ← tsum_mul_left]
    exact Summable.tsum_mono hsummable' (hgeom.summable.mul_left (r ^ 2)) hshift
  refine hbound.trans ?_
  have hmono : (1 - r ^ 2)⁻¹ ≤ (1 - ρ ^ 2)⁻¹ := by
    refine inv_anti₀ hden ?_
    nlinarith
  have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  calc r ^ 2 * (1 - r ^ 2)⁻¹ ≤ r ^ 2 * (1 - ρ ^ 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hmono hr2
    _ = (1 - ρ ^ 2)⁻¹ * r ^ 2 := by ring

/-- The total second moment `V(σ) = ∑_p ∑_k p^(−2kσ)/k²`. -/
noncomputable def randomEulerV (σ : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then eulerLocalSecondMoment σ n else 0

/-- **The total second moment is finite past the half line.** -/
theorem summable_eulerLocalSecondMoment {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => if n.Prime then eulerLocalSecondMoment σ n else 0) := by
  have hσ0 : 0 < σ := by linarith
  have hcomp := (summable_ite_prime_rpow (t := 2 * σ) (by linarith)).mul_left
    ((1 - ((2 : ℝ) ^ (-σ)) ^ 2)⁻¹)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hcomp
  · by_cases h : n.Prime
    · rw [if_pos h]
      exact eulerLocalSecondMoment_nonneg σ n
    · rw [if_neg h]
  · by_cases h : n.Prime
    · rw [if_pos h, if_pos h]
      refine (eulerLocalSecondMoment_le h hσ0).trans_eq ?_
      congr 1
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (le_of_lt
        (by exact_mod_cast h.pos))]
      congr 1
      push_cast
      ring
    · rw [if_neg h, if_neg h, mul_zero]

end

end GaloisForLFunctions.RHTower
