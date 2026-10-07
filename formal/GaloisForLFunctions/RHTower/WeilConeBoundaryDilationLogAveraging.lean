import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationInequality
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare
import GaloisForLFunctions.RHTower.XiSliceCircleDecay
import GaloisForLFunctions.RHTower.OuterDecompositionLawMollifiedProduct

/-!
# Averaging the boundary inequality against the softened logarithm of Hardy Z

For `η > 0` put `L_η = ½ log(Z² + η²)`, a smooth function with `L_η' = Z Z'/(Z² + η²)`.
Multiplying the boundary inequality `(Re A − 1)·θ'·Z² ≤ Im A·Z Z' − Re V·Z²` by `w/(Z² + η²)` for
a nonnegative `C¹` weight `w` and integrating by parts gives

`∫ (Re A − 1) θ' w q ≤ [Im A · w · L_η] − ∫ (Im A · w)' L_η − ∫ Re V · w q`,
`q = Z²/(Z² + η²)`.

The softened logarithm is controlled by three classical inputs: the pointwise bounds
`log η ≤ L_η ≤ ½ log(1 + Z²)`, the concavity bound `∫ log(1 + Z²) ≤ |I| log(1 + M)` from the mean
square `∫ Z² ≤ M|I|`, and Littlewood's floor `∫ log|ζ(½ + it)| ≥ −C − K log T₂`, which bounds
`∫ L_η` from below because `L_η ≥ log|Z|` off the finitely many zeros. The loss of the factor
`Z²/(Z² + η²)` is controlled by `η²/(Z² + η²) ≤ η + 2(½ log(1 + Z²) − L_η)/log(1/(2η))`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower.WeilBoundaryDilation

open RHTower.WeilInfiniteDilation RHTower.WeilFiniteType

variable {a v : ℕ → ℝ}

theorem HalfSummable.half (ha : HalfSummable a) : LSeriesSummable (fun n => (a n : ℂ)) (1 / 2) := by
  have e : ((1 / 2 - 0 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have h : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - 0 : ℝ) : ℂ) := ha
  rwa [e] at h

/-- The derivative of the line function `t ↦ A(½ + it)`. -/
def lineDeriv (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  -I * LSeries (LSeries.logMul fun n => (a n : ℂ)) (linePt t)

theorem hasDerivAt_lineSeries (ha : HalfSummable a)
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => dilSeries a (linePt t)) (lineDeriv a t) t :=
  hasDerivAt_LSeries_linePt ha.half hlog t

theorem continuous_lineSeries (ha : HalfSummable a) :
    Continuous fun t : ℝ => dilSeries a (linePt t) :=
  continuous_LSeries_linePt ha.half

theorem continuous_lineDeriv (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) :
    Continuous (lineDeriv a) :=
  continuous_const.mul (continuous_LSeries_linePt hlog)

theorem norm_LSeries_linePt_le {f : ℕ → ℂ} (hf : LSeriesSummable f (1 / 2)) (t : ℝ) :
    ‖LSeries f (linePt t)‖ ≤ ∑' n, ‖LSeries.term f (1 / 2) n‖ := by
  have he : ∀ n, ‖LSeries.term f (linePt t) n‖ = ‖LSeries.term f (1 / 2) n‖ := fun n => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, linePt_re]; norm_num
  have hs : Summable fun n => ‖LSeries.term f (linePt t) n‖ := by
    simp_rw [he]; exact summable_norm_iff.mpr hf
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  exact tsum_congr he

/-! ## Hardy Z and the softened logarithm -/

theorem continuous_deriv_hardyZ : Continuous (deriv hardyZ) := by
  have h : deriv hardyZ = fun t => (Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      (deriv riemannZeta (linePt t) * I)).re := by
    funext t
    rw [← re_exp_theta_mul_deriv_riemannZeta_line, deriv_riemannZeta_line]
  rw [h]
  refine Complex.continuous_re.comp (Continuous.mul ?_ (Continuous.mul ?_ continuous_const))
  · exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp differentiable_gammaHardyTheta.continuous))
  · refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ((analyticOn_riemannZeta (linePt t) (linePt_ne_one t)).deriv.continuousAt).comp
      continuous_linePt.continuousAt

/-- `L_η = ½ log(Z² + η²)`. -/
def softLog (η t : ℝ) : ℝ := Real.log (hardyZ t ^ 2 + η ^ 2) / 2

theorem continuous_softLog {η : ℝ} (hη : 0 < η) : Continuous (softLog η) := by
  have hc := differentiable_hardyZ.continuous
  unfold softLog
  refine (Continuous.log ((hc.pow 2).add continuous_const) fun t => ?_).div_const 2
  show hardyZ t ^ 2 + η ^ 2 ≠ 0
  positivity

theorem hasDerivAt_softLog {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (softLog η) (hardyZ t * deriv hardyZ t / (hardyZ t ^ 2 + η ^ 2)) t := by
  have hpos : 0 < hardyZ t ^ 2 + η ^ 2 := by positivity
  have hZ : HasDerivAt hardyZ (deriv hardyZ t) t := (differentiable_hardyZ t).hasDerivAt
  have h2 : HasDerivAt (fun t => hardyZ t ^ 2 + η ^ 2) (2 * hardyZ t * deriv hardyZ t) t :=
    ((hZ.pow 2).add_const (η ^ 2)).congr_deriv (by norm_num)
  have := (h2.log hpos.ne').div_const 2
  unfold softLog
  refine this.congr_deriv ?_
  field_simp

theorem softLog_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (t : ℝ) :
    softLog η t ≤ Real.log (1 + hardyZ t ^ 2) / 2 := by
  unfold softLog
  have hp : 0 < hardyZ t ^ 2 + η ^ 2 := by positivity
  have : hardyZ t ^ 2 + η ^ 2 ≤ 1 + hardyZ t ^ 2 := by nlinarith
  linarith [Real.log_le_log hp this]

theorem log_le_softLog {η : ℝ} (hη : 0 < η) (t : ℝ) : Real.log η ≤ softLog η t := by
  unfold softLog
  have h : Real.log (η ^ 2) ≤ Real.log (hardyZ t ^ 2 + η ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (hardyZ t)])
  rw [Real.log_pow] at h
  push_cast at h
  linarith

theorem log_one_add_sq_nonneg (t : ℝ) : 0 ≤ Real.log (1 + hardyZ t ^ 2) :=
  Real.log_nonneg (by nlinarith [sq_nonneg (hardyZ t)])

theorem abs_softLog_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (t : ℝ) :
    |softLog η t| ≤ Real.log (1 + hardyZ t ^ 2) - softLog η t := by
  have h1 := softLog_le hη hη1 t
  have h0 := log_one_add_sq_nonneg t
  rw [abs_le]; constructor <;> linarith

theorem abs_softLog_le_log {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (t : ℝ) :
    |softLog η t| ≤ Real.log (1 / η) + Real.log (1 + hardyZ t ^ 2) := by
  have h1 := softLog_le hη hη1 t
  have h2 := log_le_softLog hη t
  have h0 := log_one_add_sq_nonneg t
  have hinv : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
  have hη0 : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  rw [abs_le]; constructor <;> linarith

/-- The loss of the softening factor is controlled by the logarithmic gap. -/
theorem softening_defect_le {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (t : ℝ) :
    η ^ 2 / (hardyZ t ^ 2 + η ^ 2) ≤
      η + 2 * (Real.log (1 + hardyZ t ^ 2) / 2 - softLog η t) / Real.log (1 / (2 * η)) := by
  have hL : 0 < Real.log (1 / (2 * η)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
  have hp : 0 < hardyZ t ^ 2 + η ^ 2 := by positivity
  have hgap : 0 ≤ Real.log (1 + hardyZ t ^ 2) / 2 - softLog η t := by
    linarith [softLog_le hη (by linarith) t]
  by_cases hZ : η ≤ hardyZ t ^ 2
  · have h1 : η ^ 2 / (hardyZ t ^ 2 + η ^ 2) ≤ η := by
      rw [div_le_iff₀ hp]; nlinarith
    have h2 : 0 ≤ 2 * (Real.log (1 + hardyZ t ^ 2) / 2 - softLog η t) /
        Real.log (1 / (2 * η)) := by positivity
    linarith
  · push Not at hZ
    have hsl : softLog η t ≤ Real.log (2 * η) / 2 := by
      unfold softLog
      have : hardyZ t ^ 2 + η ^ 2 ≤ 2 * η := by nlinarith
      linarith [Real.log_le_log hp this]
    have hlog2 : Real.log (1 / (2 * η)) = -Real.log (2 * η) := by rw [one_div, Real.log_inv]
    have h0 := log_one_add_sq_nonneg t
    have hge : 1 ≤ 2 * (Real.log (1 + hardyZ t ^ 2) / 2 - softLog η t) /
        Real.log (1 / (2 * η)) := by
      rw [le_div_iff₀ hL]; linarith
    have hle1 : η ^ 2 / (hardyZ t ^ 2 + η ^ 2) ≤ 1 := by
      rw [div_le_one hp]; nlinarith [sq_nonneg (hardyZ t)]
    linarith

/-! ## The integrated inequality -/

/-- The boundary inequality multiplied by `w/(Z² + η²)`. -/
theorem regularized_ineq (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {η : ℝ} (hη : 0 < η) {w : ℝ} (hw : 0 ≤ w)
    (t : ℝ) :
    ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) ≤
      ((dilSeries a (linePt t)).im * w) *
          (hardyZ t * deriv hardyZ t / (hardyZ t ^ 2 + η ^ 2)) -
        (regSeries v (linePt t)).re * w * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) := by
  have h := boundary_ineq_sq ha hv hW t
  have hpos : 0 < hardyZ t ^ 2 + η ^ 2 := by positivity
  have hc : 0 ≤ w / (hardyZ t ^ 2 + η ^ 2) := div_nonneg hw hpos.le
  have := mul_le_mul_of_nonneg_right h hc
  calc ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))
      = ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * hardyZ t ^ 2 *
          (w / (hardyZ t ^ 2 + η ^ 2)) := by ring
    _ ≤ ((dilSeries a (linePt t)).im * (hardyZ t * deriv hardyZ t) -
          (regSeries v (linePt t)).re * hardyZ t ^ 2) * (w / (hardyZ t ^ 2 + η ^ 2)) := this
    _ = _ := by ring

/-- **The integrated boundary inequality**, after integration by parts against `L_η`. -/
theorem integral_regularized_le (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) {η : ℝ} (hη : 0 < η)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) {w w' : ℝ → ℝ} (hw : ∀ t, HasDerivAt w (w' t) t)
    (hwc : Continuous w') (hw0 : ∀ t, 0 ≤ w t) :
    ∫ t in T₁..T₂, ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) ≤
      (dilSeries a (linePt T₂)).im * w T₂ * softLog η T₂ -
        (dilSeries a (linePt T₁)).im * w T₁ * softLog η T₁ -
        (∫ t in T₁..T₂, ((lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t) *
          softLog η t) -
        ∫ t in T₁..T₂, (regSeries v (linePt t)).re * w t *
          (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) := by
  have hV : ∀ t, HasDerivAt (fun t => (dilSeries a (linePt t)).im) (lineDeriv a t).im t :=
    fun t => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_lineSeries ha hlog t)
  have hBc := continuous_lineSeries ha
  have hB'c := continuous_lineDeriv hlog
  have hVc : Continuous fun t => regSeries v (linePt t) := continuous_LSeries_linePt hv.summable
  have hwcont : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  have hZc : Continuous hardyZ := differentiable_hardyZ.continuous
  have hpos : ∀ t, hardyZ t ^ 2 + η ^ 2 ≠ 0 := fun t => by positivity
  have hq : Continuous fun t => hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2) :=
    (hZc.pow 2).div ((hZc.pow 2).add continuous_const) hpos
  have hd : Continuous fun t => hardyZ t * deriv hardyZ t / (hardyZ t ^ 2 + η ^ 2) :=
    (hZc.mul continuous_deriv_hardyZ).div ((hZc.pow 2).add continuous_const) hpos
  have hIV : IntervalIntegrable (fun t => (regSeries v (linePt t)).re * w t *
      (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))) volume T₁ T₂ :=
    (((Complex.continuous_re.comp hVc).mul hwcont).mul hq).intervalIntegrable _ _
  have hIP : IntervalIntegrable (fun t => ((dilSeries a (linePt t)).im * w t) *
      (hardyZ t * deriv hardyZ t / (hardyZ t ^ 2 + η ^ 2))) volume T₁ T₂ :=
    (((Complex.continuous_im.comp hBc).mul hwcont).mul hd).intervalIntegrable _ _
  have h1 : ∫ t in T₁..T₂, ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) ≤
      ∫ t in T₁..T₂, (((dilSeries a (linePt t)).im * w t) *
          (hardyZ t * deriv hardyZ t / (hardyZ t ^ 2 + η ^ 2)) -
        (regSeries v (linePt t)).re * w t * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))) := by
    refine intervalIntegral.integral_mono_on hT ?_ (hIP.sub hIV) fun t _ =>
      regularized_ineq ha hv hW hη (hw0 t) t
    exact (((((Complex.continuous_re.comp hBc).sub continuous_const).mul
      continuous_gammaHardyPhaseRate).mul hwcont).mul hq).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hIP hIV] at h1
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := T₁) (b := T₂)
    (u := fun t => (dilSeries a (linePt t)).im * w t) (v := softLog η)
    (u' := fun t => (lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t)
    (v' := fun t => hardyZ t * deriv hardyZ t / (hardyZ t ^ 2 + η ^ 2))
    (fun t _ => (hV t).mul (hw t)) (fun t _ => hasDerivAt_softLog hη t)
    ((((Complex.continuous_im.comp hB'c).mul hwcont).add
      ((Complex.continuous_im.comp hBc).mul hwc)).intervalIntegrable _ _)
    (hd.intervalIntegrable _ _)
  rw [h2] at h1
  exact h1

/-! ## The three averages -/

/-- **Concavity.**  If `∫ f ≤ M |I|` then `∫ log(1 + f) ≤ |I| log(1 + M)`. -/
theorem integral_log_one_add_le {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {T₁ T₂ M : ℝ} (hT : T₁ ≤ T₂) (hM : 0 ≤ M) (hmean : ∫ t in T₁..T₂, f t ≤ M * (T₂ - T₁)) :
    ∫ t in T₁..T₂, Real.log (1 + f t) ≤ (T₂ - T₁) * Real.log (1 + M) := by
  have h2 : 0 < 1 + M := by linarith
  set k := 1 / (1 + M) with hk
  have hk0 : 0 ≤ k := by positivity
  have hpt : ∀ t, Real.log (1 + f t) ≤ (Real.log (1 + M) - M * k) + f t * k := by
    intro t
    have h1 : 0 < 1 + f t := by linarith [hf0 t]
    have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at this
    have e : (1 + f t) / (1 + M) - 1 = f t * k - M * k := by
      rw [hk]; field_simp; ring
    linarith
  have hlogc : Continuous fun t => Real.log (1 + f t) :=
    (continuous_const.add hf).log fun t => (show (0 : ℝ) < 1 + f t by linarith [hf0 t]).ne'
  have hint : ∫ t in T₁..T₂, Real.log (1 + f t) ≤
      ∫ t in T₁..T₂, ((Real.log (1 + M) - M * k) + f t * k) :=
    intervalIntegral.integral_mono_on hT (hlogc.intervalIntegrable _ _)
      ((continuous_const.add (hf.mul continuous_const)).intervalIntegrable _ _) fun t _ => hpt t
  have hfk : IntervalIntegrable (fun t => f t * k) volume T₁ T₂ :=
    (hf.mul continuous_const).intervalIntegrable _ _
  have heval : ∫ t in T₁..T₂, ((Real.log (1 + M) - M * k) + f t * k) =
      (T₂ - T₁) * (Real.log (1 + M) - M * k) + (∫ t in T₁..T₂, f t) * k := by
    rw [intervalIntegral.integral_add intervalIntegrable_const hfk, intervalIntegral.integral_const,
      intervalIntegral.integral_mul_const, smul_eq_mul]
  rw [heval] at hint
  have : (∫ t in T₁..T₂, f t) * k ≤ M * (T₂ - T₁) * k := mul_le_mul_of_nonneg_right hmean hk0
  nlinarith

theorem ofReal_half_add_eq_linePt (t : ℝ) : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = linePt t := by
  simp [linePt]

theorem normSq_zeta_eq_hardyZ_sq (t : ℝ) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 = hardyZ t ^ 2 := by
  rw [ofReal_half_add_eq_linePt, norm_riemannZeta_linePt, sq_abs]

/-- **Mean square of Hardy Z on `[T₁, T₂]`.** -/
theorem exists_integral_hardyZ_sq_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {T₁ T₂ : ℝ}, 0 ≤ T₁ → T₁ ≤ T₂ → 4 ≤ T₂ →
      ∫ t in T₁..T₂, hardyZ t ^ 2 ≤ D * (T₂ + 1) * (1 + Real.log (T₂ + 1)) ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_integral_normSq_zeta_critical_le
  refine ⟨D, hD, fun {T₁ T₂} h0 hT h4 => ?_⟩
  set N := ⌈T₂⌉₊ with hN
  have hNT : T₂ ≤ N := Nat.le_ceil T₂
  have hN1 : (N : ℝ) ≤ T₂ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hN4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := le_trans h4 hNT
    exact_mod_cast this
  have hb := hbound hN4
  have hc : Continuous fun t : ℝ => hardyZ t ^ 2 := differentiable_hardyZ.continuous.pow 2
  have hmono : ∫ t in T₁..T₂, hardyZ t ^ 2 ≤ ∫ t in (-(N : ℝ))..(N : ℝ), hardyZ t ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) hT hNT
      (Filter.Eventually.of_forall fun t => sq_nonneg _) (hc.intervalIntegrable _ _)
  simp_rw [normSq_zeta_eq_hardyZ_sq] at hb
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : Real.log N ≤ Real.log (T₂ + 1) := Real.log_le_log hN0 hN1
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hsq : (1 + Real.log N) ^ 2 ≤ (1 + Real.log (T₂ + 1)) ^ 2 := by
    gcongr
  calc ∫ t in T₁..T₂, hardyZ t ^ 2 ≤ D * N * (1 + Real.log N) ^ 2 := hmono.trans hb
    _ ≤ D * (T₂ + 1) * (1 + Real.log (T₂ + 1)) ^ 2 := by
      gcongr

/-- **Littlewood's floor for the softened logarithm.** -/
theorem exists_integral_softLog_ge :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {η T₁ T₂ : ℝ}, 0 < η → 20 ≤ T₁ → T₁ < T₂ →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        -(C + K * Real.log T₂) ≤ ∫ t in T₁..T₂, softLog η t := by
  obtain ⟨C, K, hC, hK, hfloor⟩ := exists_zetaLine_logMean_floor
  refine ⟨C, K, hC, hK, fun {η T₁ T₂} hη h20 hT hG1 hG2 => ?_⟩
  refine (hfloor T₁ T₂ h20 hT hG1 hG2).trans ?_
  obtain ⟨Zs, hZs⟩ := exists_zetaRectangleZeros_finset h20 hT
  have hfin : (Set.Icc T₁ T₂ ∩ {t | hardyZ t = 0}).Finite := by
    refine (Zs.finite_toSet.image Complex.im).subset ?_
    rintro t ⟨ht, hZ⟩
    refine ⟨linePt t, ?_, by simp [linePt]⟩
    have hζ : riemannZeta (linePt t) = 0 := by
      have := norm_riemannZeta_linePt t
      rw [show hardyZ t = 0 from hZ, abs_zero] at this
      exact norm_eq_zero.mp this
    refine (hZs _).mpr ⟨?_, hζ⟩
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [linePt_re]; exact Set.left_mem_uIcc
    · have : (linePt t).im = t := by simp [linePt]
      rw [this]; exact Set.mem_uIcc_of_le ht.1 ht.2
  refine intervalIntegral.integral_mono_ae_restrict hT.le
    (intervalIntegrable_log_norm_riemannZeta_line _ _)
    ((continuous_softLog hη).intervalIntegrable _ _) ?_
  have hnull : volume (Set.Icc T₁ T₂ ∩ {t | hardyZ t = 0}) = 0 := hfin.measure_zero _
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht hmem
  have hZ : hardyZ t ≠ 0 := fun h => ht ⟨hmem, h⟩
  rw [ofReal_half_add_eq_linePt, norm_riemannZeta_linePt, Real.log_abs]
  unfold softLog
  have hp : 0 < hardyZ t ^ 2 := by positivity
  have h1 : Real.log (hardyZ t ^ 2) ≤ Real.log (hardyZ t ^ 2 + η ^ 2) :=
    Real.log_le_log hp (by nlinarith)
  have h2 := Real.log_pow (hardyZ t) 2
  push_cast at h2
  linarith

/-- Every unit height window contains a height whose horizontal segment is zero-free. -/
theorem exists_zeroFree_height {T : ℝ} (hT : 20 ≤ T) :
    ∃ T' ∈ Set.Icc T (T + 1),
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T' : ℂ) * I) ≠ 0 := by
  obtain ⟨Zs, hZs⟩ := exists_zetaRectangleZeros_finset hT (show T < T + 1 by linarith)
  obtain ⟨T', hT', hnot⟩ := ((Set.Icc_infinite (show T < T + 1 by linarith)).sdiff
    (Zs.finite_toSet.image Complex.im)).nonempty
  refine ⟨T', hT', fun x hx hζ => hnot ⟨(x : ℂ) + (T' : ℂ) * I, ?_, by simp⟩⟩
  refine (hZs _).mpr ⟨?_, hζ⟩
  rw [Complex.mem_reProdIm]
  have hre : ((x : ℂ) + (T' : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (T' : ℂ) * I).im = T' := by simp
  rw [hre, him]
  exact ⟨Set.mem_uIcc_of_le hx.1 hx.2, Set.mem_uIcc_of_le hT'.1 hT'.2⟩

end RHTower.WeilBoundaryDilation
