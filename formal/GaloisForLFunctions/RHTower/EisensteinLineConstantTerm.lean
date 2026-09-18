import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly
import GaloisForLFunctions.RHTower.SeamVerticalDecay

/-!
# The constant term of `E*(·, 1/2 + it)`

The constant term of the completed Eisenstein series on the line is
`c(Y) = Λ(2it) Y^{1/2 - it} + Λ(1 + 2it) Y^{1/2 + it}`, with `Λ(2it) = conj Λ(1 + 2it)` by the
functional equation, so `c(Y) = 2 √Y · Re(Λ(1+2it) Y^{it})` is real.  This module records

* `‖c(Y)‖ ≤ 2 ‖Λ(1+2it)‖ √Y`;
* the mean-square lower bound `∫_1^{e²} ‖c(y)‖² y⁻² dy ≥ (5/2) ‖Λ(1+2it)‖²` for `t ≥ 2`, from the
  explicit antiderivative of `y ↦ Re(b e^{it log y})² / y`;
* `‖Λ(1+2it)‖² ≥ e^{-πt} ‖ζ(1+2it)‖²`, from `‖Γ(1/2 + it)‖² cosh(πt) = π`.
-/

open Complex Set Filter Topology intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

/-- `Λ(1 + 2it)`. -/
def eisLineLambda (t : ℝ) : ℂ := reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I))

/-- The constant term of `E*(·, 1/2 + it)` at height `Y`. -/
def eisLineConst (t Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * I) Y

/-! ## `Λ` on the line: conjugation and the functional equation -/

theorem reflectedCompletedLambda_conj (s : ℂ) :
    reflectedCompletedLambda ((starRingEnd ℂ) s) = (starRingEnd ℂ) (reflectedCompletedLambda s) := by
  rw [reflectedCompletedLambda_eq, reflectedCompletedLambda_eq, map_mul, map_mul]
  have hπ : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have key : ((Real.pi : ℝ) : ℂ) ^ (-(starRingEnd ℂ) s / 2) =
      (starRingEnd ℂ) (((Real.pi : ℝ) : ℂ) ^ (-s / 2)) := by
    have := Complex.conj_cpow ((Real.pi : ℝ) : ℂ) (-(starRingEnd ℂ) s / 2) hπ
    rw [Complex.conj_ofReal] at this
    rw [this]
    congr 2
    rw [map_div₀, map_neg, Complex.conj_conj, map_ofNat]
  rw [key, ← Complex.Gamma_conj, ← riemannZeta_conj, map_div₀, map_ofNat]

theorem reflectedCompletedLambda_eq_completed {s : ℂ} (hs : s ≠ 0) (hG : s.Gammaℝ ≠ 0) :
    reflectedCompletedLambda s = completedRiemannZeta s := by
  rw [reflectedCompletedLambda_eq, riemannZeta_def_of_ne_zero hs, ← Complex.Gammaℝ_def]
  field_simp

theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s.Gammaℝ ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply hs
  rw [hn]; simp

/-- `Λ(2it) = conj Λ(1 + 2it)` for `t ≠ 0`. -/
theorem reflectedCompletedLambda_two_mul_I_eq_conj {t : ℝ} (ht : t ≠ 0) :
    reflectedCompletedLambda (2 * ((t : ℂ) * I)) = (starRingEnd ℂ) (eisLineLambda t) := by
  unfold eisLineLambda
  have h1 : reflectedCompletedLambda (2 * ((t : ℂ) * I)) =
      completedRiemannZeta (2 * ((t : ℂ) * I)) := by
    refine reflectedCompletedLambda_eq_completed ?_ (Gammaℝ_ne_zero_of_im_ne_zero ?_)
    · intro h
      have := congrArg Complex.im h
      simp at this
      exact ht this
    · simp [ht]
  have h2 : reflectedCompletedLambda (1 - 2 * ((t : ℂ) * I)) =
      completedRiemannZeta (1 - 2 * ((t : ℂ) * I)) := by
    refine reflectedCompletedLambda_eq_completed ?_ (Gammaℝ_ne_zero_of_im_ne_zero ?_)
    · intro h
      have := congrArg Complex.im h
      simp at this
      exact ht this
    · simp [ht]
  rw [h1, ← completedRiemannZeta_one_sub, ← h2, ← reflectedCompletedLambda_conj]
  congr 1
  simp [Complex.ext_iff]

theorem norm_reflectedCompletedLambda_two_mul_I {t : ℝ} (ht : t ≠ 0) :
    ‖reflectedCompletedLambda (2 * ((t : ℂ) * I))‖ = ‖eisLineLambda t‖ := by
  rw [reflectedCompletedLambda_two_mul_I_eq_conj ht, Complex.norm_conj]

/-! ## The constant term as `2√Y · Re(b Y^{it})` -/

theorem eisLineConst_eq (t Y : ℝ) :
    eisLineConst t Y =
      reflectedCompletedLambda (2 * ((t : ℂ) * I)) * (Y : ℂ) ^ ((1 / 2 : ℂ) + (-1 : ℤ) * ((t : ℂ) * I)) +
        eisLineLambda t * (Y : ℂ) ^ ((1 / 2 : ℂ) + (1 : ℤ) * ((t : ℂ) * I)) := by
  unfold eisLineConst eisLineLambda d4BMCompletedEisensteinCuspConstantPart
    d4BMCompletedEisensteinCuspConstantTerm d4BMCompletedEisensteinCuspConstantCoefficient
    d4BMCompletedEisensteinCuspConstantMaassFactor d4BMCompletedEisensteinCuspWeylExponent
    d4BMCuspSign
  simp

/-- The Weyl monomial `Y^{1/2 + w}` at a positive height factors as `√Y · Y^w`. -/
theorem cpow_half_add {Y : ℝ} (hY : 0 < Y) (w : ℂ) :
    (Y : ℂ) ^ ((1 / 2 : ℂ) + w) = ((Real.sqrt Y : ℝ) : ℂ) * (Y : ℂ) ^ w := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hY.ne'), Real.sqrt_eq_rpow,
    Complex.ofReal_cpow hY.le]
  push_cast
  ring

theorem norm_cpow_I_mul {Y : ℝ} (hY : 0 < Y) (t : ℝ) : ‖(Y : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp

/-- `‖c(Y)‖ ≤ 2 ‖Λ(1+2it)‖ √Y`. -/
theorem norm_eisLineConst_le {t : ℝ} (ht : t ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    ‖eisLineConst t Y‖ ≤ 2 * ‖eisLineLambda t‖ * Real.sqrt Y := by
  rw [eisLineConst_eq]
  have e1 : ((1 / 2 : ℂ) + (-1 : ℤ) * ((t : ℂ) * I)) = (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : ((1 / 2 : ℂ) + (1 : ℤ) * ((t : ℂ) * I)) = (1 / 2 : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  rw [e1, e2, cpow_half_add hY, cpow_half_add hY]
  have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  calc ‖reflectedCompletedLambda (2 * ((t : ℂ) * I)) * (((Real.sqrt Y : ℝ) : ℂ) *
          (Y : ℂ) ^ (((-t : ℝ) : ℂ) * I)) +
        eisLineLambda t * (((Real.sqrt Y : ℝ) : ℂ) * (Y : ℂ) ^ ((t : ℂ) * I))‖
      ≤ ‖reflectedCompletedLambda (2 * ((t : ℂ) * I)) * (((Real.sqrt Y : ℝ) : ℂ) *
          (Y : ℂ) ^ (((-t : ℝ) : ℂ) * I))‖ +
        ‖eisLineLambda t * (((Real.sqrt Y : ℝ) : ℂ) * (Y : ℂ) ^ ((t : ℂ) * I))‖ := norm_add_le _ _
    _ = ‖eisLineLambda t‖ * Real.sqrt Y + ‖eisLineLambda t‖ * Real.sqrt Y := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cpow_I_mul hY, norm_cpow_I_mul hY,
          norm_reflectedCompletedLambda_two_mul_I ht, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs]
        ring
    _ = 2 * ‖eisLineLambda t‖ * Real.sqrt Y := by ring

/-- The unit phase `Y^{it} = exp(i t log Y)`. -/
theorem cpow_I_mul_eq_exp {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    (Y : ℂ) ^ ((t : ℂ) * I) = Complex.exp (((t * Real.log Y : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hY.ne'), ← Complex.ofReal_log hY.le]
  congr 1
  push_cast
  ring

/-- `c(Y) = √Y · (conj z + z)` with `z = Λ(1+2it) Y^{it}`, i.e. `2√Y Re z`. -/
theorem eisLineConst_eq_two_re {t : ℝ} (ht : t ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    eisLineConst t Y =
      ((2 * Real.sqrt Y * (eisLineLambda t *
        Complex.exp (((t * Real.log Y : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := by
  rw [eisLineConst_eq]
  have e1 : ((1 / 2 : ℂ) + (-1 : ℤ) * ((t : ℂ) * I)) = (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : ((1 / 2 : ℂ) + (1 : ℤ) * ((t : ℂ) * I)) = (1 / 2 : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  rw [e1, e2, cpow_half_add hY, cpow_half_add hY, reflectedCompletedLambda_two_mul_I_eq_conj ht,
    cpow_I_mul_eq_exp hY, cpow_I_mul_eq_exp hY]
  set z : ℂ := eisLineLambda t * Complex.exp (((t * Real.log Y : ℝ) : ℂ) * I) with hz
  have hconj : (starRingEnd ℂ) (eisLineLambda t) *
      Complex.exp (((-t * Real.log Y : ℝ) : ℂ) * I) = (starRingEnd ℂ) z := by
    rw [hz, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast; ring
  have hre : ((Real.sqrt Y : ℝ) : ℂ) * ((starRingEnd ℂ) z + z) =
      ((2 * Real.sqrt Y * z.re : ℝ) : ℂ) := by
    rw [add_comm, Complex.add_conj]
    push_cast; ring
  calc _ = ((Real.sqrt Y : ℝ) : ℂ) * ((starRingEnd ℂ) z + z) := by
        rw [← hconj, hz]; ring
    _ = _ := hre

/-- `‖c(Y)‖² = 4 Y · Re(b e^{it log Y})²`. -/
theorem normSq_eisLineConst_eq {t : ℝ} (ht : t ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    ‖eisLineConst t Y‖ ^ 2 = 4 * Y * (eisLineLambda t *
      Complex.exp (((t * Real.log Y : ℝ) : ℂ) * I)).re ^ 2 := by
  rw [eisLineConst_eq_two_re ht hY, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY.le
  rw [mul_pow, mul_pow, hsq]; ring

/-! ## The mean square of the constant term on `[1, e²]` -/

/-- The oscillatory real part in the variable `v = log y`. -/
def lambdaPhase (b : ℂ) (t v : ℝ) : ℝ := (b * Complex.exp (((t * v : ℝ) : ℂ) * I)).re

theorem lambdaPhase_eq (b : ℂ) (t v : ℝ) :
    lambdaPhase b t v = b.re * Real.cos (t * v) - b.im * Real.sin (t * v) := by
  unfold lambdaPhase
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The antiderivative of `lambdaPhase² / y` in `y` (through `v = log y`). -/
def lambdaPhasePrimitive (b : ℂ) (t y : ℝ) : ℝ :=
  (‖b‖ ^ 2 / 2) * Real.log y + (b.re ^ 2 - b.im ^ 2) * Real.sin (2 * t * Real.log y) / (4 * t) -
    b.re * b.im * (1 - Real.cos (2 * t * Real.log y)) / (2 * t)

theorem hasDerivAt_lambdaPhasePrimitive (b : ℂ) {t : ℝ} (ht : t ≠ 0) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (lambdaPhasePrimitive b t) (lambdaPhase b t (Real.log y) ^ 2 / y) y := by
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  have h1 : HasDerivAt (fun y => (‖b‖ ^ 2 / 2) * Real.log y) ((‖b‖ ^ 2 / 2) * y⁻¹) y :=
    hlog.const_mul _
  have harg : HasDerivAt (fun y => 2 * t * Real.log y) (2 * t * y⁻¹) y := hlog.const_mul _
  have h2 : HasDerivAt (fun y => (b.re ^ 2 - b.im ^ 2) * Real.sin (2 * t * Real.log y) / (4 * t))
      ((b.re ^ 2 - b.im ^ 2) * (Real.cos (2 * t * Real.log y) * (2 * t * y⁻¹)) / (4 * t)) y :=
    (harg.sin.const_mul _).div_const _
  have h3 : HasDerivAt (fun y => b.re * b.im * (1 - Real.cos (2 * t * Real.log y)) / (2 * t))
      (b.re * b.im * (0 - (-Real.sin (2 * t * Real.log y) * (2 * t * y⁻¹))) / (2 * t)) y :=
    (((hasDerivAt_const y (1 : ℝ)).sub harg.cos).const_mul _).div_const _
  have h := (h1.add h2).sub h3
  have hpyth := Real.sin_sq_add_cos_sq (t * Real.log y)
  have hphase : lambdaPhase b t (Real.log y) ^ 2 =
      (b.re ^ 2 + b.im ^ 2) / 2 + (b.re ^ 2 - b.im ^ 2) / 2 * Real.cos (2 * t * Real.log y) -
        b.re * b.im * Real.sin (2 * t * Real.log y) := by
    rw [lambdaPhase_eq, show 2 * t * Real.log y = 2 * (t * Real.log y) by ring, Real.cos_two_mul,
      Real.sin_two_mul]
    linear_combination (b.im ^ 2) * hpyth
  refine h.congr_deriv ?_
  rw [hphase, Complex.sq_norm, Complex.normSq_apply]
  field_simp
  ring

theorem continuous_lambdaPhase_sq_div (b : ℂ) (t : ℝ) :
    ContinuousOn (fun y : ℝ => lambdaPhase b t (Real.log y) ^ 2 / y) (Ioi 0) := by
  simp_rw [lambdaPhase_eq]
  refine ContinuousOn.div ?_ continuousOn_id (fun y hy => (mem_Ioi.mp hy).ne')
  refine ContinuousOn.pow ?_ 2
  refine ContinuousOn.sub (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
  · exact Real.continuous_cos.comp_continuousOn
      (continuousOn_const.mul (Real.continuousOn_log.mono fun y hy => (mem_Ioi.mp hy).ne'))
  · exact Real.continuous_sin.comp_continuousOn
      (continuousOn_const.mul (Real.continuousOn_log.mono fun y hy => (mem_Ioi.mp hy).ne'))

/-- `∫_1^H lambdaPhase(log y)² / y dy ≥ (‖b‖²/2)(log H − 3/(2t))` for `t > 0`, `H ≥ 1`. -/
theorem integral_lambdaPhase_sq_div_ge (b : ℂ) {t : ℝ} (ht : 0 < t) {H : ℝ} (hH : 1 ≤ H) :
    (‖b‖ ^ 2 / 2) * (Real.log H - 3 / (2 * t)) ≤
      ∫ y in (1 : ℝ)..H, lambdaPhase b t (Real.log y) ^ 2 / y := by
  have hderiv : ∀ y ∈ uIcc (1 : ℝ) H, HasDerivAt (lambdaPhasePrimitive b t)
      (lambdaPhase b t (Real.log y) ^ 2 / y) y := by
    intro y hy
    rw [uIcc_of_le hH] at hy
    exact hasDerivAt_lambdaPhasePrimitive b ht.ne' (by linarith [hy.1])
  have hint : IntervalIntegrable (fun y => lambdaPhase b t (Real.log y) ^ 2 / y) volume 1 H := by
    refine ((continuous_lambdaPhase_sq_div b t).mono ?_).intervalIntegrable
    intro y hy
    rw [uIcc_of_le hH] at hy
    exact mem_Ioi.mpr (by linarith [hy.1])
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold lambdaPhasePrimitive
  simp only [Real.log_one, mul_zero, Real.sin_zero, Real.cos_zero, sub_self, zero_div, add_zero,
    sub_zero]
  have hb : b.re ^ 2 + b.im ^ 2 = ‖b‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs := Real.neg_one_le_sin (2 * t * Real.log H)
  have hs' := Real.sin_le_one (2 * t * Real.log H)
  have hc := Real.neg_one_le_cos (2 * t * Real.log H)
  have hc' := Real.cos_le_one (2 * t * Real.log H)
  have hre : b.re ^ 2 - b.im ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [sq_nonneg b.im]
  have hre' : -(‖b‖ ^ 2) ≤ b.re ^ 2 - b.im ^ 2 := by nlinarith [sq_nonneg b.re]
  have hri : b.re * b.im ≤ ‖b‖ ^ 2 / 2 := by nlinarith [sq_nonneg (b.re - b.im)]
  have hri' : -(‖b‖ ^ 2 / 2) ≤ b.re * b.im := by nlinarith [sq_nonneg (b.re + b.im)]
  have h4t : 0 < 4 * t := by positivity
  have h2t : 0 < 2 * t := by positivity
  -- the two oscillatory terms are bounded by `‖b‖²/(4t)` and `‖b‖²/(2t)`
  have hA : -(‖b‖ ^ 2 / (4 * t)) ≤ (b.re ^ 2 - b.im ^ 2) * Real.sin (2 * t * Real.log H) / (4 * t) := by
    rw [le_div_iff₀ h4t]
    have : -(‖b‖ ^ 2) ≤ (b.re ^ 2 - b.im ^ 2) * Real.sin (2 * t * Real.log H) := by
      nlinarith [mul_le_mul_of_nonneg_left hs' (sq_nonneg b.re), sq_nonneg b.im]
    calc -(‖b‖ ^ 2 / (4 * t)) * (4 * t) = -(‖b‖ ^ 2) := by field_simp
      _ ≤ _ := this
  have hB : b.re * b.im * (1 - Real.cos (2 * t * Real.log H)) / (2 * t) ≤ ‖b‖ ^ 2 / (2 * t) := by
    rw [div_le_div_iff_of_pos_right h2t]
    have h01 : 0 ≤ 1 - Real.cos (2 * t * Real.log H) := by linarith
    have h2 : 1 - Real.cos (2 * t * Real.log H) ≤ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hri h01]
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hkey : (‖b‖ ^ 2 / 2) * (Real.log H - 3 / (2 * t)) =
      (‖b‖ ^ 2 / 2) * Real.log H - ‖b‖ ^ 2 / (4 * t) - ‖b‖ ^ 2 / (2 * t) := by
    field_simp; ring
  linarith

/-- **Mean square of the constant term on `[1, e²]`:** for `t ≥ 2`,
`∫_1^{e²} ‖c(y)‖² / y² dy ≥ (5/2) ‖Λ(1+2it)‖²`. -/
theorem integral_normSq_eisLineConst_ge {t : ℝ} (ht : 2 ≤ t) :
    (5 / 2) * ‖eisLineLambda t‖ ^ 2 ≤
      ∫ y in (1 : ℝ)..Real.exp 2, ‖eisLineConst t y‖ ^ 2 / y ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hH : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hcongr : ∀ y ∈ uIcc (1 : ℝ) (Real.exp 2), ‖eisLineConst t y‖ ^ 2 / y ^ 2 =
      4 * (lambdaPhase (eisLineLambda t) t (Real.log y) ^ 2 / y) := by
    intro y hy
    rw [uIcc_of_le hH] at hy
    have hy0 : 0 < y := by linarith [hy.1]
    rw [normSq_eisLineConst_eq ht0.ne' hy0]
    unfold lambdaPhase
    field_simp
  rw [integral_congr hcongr, intervalIntegral.integral_const_mul]
  have h := integral_lambdaPhase_sq_div_ge (eisLineLambda t) ht0 hH
  rw [Real.log_exp] at h
  have h32 : 3 / (2 * t) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hb : 0 ≤ ‖eisLineLambda t‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h32 hb]

/-! ## The size of `Λ(1 + 2it)` -/

theorem norm_eisLineLambda_eq (t : ℝ) :
    ‖eisLineLambda t‖ = Real.pi ^ (-(1 / 2 : ℝ)) * ‖Complex.Gamma ((1 : ℂ) / 2 + t * I)‖ *
      ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ := by
  unfold eisLineLambda
  rw [reflectedCompletedLambda_eq, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
    Real.pi_pos]
  have e1 : (-(1 + 2 * ((t : ℂ) * I)) / 2).re = -(1 / 2 : ℝ) := by
    norm_num [Complex.div_re]
  have e2 : (1 + 2 * ((t : ℂ) * I)) / 2 = (1 : ℂ) / 2 + t * I := by ring
  rw [e1, e2]

/-- `‖Λ(1+2it)‖² = ‖ζ(1+2it)‖² / cosh(πt)`. -/
theorem normSq_eisLineLambda_eq (t : ℝ) :
    ‖eisLineLambda t‖ ^ 2 * Real.cosh (Real.pi * t) = ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ ^ 2 := by
  rw [norm_eisLineLambda_eq, mul_pow, mul_pow]
  have hG := norm_Gamma_half_add_sq t
  have hπ : (Real.pi ^ (-(1 / 2 : ℝ))) ^ 2 = Real.pi⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num [Real.rpow_neg_one]
  rw [hπ]
  calc Real.pi⁻¹ * ‖Complex.Gamma ((1 : ℂ) / 2 + t * I)‖ ^ 2 *
        ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ ^ 2 * Real.cosh (Real.pi * t)
      = Real.pi⁻¹ * (‖Complex.Gamma ((1 : ℂ) / 2 + t * I)‖ ^ 2 * Real.cosh (Real.pi * t)) *
        ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ ^ 2 := by ring
    _ = _ := by rw [hG]; field_simp

theorem cosh_le_exp_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- `‖Λ(1+2it)‖² ≥ e^{-πt} ‖ζ(1+2it)‖²` for `t ≥ 0`. -/
theorem normSq_eisLineLambda_ge {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(Real.pi * t)) * ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ ^ 2 ≤ ‖eisLineLambda t‖ ^ 2 := by
  have h := normSq_eisLineLambda_eq t
  have hc := cosh_le_exp_nonneg (x := Real.pi * t) (by positivity)
  have hcpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  rw [Real.exp_neg, ← h]
  have hb : 0 ≤ ‖eisLineLambda t‖ ^ 2 := by positivity
  calc (Real.exp (Real.pi * t))⁻¹ * (‖eisLineLambda t‖ ^ 2 * Real.cosh (Real.pi * t))
      ≤ (Real.cosh (Real.pi * t))⁻¹ * (‖eisLineLambda t‖ ^ 2 * Real.cosh (Real.pi * t)) := by
        gcongr
    _ = ‖eisLineLambda t‖ ^ 2 := by field_simp

/-! ## Continuity of the constant term in the height -/

theorem continuousOn_eisLineConst (t : ℝ) : ContinuousOn (eisLineConst t) (Ioi 0) := by
  have heq : eisLineConst t = fun Y : ℝ => reflectedCompletedLambda (2 * ((t : ℂ) * I)) *
      (Y : ℂ) ^ ((1 / 2 : ℂ) + (-1 : ℤ) * ((t : ℂ) * I)) +
        eisLineLambda t * (Y : ℂ) ^ ((1 / 2 : ℂ) + (1 : ℤ) * ((t : ℂ) * I)) :=
    funext (eisLineConst_eq t)
  rw [heq]
  have hc : ∀ w : ℂ, ContinuousOn (fun Y : ℝ => (Y : ℂ) ^ w) (Ioi 0) := by
    intro w Y hY
    have hslit : ((Y : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; show (0 : ℝ) < Y; exact mem_Ioi.mp hY
    exact ((continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  exact (continuousOn_const.mul (hc _)).add (continuousOn_const.mul (hc _))

end

end RHTower
