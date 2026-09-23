import GaloisForLFunctions.RHTower.SelbergThetaSourceVariance

/-!
# Quantitative energy of the actual theta zero mode

At every actual Xi divisor, the spectral-gauge mode energy lies strictly
between one and two source-mass units divided by the squared zero ordinate.
The proof retains the original theta source, establishes the first-moment
identities and vanishing endpoints, and uses strict logarithmic concavity
through an integrable centered covariance. A pointwise energy law places the
normalized mode/source ratio in a strict disk and proves positive phase current
after the required half-spectral gauge. No native occurrence is assumed.
-/

open Complex MeasureTheory Set Filter Topology
namespace RHTower.SelbergThetaSourceEnergy
noncomputable section
open SelbergThetaSourcePhase SelbergThetaSourceVariance

private def b (q : XiZeroCopy) : ℝ := (xiSpectralPoint q).re
private def c (q : XiZeroCopy) : ℝ := (xiSpectralPoint q).im
private def Q (x : ℝ) : ℝ := deriv thetaCuspLogSource x

private theorem c_strip (q : XiZeroCopy) : |c q| < 1 := by
  have h := xiSpectralPoint_im_mem_openHalf q
  rw [abs_lt]
  constructor <;> dsimp [c] <;> linarith

private theorem b_ne_zero (q : XiZeroCopy) : b q ≠ 0 := by
  simpa [b, xiSpectralPoint, Complex.mul_re, Complex.mul_im] using xi_divisor_support_im_ne_zero q.1

private def f (q : XiZeroCopy) : SchwartzMap ℝ ℝ :=
  thetaCuspTiltedSchwartzReal (-c q) (by simpa using c_strip q)

private def w (q : XiZeroCopy) (x : ℝ) : ℝ := weightedEnergy q (-c q) x
private def U (q : XiZeroCopy) (x : ℝ) : ℂ := weightedMode q (-c q) x

private theorem f_eq (q : XiZeroCopy) (x : ℝ) : f q x = tiltedSource (-c q) x := rfl

private theorem w_eq (q : XiZeroCopy) (x : ℝ) : w q x = f q x*‖sourceRatio q x‖^(2 : ℕ) := rfl

private theorem U_eq (q : XiZeroCopy) (x : ℝ) : U q x = (f q x:ℂ)*sourceRatio q x :=
  weightedMode_eq q (-c q) x

private def X (g : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x) g

private theorem X_apply (g : SchwartzMap ℝ ℝ) (x : ℝ) : X g x = x*g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) g x

private theorem ratio_mul_integrable (q : XiZeroCopy) (g : SchwartzMap ℝ ℝ) :
    Integrable (fun x => (g x:ℂ)*sourceRatio q x) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  exact g.integrable.ofReal.mul_bdd (continuous_sourceRatio q).aestronglyMeasurable
    (Eventually.of_forall hC)

private theorem ratio_sq_integrable (q : XiZeroCopy) (g : SchwartzMap ℝ ℝ) :
    Integrable (fun x => g x*‖sourceRatio q x‖^(2 : ℕ)) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  have hb : ∀ x, ‖‖sourceRatio q x‖^(2 : ℕ)‖ ≤ C^(2 : ℕ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  exact g.integrable.mul_bdd ((continuous_sourceRatio q).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall hb)

private theorem ratio_mul_tendsto (q : XiZeroCopy) (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun x => (g x:ℂ)*sourceRatio q x) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  apply squeeze_zero_norm (a := fun x => C*‖g x‖)
  · intro x
    rw [norm_mul, Complex.norm_real]
    nlinarith [hC x, norm_nonneg (g x)]
  · simpa using g.tendsto_cocompact.norm.const_mul C

private theorem ratio_sq_tendsto (q : XiZeroCopy) (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun x => g x*‖sourceRatio q x‖^(2 : ℕ)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  apply squeeze_zero_norm (a := fun x => C^(2 : ℕ)*‖g x‖)
  · intro x
    rw [norm_mul, Real.norm_eq_abs (‖sourceRatio q x‖^(2 : ℕ)), abs_of_nonneg (sq_nonneg _)]
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    nlinarith [norm_nonneg (g x)]
  · simpa using g.tendsto_cocompact.norm.const_mul (C^(2 : ℕ))

private theorem U_integrable (q : XiZeroCopy) : Integrable (U q) := by
  simpa only [← U_eq] using ratio_mul_integrable q (f q)

private theorem xU_integrable (q : XiZeroCopy) : Integrable (fun x : ℝ => (x:ℂ)*U q x) := by
  simpa only [X_apply, Complex.ofReal_mul, mul_assoc, ← U_eq] using ratio_mul_integrable q (X (f q))

private theorem w_integrable (q : XiZeroCopy) : Integrable (w q) := gauge_energy_integrable q

private theorem xw_integrable (q : XiZeroCopy) : Integrable (fun x : ℝ => x*w q x) := by
  simpa only [X_apply, mul_assoc, ← w_eq] using ratio_sq_integrable q (X (f q))

private theorem U_tendsto (q : XiZeroCopy) : Tendsto (U q) (cocompact ℝ) (𝓝 0) := by
  simpa only [← U_eq] using ratio_mul_tendsto q (f q)

private theorem xU_tendsto (q : XiZeroCopy) :
    Tendsto (fun x : ℝ => (x:ℂ)*U q x) (cocompact ℝ) (𝓝 0) := by
  simpa only [X_apply, Complex.ofReal_mul, mul_assoc, ← U_eq] using ratio_mul_tendsto q (X (f q))

private theorem xw_tendsto (q : XiZeroCopy) :
    Tendsto (fun x : ℝ => x*w q x) (cocompact ℝ) (𝓝 0) := by
  simpa only [X_apply, mul_assoc, ← w_eq] using ratio_sq_tendsto q (X (f q))

private theorem w_pos (q : XiZeroCopy) (x : ℝ) : 0 < w q x := by
  rw [w, weightedEnergy_eq]
  apply div_pos _ (thetaCuspFullSource_pos_all x)
  exact mul_pos (Real.exp_pos _) (sq_pos_of_pos (norm_pos_iff.mpr (mode_ne_zero q x)))

private theorem f_deriv (q : XiZeroCopy) (x : ℝ) : deriv (f q) x = (Q x-c q)*f q x := by
  have hp : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x :=
    thetaCuspSchwartzReal.hasDerivAt x
  have hraw := (((hasDerivAt_id x).const_mul (-c q)).exp).mul hp
  have h : HasDerivAt (f q)
      (Real.exp (-c q*x)*(-c q)*thetaCuspFullSource x + Real.exp (-c q*x)*deriv thetaCuspFullSource x) x := by
    have hf : (f q : ℝ → ℝ) = fun y => Real.exp (-c q*y)*thetaCuspFullSource y := by
      ext y
      rfl
    rw [hf]
    simpa using! hraw
  have hQ := (hasDerivAt_thetaCuspLogSource x).deriv
  simp only [iteratedDeriv_one] at hQ
  rw [h.deriv]
  dsimp [Q, f, thetaCuspTiltedSource]
  rw [hQ]
  field_simp [(thetaCuspFullSource_pos_all x).ne']
  ring

private theorem Qw_integrable (q : XiZeroCopy) : Integrable (fun x => Q x*w q x) :=
  gauge_current_integrable q

private theorem xQw_integrable (q : XiZeroCopy) : Integrable (fun x => x*(Q x*w q x)) := by
  have h := (ratio_sq_integrable q (X (SchwartzMap.derivCLM ℝ ℝ (f q)))).add
    ((xw_integrable q).const_mul (c q))
  apply h.congr
  filter_upwards with x
  change X (SchwartzMap.derivCLM ℝ ℝ (f q)) x*‖sourceRatio q x‖^(2 : ℕ)+c q*(x*w q x) = _
  rw [X_apply]
  change x*deriv (f q) x*‖sourceRatio q x‖^(2 : ℕ)+c q*(x*w q x) = _
  rw [f_deriv, w_eq]
  ring

private theorem U_deriv (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (U q) (-I*(b q:ℂ)*U q x-I*(f q x:ℂ)) x := by
  have h := weightedMode_hasDerivAt q (-c q) x
  have he : xiSpectralPoint q+I*(-c q:ℝ) = (b q:ℂ) := by
    apply Complex.ext <;> simp [b, c, Complex.mul_re, Complex.mul_im]
  rw [he] at h
  exact h

private theorem xU_deriv (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (x:ℂ)*U q x)
      (U q x-I*(b q:ℂ)*((x:ℂ)*U q x)-I*(X (f q) x:ℂ)) x := by
  have h := ((hasDerivAt_id x).ofReal_comp).mul (U_deriv q x)
  refine h.congr_deriv ?_
  rw [X_apply]
  simp only [id_eq]
  push_cast
  ring

private theorem xw_deriv (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (fun x : ℝ => x*w q x)
      (w q x - x*((Q x-c q)*w q x)-2*((x:ℂ)*U q x).im) x := by
  have hw := weightedEnergy_hasDerivAt q (-c q) x
  have h := (hasDerivAt_id x).mul hw
  refine h.congr_deriv ?_
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  dsimp [w, U, Q, c]
  ring

private theorem first_mode_moment (q : XiZeroCopy) :
    (∫ x : ℝ, (x:ℂ)*U q x).im = (∫ x, f q x)/(b q)^(2 : ℕ) := by
  have hu := U_integrable q
  have hxu := xU_integrable q
  have h0raw := integral_of_hasDerivAt_of_tendsto (U_deriv q)
    ((hu.const_mul (-I*(b q:ℂ))).sub ((f q).integrable.ofReal.const_mul I))
    ((U_tendsto q).mono_left atBot_le_cocompact)
    ((U_tendsto q).mono_left atTop_le_cocompact)
  have h0 : (∫ x, -I*(b q:ℂ)*U q x-I*(f q x:ℂ)) = 0 := by simpa using! h0raw
  have hs0 : (∫ x, -I*(b q:ℂ)*U q x-I*(f q x:ℂ)) =
      -I*(b q:ℂ)*(∫ x, U q x)-I*(∫ x, f q x:ℝ) := by
    have hs : (∫ x, -I*(b q:ℂ)*U q x-I*(f q x:ℂ)) =
        (∫ x, -I*(b q:ℂ)*U q x)-(∫ x, I*(f q x:ℂ)) := by
      simpa using! integral_sub (hu.const_mul (-I*(b q:ℂ))) ((f q).integrable.ofReal.const_mul I)
    rw [hs, integral_const_mul, integral_const_mul, integral_complex_ofReal]
  rw [hs0] at h0
  have h1raw := integral_of_hasDerivAt_of_tendsto (xU_deriv q)
    ((hu.sub (hxu.const_mul (I*(b q:ℂ)))).sub ((X (f q)).integrable.ofReal.const_mul I))
    ((xU_tendsto q).mono_left atBot_le_cocompact)
    ((xU_tendsto q).mono_left atTop_le_cocompact)
  have h1 : (∫ x : ℝ, U q x-I*(b q:ℂ)*((x:ℂ)*U q x)-I*(X (f q) x:ℂ)) = 0 := by
    simpa using! h1raw
  have hs1 : (∫ x : ℝ, U q x-I*(b q:ℂ)*((x:ℂ)*U q x)-I*(X (f q) x:ℂ)) =
      (∫ x, U q x)-I*(b q:ℂ)*(∫ x : ℝ, (x:ℂ)*U q x)-I*(∫ x, X (f q) x:ℝ) := by
    have hs : (∫ x : ℝ, U q x-I*(b q:ℂ)*((x:ℂ)*U q x)-I*(X (f q) x:ℂ)) =
        (∫ x : ℝ, U q x-I*(b q:ℂ)*((x:ℂ)*U q x))-(∫ x, I*(X (f q) x:ℂ)) := by
      simpa using! integral_sub (hu.sub (hxu.const_mul (I*(b q:ℂ))))
        ((X (f q)).integrable.ofReal.const_mul I)
    have ht : (∫ x : ℝ, U q x-I*(b q:ℂ)*((x:ℂ)*U q x)) =
        (∫ x, U q x)-(∫ x : ℝ, I*(b q:ℂ)*((x:ℂ)*U q x)) := by
      simpa using! integral_sub hu (hxu.const_mul (I*(b q:ℂ)))
    rw [hs, ht, integral_const_mul, integral_const_mul, integral_complex_ofReal]
  rw [hs1] at h1
  have hi := congrArg Complex.im h0
  have hr := congrArg Complex.re h1
  simp [Complex.mul_re, Complex.mul_im] at hi hr
  apply (eq_div_iff (pow_ne_zero 2 (b_ne_zero q))).2
  linear_combination hi+b q*hr

private def D (q : XiZeroCopy) (x : ℝ) : ℝ := x*((Q x-c q)*w q x)

private theorem D_integrable (q : XiZeroCopy) : Integrable (D q) := by
  have h := (xQw_integrable q).sub ((xw_integrable q).const_mul (c q))
  apply h.congr
  filter_upwards with x
  change x*(Q x*w q x)-c q*(x*w q x) = D q x
  dsimp [D]
  ring

private theorem moment_identity (q : XiZeroCopy) :
    (∫ x, D q x) = (∫ x, w q x)-2*(∫ x, f q x)/(b q)^(2 : ℕ) := by
  have hw := w_integrable q
  have hD := D_integrable q
  have hi := (xU_integrable q).im
  have hdRaw := integral_of_hasDerivAt_of_tendsto (xw_deriv q)
    ((hw.sub hD).sub (hi.const_mul 2))
    ((xw_tendsto q).mono_left atBot_le_cocompact)
    ((xw_tendsto q).mono_left atTop_le_cocompact)
  have hd : (∫ x : ℝ, w q x-D q x-2*((x:ℂ)*U q x).im) = 0 := by simpa using! hdRaw
  have hs : (∫ x : ℝ, w q x-D q x-2*((x:ℂ)*U q x).im) =
      (∫ x, w q x-D q x)-(∫ x : ℝ, 2*((x:ℂ)*U q x).im) := by
    simpa using! integral_sub (hw.sub hD) (hi.const_mul 2)
  have ht : (∫ x, w q x-D q x) = (∫ x, w q x)-(∫ x, D q x) := by
    simpa using! integral_sub hw hD
  rw [hs, ht, integral_const_mul] at hd
  have him := integral_im (𝕜 := ℂ) (xU_integrable q)
  change (∫ x : ℝ, ((x:ℂ)*U q x).im) = (∫ x : ℝ, (x:ℂ)*U q x).im at him
  rw [him, first_mode_moment] at hd
  rw [← mul_div_assoc] at hd
  linarith

private theorem Q_strictAnti : StrictAnti Q :=
  strictAntiOn_univ.mp <|
    strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv
      (fun x _ => (hasDerivAt_thetaCuspLogSource x).differentiableAt)

private theorem Q_continuous : Continuous Q :=
  contDiff_thetaCuspLogSource.continuous_deriv (by simp)

private def center (q : XiZeroCopy) : ℝ := (∫ x, x*w q x)/(∫ x, w q x)

private def cx (q : XiZeroCopy) (x : ℝ) : ℝ := (x-center q)*w q x
private def cq (q : XiZeroCopy) (x : ℝ) : ℝ := (Q x-c q)*w q x

private theorem cx_integrable (q : XiZeroCopy) : Integrable (cx q) := by
  apply ((xw_integrable q).sub ((w_integrable q).const_mul (center q))).congr
  filter_upwards with x
  change x*w q x-center q*w q x = cx q x
  simp only [cx, sub_mul]

private theorem cq_integrable (q : XiZeroCopy) : Integrable (cq q) := by
  apply ((Qw_integrable q).sub ((w_integrable q).const_mul (c q))).congr
  filter_upwards with x
  change Q x*w q x-c q*w q x = cq q x
  simp only [cq, sub_mul]

private theorem integral_cx (q : XiZeroCopy) : (∫ x, cx q x) = 0 := by
  have hm : 0 < ∫ x, w q x := gauge_energy_pos q
  have hs : (∫ x, cx q x) = (∫ x, x*w q x)-(∫ x, center q*w q x) := by
    simpa only [cx, sub_mul] using! integral_sub (xw_integrable q) ((w_integrable q).const_mul (center q))
  rw [hs, integral_const_mul]
  dsimp [center]
  field_simp
  ring

private theorem integral_cq (q : XiZeroCopy) : (∫ x, cq q x) = 0 := by
  have hb : (∫ x, Q x*w q x) = c q*(∫ x, w q x) := gauge_source_balance q
  have hs : (∫ x, cq q x) = (∫ x, Q x*w q x)-(∫ x, c q*w q x) := by
    simpa only [cq, sub_mul] using! integral_sub (Qw_integrable q) ((w_integrable q).const_mul (c q))
  rw [hs, integral_const_mul, hb, sub_self]

private def covarianceDensity (q : XiZeroCopy) (x : ℝ) : ℝ :=
  -(x-center q)*(Q x-Q (center q))*w q x

private theorem covariance_split (q : XiZeroCopy) (x : ℝ) : covarianceDensity q x =
    -D q x + (Q (center q)-c q)*cx q x+center q*cq q x := by
  dsimp [covarianceDensity, D, cx, cq]
  ring

private theorem covariance_integrable (q : XiZeroCopy) : Integrable (covarianceDensity q) := by
  have h := ((D_integrable q).neg.add ((cx_integrable q).const_mul (Q (center q)-c q))).add
    ((cq_integrable q).const_mul (center q))
  apply h.congr
  filter_upwards with x
  exact (covariance_split q x).symm

private theorem covariance_nonneg (q : XiZeroCopy) (x : ℝ) : 0 ≤ covarianceDensity q x := by
  unfold covarianceDensity
  apply mul_nonneg _ (w_pos q x).le
  rcases le_total x (center q) with h | h
  · exact mul_nonneg (by linarith) (sub_nonneg.mpr (Q_strictAnti.antitone h))
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (sub_nonpos.mpr (Q_strictAnti.antitone h))

private theorem covariance_pos (q : XiZeroCopy) : 0 < ∫ x, covarianceDensity q x := by
  have hw : Continuous (w q) := (f q).continuous.mul ((continuous_sourceRatio q).norm.pow 2)
  have hc : Continuous (covarianceDensity q) :=
    ((continuous_id.sub continuous_const).neg.mul (Q_continuous.sub continuous_const)).mul hw
  rw [integral_pos_iff_support_of_nonneg (covariance_nonneg q) (covariance_integrable q)]
  apply IsOpen.measure_pos volume hc.isOpen_support
  refine ⟨center q+1, ?_⟩
  have hn : Q (center q+1) < Q (center q) := Q_strictAnti (by linarith)
  have hp : 0 < covarianceDensity q (center q+1) := by
    dsimp [covarianceDensity]
    apply mul_pos _ (w_pos q _)
    exact mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr hn)
  exact hp.ne'

private theorem integral_covariance (q : XiZeroCopy) :
    (∫ x, covarianceDensity q x) = -(∫ x, D q x) := by
  have hs : (∫ x, covarianceDensity q x) =
      (∫ x, -D q x+(Q (center q)-c q)*cx q x)+(∫ x, center q*cq q x) := by
    simpa only [covariance_split] using! integral_add
      ((D_integrable q).neg.add ((cx_integrable q).const_mul (Q (center q)-c q)))
      ((cq_integrable q).const_mul (center q))
  have ht : (∫ x, -D q x+(Q (center q)-c q)*cx q x) =
      (∫ x, -D q x)+(∫ x, (Q (center q)-c q)*cx q x) := by
    simpa using! integral_add (D_integrable q).neg ((cx_integrable q).const_mul (Q (center q)-c q))
  rw [hs, ht, integral_neg, integral_const_mul, integral_const_mul, integral_cx, integral_cq]
  ring

/-- Exact first imaginary moment of the actual mode in the spectral gauge. -/
theorem gauge_first_mode_moment (q : XiZeroCopy) :
    (∫ x : ℝ, (x:ℂ)*weightedMode q (-(xiSpectralPoint q).im) x).im =
      (∫ x, tiltedSource (-(xiSpectralPoint q).im) x)/(xiSpectralPoint q).re^(2 : ℕ) :=
  first_mode_moment q

/-- The gauge energy lies strictly above source mass divided by the squared ordinate. -/
theorem gauge_energy_lower (q : XiZeroCopy) :
    (∫ x, tiltedSource (-(xiSpectralPoint q).im) x)/(xiSpectralPoint q).re^(2 : ℕ) <
      ∫ x, weightedEnergy q (-(xiSpectralPoint q).im) x := by
  let a : Ioo (-1:ℝ) 1 := ⟨-c q, by have h := abs_lt.mp (c_strip q); constructor <;> linarith⟩
  have h := tilted_energy_strict_floor q a
  have he : xiSpectralPoint q+I*(a.val:ℂ) = (b q:ℂ) := by
    apply Complex.ext <;> simp [a, b, c, Complex.mul_re, Complex.mul_im]
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- Strict theta curvature bounds actual gauge energy by twice the source mass scale. -/
theorem gauge_energy_upper (q : XiZeroCopy) :
    (∫ x, weightedEnergy q (-(xiSpectralPoint q).im) x) <
      2*(∫ x, tiltedSource (-(xiSpectralPoint q).im) x)/(xiSpectralPoint q).re^(2 : ℕ) := by
  have hp := covariance_pos q
  rw [integral_covariance, moment_identity] at hp
  change (∫ x, w q x) < 2*(∫ x, f q x)/(b q)^(2 : ℕ)
  linarith

private def H (q : XiZeroCopy) (x : ℝ) : ℝ := w q x+(2/b q)*(U q x).re

private theorem H_deriv (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (H q) ((c q-Q x)*w q x) x := by
  have hr : HasDerivAt (fun x => (U q x).re) (-I*(b q:ℂ)*U q x-I*(f q x:ℂ)).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (U_deriv q x)
  have h := (weightedEnergy_hasDerivAt q (-c q) x).add (hr.const_mul (2/b q))
  refine h.congr_deriv ?_
  dsimp [c, Q, w, U]
  simp [Complex.mul_re, Complex.mul_im]
  field_simp [b_ne_zero q]
  ring

private theorem H_tendsto (q : XiZeroCopy) : Tendsto (H q) (cocompact ℝ) (𝓝 0) := by
  have hw : Tendsto (w q) (cocompact ℝ) (𝓝 0) := by
    simpa only [← w_eq] using ratio_sq_tendsto q (f q)
  have hu := (Complex.continuous_re.tendsto (0:ℂ)).comp (U_tendsto q)
  have hh := hw.add (hu.const_mul (2/b q))
  simpa [H] using! hh

private theorem H_neg (q : XiZeroCopy) (x : ℝ) : H q x < 0 := by
  rcases le_total (c q) (Q x) with hx | hx
  · have ha : StrictAntiOn (H q) (Iic x) := by
      apply strictAntiOn_of_deriv_neg (convex_Iic x)
      · exact fun y _ => (H_deriv q y).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Iic] at hy
        rw [(H_deriv q y).deriv]
        exact mul_neg_of_neg_of_pos (by linarith [Q_strictAnti hy]) (w_pos q y)
    have hn : H q (x-1) ≤ 0 := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds ((H_tendsto q).mono_left atBot_le_cocompact)
      filter_upwards [eventually_le_atBot (x-1)] with y hy
      exact ha.antitoneOn (by change y ≤ x; linarith) (by change x-1 ≤ x; linarith) hy
    exact lt_of_lt_of_le (ha (by change x-1 ≤ x; linarith) (mem_Iic.mpr le_rfl) (by linarith)) hn
  · have hm : StrictMonoOn (H q) (Ici x) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici x)
      · exact fun y _ => (H_deriv q y).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        rw [(H_deriv q y).deriv]
        exact mul_pos (by linarith [Q_strictAnti hy]) (w_pos q y)
    have hn : H q (x+1) ≤ 0 := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds ((H_tendsto q).mono_left atTop_le_cocompact)
      filter_upwards [eventually_ge_atTop (x+1)] with y hy
      exact hm.monotoneOn (by change x ≤ x+1; linarith) (by change x ≤ y; linarith) hy
    exact lt_of_lt_of_le (hm (mem_Ici.mpr le_rfl) (by change x ≤ x+1; linarith) (by linarith)) hn

private theorem ratio_disk_quadratic (q : XiZeroCopy) (x : ℝ) :
    (b q)^(2 : ℕ)*‖sourceRatio q x‖^(2 : ℕ)+2*b q*(sourceRatio q x).re < 0 := by
  have hn := H_neg q x
  rw [H, w_eq, U_eq] at hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hn
  have hf : 0 < f q x := mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
  have he : f q x*‖sourceRatio q x‖^(2 : ℕ)+(2/b q)*(f q x*(sourceRatio q x).re) =
      f q x*(‖sourceRatio q x‖^(2 : ℕ)+(2/b q)*(sourceRatio q x).re) := by ring
  rw [he] at hn
  have hh : ‖sourceRatio q x‖^(2 : ℕ)+(2/b q)*(sourceRatio q x).re < 0 := by nlinarith
  have hp := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (b_ne_zero q)) hh
  have hb : (b q)^(2 : ℕ)*(‖sourceRatio q x‖^(2 : ℕ)+(2/b q)*(sourceRatio q x).re) =
      (b q)^(2 : ℕ)*‖sourceRatio q x‖^(2 : ℕ)+2*b q*(sourceRatio q x).re := by
    field_simp [b_ne_zero q]
  rwa [hb] at hp

/-- The actual normalized source ratio lies in the open disk centered at minus one. -/
theorem source_ratio_strict_disk (q : XiZeroCopy) (x : ℝ) :
    ‖1+((xiSpectralPoint q).re:ℂ)*sourceRatio q x‖ < 1 := by
  have hn := ratio_disk_quadratic q x
  have he : ‖1+(b q:ℂ)*sourceRatio q x‖^(2 : ℕ) =
      1+(b q)^(2 : ℕ)*‖sourceRatio q x‖^(2 : ℕ)+2*b q*(sourceRatio q x).re := by
    simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  change ‖1+(b q:ℂ)*sourceRatio q x‖ < 1
  nlinarith [norm_nonneg (1+(b q:ℂ)*sourceRatio q x)]

private theorem mode_energy_pointwise (q : XiZeroCopy) (x : ℝ) :
    (b q)^(2 : ℕ)*‖mode q x‖^(2 : ℕ) < -2*b q*thetaCuspFullSource x*(mode q x).re := by
  have hp : 0 < (b q)^(2 : ℕ)*thetaCuspFullSource x/Real.exp (-c q*x) :=
    div_pos (mul_pos (sq_pos_of_ne_zero (b_ne_zero q)) (thetaCuspFullSource_pos_all x)) (Real.exp_pos _)
  have hn := mul_neg_of_neg_of_pos (H_neg q x) hp
  have he : H q x*((b q)^(2 : ℕ)*thetaCuspFullSource x/Real.exp (-c q*x)) =
      (b q)^(2 : ℕ)*‖mode q x‖^(2 : ℕ)+2*b q*thetaCuspFullSource x*(mode q x).re := by
    rw [H, w, weightedEnergy_eq]
    dsimp [U, weightedMode]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp [b_ne_zero q, (thetaCuspFullSource_pos_all x).ne', (Real.exp_pos (-c q*x)).ne']
  rw [he] at hn
  linarith

/-- The phase current stays strictly positive after the half-spectral gauge required by the operator. -/
theorem gauge_phase_current_pos (q : XiZeroCopy) (x : ℝ) :
    0 < (xiSpectralPoint q).re*((modeLogDerivative q x).im+(xiSpectralPoint q).re/2) := by
  have hn := mode_energy_pointwise q x
  have hm : 0 < Complex.normSq (mode q x) := Complex.normSq_pos.mpr (mode_ne_zero q x)
  have hc := mode_phase_current q x
  have he : (positiveMode q x).re = -b q*(mode q x).re := by
    simp [positiveMode, b, Complex.mul_re]
  rw [he] at hc
  have hb : (b q)^(2 : ℕ)/2 < (-b q*(mode q x).re)*thetaCuspFullSource x/Complex.normSq (mode q x) := by
    apply (lt_div_iff₀ hm).2
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [← hc] at hb
  dsimp [b] at hb
  nlinarith

end
end RHTower.SelbergThetaSourceEnergy
