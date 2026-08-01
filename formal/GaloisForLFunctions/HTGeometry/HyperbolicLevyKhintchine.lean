import GaloisForLFunctions.HTGeometry.CoshFourierTransform
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory Complex


namespace HTGeometry

noncomputable section

theorem transform_sech_sq (x : ℝ) :
    (∫ t : ℝ, (((Real.cosh t) ^ (-2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I)) =
      if x = 0 then 2 else
        ((Real.pi * |x| / |Real.sinh (Real.pi * x / 2)| : ℝ) : ℂ) := by
  rw [integral_cosh_rpow_neg_mul_exp_eq_ofReal (by norm_num : (0 : ℝ) < 2)]
  by_cases hx : x = 0
  · subst x
    norm_num [Real.Gamma_two, Real.rpow_one]
  · rw [if_neg hx]
    norm_num [Real.Gamma_two]
    rw [show (((2 : ℂ) + (x : ℂ) * Complex.I) / 2) =
        1 + ((x / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    have hx2 : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
    rw [Complex.normSq_eq_norm_sq]
    rw [GaloisForLFunctions.HTGeometry.norm_Gamma_one_add_I_sq hx2]
    norm_cast
    have hs : Real.sinh (Real.pi * (x / 2)) =
        Real.sinh (Real.pi * x / 2) := by congr 1 <;> ring
    rw [hs]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    push_cast
    ring_nf

open FourierTransform FourierTransformInv

def sechSq (t : ℝ) : ℂ :=
  ((Real.cosh t ^ (-2 : ℝ) : ℝ) : ℂ)

def sechSqDeriv (t : ℝ) : ℂ :=
  ((-2 * Real.cosh t ^ (-3 : ℝ) * Real.sinh t : ℝ) : ℂ)

def sechSqDeriv2 (t : ℝ) : ℂ :=
  ((4 * Real.cosh t ^ (-2 : ℝ) - 6 * Real.cosh t ^ (-4 : ℝ) : ℝ) : ℂ)

theorem hasDerivAt_sechSqReal (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cosh u ^ (-2 : ℝ))
      (-2 * Real.cosh t ^ (-3 : ℝ) * Real.sinh t) t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h := (Real.hasDerivAt_cosh t).rpow_const (p := (-2 : ℝ)) (Or.inl hc.ne')
  have hval : Real.sinh t * (-2) * Real.cosh t ^ ((-2 : ℝ) - 1) =
      -2 * Real.cosh t ^ (-3 : ℝ) * Real.sinh t := by
    rw [show ((-2 : ℝ) - 1) = -3 by norm_num]
    ring
  rwa [hval] at h

theorem hasDerivAt_sechSqDerivReal (t : ℝ) :
    HasDerivAt (fun u : ℝ => -2 * Real.cosh u ^ (-3 : ℝ) * Real.sinh u)
      (4 * Real.cosh t ^ (-2 : ℝ) - 6 * Real.cosh t ^ (-4 : ℝ)) t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h1 := (Real.hasDerivAt_cosh t).rpow_const (p := (-3 : ℝ)) (Or.inl hc.ne')
  have h2 := (h1.const_mul (-2 : ℝ)).mul (Real.hasDerivAt_sinh t)
  have e2 : Real.cosh t ^ (-3 : ℝ) * Real.cosh t = Real.cosh t ^ (-2 : ℝ) := by
    nth_rewrite 2 [show Real.cosh t = Real.cosh t ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hc]
    norm_num
  have e4 : Real.cosh t ^ (-4 : ℝ) * Real.cosh t ^ (2 : ℝ) =
      Real.cosh t ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hc]
    norm_num
  have hsq : Real.cosh t ^ (2 : ℝ) = Real.cosh t ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have esinh : Real.sinh t ^ 2 = Real.cosh t ^ 2 - 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq t]
  have hkey : Real.cosh t ^ (-4 : ℝ) * Real.sinh t ^ 2 =
      Real.cosh t ^ (-2 : ℝ) - Real.cosh t ^ (-4 : ℝ) := by
    rw [esinh, mul_sub, mul_one, ← hsq, e4]
  have hval :
      -2 * (Real.sinh t * (-3) * Real.cosh t ^ ((-3 : ℝ) - 1)) * Real.sinh t +
          -2 * Real.cosh t ^ (-3 : ℝ) * Real.cosh t =
        4 * Real.cosh t ^ (-2 : ℝ) - 6 * Real.cosh t ^ (-4 : ℝ) := by
    rw [show ((-3 : ℝ) - 1) = -4 by norm_num]
    linear_combination 6 * hkey - 2 * e2
  rwa [hval] at h2

theorem hasDerivAt_sechSq (t : ℝ) :
    HasDerivAt sechSq (sechSqDeriv t) t :=
  (hasDerivAt_sechSqReal t).ofReal_comp

theorem hasDerivAt_sechSqDeriv (t : ℝ) :
    HasDerivAt sechSqDeriv (sechSqDeriv2 t) t :=
  (hasDerivAt_sechSqDerivReal t).ofReal_comp

theorem differentiable_sechSq : Differentiable ℝ sechSq :=
  fun t => (hasDerivAt_sechSq t).differentiableAt

theorem differentiable_sechSqDeriv : Differentiable ℝ sechSqDeriv :=
  fun t => (hasDerivAt_sechSqDeriv t).differentiableAt

theorem deriv_sechSq : deriv sechSq = sechSqDeriv :=
  funext fun t => (hasDerivAt_sechSq t).deriv

theorem deriv_sechSqDeriv : deriv sechSqDeriv = sechSqDeriv2 :=
  funext fun t => (hasDerivAt_sechSqDeriv t).deriv

theorem integrable_sechSq : Integrable sechSq := by
  have h := integrable_cosh_rpow_neg (s := (2 : ℝ)) (by norm_num)
  exact h.ofReal.congr (by filter_upwards with t using rfl)

theorem integrable_sechSqDeriv : Integrable sechSqDeriv := by
  have hbase := (integrable_cosh_rpow_neg (s := (2 : ℝ)) (by norm_num)).const_mul 2
  refine hbase.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous fun t : ℝ => Real.cosh t ^ (-3 : ℝ) :=
      Real.continuous_cosh.rpow_const fun x => Or.inl (Real.cosh_pos x).ne'
    exact Complex.continuous_ofReal.comp ((h1.const_mul _).mul Real.continuous_sinh)
  · filter_upwards with t
    have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
    have habs : |Real.sinh t| ≤ Real.cosh t := by
      nlinarith [Real.cosh_sq_sub_sinh_sq t, sq_abs (Real.sinh t),
        abs_nonneg (Real.sinh t)]
    have e2 : Real.cosh t ^ (-3 : ℝ) * Real.cosh t = Real.cosh t ^ (-2 : ℝ) := by
      nth_rewrite 2 [show Real.cosh t = Real.cosh t ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hc]
      norm_num
    have hpow : (0 : ℝ) < Real.cosh t ^ (-3 : ℝ) := Real.rpow_pos_of_pos hc _
    rw [sechSqDeriv, Complex.norm_real, Real.norm_eq_abs]
    calc
      |(-2 * Real.cosh t ^ (-3 : ℝ) * Real.sinh t)| =
          2 * Real.cosh t ^ (-3 : ℝ) * |Real.sinh t| := by
        rw [abs_mul, abs_mul, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0), abs_of_pos hpow]
        ring
      _ ≤ 2 * Real.cosh t ^ (-3 : ℝ) * Real.cosh t := by gcongr
      _ = 2 * Real.cosh t ^ (-2 : ℝ) := by rw [mul_assoc, e2]

theorem integrable_sechSqDeriv2 : Integrable sechSqDeriv2 := by
  have h1 := (integrable_cosh_rpow_neg (s := (2 : ℝ)) (by norm_num)).const_mul 4
  have h2 := (integrable_cosh_rpow_neg (s := (4 : ℝ)) (by norm_num)).const_mul 6
  exact (h1.sub h2).ofReal.congr (by filter_upwards with t using rfl)

theorem fourier_sechSqDeriv2 (x : ℝ) :
    𝓕 sechSqDeriv2 x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2 * 𝓕 sechSq x := by
  have h1 := Real.fourier_deriv integrable_sechSq differentiable_sechSq
    (by rw [deriv_sechSq]; exact integrable_sechSqDeriv)
  have h2 := Real.fourier_deriv integrable_sechSqDeriv
    differentiable_sechSqDeriv
    (by rw [deriv_sechSqDeriv]; exact integrable_sechSqDeriv2)
  rw [deriv_sechSq] at h1
  rw [deriv_sechSqDeriv] at h2
  have e2 : 𝓕 sechSqDeriv2 x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • 𝓕 sechSqDeriv x := by
    rw [h2]
  have e1 : 𝓕 sechSqDeriv x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • 𝓕 sechSq x := by
    rw [h1]
  rw [e2, e1, smul_eq_mul, smul_eq_mul]
  ring

theorem integrable_fourier_sechSq : Integrable (𝓕 sechSq) := by
  have hA : (0 : ℝ) ≤ ∫ t : ℝ, ‖sechSq t‖ :=
    integral_nonneg fun t => norm_nonneg _
  have hB : (0 : ℝ) ≤ ∫ t : ℝ, ‖sechSqDeriv2 t‖ :=
    integral_nonneg fun t => norm_nonneg _
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hbound : ∀ x : ℝ, ‖𝓕 sechSq x‖ ≤
      2 * ((∫ t : ℝ, ‖sechSq t‖) +
        ∫ t : ℝ, ‖sechSqDeriv2 t‖) * (1 + x ^ 2)⁻¹ := by
    intro x
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hN : (0 : ℝ) ≤ ‖𝓕 sechSq x‖ := norm_nonneg _
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    by_cases hx : x ^ 2 ≤ 1
    · have h1 : ‖𝓕 sechSq x‖ ≤ ∫ t : ℝ, ‖sechSq t‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      nlinarith [h1, hA, hB, hN]
    · have hx' : 1 < x ^ 2 := not_le.mp hx
      have heq := fourier_sechSqDeriv2 x
      have hval : ‖(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2‖ =
          4 * Real.pi ^ 2 * x ^ 2 := by
        rw [norm_pow]
        simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_ofNat]
        rw [abs_of_pos Real.pi_pos, mul_pow, mul_pow, sq_abs]
        ring
      have hle : ‖𝓕 sechSqDeriv2 x‖ ≤
          ∫ t : ℝ, ‖sechSqDeriv2 t‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      rw [heq, norm_mul, hval] at hle
      have hstep1 : ‖𝓕 sechSq x‖ * x ^ 2 ≤
          ‖𝓕 sechSq x‖ * x ^ 2 * (4 * Real.pi ^ 2) := by
        have := mul_le_mul_of_nonneg_left hpi (by positivity :
          0 ≤ ‖𝓕 sechSq x‖ * x ^ 2)
        nlinarith
      have hstep2 : ‖𝓕 sechSq x‖ * x ^ 2 ≤
          ∫ t : ℝ, ‖sechSqDeriv2 t‖ := by nlinarith
      have hprod : 0 ≤ ‖𝓕 sechSq x‖ * (x ^ 2 - 1) :=
        mul_nonneg hN (by linarith)
      nlinarith
  refine Integrable.mono' (g := fun x : ℝ =>
    2 * ((∫ t : ℝ, ‖sechSq t‖) +
      ∫ t : ℝ, ‖sechSqDeriv2 t‖) * (1 + x ^ 2)⁻¹) ?_ ?_
      (Filter.Eventually.of_forall hbound)
  · exact integrable_inv_one_add_sq.const_mul _
  · refine (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
      integrable_sechSq).aestronglyMeasurable
    fun_prop

theorem fourierInv_fourier_sechSq : 𝓕⁻ (𝓕 sechSq) = sechSq := by
  exact differentiable_sechSq.continuous.fourierInv_fourier_eq
      integrable_sechSq integrable_fourier_sechSq

def sechSqDensity (x : ℝ) : ℝ :=
  if x = 0 then 2 else
    2 * Real.pi ^ 2 * |x| / |Real.sinh (Real.pi ^ 2 * x)|

theorem fourier_sechSq_apply (x : ℝ) :
    𝓕 sechSq x = ((sechSqDensity x : ℝ) : ℂ) := by
  rw [Real.fourier_eq]
  have hcongr : ∀ v : ℝ, (𝐞 (-(inner ℝ v x)) • sechSq v) =
      (((Real.cosh v) ^ (-2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ)) * Complex.I) := by
    intro v
    have hexp : ((2 * Real.pi * (-(v * x)) : ℝ) : ℂ) * Complex.I =
        -(((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      hexp, sechSq, mul_comm]
  simp_rw [hcongr]
  rw [transform_sech_sq (2 * Real.pi * x)]
  rw [sechSqDensity]
  by_cases hx : x = 0
  · subst x
    simp
  · rw [if_neg hx, if_neg (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)]
    norm_cast
    congr 1
    · rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      ring
    · congr 2
      ring

theorem integrable_sechSqDensity : Integrable sechSqDensity := by
  have h := integrable_fourier_sechSq.re
  refine h.congr ?_
  filter_upwards with x
  rw [fourier_sechSq_apply]
  simp

theorem integral_exp_mul_sechSqDensity (h : ℝ) :
    (∫ x : ℝ, Complex.exp (((2 * Real.pi * (x * h) : ℝ) : ℂ) * Complex.I) *
        ((sechSqDensity x : ℝ) : ℂ)) =
      ((Real.cosh h ^ (-2 : ℝ) : ℝ) : ℂ) := by
  have hinv := congrFun fourierInv_fourier_sechSq h
  rw [Real.fourierInv_eq] at hinv
  have hcongr : ∀ x : ℝ, (𝐞 (inner ℝ x h) • 𝓕 sechSq x) =
      Complex.exp (((2 * Real.pi * (x * h) : ℝ) : ℂ) * Complex.I) *
        ((sechSqDensity x : ℝ) : ℂ) := by
    intro x
    rw [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      fourier_sechSq_apply]
  simp_rw [hcongr] at hinv
  rw [hinv, sechSq]

theorem integrable_cos_mul_sechSqDensity (a : ℝ) :
    Integrable fun x : ℝ => Real.cos (2 * Real.pi * (x * a)) * sechSqDensity x := by
  refine Integrable.mono' (g := fun x => |sechSqDensity x|)
    integrable_sechSqDensity.abs ?_ ?_
  · exact ((Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable).mul
      integrable_sechSqDensity.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [Real.abs_cos_le_one (2 * Real.pi * (x * a)),
      abs_nonneg (sechSqDensity x)]

theorem integral_cos_mul_sechSqDensity (a : ℝ) :
    (∫ x : ℝ, Real.cos (2 * Real.pi * (x * a)) * sechSqDensity x) =
      Real.cosh a ^ (-2 : ℝ) := by
  have hint : Integrable fun x : ℝ =>
      Complex.exp (((2 * Real.pi * (x * a) : ℝ) : ℂ) * Complex.I) *
        ((sechSqDensity x : ℝ) : ℂ) := by
    refine Integrable.mono' (g := fun x => |sechSqDensity x|)
      integrable_sechSqDensity.abs ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable
          integrable_sechSqDensity.aestronglyMeasurable)
      exact Complex.continuous_exp.comp (by fun_prop)
    · filter_upwards with x
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
  have hre := Complex.reCLM.integral_comp_comm hint
  rw [integral_exp_mul_sechSqDensity a] at hre
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  rw [← hre]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]

theorem sechSqDensity_neg (x : ℝ) :
    sechSqDensity (-x) = sechSqDensity x := by
  unfold sechSqDensity
  by_cases hx : x = 0
  · subst x
    simp
  · simp [hx, Real.sinh_neg]

theorem sechSqDensity_abs (x : ℝ) :
    sechSqDensity |x| = sechSqDensity x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, sechSqDensity_neg]

theorem integral_Ioi_cos_mul_sechSqDensity (a : ℝ) :
    (∫ x : ℝ in Set.Ioi 0,
        Real.cos (2 * Real.pi * (x * a)) * sechSqDensity x) =
      (1 / 2 : ℝ) * Real.cosh a ^ (-2 : ℝ) := by
  let f : ℝ → ℝ := fun r =>
    Real.cos (2 * Real.pi * (r * a)) * sechSqDensity r
  have hpoint : (fun x : ℝ =>
      Real.cos (2 * Real.pi * (x * a)) * sechSqDensity x) =
      fun x => f |x| := by
    funext x
    dsimp [f]
    rw [sechSqDensity_abs]
    congr 1
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      rw [show 2 * Real.pi * (-x * a) = -(2 * Real.pi * (x * a)) by ring,
        Real.cos_neg]
  have hwhole := integral_cos_mul_sechSqDensity a
  rw [hpoint, integral_comp_abs] at hwhole
  dsimp [f] at hwhole
  linarith

theorem integral_t_cos_div_sinh_base (y : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
        t * Real.cos (t * y) / Real.sinh (Real.pi * t / 2)) =
      Real.cosh y ^ (-2 : ℝ) := by
  let g : ℝ → ℝ := fun t =>
    t * Real.cos (t * y) / Real.sinh (Real.pi * t / 2)
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi g (0 : ℝ)
    (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have hhalf := integral_Ioi_cos_mul_sechSqDensity y
  have hpoint : ∀ x ∈ Set.Ioi (0 : ℝ),
      Real.cos (2 * Real.pi * (x * y)) * sechSqDensity x =
        Real.pi * g (2 * Real.pi * x) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.ne'
    rw [sechSqDensity, if_neg hx0, abs_of_pos hx]
    have hspos : 0 < Real.sinh (Real.pi ^ 2 * x) :=
      (Real.sinh_pos_iff.mpr (mul_pos (sq_pos_of_pos Real.pi_pos) hx))
    rw [abs_of_pos hspos]
    dsimp [g]
    have hcos : Real.cos (2 * Real.pi * (x * y)) =
        Real.cos ((2 * Real.pi * x) * y) := by congr 1 <;> ring
    have hs : Real.sinh (Real.pi ^ 2 * x) =
        Real.sinh (Real.pi * (2 * Real.pi * x) / 2) := by congr 1 <;> ring
    rw [hcos, hs]
    field_simp
  have hhalf' : (∫ x : ℝ in Set.Ioi 0, Real.pi * g (2 * Real.pi * x)) =
      (1 / 2 : ℝ) * Real.cosh y ^ (-2 : ℝ) := by
    calc
      _ = ∫ x : ℝ in Set.Ioi 0,
          Real.cos (2 * Real.pi * (x * y)) * sechSqDensity x :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => (hpoint x hx).symm
      _ = _ := hhalf
  rw [MeasureTheory.integral_const_mul, hscale] at hhalf'
  simp only [smul_eq_mul, mul_zero] at hhalf'
  have hcoeff : Real.pi * (2 * Real.pi)⁻¹ = (1 / 2 : ℝ) := by
    field_simp
  rw [← mul_assoc, hcoeff] at hhalf'
  linarith

theorem integral_t_cos_div_sinh {a y : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi 0,
        t * Real.cos (t * y) / Real.sinh (Real.pi * t / (2 * a))) =
      a ^ 2 * Real.cosh (a * y) ^ (-2 : ℝ) := by
  let f : ℝ → ℝ := fun t =>
    t * Real.cos (t * y) / Real.sinh (Real.pi * t / (2 * a))
  let g : ℝ → ℝ := fun s =>
    s * Real.cos (s * (a * y)) / Real.sinh (Real.pi * s / 2)
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi f (0 : ℝ) ha
  have hpoint : ∀ s : ℝ, f (a * s) = a * g s := by
    intro s
    dsimp [f, g]
    have harg : Real.pi * (a * s) / (2 * a) = Real.pi * s / 2 := by
      field_simp [ha.ne']
    rw [harg]
    ring
  have hleft : (∫ s : ℝ in Set.Ioi 0, f (a * s)) =
      a * ∫ s : ℝ in Set.Ioi 0, g s := by
    simp_rw [hpoint]
    rw [MeasureTheory.integral_const_mul]
  rw [hleft] at hscale
  simp only [smul_eq_mul, mul_zero] at hscale
  have hbase := integral_t_cos_div_sinh_base (a * y)
  change (∫ s : ℝ in Set.Ioi 0, g s) =
      Real.cosh (a * y) ^ (-2 : ℝ) at hbase
  rw [hbase] at hscale
  change (∫ t : ℝ in Set.Ioi 0, f t) =
      a ^ 2 * Real.cosh (a * y) ^ (-2 : ℝ)
  have ha0 : a ≠ 0 := ha.ne'
  field_simp [ha0] at hscale ⊢
  nlinarith

theorem integrableOn_t_div_sinh_base :
    IntegrableOn (fun t : ℝ => t / Real.sinh (Real.pi * t / 2)) (Set.Ioi 0) := by
  let w : ℝ → ℝ := fun t => t / Real.sinh (Real.pi * t / 2)
  have hd : IntegrableOn sechSqDensity (Set.Ioi 0) :=
    integrable_sechSqDensity.integrableOn
  have hd' : IntegrableOn (fun x => Real.pi⁻¹ * sechSqDensity x) (Set.Ioi 0) :=
    hd.const_mul Real.pi⁻¹
  have hcomp : IntegrableOn (fun x : ℝ => w (2 * Real.pi * x)) (Set.Ioi 0) := by
    refine hd'.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := hx.ne'
    have hspos : 0 < Real.sinh (Real.pi ^ 2 * x) :=
      Real.sinh_pos_iff.mpr (mul_pos (sq_pos_of_pos Real.pi_pos) hx)
    dsimp [w]
    change Real.pi⁻¹ *
        (if x = 0 then 2 else
          2 * Real.pi ^ 2 * |x| / |Real.sinh (Real.pi ^ 2 * x)|) = _
    rw [if_neg hx0, abs_of_pos hx, abs_of_pos hspos]
    have hs : Real.sinh (Real.pi * (2 * Real.pi * x) / 2) =
        Real.sinh (Real.pi ^ 2 * x) := by congr 1 <;> ring
    rw [hs]
    field_simp [Real.pi_ne_zero]
  simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff w 0
    (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).mp hcomp

theorem integrableOn_t_div_sinh {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t / Real.sinh (Real.pi * t / (2 * a)))
      (Set.Ioi 0) := by
  let wa : ℝ → ℝ := fun t => t / Real.sinh (Real.pi * t / (2 * a))
  let w : ℝ → ℝ := fun s => s / Real.sinh (Real.pi * s / 2)
  have hbase : IntegrableOn w (Set.Ioi 0) := integrableOn_t_div_sinh_base
  have hbase' : IntegrableOn (fun s => a * w s) (Set.Ioi 0) := hbase.const_mul a
  have hcomp : IntegrableOn (fun s : ℝ => wa (a * s)) (Set.Ioi 0) := by
    refine hbase'.congr_fun ?_ measurableSet_Ioi
    intro s hs
    dsimp [wa, w]
    have harg : Real.pi * (a * s) / (2 * a) = Real.pi * s / 2 := by
      field_simp [ha.ne']
    rw [harg]
    ring
  simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff wa 0 ha).mp hcomp

theorem one_sub_cos_le_sq_div_two (u : ℝ) :
    1 - Real.cos u ≤ u ^ 2 / 2 := by
  have hid : 1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
    have hcos := Real.cos_two_mul' (u / 2)
    have harg : 2 * (u / 2) = u := by ring
    rw [harg] at hcos
    nlinarith [Real.sin_sq_add_cos_sq (u / 2)]
  have hsin : |Real.sin (u / 2)| ≤ |u / 2| := Real.abs_sin_le_abs
  have hsq : Real.sin (u / 2) ^ 2 ≤ (u / 2) ^ 2 := by
    exact sq_le_sq.mpr hsin
  rw [hid]
  nlinarith

def hyperbolicLevyIntegrand (a y t : ℝ) : ℝ :=
  (1 - Real.cos (t * y)) / (t * Real.sinh (Real.pi * t / (2 * a)))

def hyperbolicLevyDerivIntegrand (a y t : ℝ) : ℝ :=
  Real.sin (t * y) / Real.sinh (Real.pi * t / (2 * a))

def hyperbolicLevyDeriv2Integrand (a y t : ℝ) : ℝ :=
  t * Real.cos (t * y) / Real.sinh (Real.pi * t / (2 * a))

def hyperbolicLevyIntegral (a y : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, hyperbolicLevyIntegrand a y t

def hyperbolicLevyDerivIntegral (a y : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, hyperbolicLevyDerivIntegrand a y t

theorem integrableOn_hyperbolicLevyDeriv2Integrand
    {a y : ℝ} (ha : 0 < a) :
    IntegrableOn (hyperbolicLevyDeriv2Integrand a y) (Set.Ioi 0) := by
  have hb := integrableOn_t_div_sinh ha
  refine hb.mono' ?_ ?_
  · exact (by
      unfold hyperbolicLevyDeriv2Integrand
      measurability : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hs : 0 < Real.sinh (Real.pi * t / (2 * a)) := by
      rw [Real.sinh_pos_iff]
      exact div_pos (mul_pos Real.pi_pos ht) (mul_pos (by norm_num) ha)
    rw [hyperbolicLevyDeriv2Integrand, Real.norm_eq_abs, abs_div,
      abs_mul, abs_of_nonneg ht0, abs_of_pos hs]
    have hc := Real.abs_cos_le_one (t * y)
    calc
      t * |Real.cos (t * y)| / Real.sinh (Real.pi * t / (2 * a)) ≤
          t * 1 / Real.sinh (Real.pi * t / (2 * a)) := by gcongr
      _ = t / Real.sinh (Real.pi * t / (2 * a)) := by ring

theorem integrableOn_hyperbolicLevyDerivIntegrand
    {a y : ℝ} (ha : 0 < a) :
    IntegrableOn (hyperbolicLevyDerivIntegrand a y) (Set.Ioi 0) := by
  have hb := (integrableOn_t_div_sinh ha).const_mul |y|
  refine hb.mono' ?_ ?_
  · exact (by
      unfold hyperbolicLevyDerivIntegrand
      measurability : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hs : 0 < Real.sinh (Real.pi * t / (2 * a)) := by
      rw [Real.sinh_pos_iff]
      exact div_pos (mul_pos Real.pi_pos ht) (mul_pos (by norm_num) ha)
    rw [hyperbolicLevyDerivIntegrand, Real.norm_eq_abs, abs_div,
      abs_of_pos hs]
    have hsin : |Real.sin (t * y)| ≤ |t * y| := Real.abs_sin_le_abs
    rw [abs_mul, abs_of_nonneg ht0] at hsin
    calc
      |Real.sin (t * y)| / Real.sinh (Real.pi * t / (2 * a)) ≤
          (t * |y|) / Real.sinh (Real.pi * t / (2 * a)) := by gcongr
      _ = |y| * (t / Real.sinh (Real.pi * t / (2 * a))) := by ring

theorem integrableOn_hyperbolicLevyIntegrand
    {a y : ℝ} (ha : 0 < a) :
    IntegrableOn (hyperbolicLevyIntegrand a y) (Set.Ioi 0) := by
  have hb := (integrableOn_t_div_sinh ha).const_mul (|y| ^ 2 / 2)
  refine hb.mono' ?_ ?_
  · exact (by
      unfold hyperbolicLevyIntegrand
      measurability : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have hs : 0 < Real.sinh (Real.pi * t / (2 * a)) := by
      rw [Real.sinh_pos_iff]
      positivity
    have hnum0 : 0 ≤ 1 - Real.cos (t * y) := sub_nonneg.mpr (Real.cos_le_one _)
    rw [hyperbolicLevyIntegrand, Real.norm_eq_abs, abs_div,
      abs_of_nonneg hnum0, abs_mul, abs_of_pos htpos, abs_of_pos hs]
    have hquad := one_sub_cos_le_sq_div_two (t * y)
    have hden : 0 < t * Real.sinh (Real.pi * t / (2 * a)) := mul_pos htpos hs
    apply (div_le_iff₀ hden).2
    have habsy : |y| ^ 2 = y ^ 2 := sq_abs y
    rw [habsy]
    calc
      1 - Real.cos (t * y) ≤ (t * y) ^ 2 / 2 := hquad
      _ = (y ^ 2 / 2 * (t / Real.sinh (Real.pi * t / (2 * a)))) *
          (t * Real.sinh (Real.pi * t / (2 * a))) := by
        field_simp [hs.ne']

theorem hasDerivAt_hyperbolicLevyIntegrand
    {a t y : ℝ} (ht : 0 < t) (ha : 0 < a) :
    HasDerivAt (fun x => hyperbolicLevyIntegrand a x t)
      (hyperbolicLevyDerivIntegrand a y t) y := by
  unfold hyperbolicLevyIntegrand hyperbolicLevyDerivIntegrand
  have hs : Real.sinh (Real.pi * t / (2 * a)) ≠ 0 := by
    exact (Real.sinh_pos_iff.mpr
      (div_pos (mul_pos Real.pi_pos ht) (mul_pos (by norm_num) ha))).ne'
  have hlin : HasDerivAt (fun x : ℝ => t * x) t y :=
    hasDerivAt_const_mul t
  have hnum := (hasDerivAt_const y (1 : ℝ)).sub hlin.cos
  have hquot := hnum.div_const (t * Real.sinh (Real.pi * t / (2 * a)))
  refine hquot.congr_deriv ?_
  ·
    field_simp [ht.ne', hs]
    ring

theorem hasDerivAt_hyperbolicLevyDerivIntegrand
    {a t y : ℝ} (ht : 0 < t) (ha : 0 < a) :
    HasDerivAt (fun x => hyperbolicLevyDerivIntegrand a x t)
      (hyperbolicLevyDeriv2Integrand a y t) y := by
  unfold hyperbolicLevyDerivIntegrand hyperbolicLevyDeriv2Integrand
  have hs : Real.sinh (Real.pi * t / (2 * a)) ≠ 0 := by
    exact (Real.sinh_pos_iff.mpr
      (div_pos (mul_pos Real.pi_pos ht) (mul_pos (by norm_num) ha))).ne'
  have hlin : HasDerivAt (fun x : ℝ => t * x) t y :=
    hasDerivAt_const_mul t
  have hquot := hlin.sin.div_const (Real.sinh (Real.pi * t / (2 * a)))
  refine hquot.congr_deriv ?_
  ·
    ring

theorem hasDerivAt_hyperbolicLevyDerivIntegral
    {a y : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x => ∫ t : ℝ in Set.Ioi 0,
        hyperbolicLevyDerivIntegrand a x t)
      (∫ t : ℝ in Set.Ioi 0, hyperbolicLevyDeriv2Integrand a y t) y := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0))
    (F := fun x t => hyperbolicLevyDerivIntegrand a x t)
    (F' := fun x t => hyperbolicLevyDeriv2Integrand a x t)
    (bound := fun t => t / Real.sinh (Real.pi * t / (2 * a)))
    (x₀ := y) (s := Set.univ)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x => (by
      unfold hyperbolicLevyDerivIntegrand
      measurability : Measurable _).aestronglyMeasurable)
    (integrableOn_hyperbolicLevyDerivIntegrand ha)
    ((by
      unfold hyperbolicLevyDeriv2Integrand
      measurability : Measurable _).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      have hs : 0 < Real.sinh (Real.pi * t / (2 * a)) := by
        rw [Real.sinh_pos_iff]
        exact div_pos (mul_pos Real.pi_pos ht) (mul_pos (by norm_num) ha)
      rw [hyperbolicLevyDeriv2Integrand, Real.norm_eq_abs, abs_div,
        abs_mul, abs_of_pos ht, abs_of_pos hs]
      calc
        t * |Real.cos (t * x)| / Real.sinh (Real.pi * t / (2 * a)) ≤
            t * 1 / Real.sinh (Real.pi * t / (2 * a)) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) ht.le) hs.le
        _ = t / Real.sinh (Real.pi * t / (2 * a)) := by ring)
    (integrableOn_t_div_sinh ha)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      exact hasDerivAt_hyperbolicLevyDerivIntegrand ht ha)
  exact h.2

theorem hasDerivAt_hyperbolicLevyIntegral
    {a y : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x => ∫ t : ℝ in Set.Ioi 0,
        hyperbolicLevyIntegrand a x t)
      (∫ t : ℝ in Set.Ioi 0, hyperbolicLevyDerivIntegrand a y t) y := by
  let M : ℝ := |y| + 1
  have hMint : IntegrableOn
      (fun t => M * (t / Real.sinh (Real.pi * t / (2 * a)))) (Set.Ioi 0) :=
    (integrableOn_t_div_sinh ha).const_mul M
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0))
    (F := fun x t => hyperbolicLevyIntegrand a x t)
    (F' := fun x t => hyperbolicLevyDerivIntegrand a x t)
    (bound := fun t => M * (t / Real.sinh (Real.pi * t / (2 * a))))
    (x₀ := y) (s := Set.Ioo (y - 1) (y + 1))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun x => (by
      unfold hyperbolicLevyIntegrand
      measurability : Measurable _).aestronglyMeasurable)
    (integrableOn_hyperbolicLevyIntegrand ha)
    ((by
      unfold hyperbolicLevyDerivIntegrand
      measurability : Measurable _).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      have hs : 0 < Real.sinh (Real.pi * t / (2 * a)) := by
        rw [Real.sinh_pos_iff]
        exact div_pos (mul_pos Real.pi_pos ht) (mul_pos (by norm_num) ha)
      have hxabs : |x| ≤ M := by
        rcases hx with ⟨hxlo, hxhi⟩
        dsimp [M]
        apply (abs_le).2
        constructor
        · linarith [neg_abs_le y]
        · linarith [le_abs_self y]
      have hsin : |Real.sin (t * x)| ≤ |t * x| := Real.abs_sin_le_abs
      have habsmul : |t * x| = t * |x| := by rw [abs_mul, abs_of_pos ht]
      rw [habsmul] at hsin
      rw [hyperbolicLevyDerivIntegrand, Real.norm_eq_abs, abs_div,
        abs_of_pos hs]
      calc
        |Real.sin (t * x)| / Real.sinh (Real.pi * t / (2 * a)) ≤
            (t * |x|) / Real.sinh (Real.pi * t / (2 * a)) :=
          div_le_div_of_nonneg_right hsin hs.le
        _ ≤ (t * M) / Real.sinh (Real.pi * t / (2 * a)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxabs ht.le) hs.le
        _ = M * (t / Real.sinh (Real.pi * t / (2 * a))) := by ring)
    hMint
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      exact hasDerivAt_hyperbolicLevyIntegrand ht ha)
  exact h.2

theorem hasDerivAt_a_mul_tanh {a y : ℝ} :
    HasDerivAt (fun x => a * Real.tanh (a * x))
      (a ^ 2 * Real.cosh (a * y) ^ (-2 : ℝ)) y := by
  have hlin : HasDerivAt (fun x : ℝ => a * x) a y := hasDerivAt_const_mul a
  have hcomp := (GaloisForLFunctions.HTGeometry.hasDerivAt_tanh (a * y)).comp y hlin
  have hmul := hcomp.const_mul a
  refine hmul.congr_deriv ?_
  rw [Real.rpow_neg (Real.cosh_pos _).le, Real.rpow_two]
  ring

theorem hyperbolicLevyDerivIntegral_eq_tanh
    {a y : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi 0, hyperbolicLevyDerivIntegrand a y t) =
      a * Real.tanh (a * y) := by
  let f : ℝ → ℝ := fun x =>
    ∫ t : ℝ in Set.Ioi 0, hyperbolicLevyDerivIntegrand a x t
  let g : ℝ → ℝ := fun x => a * Real.tanh (a * x)
  have hfderiv : ∀ x, HasDerivAt f
      (a ^ 2 * Real.cosh (a * x) ^ (-2 : ℝ)) x := by
    intro x
    have h := hasDerivAt_hyperbolicLevyDerivIntegral (a := a) (y := x) ha
    rw [show (∫ t : ℝ in Set.Ioi 0,
        hyperbolicLevyDeriv2Integrand a x t) =
          a ^ 2 * Real.cosh (a * x) ^ (-2 : ℝ) by
      simpa only [hyperbolicLevyDeriv2Integrand] using
        integral_t_cos_div_sinh (a := a) (y := x) ha] at h
    exact h
  have hgderiv : ∀ x, HasDerivAt g
      (a ^ 2 * Real.cosh (a * x) ^ (-2 : ℝ)) x := by
    intro x
    exact hasDerivAt_a_mul_tanh
  have hf : Differentiable ℝ f := fun x => (hfderiv x).differentiableAt
  have hg : Differentiable ℝ g := fun x => (hgderiv x).differentiableAt
  have hfd : ∀ x, fderiv ℝ f x = fderiv ℝ g x := by
    intro x
    ext z
    rw [fderiv_eq_smul_deriv, fderiv_eq_smul_deriv,
      (hfderiv x).deriv, (hgderiv x).deriv]
  have hzero : f 0 = g 0 := by
    simp [f, g, hyperbolicLevyDerivIntegrand]
  have heq := eq_of_fderiv_eq hf hg hfd 0 hzero
  exact congrFun heq y

theorem hasDerivAt_log_cosh_mul {a y : ℝ} :
    HasDerivAt (fun x => Real.log (Real.cosh (a * x)))
      (a * Real.tanh (a * y)) y := by
  have hlin : HasDerivAt (fun x : ℝ => a * x) a y := hasDerivAt_const_mul a
  have hlog := hlin.cosh.log (Real.cosh_pos (a * y)).ne'
  refine hlog.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  ring

theorem log_cosh_eq_hyperbolicLevyIntegral
    {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Real.log (Real.cosh (a * y)) =
      ∫ t : ℝ in Set.Ioi 0, hyperbolicLevyIntegrand a y t := by
  let f : ℝ → ℝ := fun x =>
    ∫ t : ℝ in Set.Ioi 0, hyperbolicLevyIntegrand a x t
  let g : ℝ → ℝ := fun x => Real.log (Real.cosh (a * x))
  have hfderiv : ∀ x, HasDerivAt f (a * Real.tanh (a * x)) x := by
    intro x
    have h := hasDerivAt_hyperbolicLevyIntegral (a := a) (y := x) ha
    rw [hyperbolicLevyDerivIntegral_eq_tanh (a := a) (y := x) ha] at h
    exact h
  have hgderiv : ∀ x, HasDerivAt g (a * Real.tanh (a * x)) x := by
    intro x
    exact hasDerivAt_log_cosh_mul
  have hf : Differentiable ℝ f := fun x => (hfderiv x).differentiableAt
  have hg : Differentiable ℝ g := fun x => (hgderiv x).differentiableAt
  have hfd : ∀ x, fderiv ℝ f x = fderiv ℝ g x := by
    intro x
    ext z
    rw [fderiv_eq_smul_deriv, fderiv_eq_smul_deriv,
      (hfderiv x).deriv, (hgderiv x).deriv]
  have hzero : f 0 = g 0 := by
    simp [f, g, hyperbolicLevyIntegrand]
  have heq := eq_of_fderiv_eq hf hg hfd 0 hzero
  exact (congrFun heq y).symm

end
end HTGeometry
