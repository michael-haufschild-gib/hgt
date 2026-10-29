import GaloisForLFunctions.RHTower.DeBruijnNegativeTimeContour

/-!
# Reverse Gaussian averages at positive heat

A real Gaussian average subtracts time from the de Bruijn–Newman flow.
The actual heated kernel supplies integrability and horizontal-strip
bounds, so the averaging contour can be translated by any complex number.
Completing the square then removes an arbitrary linear exponential slope.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

private def reverseHeatProduct (t τ : ℝ) (z : ℂ) (x u : ℝ) : ℂ :=
  (gaussDensity τ u : ℂ) * Complex.exp (u * (I * x)) *
    (((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * x))

private theorem integrable_reverseHeatProduct {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z : ℂ) :
    Integrable (Function.uncurry (reverseHeatProduct t τ z)) (volume.prod volume) := by
  have hcont : Continuous (Function.uncurry (reverseHeatProduct t τ z)) := by
    have hg : Continuous fun u => gaussDensity τ u := by unfold gaussDensity; fun_prop
    have hΦ := continuous_riemannKernelReal
    simp only [reverseHeatProduct, Function.uncurry_def]
    fun_prop
  refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · simp only [Function.uncurry_apply_pair, reverseHeatProduct]
    exact (integrable_gaussDensity_mul_exp hτ (I * x)).mul_const _
  · have hheat := ((riemannKernel_superExp.mul_exp_sq ht).integrable z).norm
    refine hheat.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair, reverseHeatProduct]
    have hnorm : ∀ u : ℝ, ‖(gaussDensity τ u : ℂ) * Complex.exp (u * (I * x)) *
        (((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * x))‖ =
        gaussDensity τ u *
          ‖((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * x)‖ := by
      intro u
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (gaussDensity_pos hτ u), Complex.norm_exp]
      have hre : (u * (I * x) : ℂ).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
    simp_rw [hnorm]
    rw [integral_mul_const]
    have h1 := integral_gaussDensity_mul_rexp hτ 0
    simp only [mul_zero, Real.exp_zero, mul_one, zero_pow two_ne_zero] at h1
    rw [h1, one_mul]

private theorem integral_reverseHeatProduct_left {τ : ℝ} (hτ : 0 < τ)
    (t : ℝ) (z : ℂ) (x : ℝ) :
    ∫ u, reverseHeatProduct t τ z x u =
      ((riemannKernelReal x * Real.exp ((t - τ) * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * x) := by
  simp only [reverseHeatProduct]
  rw [integral_mul_const, integral_gaussDensity_mul_exp hτ]
  have hphase : (τ : ℂ) * (I * (x : ℂ)) ^ 2 = ((-τ * x ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, I_sq]
    ring
  rw [hphase, ← Complex.ofReal_exp]
  have he : Real.exp (-τ * x ^ 2) * (riemannKernelReal x * Real.exp (t * x ^ 2)) =
      riemannKernelReal x * Real.exp ((t - τ) * x ^ 2) := by
    calc
      _ = riemannKernelReal x * (Real.exp (-τ * x ^ 2) * Real.exp (t * x ^ 2)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [← mul_assoc, ← Complex.ofReal_mul, he]

private theorem integral_reverseHeatProduct_right (t τ : ℝ) (z : ℂ) (u : ℝ) :
    ∫ x, reverseHeatProduct t τ z x u = (gaussDensity τ u : ℂ) * riemannHeat t (z + u) := by
  have hre : ∀ x : ℝ, reverseHeatProduct t τ z x u =
      (gaussDensity τ u : ℂ) *
        (((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * (z + u) * x)) := by
    intro x
    have he : Complex.exp (u * (I * x)) * Complex.exp (I * z * x) =
        Complex.exp (I * (z + u) * x) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    simp only [reverseHeatProduct]
    linear_combination ((gaussDensity τ u : ℂ) *
      ((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ)) * he
  simp_rw [hre]
  rw [integral_const_mul]
  rfl

/-- Real Gaussian averaging subtracts time from the actual heat flow. -/
theorem riemannHeat_sub_eq_integral_gaussian {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z : ℂ) :
    riemannHeat (t - τ) z = ∫ u : ℝ, cgauss τ u * riemannHeat t (z + u) := by
  simp_rw [cgauss_ofReal]
  calc
    riemannHeat (t - τ) z = ∫ x, ∫ u, reverseHeatProduct t τ z x u := by
      unfold riemannHeat cosTransform
      simp_rw [integral_reverseHeatProduct_left hτ]
    _ = ∫ u, ∫ x, reverseHeatProduct t τ z x u :=
      integral_integral_swap (integrable_reverseHeatProduct ht hτ z)
    _ = _ := by simp_rw [integral_reverseHeatProduct_right]

/-- The actual heated kernel bounds the heat flow on every horizontal strip. -/
theorem norm_riemannHeat_le_strip_integral {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    ‖riemannHeat t w‖ ≤
      ∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp (|w.im| * |x|) := by
  have hint := (riemannKernel_superExp.mul_exp_sq ht).integrable_mul_exp |w.im|
  unfold riemannHeat cosTransform
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) hint (Eventually.of_forall fun x => ?_))
  have h := norm_integrand_le (fun x => riemannKernelReal x * Real.exp (t * x ^ 2)) w x
  simpa only [abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))] using h

private theorem integral_heated_kernel_exp_mono {t : ℝ} (ht : 0 ≤ t) {a b : ℝ}
    (hab : a ≤ b) :
    (∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp (a * |x|)) ≤
      ∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp (b * |x|) := by
  exact integral_mono ((riemannKernel_superExp.mul_exp_sq ht).integrable_mul_exp _)
    ((riemannKernel_superExp.mul_exp_sq ht).integrable_mul_exp _) fun x =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hab (abs_nonneg x)))
        (mul_nonneg (riemannKernelReal_pos x).le (Real.exp_pos _).le)

private theorem norm_cgauss_mul_heat_decay {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z : ℂ) {c : ℝ} (v : ℂ) (hv : |v.im| ≤ c) :
    ‖cgauss τ v * riemannHeat t (z + v)‖ ≤
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (c ^ 2 / (4 * τ) + τ) *
        (∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp ((|z.im| + c) * |x|)) *
          Real.exp (-(1 * |v.re|)) := by
  rw [norm_mul, norm_cgauss hτ]
  have hH := (norm_riemannHeat_le_strip_integral ht (z + v)).trans
    (integral_heated_kernel_exp_mono ht (b := |z.im| + c)
      (by rw [Complex.add_im]; exact (abs_add_le _ _).trans (by linarith only [hv])))
  have hexp : Real.exp ((v.im ^ 2 - v.re ^ 2) / (4 * τ)) ≤
      Real.exp (c ^ 2 / (4 * τ) + τ) * Real.exp (-(1 * |v.re|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : v.im ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hv 2
    have h2 : -(v.re ^ 2) / (4 * τ) ≤ τ - |v.re| := by
      rw [div_le_iff₀ (by positivity), ← sq_abs]
      nlinarith only [sq_nonneg (|v.re| - 2 * τ)]
    have he : (v.im ^ 2 - v.re ^ 2) / (4 * τ) =
        v.im ^ 2 / (4 * τ) + -(v.re ^ 2) / (4 * τ) := by ring
    rw [he]
    have h3 := div_le_div_of_nonneg_right h1 (show 0 ≤ 4 * τ by positivity)
    linarith only [h2, h3]
  calc
    _ ≤ (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (c ^ 2 / (4 * τ) + τ) * Real.exp (-(1 * |v.re|))) *
        (∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp ((|z.im| + c) * |x|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hexp (by positivity)) hH (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The reverse-heat integral may be taken on every horizontal line. -/
theorem riemannHeat_sub_eq_integral_vertical {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z : ℂ) (a : ℝ) :
    riemannHeat (t - τ) z =
      ∫ u : ℝ, cgauss τ ((u : ℂ) + a * I) * riemannHeat t (z + ((u : ℂ) + a * I)) := by
  rw [riemannHeat_sub_eq_integral_gaussian ht hτ]
  set F : ℂ → ℂ := fun v => cgauss τ v * riemannHeat t (z + v)
  have hFd : ∀ v : ℂ, DifferentiableAt ℂ F v := fun v =>
    ((differentiable_cgauss τ) v).mul
      (((differentiable_riemannHeat ht).comp ((differentiable_const z).add differentiable_id)) v)
  have hbound : ∀ v : ℂ, |v.im| ≤ |a| → ‖F v‖ ≤
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (|a| ^ 2 / (4 * τ) + τ) *
        (∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp ((|z.im| + |a|) * |x|)) *
          Real.exp (-(1 * |v.re|)) := fun v hv => norm_cgauss_mul_heat_decay ht hτ z v hv
  change ∫ u : ℝ, F u = ∫ u : ℝ, F ((u : ℂ) + a * I)
  rcases le_or_gt 0 a with ha | ha
  · have h := integral_horizontal_shift_of_decay (F := F) ha one_pos
      (fun v _ => hFd v) (fun v hv => hbound v (by simpa only [abs_of_nonneg ha] using hv))
    exact h.symm
  · have h := integral_horizontal_shift_neg_of_lower_decay (F := F) (c := -a)
      (by linarith only [ha]) one_pos (fun v _ _ => hFd v)
      (fun v hlo hhi => hbound v (by
        rw [abs_of_neg ha, abs_of_nonpos hhi]
        linarith only [hlo]))
    simpa only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add] using h.symm

/-- Every complex translate of the averaging line gives the same reverse heat value. -/
theorem riemannHeat_sub_eq_integral_complex_shift {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z b : ℂ) :
    riemannHeat (t - τ) z =
      ∫ u : ℝ, cgauss τ ((u : ℂ) + b) * riemannHeat t (z + ((u : ℂ) + b)) := by
  rw [riemannHeat_sub_eq_integral_vertical ht hτ z b.im]
  rw [← integral_add_right_eq_self
    (fun u : ℝ => cgauss τ ((u : ℂ) + b.im * I) * riemannHeat t (z + ((u : ℂ) + b.im * I))) b.re]
  congr 1
  funext u
  have he : ((u + b.re : ℝ) : ℂ) + b.im * I = (u : ℂ) + b := by
    calc
      _ = (u : ℂ) + ((b.re : ℂ) + (b.im : ℂ) * I) := by push_cast; ring
      _ = _ := by rw [Complex.re_add_im]
  rw [he]

/-- Absolute integrability holds on each translated reverse-heat contour. -/
theorem integrable_cgauss_mul_heat_shift {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z b : ℂ) :
    Integrable (fun u : ℝ => cgauss τ ((u : ℂ) + b) * riemannHeat t (z + ((u : ℂ) + b))) := by
  set C := (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (|b.im| ^ 2 / (4 * τ) + τ) *
    (∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp ((|z.im| + |b.im|) * |x|))
  have hC : 0 ≤ C := by
    have hmass : 0 ≤ ∫ x, riemannKernelReal x * Real.exp (t * x ^ 2) *
        Real.exp ((|z.im| + |b.im|) * |x|) :=
      integral_nonneg fun x => by positivity [riemannKernelReal_pos x]
    dsimp [C]
    positivity
  have hcont : Continuous (fun u : ℝ =>
      cgauss τ ((u : ℂ) + b) * riemannHeat t (z + ((u : ℂ) + b))) :=
    ((differentiable_cgauss τ).continuous.comp (by fun_prop)).mul
      ((differentiable_riemannHeat ht).continuous.comp (by fun_prop))
  refine ((integrable_exp_neg_mul_abs' (by norm_num : (0 : ℝ) < 1)).const_mul
    (C * Real.exp |b.re|)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have h := norm_cgauss_mul_heat_decay ht hτ z ((u : ℂ) + b) (c := |b.im|) (by simp)
  change _ ≤ C * Real.exp (-(1 * |((u : ℂ) + b).re|)) at h
  simp only [Complex.add_re, Complex.ofReal_re] at h
  have habs : |u| ≤ |u + b.re| + |b.re| := by
    calc
      |u| = |(u + b.re) + (-b.re)| := by congr 1; ring
      _ ≤ |u + b.re| + |-b.re| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have he : Real.exp (-(1 * |u + b.re|)) ≤ Real.exp |b.re| * Real.exp (-(1 * |u|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [habs]
  exact h.trans ((mul_le_mul_of_nonneg_left he hC).trans_eq (by ring))

/-- Completing the square cancels a prescribed linear slope in the shifted Gaussian. -/
theorem cgauss_add_two_mul {τ : ℝ} (hτ : 0 < τ) (u : ℝ) (a : ℂ) :
    cgauss τ ((u : ℂ) + 2 * τ * a) =
      (gaussDensity τ u : ℂ) * Complex.exp (-(τ : ℂ) * a ^ 2) * Complex.exp (-(u : ℂ) * a) := by
  rw [← cgauss_ofReal τ u]
  unfold cgauss
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have he : -(((u : ℂ) + 2 * τ * a) ^ 2) / (4 * τ) =
      -((u : ℂ) ^ 2) / (4 * τ) + (-(τ : ℂ) * a ^ 2) + (-(u : ℂ) * a) := by
    field_simp
    ring
  rw [he, Complex.exp_add, Complex.exp_add]
  ring

/-- The reverse heat formula with the linear exponential slope removed exactly. -/
theorem riemannHeat_sub_eq_reverse_saddle {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (z a : ℂ) :
    riemannHeat (t - τ) z = Complex.exp (-(τ : ℂ) * a ^ 2) *
      ∫ u : ℝ, (gaussDensity τ u : ℂ) * Complex.exp (-(u : ℂ) * a) *
        riemannHeat t (z + 2 * τ * a + u) := by
  rw [riemannHeat_sub_eq_integral_complex_shift ht hτ z (2 * τ * a)]
  simp_rw [cgauss_add_two_mul hτ]
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [show z + ((u : ℂ) + 2 * τ * a) = z + 2 * τ * a + u by ring]
  ring

/-- The unheated function is recovered from positive heat in the completed-square form. -/
theorem riemannHeat_zero_eq_reverse_saddle {t : ℝ} (ht : 0 < t) (z a : ℂ) :
    riemannHeat 0 z = Complex.exp (-(t : ℂ) * a ^ 2) *
      ∫ u : ℝ, (gaussDensity t u : ℂ) * Complex.exp (-(u : ℂ) * a) *
        riemannHeat t (z + 2 * t * a + u) := by
  simpa only [sub_self] using riemannHeat_sub_eq_reverse_saddle ht.le ht z a

end

end RHTower.DeBruijn
