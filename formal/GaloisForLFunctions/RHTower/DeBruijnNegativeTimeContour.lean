import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness

/-!
# Negative heat times: `H_{−τ}` is a vertical Gaussian average of `ξ`

For `τ > 0` the characteristic function of the normal law, `∫ g_τ(u) e^{iux} du = e^{−τx²}`, and
Fubini give

`H_{−τ}(z) = ∫ g_τ(u) H_0(z + u) du = ∫ g_τ(u) ξ(s + iu) du`,   `s = ½ + iz`

(`riemannHeat_neg_eq_integral`): backward in time the flow averages `ξ` along the vertical line through
`s`. Since `H_0` is bounded on every horizontal strip (`norm_riemannHeat_zero_le`) and the complex
Gaussian `g_τ(v) = (4πτ)^{−1/2} e^{−v²/(4τ)}` decays like `e^{−(Re v)²/(4τ)}` there, the line of
integration can be moved: for every real `a`,

`H_{−τ}(z) = ∫ g_τ(u − ia) ξ(s + a + iu) du`   (`riemannHeat_neg_eq_integral_shift`),

i.e. the average may be taken along any vertical line, with the complex Gaussian weight.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The complex Gaussian `g_τ(v) = (4πτ)^{−1/2} e^{−v²/(4τ)}`. -/
def cgauss (τ : ℝ) (v : ℂ) : ℂ :=
  (((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(v ^ 2) / (4 * τ))

theorem cgauss_ofReal (τ u : ℝ) : cgauss τ u = (gaussDensity τ u : ℂ) := by
  simp only [cgauss, gaussDensity]
  push_cast
  congr 2
  ring

theorem differentiable_cgauss (τ : ℝ) : Differentiable ℂ (cgauss τ) := by
  unfold cgauss; fun_prop

theorem norm_cgauss {τ : ℝ} (hτ : 0 < τ) (v : ℂ) :
    ‖cgauss τ v‖ = (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
      Real.exp ((v.im ^ 2 - v.re ^ 2) / (4 * τ)) := by
  rw [cgauss, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    Complex.norm_exp]
  congr 2
  have h4 : (4 * (τ : ℂ)) = ((4 * τ : ℝ) : ℂ) := by push_cast; ring
  rw [h4, Complex.div_ofReal_re]
  simp only [Complex.neg_re, pow_two, Complex.mul_re]
  ring

/-- `H_0` is bounded on horizontal strips: `|H_0(w)| ≤ ∫ Φ(x) e^{|Im w||x|} dx`. -/
theorem norm_riemannHeat_zero_le (w : ℂ) :
    ‖riemannHeat 0 w‖ ≤ ∫ x, riemannKernelReal x * Real.exp (|w.im| * |x|) := by
  have hint := riemannKernel_superExp.integrable_mul_exp |w.im|
  unfold riemannHeat cosTransform
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) hint (Eventually.of_forall fun x => ?_))
  have h := norm_integrand_le (fun x => riemannKernelReal x * Real.exp (0 * x ^ 2)) w x
  simp only [zero_mul, Real.exp_zero, mul_one] at h ⊢
  rwa [abs_of_pos (riemannKernelReal_pos x)] at h

theorem integral_riemannKernel_mul_exp_mono {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    ∫ x, riemannKernelReal x * Real.exp (y₁ * |x|) ≤
      ∫ x, riemannKernelReal x * Real.exp (y₂ * |x|) :=
  integral_mono (riemannKernel_superExp.integrable_mul_exp _)
    (riemannKernel_superExp.integrable_mul_exp _) fun x =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hy (abs_nonneg x))) (riemannKernelReal_pos x).le

/-! ## The vertical Gaussian average -/

/-- The product integrand behind the representation. -/
def negHeatProduct (τ : ℝ) (z : ℂ) (x u : ℝ) : ℂ :=
  (gaussDensity τ u : ℂ) * Complex.exp (u * (I * x)) *
    ((riemannKernelReal x : ℂ) * Complex.exp (I * z * x))

theorem integrable_negHeatProduct {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    Integrable (Function.uncurry (negHeatProduct τ z)) (volume.prod volume) := by
  have hcont : Continuous (Function.uncurry (negHeatProduct τ z)) := by
    have hg : Continuous fun u => gaussDensity τ u := by unfold gaussDensity; fun_prop
    have hΦ := continuous_riemannKernelReal
    simp only [negHeatProduct, Function.uncurry_def]
    fun_prop
  refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · simp only [Function.uncurry_apply_pair, negHeatProduct]
    exact (integrable_gaussDensity_mul_exp hτ (I * x)).mul_const _
  · have hheat := (riemannKernel_superExp.integrable z).norm
    refine hheat.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair, negHeatProduct]
    have hnorm : ∀ u : ℝ, ‖(gaussDensity τ u : ℂ) * Complex.exp (u * (I * x)) *
        ((riemannKernelReal x : ℂ) * Complex.exp (I * z * x))‖ =
        gaussDensity τ u * ‖(riemannKernelReal x : ℂ) * Complex.exp (I * z * x)‖ := by
      intro u
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (gaussDensity_pos hτ u), Complex.norm_exp]
      have : (u * (I * x) : ℂ).re = 0 := by simp
      rw [this, Real.exp_zero, mul_one]
    simp_rw [hnorm]
    rw [integral_mul_const]
    have h1 := integral_gaussDensity_mul_rexp hτ 0
    simp only [mul_zero, Real.exp_zero, mul_one, zero_pow two_ne_zero] at h1
    rw [h1, one_mul]

theorem integral_negHeatProduct_left {τ : ℝ} (hτ : 0 < τ) (z : ℂ) (x : ℝ) :
    ∫ u, negHeatProduct τ z x u =
      ((riemannKernelReal x * Real.exp (-τ * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * x) := by
  simp only [negHeatProduct]
  rw [integral_mul_const, integral_gaussDensity_mul_exp hτ]
  push_cast
  rw [mul_pow, I_sq]
  ring_nf

theorem integral_negHeatProduct_right (τ : ℝ) (z : ℂ) (u : ℝ) :
    ∫ x, negHeatProduct τ z x u = (gaussDensity τ u : ℂ) * riemannHeat 0 (z + u) := by
  have hre : ∀ x : ℝ, negHeatProduct τ z x u =
      (gaussDensity τ u : ℂ) * ((riemannKernelReal x : ℂ) * Complex.exp (I * (z + u) * x)) := by
    intro x
    have he : Complex.exp (u * (I * x)) * Complex.exp (I * z * x) =
        Complex.exp (I * (z + u) * x) := by
      rw [← Complex.exp_add]; congr 1; ring
    simp only [negHeatProduct]
    linear_combination ((gaussDensity τ u : ℂ) * (riemannKernelReal x : ℂ)) * he
  simp_rw [hre]
  rw [integral_const_mul]
  congr 1
  unfold riemannHeat cosTransform
  simp

/-- **Backward in time the flow averages `ξ` along vertical lines.** For `τ > 0`,
`H_{−τ}(z) = ∫ g_τ(u) H_0(z + u) du`. -/
theorem riemannHeat_neg_eq_integral {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    riemannHeat (-τ) z = ∫ u : ℝ, cgauss τ u * riemannHeat 0 (z + u) := by
  simp_rw [cgauss_ofReal]
  calc riemannHeat (-τ) z = ∫ x, ∫ u, negHeatProduct τ z x u := by
        unfold riemannHeat cosTransform
        simp_rw [integral_negHeatProduct_left hτ]
    _ = ∫ u, ∫ x, negHeatProduct τ z x u := integral_integral_swap (integrable_negHeatProduct hτ z)
    _ = _ := by simp_rw [integral_negHeatProduct_right]

/-! ## Moving the line of integration -/

theorem norm_cgauss_mul_riemannHeat_le {τ : ℝ} (hτ : 0 < τ) (z : ℂ) {c : ℝ} (v : ℂ)
    (hv : |v.im| ≤ c) :
    ‖cgauss τ v * riemannHeat 0 (z + v)‖ ≤
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (c ^ 2 / (4 * τ) + τ) *
        (∫ x, riemannKernelReal x * Real.exp ((|z.im| + c) * |x|)) *
          Real.exp (-(1 * |v.re|)) := by
  rw [norm_mul, norm_cgauss hτ]
  have hH := (norm_riemannHeat_zero_le (z + v)).trans (integral_riemannKernel_mul_exp_mono
    (y₂ := |z.im| + c) (by rw [Complex.add_im]; exact (abs_add_le _ _).trans (by linarith)))
  have hexp : Real.exp ((v.im ^ 2 - v.re ^ 2) / (4 * τ)) ≤
      Real.exp (c ^ 2 / (4 * τ) + τ) * Real.exp (-(1 * |v.re|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : v.im ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
    have h2 : -(v.re ^ 2) / (4 * τ) ≤ τ - |v.re| := by
      rw [div_le_iff₀ (by positivity), ← sq_abs]
      nlinarith [sq_nonneg (|v.re| - 2 * τ)]
    have e : (v.im ^ 2 - v.re ^ 2) / (4 * τ) = v.im ^ 2 / (4 * τ) + -(v.re ^ 2) / (4 * τ) := by
      ring
    rw [e]
    have h3 : v.im ^ 2 / (4 * τ) ≤ c ^ 2 / (4 * τ) := by gcongr
    linarith
  have hM : 0 ≤ ∫ x, riemannKernelReal x * Real.exp ((|z.im| + c) * |x|) :=
    integral_nonneg fun x => by have := riemannKernelReal_pos x; positivity
  calc (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp ((v.im ^ 2 - v.re ^ 2) / (4 * τ)) *
        ‖riemannHeat 0 (z + v)‖
      ≤ (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (c ^ 2 / (4 * τ) + τ) * Real.exp (-(1 * |v.re|))) *
          (∫ x, riemannKernelReal x * Real.exp ((|z.im| + c) * |x|)) := by gcongr
    _ = _ := by ring

/-- **Moving the vertical line.** For `τ > 0` and every real `a`,
`H_{−τ}(z) = ∫ g_τ(u − ia) H_0(z + u − ia) du`; with `s = ½ + iz` the integrand is
`g_τ(u − ia) ξ(s + a + iu)`. -/
theorem riemannHeat_neg_eq_integral_shift {τ : ℝ} (hτ : 0 < τ) (z : ℂ) (a : ℝ) :
    riemannHeat (-τ) z =
      ∫ u : ℝ, cgauss τ ((u : ℂ) - a * I) * riemannHeat 0 (z + ((u : ℂ) - a * I)) := by
  rw [riemannHeat_neg_eq_integral hτ]
  set F : ℂ → ℂ := fun v => cgauss τ v * riemannHeat 0 (z + v) with hF
  have hFd : ∀ v : ℂ, DifferentiableAt ℂ F v := fun v =>
    ((differentiable_cgauss τ) v).mul
      (((differentiable_riemannHeat le_rfl).comp (differentiable_const z |>.add differentiable_id)) v)
  set c := |a|
  have hbound : ∀ v : ℂ, |v.im| ≤ c → ‖F v‖ ≤
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (c ^ 2 / (4 * τ) + τ) *
        (∫ x, riemannKernelReal x * Real.exp ((|z.im| + c) * |x|)) *
          Real.exp (-(1 * |v.re|)) := fun v hv => norm_cgauss_mul_riemannHeat_le hτ z v hv
  change ∫ u : ℝ, F u = ∫ u : ℝ, F ((u : ℂ) - a * I)
  rcases le_or_gt a 0 with ha | ha
  · have h := integral_horizontal_shift_of_decay (F := F) (c := c) (abs_nonneg a) one_pos
      (fun v _ => hFd v) hbound
    have e : ∀ u : ℝ, ((u : ℂ) + (c : ℂ) * I) = (u : ℂ) - a * I := by
      intro u; simp only [c, abs_of_nonpos ha]; push_cast; ring
    simp_rw [e] at h
    exact h.symm
  · -- reflect `v ↦ −v` and use the upper shift
    set G : ℂ → ℂ := fun v => F (-v) with hG
    have hGd : ∀ v : ℂ, |v.im| ≤ c → DifferentiableAt ℂ G v := fun v _ =>
      (hFd (-v)).comp v differentiable_neg.differentiableAt
    have hGb : ∀ v : ℂ, |v.im| ≤ c → ‖G v‖ ≤
        (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (c ^ 2 / (4 * τ) + τ) *
          (∫ x, riemannKernelReal x * Real.exp ((|z.im| + c) * |x|)) *
            Real.exp (-(1 * |v.re|)) := by
      intro v hv
      have := hbound (-v) (by simpa using hv)
      simpa [hG] using this
    have h := integral_horizontal_shift_of_decay (F := G) (c := c) (abs_nonneg a) one_pos hGd hGb
    have hl : ∫ x : ℝ, G ((x : ℂ) + (c : ℂ) * I) = ∫ x : ℝ, F ((x : ℂ) - a * I) := by
      rw [← integral_neg_eq_self (fun x : ℝ => F ((x : ℂ) - a * I)) volume]
      congr 1; funext x
      simp only [hG, c, abs_of_pos ha]
      congr 1; push_cast; ring
    have hr : ∫ x : ℝ, G (x : ℂ) = ∫ x : ℝ, F (x : ℂ) := by
      rw [← integral_neg_eq_self (fun x : ℝ => F (x : ℂ)) volume]
      congr 1; funext x
      simp only [hG]
      push_cast; ring_nf
    rw [← hl, h, hr]

end

end RHTower.DeBruijn
