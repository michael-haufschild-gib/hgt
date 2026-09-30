import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound

/-!
# The heat flow of `Ξ` is a Gaussian horizontal average of `ξ`

For `t > 0` let `g_t(u) = (4πt)^{−1/2} e^{−u²/(4t)}` be the normal density of variance `2t`. Its
moment generating function is `∫ g_t(u) e^{ux} du = e^{t x²}`, so Fubini gives

`H_t(z) = ∫ Φ(x) e^{t x²} e^{izx} dx = ∫ g_t(u) ξ(1/2 + iz + u) du`

(`riemannHeat_eq_integral_gaussian_xi`): the de Bruijn–Newman deformation is the average of `ξ`
along the horizontal line through `1/2 + iz`, with Gaussian weight. At height `X` the modulus of `ξ`
grows like `e^{(u/2)log(X/2π)}` in the horizontal direction, so the average concentrates at
`u ≈ t log(X/2π)`; this is where the Euler product controls `ζ` once `t log(X/2π)` is large.

With `F(w) = ξ(1/2 + w + iX)`, the functional equation and Schwarz reflection give
`F(−w) = conj F(w)`, and splitting the line at `w = 0` yields the reflection split
(`riemannHeat_eq_halfGaussAverage`)

`H_t(X + iy) = Q(−y) + conj Q(y)`,  `Q(y) = ∫_0^∞ g_t(w − y) F(w) dw`.

So `H_t(X + iy) ≠ 0` whenever `|Q(y)| ≠ |Q(−y)|`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The normal density of variance `2t`. -/
def gaussDensity (t u : ℝ) : ℝ := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (4 * t)))

theorem gaussDensity_pos {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 < gaussDensity t u := by
  unfold gaussDensity; positivity

/-- **The moment generating function**: `∫ g_t(u) e^{u x} du = e^{t x²}`. -/
theorem integral_gaussDensity_mul_exp {t : ℝ} (ht : 0 < t) (x : ℂ) :
    ∫ u : ℝ, (gaussDensity t u : ℂ) * Complex.exp (u * x) = Complex.exp (t * x ^ 2) := by
  have hb : (-(1 / (4 * t) : ℂ)).re < 0 := by
    rw [Complex.neg_re, ← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_div, Complex.ofReal_re]
    have : 0 < 1 / (4 * t) := by positivity
    linarith
  have hquad := integral_cexp_quadratic hb x 0
  have hfun : ∀ u : ℝ, (gaussDensity t u : ℂ) * Complex.exp (u * x) =
      ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) *
        Complex.exp (-(1 / (4 * t) : ℂ) * (u : ℂ) ^ 2 + x * u + 0) := by
    intro u
    unfold gaussDensity
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hfun]
  rw [integral_const_mul, hquad]
  have h4t : (4 * t : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * t : ℝ) ≠ 0)
  have hexp : (0 : ℂ) - x ^ 2 / (4 * -(1 / (4 * t))) = t * x ^ 2 := by
    field_simp
    ring
  rw [hexp, ← mul_assoc]
  have hpi : (Real.pi : ℂ) / -(-(1 / (4 * t) : ℂ)) = ((4 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hpi, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  norm_num

theorem integrable_gaussDensity_mul_exp {t : ℝ} (ht : 0 < t) (x : ℂ) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * Complex.exp (u * x)) := by
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  refine ((integrable_cexp_quadratic hb x 0).const_mul
    (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).congr (Eventually.of_forall fun u => ?_)
  unfold gaussDensity
  push_cast
  rw [mul_assoc (_ : ℂ) (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
  congr 2
  ring

/-- The real moment generating function. -/
theorem integral_gaussDensity_mul_rexp {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ u : ℝ, gaussDensity t u * Real.exp (u * x) = Real.exp (t * x ^ 2) := by
  have h := integral_gaussDensity_mul_exp ht x
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  exact h

/-- The product integrand `g_t(u) e^{ux} · Φ(x) e^{izx}` behind the Gaussian representation. -/
def heatProduct (t : ℝ) (z : ℂ) (x u : ℝ) : ℂ :=
  (gaussDensity t u : ℂ) * Complex.exp (u * x) * ((riemannKernelReal x : ℂ) * Complex.exp (I * z * x))

theorem norm_heatProduct {t : ℝ} (ht : 0 < t) (z : ℂ) (x u : ℝ) :
    ‖heatProduct t z x u‖ = gaussDensity t u * Real.exp (u * x) *
      (riemannKernelReal x * Real.exp (-(z.im * x))) := by
  rw [heatProduct, norm_mul, norm_integrand, abs_of_pos (riemannKernelReal_pos x), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht u), Complex.norm_exp]
  congr 2
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

theorem integrable_heatProduct {t : ℝ} (ht : 0 < t) (z : ℂ) :
    Integrable (Function.uncurry (heatProduct t z)) (volume.prod volume) := by
  have hcont : Continuous (Function.uncurry (heatProduct t z)) := by
    have hg : Continuous fun u => gaussDensity t u := by unfold gaussDensity; fun_prop
    have hΦ := continuous_riemannKernelReal
    simp only [heatProduct, Function.uncurry_def]
    fun_prop
  refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · simp only [Function.uncurry_apply_pair, heatProduct]
    exact (integrable_gaussDensity_mul_exp ht x).mul_const _
  · have hheat := ((riemannKernel_superExp.mul_exp_sq ht.le).integrable z).norm
    refine hheat.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair, norm_heatProduct ht]
    have h := norm_integrand (fun x => riemannKernelReal x * Real.exp (t * x ^ 2)) z x
    rw [integral_mul_const, integral_gaussDensity_mul_rexp ht, h,
      abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]
    ring

theorem integral_heatProduct_left {t : ℝ} (ht : 0 < t) (z : ℂ) (x : ℝ) :
    ∫ u, heatProduct t z x u =
      ((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * x) := by
  simp only [heatProduct]
  rw [integral_mul_const, integral_gaussDensity_mul_exp ht]
  push_cast
  ring

theorem integral_heatProduct_right (t : ℝ) (z : ℂ) (u : ℝ) :
    ∫ x, heatProduct t z x u = (gaussDensity t u : ℂ) * xi (1 / 2 + I * z + u) := by
  have hre : ∀ x : ℝ, heatProduct t z x u =
      (gaussDensity t u : ℂ) * ((riemannKernelReal x : ℂ) * Complex.exp (I * (z - I * u) * x)) := by
    intro x
    have he : Complex.exp (u * x) * Complex.exp (I * z * x) =
        Complex.exp (I * (z - I * u) * x) := by
      rw [← Complex.exp_add]
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    simp only [heatProduct]
    linear_combination ((gaussDensity t u : ℂ) * (riemannKernelReal x : ℂ)) * he
  simp_rw [hre]
  rw [integral_const_mul]
  change _ * cosTransform riemannKernelReal (z - I * u) = _
  rw [cosTransform_riemannKernel]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Gaussian average of `ξ` along a horizontal line is absolutely convergent. -/
theorem integrable_gaussDensity_mul_xi {t : ℝ} (ht : 0 < t) (z : ℂ) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * xi (1 / 2 + I * z + u)) := by
  have h := (integrable_heatProduct ht z).integral_prod_right
  simp only [Function.uncurry_apply_pair, integral_heatProduct_right] at h
  exact h

/-- **The heat flow is a Gaussian horizontal average of `ξ`.** For `t > 0`,
`H_t(z) = ∫ g_t(u) ξ(1/2 + iz + u) du`. -/
theorem riemannHeat_eq_integral_gaussian_xi {t : ℝ} (ht : 0 < t) (z : ℂ) :
    riemannHeat t z = ∫ u : ℝ, (gaussDensity t u : ℂ) * xi (1 / 2 + I * z + u) := by
  calc riemannHeat t z = ∫ x, ∫ u, heatProduct t z x u := by
        unfold riemannHeat cosTransform
        simp_rw [integral_heatProduct_left ht]
    _ = ∫ u, ∫ x, heatProduct t z x u := integral_integral_swap (integrable_heatProduct ht z)
    _ = _ := by simp_rw [integral_heatProduct_right]

theorem gaussDensity_neg (t u : ℝ) : gaussDensity t (-u) = gaussDensity t u := by
  simp [gaussDensity]

/-- The one-sided Gaussian average `Q_t(X, y) = ∫_0^∞ g_t(w − y) ξ(1/2 + w + iX) dw`. -/
def halfGaussAverage (t X y : ℝ) : ℂ :=
  ∫ w in Ioi (0 : ℝ), (gaussDensity t (w - y) : ℂ) * xi (1 / 2 + w + I * X)

/-- `ξ(1/2 − w + iX) = conj ξ(1/2 + w + iX)`: the functional equation and Schwarz reflection. -/
theorem xi_half_sub_eq_conj (w X : ℝ) :
    xi (1 / 2 + (-w : ℝ) + I * X) = starRingEnd ℂ (xi (1 / 2 + w + I * X)) := by
  rw [← xi_conj, ← xi_one_sub]
  congr 1
  apply Complex.ext
  · simp
    ring
  · simp

/-- **The reflection split.** For `t > 0` and real `X, y`,
`H_t(X + iy) = Q_t(X, −y) + conj Q_t(X, y)`. -/
theorem riemannHeat_eq_halfGaussAverage {t : ℝ} (ht : 0 < t) (X y : ℝ) :
    riemannHeat t (X + I * y) = halfGaussAverage t X (-y) + starRingEnd ℂ (halfGaussAverage t X y) := by
  set f : ℝ → ℂ := fun w => (gaussDensity t (w + y) : ℂ) * xi (1 / 2 + w + I * X) with hf
  have hshift : riemannHeat t (X + I * y) = ∫ w, f w := by
    rw [riemannHeat_eq_integral_gaussian_xi ht, ← integral_add_right_eq_self _ y]
    congr 1
    funext w
    rw [hf]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfi : Integrable f := by
    have h := (integrable_gaussDensity_mul_xi ht (X + I * y)).comp_add_right y
    refine h.congr (Eventually.of_forall fun w => ?_)
    simp only [hf]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hneg : ∫ w in Iic (0 : ℝ), f w = ∫ w in Ioi (0 : ℝ), f (-w) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  rw [hshift, ← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hfi, compl_Ioi, hneg,
    halfGaussAverage, halfGaussAverage, ← integral_conj]
  congr 1
  · refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun w _ => ?_
    simp only [hf, sub_neg_eq_add]
  · refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun w _ => ?_
    simp only [hf]
    rw [map_mul, Complex.conj_ofReal, ← xi_half_sub_eq_conj, ← gaussDensity_neg t (w - y)]
    push_cast
    ring_nf

end

end RHTower.DeBruijn
