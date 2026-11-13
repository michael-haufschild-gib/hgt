import GaloisForLFunctions.GaloisTheoryOfZeros.TheTraceOfAFibreOfTheHeatCover
import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage

/-!
# The heat family at forward times is a complex Gaussian average of `ξ`

For a time `τ` with `Re τ > 0` let `g_τ(w) = (4πτ)^{−1/2} e^{−w²/(4τ)}`. Its moment generating
function is `∫ g_τ(u) e^{ux} du = e^{τx²}`, so Fubini gives

`H_τ(z) = ∫ g_τ(u) ξ(1/2 + iz + u) du`  (`complexHeat_eq_integral_complexGauss_mul_xi`).

The Gaussian is complex: its modulus on the real axis is a Gaussian of variance `2‖τ‖²/Re τ`, and
its phase oscillates when `Im τ ≠ 0`.

* **The half transform.** `𝒜(τ, z) = ∫_0^∞ g_τ(u) ξ(1/2 + iz + u) du` is entire in `z`, and
  `H_τ(z) = 𝒜(τ, z) + 𝒜(τ, −z)`, `𝒜(τ, −z) = conj 𝒜(conj τ, conj z)`
  (`complexHeat_eq_halfHeat_add`, `halfHeat_neg_eq_conj`). A zero of `H_τ` is a place where the two
  half transforms cancel.
* **Completing the square.** `g_τ(w + 2τa) = e^{−τa² − aw} g_τ(w)` (`complexGauss_add_saddle`): against
  an exponential `e^{au}` the Gaussian concentrates at the complex point `2τa`.
* **Corner shift.** Since `ξ` grows more slowly than any Gaussian (`exists_norm_xi_le_exp_sq`), the
  ray `[u₂, ∞)` may be moved to the height `c`:
  `∫_{u₂}^∞ g_τ(u) ξ(s + u) du = ∫_{u₂}^∞ g_τ(u + ic) ξ(s + u + ic) du + i ∫_0^c g_τ(u₂ + iv) ξ(s + u₂ + iv) dv`
  (`integral_Ioi_complexGauss_mul_xi_eq_corner`, `halfHeat_eq_corner`). With `c = Im(2τa)` the ray
  passes through the saddle point.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## `ξ` grows more slowly than any Gaussian -/

/-- For every `δ > 0`, `‖ξ(s)‖ ≤ exp(δ‖s‖² + D)` on the whole plane. -/
theorem exists_norm_xi_le_exp_sq {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℝ, ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (δ * ‖s‖ ^ 2 + D) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_complexHeat_le 0
  set ε : ℝ := δ / (4 * (C + 1)) with hε
  have hε0 : 0 < ε := by positivity
  set K : ℝ := -1 - Real.log ε with hK
  refine ⟨25 * C * ε + C * (K ^ 2 / (4 * ε)), fun s => ?_⟩
  have hxi : xi s = complexHeat 0 (-I * (s - 1 / 2)) := by
    have h := complexHeat_ofReal 0 (-I * (s - 1 / 2))
    rw [Complex.ofReal_zero] at h
    rw [h, riemannHeat_zero]
    congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hxi]
  refine (hb _).trans (Real.exp_le_exp.2 ?_)
  set r : ℝ := ‖-I * (s - 1 / 2)‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrs : r ≤ ‖s‖ + 1 / 2 := by
    rw [hr, norm_mul, norm_neg, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  set b : ℝ := 5 / 2 + ‖s‖ with hb'
  have hb0 : 0 < b := by positivity
  have hlog0 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hlogb : Real.log (2 + r) ≤ Real.log b := Real.log_le_log (by linarith) (by linarith)
  have hlin : Real.log b ≤ ε * b + K := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hε0 hb0)
    rw [Real.log_mul hε0.ne' hb0.ne'] at h
    linarith
  have h1 : C * (1 + r) * Real.log (2 + r) ≤ C * b * (ε * b + K) := by
    have hCb : C * (1 + r) ≤ C * b := mul_le_mul_of_nonneg_left (by linarith) hC
    calc C * (1 + r) * Real.log (2 + r) ≤ C * b * Real.log (2 + r) :=
          mul_le_mul_of_nonneg_right hCb hlog0
      _ ≤ C * b * (ε * b + K) :=
          mul_le_mul_of_nonneg_left (hlogb.trans hlin) (by positivity)
  have h2 : K * b ≤ ε * b ^ 2 + K ^ 2 / (4 * ε) := by
    have e : ε * b ^ 2 + K ^ 2 / (4 * ε) - K * b = (2 * ε * b - K) ^ 2 / (4 * ε) := by
      field_simp
      ring
    have : 0 ≤ (2 * ε * b - K) ^ 2 / (4 * ε) := by positivity
    linarith
  have h3 : b ^ 2 ≤ 2 * ‖s‖ ^ 2 + 25 / 2 := by
    rw [hb']
    nlinarith [sq_nonneg (‖s‖ - 5 / 2)]
  have h4 : 4 * C * ε ≤ δ := by
    have e : 4 * C * ε = δ * (C / (C + 1)) := by
      rw [hε]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right hδ.le ((div_le_one (by positivity)).2 (by linarith))
  have h5 : C * b * (ε * b + K) ≤ 2 * C * ε * b ^ 2 + C * (K ^ 2 / (4 * ε)) := by
    have := mul_le_mul_of_nonneg_left h2 hC
    nlinarith
  have h6 : 2 * C * ε * b ^ 2 ≤ 4 * C * ε * ‖s‖ ^ 2 + 25 * C * ε := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * C * ε)
    nlinarith
  have h7 : 4 * C * ε * ‖s‖ ^ 2 ≤ δ * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
  linarith

/-! ## The complex Gaussian -/

/-- The complex Gaussian `g_τ(w) = (4πτ)^{−1/2} e^{−w²/(4τ)}`. -/
def complexGauss (τ w : ℂ) : ℂ := cexp (-(w ^ 2) / (4 * τ)) / (4 * Real.pi * τ) ^ (1 / 2 : ℂ)

theorem complexGauss_neg (τ w : ℂ) : complexGauss τ (-w) = complexGauss τ w := by
  simp only [complexGauss, neg_sq]

theorem differentiable_complexGauss (τ : ℂ) : Differentiable ℂ (complexGauss τ) := by
  unfold complexGauss
  fun_prop

theorem ne_zero_of_re_pos {τ : ℂ} (hτ : 0 < τ.re) : τ ≠ 0 := by
  rintro rfl
  simp at hτ

theorem four_pi_mul_ne_zero {τ : ℂ} (hτ : 0 < τ.re) : (4 * Real.pi * τ : ℂ) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) (ne_zero_of_re_pos hτ)

theorem four_pi_mul_cpow_ne_zero {τ : ℂ} (hτ : 0 < τ.re) :
    (4 * Real.pi * τ : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => four_pi_mul_ne_zero hτ h.1

theorem norm_four_pi_mul_cpow {τ : ℂ} (hτ : 0 < τ.re) :
    ‖(4 * Real.pi * τ : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt (4 * Real.pi * ‖τ‖) := by
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.norm_cpow_of_ne_zero (four_pi_mul_ne_zero hτ), h12, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Real.exp_zero, div_one, Real.sqrt_eq_rpow]
  congr 1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp

theorem re_one_div_four_mul_pos {τ : ℂ} (hτ : 0 < τ.re) : 0 < (1 / (4 * τ)).re := by
  have h4 : (4 * τ).re = 4 * τ.re := by simp
  rw [one_div, Complex.inv_re, h4]
  exact div_pos (by linarith)
    (Complex.normSq_pos.2 (mul_ne_zero (by norm_num) (ne_zero_of_re_pos hτ)))

/-- `Re(w²/(4τ)) = ((u² − v²) Re τ + 2uv Im τ)/(4‖τ‖²)` for `w = u + iv`. -/
theorem re_sq_div_four_mul {τ : ℂ} (hτ : 0 < τ.re) (w : ℂ) :
    (w ^ 2 / (4 * τ)).re =
      ((w.re ^ 2 - w.im ^ 2) * τ.re + 2 * w.re * w.im * τ.im) / (4 * ‖τ‖ ^ 2) := by
  have hτ0 := ne_zero_of_re_pos hτ
  have hc : starRingEnd ℂ τ ≠ 0 := (map_ne_zero _).2 hτ0
  have hnn : ((‖τ‖ ^ 2 : ℝ) : ℂ) = τ * starRingEnd ℂ τ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h : w ^ 2 / (4 * τ) = ((1 / (4 * ‖τ‖ ^ 2) : ℝ) : ℂ) * (w ^ 2 * starRingEnd ℂ τ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, hnn, Complex.ofReal_ofNat]
    field_simp
  rw [h, Complex.re_ofReal_mul]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq, Complex.mul_im]
  ring

theorem norm_complexGauss {τ : ℂ} (hτ : 0 < τ.re) (w : ℂ) :
    ‖complexGauss τ w‖ =
      Real.exp (-(w ^ 2 / (4 * τ)).re) / Real.sqrt (4 * Real.pi * ‖τ‖) := by
  rw [complexGauss, norm_div, Complex.norm_exp, norm_four_pi_mul_cpow hτ, neg_div, Complex.neg_re]

/-- On the real axis the modulus is a Gaussian of rate `Re τ/(4‖τ‖²)`. -/
theorem norm_complexGauss_ofReal {τ : ℂ} (hτ : 0 < τ.re) (u : ℝ) :
    ‖complexGauss τ u‖ =
      Real.exp (-(τ.re / (4 * ‖τ‖ ^ 2)) * u ^ 2) / Real.sqrt (4 * Real.pi * ‖τ‖) := by
  rw [norm_complexGauss hτ, re_sq_div_four_mul hτ]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  congr 2
  ring

/-- Off the real axis the modulus still decays in the real direction, at half the rate. -/
theorem norm_complexGauss_le {τ : ℂ} (hτ : 0 < τ.re) (w : ℂ) :
    ‖complexGauss τ w‖ ≤
      Real.exp (-(τ.re / (8 * ‖τ‖ ^ 2)) * w.re ^ 2 +
        (τ.re + 2 * τ.im ^ 2 / τ.re) / (4 * ‖τ‖ ^ 2) * w.im ^ 2) /
        Real.sqrt (4 * Real.pi * ‖τ‖) := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  rw [norm_complexGauss hτ, re_sq_div_four_mul hτ]
  have key : -((w.re ^ 2 - w.im ^ 2) * τ.re + 2 * w.re * w.im * τ.im) ≤
      -(τ.re / 2) * w.re ^ 2 + (τ.re + 2 * τ.im ^ 2 / τ.re) * w.im ^ 2 := by
    have e : τ.re / 2 * w.re ^ 2 + 2 * w.re * w.im * τ.im + 2 * τ.im ^ 2 / τ.re * w.im ^ 2 =
        (τ.re * w.re + 2 * τ.im * w.im) ^ 2 / (2 * τ.re) := by
      field_simp
      ring
    have : 0 ≤ (τ.re * w.re + 2 * τ.im * w.im) ^ 2 / (2 * τ.re) := by positivity
    linarith
  have e2 : -(τ.re / (8 * ‖τ‖ ^ 2)) * w.re ^ 2 +
      (τ.re + 2 * τ.im ^ 2 / τ.re) / (4 * ‖τ‖ ^ 2) * w.im ^ 2 =
      (-(τ.re / 2) * w.re ^ 2 + (τ.re + 2 * τ.im ^ 2 / τ.re) * w.im ^ 2) / (4 * ‖τ‖ ^ 2) := by
    field_simp
    ring
  rw [e2, ← neg_div]
  exact div_le_div_of_nonneg_right
    (Real.exp_le_exp.2 (div_le_div_of_nonneg_right key (by positivity))) (Real.sqrt_nonneg _)

/-- **The moment generating function**: `∫ g_τ(u) e^{ux} du = e^{τx²}`. -/
theorem integral_complexGauss_mul_exp {τ : ℂ} (hτ : 0 < τ.re) (x : ℂ) :
    ∫ u : ℝ, complexGauss τ u * cexp (u * x) = cexp (τ * x ^ 2) := by
  have hτ0 := ne_zero_of_re_pos hτ
  have hb : (-(1 / (4 * τ))).re < 0 := by
    rw [Complex.neg_re]
    linarith [re_one_div_four_mul_pos hτ]
  have hquad := integral_cexp_quadratic hb x 0
  have hfun : ∀ u : ℝ, complexGauss τ u * cexp (u * x) =
      cexp (-(1 / (4 * τ)) * (u : ℂ) ^ 2 + x * u + 0) / (4 * Real.pi * τ) ^ (1 / 2 : ℂ) := by
    intro u
    rw [complexGauss, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hfun]
  rw [integral_div, hquad]
  have hpi : (Real.pi : ℂ) / -(-(1 / (4 * τ))) = 4 * Real.pi * τ := by
    rw [neg_neg, div_div_eq_mul_div, div_one]
    ring
  have hexp : (0 : ℂ) - x ^ 2 / (4 * -(1 / (4 * τ))) = τ * x ^ 2 := by
    field_simp
    ring
  rw [hpi, hexp]
  exact mul_div_cancel_left₀ _ (four_pi_mul_cpow_ne_zero hτ)

theorem integrable_complexGauss_mul_exp {τ : ℂ} (hτ : 0 < τ.re) (x : ℂ) :
    Integrable fun u : ℝ => complexGauss τ u * cexp (u * x) := by
  refine ((integrable_cexp_quadratic (re_one_div_four_mul_pos hτ) x 0).div_const
    ((4 * Real.pi * τ) ^ (1 / 2 : ℂ))).congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [complexGauss, div_mul_eq_mul_div, ← Complex.exp_add]
  congr 2
  ring

/-- **Completing the square**: `g_τ(w + 2τa) = e^{−τa² − aw} g_τ(w)`. -/
theorem complexGauss_add_saddle {τ : ℂ} (hτ : τ ≠ 0) (a w : ℂ) :
    complexGauss τ (w + 2 * τ * a) = cexp (-(τ * a ^ 2) - a * w) * complexGauss τ w := by
  rw [complexGauss, complexGauss, ← mul_div_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

theorem complexGauss_conj {τ : ℂ} (hτ : 0 < τ.re) (w : ℂ) :
    starRingEnd ℂ (complexGauss τ w) = complexGauss (starRingEnd ℂ τ) (starRingEnd ℂ w) := by
  have harg : (4 * Real.pi * τ : ℂ).arg ≠ Real.pi := by
    have hre : 0 < (4 * Real.pi * τ : ℂ).re := by
      have : (4 * Real.pi * τ : ℂ).re = 4 * Real.pi * τ.re := by
        rw [show (4 * Real.pi * τ : ℂ) = ((4 * Real.pi : ℝ) : ℂ) * τ by push_cast; ring,
          Complex.re_ofReal_mul]
      rw [this]
      positivity
    have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    intro h'
    rw [h', abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_pos]
  have hc := Complex.conj_cpow (4 * Real.pi * τ) (1 / 2 : ℂ) harg
  have h12 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp
  have h4 : starRingEnd ℂ (4 * Real.pi * τ : ℂ) = 4 * Real.pi * starRingEnd ℂ τ := by
    simp [Complex.conj_ofReal]
  rw [h12, h4] at hc
  rw [complexGauss, complexGauss, map_div₀, ← Complex.exp_conj, hc]
  congr 2
  simp

theorem continuous_complexGauss_mul_xi (τ s : ℂ) (h : ℝ) :
    Continuous fun u : ℝ => complexGauss τ (u + h * I) * xi (s + (u + h * I)) := by
  have h1 := (differentiable_complexGauss τ).continuous
  have h2 := xi_differentiable.continuous
  fun_prop

/-! ## The Gaussian representation -/

/-- The product integrand `g_τ(u) e^{ux} · Φ(x) e^{izx}`. -/
def complexGaussProduct (τ z : ℂ) (x u : ℝ) : ℂ :=
  complexGauss τ u * cexp (u * x) * ((riemannKernelReal x : ℂ) * cexp (I * z * x))

/-- On the real axis the modulus of `g_τ` is a multiple of the normal density of variance
`2‖τ‖²/Re τ`. -/
theorem exists_norm_complexGauss_eq_mul_gaussDensity {τ : ℂ} (hτ : 0 < τ.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, ‖complexGauss τ u‖ = c * gaussDensity (‖τ‖ ^ 2 / τ.re) u := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  have ht' : 0 < ‖τ‖ ^ 2 / τ.re := by positivity
  have hp : 0 < (4 * Real.pi * (‖τ‖ ^ 2 / τ.re)) ^ (-(1 / 2 : ℝ)) := by positivity
  have hs : 0 < Real.sqrt (4 * Real.pi * ‖τ‖) := Real.sqrt_pos.2 (by positivity)
  refine ⟨1 / Real.sqrt (4 * Real.pi * ‖τ‖) / (4 * Real.pi * (‖τ‖ ^ 2 / τ.re)) ^ (-(1 / 2 : ℝ)),
    by positivity, fun u => ?_⟩
  rw [norm_complexGauss_ofReal hτ, gaussDensity]
  have e : -(τ.re / (4 * ‖τ‖ ^ 2)) * u ^ 2 = -(u ^ 2 / (4 * (‖τ‖ ^ 2 / τ.re))) := by
    field_simp
  rw [e, div_mul_eq_mul_div, one_mul, ← mul_assoc, div_mul_cancel₀ _ hp.ne', one_div,
    inv_mul_eq_div]

theorem integrable_complexGaussProduct {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) :
    Integrable (Function.uncurry (complexGaussProduct τ z)) (volume.prod volume) := by
  obtain ⟨c, -, hnorm⟩ := exists_norm_complexGauss_eq_mul_gaussDensity hτ
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  set t' : ℝ := ‖τ‖ ^ 2 / τ.re with ht'
  have ht'0 : 0 < t' := by positivity
  have hcont : Continuous (Function.uncurry (complexGaussProduct τ z)) := by
    have hg := (differentiable_complexGauss τ).continuous
    have hΦ := continuous_riemannKernelReal
    simp only [complexGaussProduct, Function.uncurry_def]
    fun_prop
  refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · simp only [Function.uncurry_apply_pair, complexGaussProduct]
    exact (integrable_complexGauss_mul_exp hτ x).mul_const _
  · have hheat := (((riemannKernel_superExp.mul_exp_sq ht'0.le).integrable z).norm).const_mul c
    refine hheat.congr (Eventually.of_forall fun x => ?_)
    have hpt : ∀ u : ℝ, ‖Function.uncurry (complexGaussProduct τ z) (x, u)‖ =
        c * (gaussDensity t' u * Real.exp (u * x)) *
          (riemannKernelReal x * Real.exp (-(z.im * x))) := by
      intro u
      rw [Function.uncurry_apply_pair, complexGaussProduct, norm_mul, norm_mul, hnorm,
        norm_integrand, abs_of_pos (riemannKernelReal_pos x), Complex.norm_exp,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    simp_rw [hpt]
    have h := norm_integrand (fun x => riemannKernelReal x * Real.exp (t' * x ^ 2)) z x
    rw [integral_mul_const, integral_const_mul, integral_gaussDensity_mul_rexp ht'0, h,
      abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]
    ring

theorem integral_complexGaussProduct_left {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) (x : ℝ) :
    ∫ u, complexGaussProduct τ z x u =
      (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2 + I * z * x) := by
  simp only [complexGaussProduct]
  rw [integral_mul_const, integral_complexGauss_mul_exp hτ, Complex.exp_add]
  ring

theorem integral_complexGaussProduct_right (τ z : ℂ) (u : ℝ) :
    ∫ x, complexGaussProduct τ z x u = complexGauss τ u * xi (1 / 2 + I * z + u) := by
  have hre : ∀ x : ℝ, complexGaussProduct τ z x u =
      complexGauss τ u * ((riemannKernelReal x : ℂ) * cexp (I * (z - I * u) * x)) := by
    intro x
    have he : cexp (u * x) * cexp (I * z * x) = cexp (I * (z - I * u) * x) := by
      rw [← Complex.exp_add]
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    simp only [complexGaussProduct]
    linear_combination (complexGauss τ u * (riemannKernelReal x : ℂ)) * he
  simp_rw [hre]
  rw [integral_const_mul]
  change _ * cosTransform riemannKernelReal (z - I * u) = _
  rw [cosTransform_riemannKernel]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex Gaussian average of `ξ` along a horizontal line converges absolutely. -/
theorem integrable_complexGauss_mul_xi {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) :
    Integrable fun u : ℝ => complexGauss τ u * xi (1 / 2 + I * z + u) := by
  have h := (integrable_complexGaussProduct hτ z).integral_prod_right
  simp only [Function.uncurry_apply_pair, integral_complexGaussProduct_right] at h
  exact h

/-- **The heat family is a complex Gaussian average of `ξ`.** For `Re τ > 0`,
`H_τ(z) = ∫ g_τ(u) ξ(1/2 + iz + u) du`. -/
theorem complexHeat_eq_integral_complexGauss_mul_xi {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) :
    complexHeat τ z = ∫ u : ℝ, complexGauss τ u * xi (1 / 2 + I * z + u) := by
  calc complexHeat τ z = ∫ x, ∫ u, complexGaussProduct τ z x u := by
        unfold complexHeat
        simp_rw [integral_complexGaussProduct_left hτ]
    _ = ∫ u, ∫ x, complexGaussProduct τ z x u :=
        integral_integral_swap (integrable_complexGaussProduct hτ z)
    _ = _ := by simp_rw [integral_complexGaussProduct_right]

/-! ## The half transform -/

/-- The half transform `𝒜(τ, z) = ∫_0^∞ g_τ(u) ξ(1/2 + iz + u) du`. -/
def halfHeat (τ z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), complexGauss τ u * xi (1 / 2 + I * z + u)

/-- `H_τ(z) = 𝒜(τ, z) + 𝒜(τ, −z)`. -/
theorem complexHeat_eq_halfHeat_add {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) :
    complexHeat τ z = halfHeat τ z + halfHeat τ (-z) := by
  set f : ℝ → ℂ := fun u => complexGauss τ u * xi (1 / 2 + I * z + u) with hf
  have hfi : Integrable f := integrable_complexGauss_mul_xi hτ z
  have h0 : complexHeat τ z = ∫ u, f u := complexHeat_eq_integral_complexGauss_mul_xi hτ z
  have hneg : ∫ u in Iic (0 : ℝ), f u = ∫ u in Ioi (0 : ℝ), f (-u) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  rw [h0, ← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hfi, compl_Ioi, hneg,
    halfHeat, halfHeat]
  refine congrArg₂ (· + ·) rfl
    (setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun u _ => ?_)
  simp only [hf]
  rw [Complex.ofReal_neg, complexGauss_neg, ← xi_one_sub]
  congr 2
  ring

/-- `𝒜(τ, −z) = conj 𝒜(conj τ, conj z)`. -/
theorem halfHeat_neg_eq_conj {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) :
    halfHeat τ (-z) = starRingEnd ℂ (halfHeat (starRingEnd ℂ τ) (starRingEnd ℂ z)) := by
  have hτ' : 0 < (starRingEnd ℂ τ).re := by simpa using hτ
  rw [halfHeat, halfHeat, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only
  rw [map_mul, complexGauss_conj hτ', Complex.conj_conj, Complex.conj_ofReal, ← xi_conj]
  congr 2
  apply Complex.ext <;> simp

/-- The half transform is entire in the place. -/
theorem differentiable_halfHeat {τ : ℂ} (hτ : 0 < τ.re) : Differentiable ℂ (halfHeat τ) := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  set lam : ℝ := τ.re / (4 * ‖τ‖ ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  obtain ⟨D, hD⟩ := exists_norm_xi_le_exp_sq (δ := lam / 4) (by positivity)
  set S : ℝ := Real.sqrt (4 * Real.pi * ‖τ‖) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  refine differentiableOn_univ.1 (differentiableOn_integral_of_locally_bounded isOpen_univ
    (ν := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (u : ℝ) (z : ℂ) => complexGauss τ u * xi (1 / 2 + I * z + u))
    (fun u => Differentiable.differentiableOn (by have := xi_differentiable; fun_prop))
    (fun z _ => ?_) fun z₀ _ => ?_)
  · have h := continuous_complexGauss_mul_xi τ (1 / 2 + I * z) 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.aestronglyMeasurable
  · set B : ℝ := 3 / 2 + ‖z₀‖ with hB
    refine ⟨1, one_pos, subset_univ _,
      fun u => Real.exp (-(lam / 2) * u ^ 2) * (Real.exp (lam / 2 * B ^ 2 + D) / S),
      ((integrable_exp_neg_mul_sq (by positivity : 0 < lam / 2)).mul_const _).restrict,
      fun u z hz => ?_⟩
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h1 := norm_le_norm_add_norm_sub' z z₀
      have h2 : ‖z - z₀‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
      linarith
    have hs : ‖(1 / 2 : ℂ) + I * z + u‖ ≤ B + |u| := by
      have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      have h2 : ‖I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      have h3 : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have := norm_add₃_le (a := (1 / 2 : ℂ)) (b := I * z) (c := (u : ℂ))
      rw [h1, h2, h3] at this
      linarith
    have hsq : ‖(1 / 2 : ℂ) + I * z + u‖ ^ 2 ≤ 2 * B ^ 2 + 2 * u ^ 2 := by
      have hB0 : 0 ≤ B := by positivity
      have := pow_le_pow_left₀ (norm_nonneg _) hs 2
      nlinarith [sq_nonneg (B - |u|), sq_abs u]
    rw [norm_mul, norm_complexGauss_ofReal hτ]
    calc Real.exp (-lam * u ^ 2) / S * ‖xi (1 / 2 + I * z + u)‖
        ≤ Real.exp (-lam * u ^ 2) / S * Real.exp (lam / 4 * ‖(1 / 2 : ℂ) + I * z + u‖ ^ 2 + D) :=
          mul_le_mul_of_nonneg_left (hD _) (by positivity)
      _ = Real.exp (-lam * u ^ 2 + (lam / 4 * ‖(1 / 2 : ℂ) + I * z + u‖ ^ 2 + D)) / S := by
          rw [Real.exp_add (-lam * u ^ 2)]
          ring
      _ ≤ Real.exp (-(lam / 2) * u ^ 2 + (lam / 2 * B ^ 2 + D)) / S := by
          refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) hS0.le
          have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ lam / 4)
          linarith
      _ = _ := by
          rw [Real.exp_add]
          ring

/-! ## The corner shift -/

/-- On a horizontal strip `g_τ(w) ξ(s + w)` decays like a Gaussian in `Re w`. -/
theorem exists_norm_complexGauss_mul_xi_le {τ : ℂ} (hτ : 0 < τ.re) (s : ℂ) (V : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, |w.im| ≤ V →
      ‖complexGauss τ w * xi (s + w)‖ ≤ A * Real.exp (-(τ.re / (16 * ‖τ‖ ^ 2)) * w.re ^ 2) := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  set lam : ℝ := τ.re / (8 * ‖τ‖ ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  have hl2 : τ.re / (16 * ‖τ‖ ^ 2) = lam / 2 := by
    rw [hlam]
    ring
  set μ : ℝ := (τ.re + 2 * τ.im ^ 2 / τ.re) / (4 * ‖τ‖ ^ 2) with hμ
  have hμ0 : 0 ≤ μ := by positivity
  obtain ⟨D, hD⟩ := exists_norm_xi_le_exp_sq (δ := lam / 6) (by positivity)
  set S : ℝ := Real.sqrt (4 * Real.pi * ‖τ‖) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  refine ⟨Real.exp (μ * V ^ 2 + lam / 2 * (‖s‖ ^ 2 + V ^ 2) + D) / S, by positivity,
    fun w hw => ?_⟩
  have hv2 : w.im ^ 2 ≤ V ^ 2 := sq_le_sq.2 (hw.trans (le_abs_self V))
  have h1 : ‖complexGauss τ w‖ ≤ Real.exp (-lam * w.re ^ 2 + μ * w.im ^ 2) / S :=
    norm_complexGauss_le hτ w
  have h3 : ‖s + w‖ ^ 2 ≤ 3 * (‖s‖ ^ 2 + w.re ^ 2 + w.im ^ 2) := by
    have ha : ‖s + w‖ ≤ ‖s‖ + (|w.re| + |w.im|) :=
      (norm_add_le _ _).trans (add_le_add_left (Complex.norm_le_abs_re_add_abs_im w) _)
    have hb : (‖s‖ + (|w.re| + |w.im|)) ^ 2 ≤ 3 * (‖s‖ ^ 2 + w.re ^ 2 + w.im ^ 2) := by
      nlinarith [sq_nonneg (‖s‖ - |w.re|), sq_nonneg (‖s‖ - |w.im|),
        sq_nonneg (|w.re| - |w.im|), sq_abs w.re, sq_abs w.im]
    exact (pow_le_pow_left₀ (norm_nonneg _) ha 2).trans hb
  rw [norm_mul, hl2]
  calc ‖complexGauss τ w‖ * ‖xi (s + w)‖
      ≤ Real.exp (-lam * w.re ^ 2 + μ * w.im ^ 2) / S *
          Real.exp (lam / 6 * ‖s + w‖ ^ 2 + D) :=
        mul_le_mul h1 (hD _) (norm_nonneg _) (by positivity)
    _ = Real.exp (-lam * w.re ^ 2 + μ * w.im ^ 2 + (lam / 6 * ‖s + w‖ ^ 2 + D)) / S := by
        rw [Real.exp_add (-lam * w.re ^ 2 + μ * w.im ^ 2)]
        ring
    _ ≤ Real.exp (μ * V ^ 2 + lam / 2 * (‖s‖ ^ 2 + V ^ 2) + D + -(lam / 2) * w.re ^ 2) / S := by
        refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) hS0.le
        have e1 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ lam / 6)
        have e2 := mul_le_mul_of_nonneg_left hv2 hμ0
        have e3 := mul_le_mul_of_nonneg_left hv2 (by positivity : 0 ≤ lam / 2)
        linarith
    _ = _ := by
        rw [Real.exp_add]
        ring

/-- **Corner shift.** The ray `[u₂, ∞)` may be moved to the height `c`, at the cost of the
vertical side at `u₂`. -/
theorem integral_Ioi_complexGauss_mul_xi_eq_corner {τ : ℂ} (hτ : 0 < τ.re) (s : ℂ) (u₂ c : ℝ) :
    ∫ u in Ioi u₂, complexGauss τ u * xi (s + u) =
      (∫ u in Ioi u₂, complexGauss τ (u + c * I) * xi (s + (u + c * I))) +
        I * ∫ v in (0 : ℝ)..c, complexGauss τ (u₂ + v * I) * xi (s + (u₂ + v * I)) := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  set f : ℂ → ℂ := fun w => complexGauss τ w * xi (s + w) with hf
  have hfd : Differentiable ℂ f := by
    have h1 := differentiable_complexGauss τ
    have h2 := xi_differentiable
    simp only [hf]
    fun_prop
  obtain ⟨A, -, hA⟩ := exists_norm_complexGauss_mul_xi_le hτ s |c|
  set lam : ℝ := τ.re / (16 * ‖τ‖ ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  -- horizontal lines of height at most `|c|`
  have hint : ∀ h : ℝ, |h| ≤ |c| → Integrable fun u : ℝ => f (u + h * I) := by
    intro h hh
    refine ((integrable_exp_neg_mul_sq hlam0).const_mul A).mono'
      (continuous_complexGauss_mul_xi τ s h).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    have := hA (u + h * I) (by simpa using hh)
    simpa using this
  have hint0 : Integrable fun u : ℝ => f u := by
    have := hint 0 (by simp)
    simpa using this
  -- Cauchy's theorem on the rectangle with corners `u₂` and `N + ic`
  have hrect : ∀ N : ℝ, (∫ x in u₂..N, f x) =
      (∫ x in u₂..N, f (x + c * I)) - I * (∫ y in (0 : ℝ)..c, f (N + y * I)) +
        I * ∫ y in (0 : ℝ)..c, f (u₂ + y * I) := by
    intro N
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (u₂ : ℂ) (N + c * I)
      hfd.differentiableOn
    have e1 : ((u₂ : ℂ)).re = u₂ := Complex.ofReal_re _
    have e2 : ((u₂ : ℂ)).im = 0 := Complex.ofReal_im _
    have e3 : ((N : ℂ) + c * I).re = N := by simp
    have e4 : ((N : ℂ) + c * I).im = c := by simp
    rw [e1, e2, e3, e4] at h
    simp only [Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul] at h
    linear_combination h
  have hL1 : Tendsto (fun N : ℝ => ∫ x in u₂..N, f x) atTop (𝓝 (∫ x in Ioi u₂, f x)) :=
    intervalIntegral_tendsto_integral_Ioi u₂ hint0.integrableOn tendsto_id
  have hL2 : Tendsto (fun N : ℝ => ∫ x in u₂..N, f (x + c * I)) atTop
      (𝓝 (∫ x in Ioi u₂, f (x + c * I))) :=
    intervalIntegral_tendsto_integral_Ioi u₂ (hint c le_rfl).integrableOn tendsto_id
  -- the far vertical side tends to zero
  have hL3 : Tendsto (fun N : ℝ => I * ∫ y in (0 : ℝ)..c, f (N + y * I)) atTop (𝓝 0) := by
    have hb : ∀ N : ℝ, ‖I * ∫ y in (0 : ℝ)..c, f (N + y * I)‖ ≤
        A * Real.exp (-lam * N ^ 2) * |c - 0| := by
      intro N
      rw [norm_mul, Complex.norm_I, one_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      have hy' : |y| ≤ |c| := by
        rcases le_total 0 c with h | h
        · rw [uIoc_of_le h] at hy
          rw [abs_of_pos hy.1, abs_of_nonneg h]
          exact hy.2
        · rw [uIoc_of_ge h] at hy
          rw [abs_of_nonpos hy.2, abs_of_nonpos h]
          linarith [hy.1]
      have := hA (N + y * I) (by simpa using hy')
      simpa using this
    have hz : Tendsto (fun N : ℝ => A * Real.exp (-lam * N ^ 2) * |c - 0|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℝ => -lam * N ^ 2) atTop atBot := by
        have h0 : Tendsto (fun N : ℝ => lam * N ^ 2) atTop atTop :=
          (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop hlam0
        have := tendsto_neg_atTop_atBot.comp h0
        refine this.congr fun N => ?_
        simp only [Function.comp_apply]
        ring
      have h2 := ((Real.tendsto_exp_atBot.comp h1).const_mul A).mul_const |c - 0|
      simpa using h2
    exact squeeze_zero_norm hb hz
  have hR : Tendsto (fun N : ℝ => ∫ x in u₂..N, f x) atTop
      (𝓝 ((∫ x in Ioi u₂, f (x + c * I)) - 0 + I * ∫ y in (0 : ℝ)..c, f (u₂ + y * I))) :=
    ((hL2.sub hL3).add_const _).congr fun N => (hrect N).symm
  have hfin := tendsto_nhds_unique hL1 hR
  rw [sub_zero] at hfin
  exact hfin

/-- **The half transform through a corner.** For every corner `u₂` and height `c`,
`𝒜(τ, z)` is the sum of the unshifted piece on `[0, u₂]`, the vertical side at `u₂` and the ray
at height `c`. -/
theorem halfHeat_eq_corner {τ : ℂ} (hτ : 0 < τ.re) (z : ℂ) (u₂ c : ℝ) :
    halfHeat τ z =
      (∫ u in (0 : ℝ)..u₂, complexGauss τ u * xi (1 / 2 + I * z + u)) +
        I * (∫ v in (0 : ℝ)..c,
          complexGauss τ (u₂ + v * I) * xi (1 / 2 + I * z + (u₂ + v * I))) +
        ∫ u in Ioi u₂, complexGauss τ (u + c * I) * xi (1 / 2 + I * z + (u + c * I)) := by
  have hfi := integrable_complexGauss_mul_xi hτ z
  rw [halfHeat, ← intervalIntegral.integral_interval_add_Ioi (a := 0) (b := u₂) hfi.integrableOn
    hfi.integrableOn, integral_Ioi_complexGauss_mul_xi_eq_corner hτ (1 / 2 + I * z) u₂ c]
  ring

end

end GaloisForLFunctions.GaloisTheoryOfZeros
