import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage

/-!
# The complex saddle of a Gaussian average

Let `F` be entire and `S = ∫_0^{x₂} g_τ(x − y) F(x) dx`. A real saddle freezes `F` across the Gaussian window, so
it needs `|F′/F − ℓ| √τ ≪ 1`. A size bound `|F| ≤ T^ε` only gives `|F′/F − ℓ| ≍ log T`, and then the phase of `F`
rotates many times across the window.

The rotation disappears on the horizontal line through the complex fixed point `u = y + 2τℓ`, with
`ℓ = F′/F(u)`. There the Gaussian and the exponential model of `F` combine exactly:

`g_τ(u + v − y) F(u) e^{ℓv} = F(u) e^{−τℓ²} g_τ(v)`.

So only the second-order term of `log F` remains, and it costs `τ |(log F)″|`, which is small. This file proves, for
an abstract `F`:

* `integral_eq_shift_add_edges`: the contour shift;
* `integral_gaussDensity_mul_exp_sq`, `gaussExcess_le`: the Gaussian integral of `exp(Bv²)`;
* `SaddleData.norm_integral_sub_main_le`: `S = F(u) e^{−τℓ²} (1 + small)`;
* `SaddleData.norm_integral_slope_le`: the first moment about `u` is small, i.e. `S′ = ℓ S + small`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped Interval
open _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ## The complex Gaussian -/

/-- The entire Gaussian `g_τ(z) = (4πτ)^{−½} exp(−z²/(4τ))`. -/
def gaussKernel (τ : ℝ) (z : ℂ) : ℂ :=
  (((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(z ^ 2 / ((4 * τ : ℝ) : ℂ)))

theorem differentiable_gaussKernel (τ : ℝ) : Differentiable ℂ (gaussKernel τ) := by
  unfold gaussKernel
  fun_prop

theorem gaussKernel_ofReal (τ x : ℝ) : gaussKernel τ (x : ℂ) = (gaussDensity τ x : ℂ) := by
  unfold gaussKernel gaussDensity
  push_cast
  rfl

/-- The modulus of the kernel on a horizontal line. -/
theorem norm_gaussKernel {τ : ℝ} (hτ : 0 < τ) (x v : ℝ) :
    ‖gaussKernel τ ((x : ℂ) + (v : ℂ) * I)‖ =
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x ^ 2 - v ^ 2) / (4 * τ))) := by
  have hsq : (((x : ℂ) + (v : ℂ) * I) ^ 2).re = x ^ 2 - v ^ 2 := by
    rw [sq]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  unfold gaussKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp,
    Complex.neg_re, Complex.div_ofReal_re, hsq]

/-! ## The contour shift -/

/-- **Contour shift.** An entire integrand moves to the line at height `δ` at the cost of its two vertical edges. -/
theorem integral_eq_shift_add_edges {G : ℂ → ℂ} (hG : Differentiable ℂ G) (A B δ : ℝ) :
    (∫ x in A..B, G (x : ℂ)) =
      (∫ x in A..B, G ((x : ℂ) + (δ : ℂ) * I)) +
        I * (∫ v in (0 : ℝ)..δ, G ((A : ℂ) + (v : ℂ) * I)) -
        I * (∫ v in (0 : ℝ)..δ, G ((B : ℂ) + (v : ℂ) * I)) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G (A : ℂ)
    ((B : ℂ) + (δ : ℂ) * I) hG.differentiableOn
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add, Complex.ofReal_zero, zero_mul, smul_eq_mul] at h
  linear_combination h

/-! ## Gaussian integrals -/

/-- The Gaussian integral of `exp(Bv²)` below the blow-up time. -/
theorem integrable_and_integral_gaussDensity_mul_exp_sq {t B : ℝ} (ht : 0 < t) (hB : 4 * t * B < 1) :
    Integrable (fun v : ℝ => gaussDensity t v * Real.exp (B * v ^ 2)) ∧
      (∫ v : ℝ, gaussDensity t v * Real.exp (B * v ^ 2)) = (Real.sqrt (1 - 4 * t * B))⁻¹ := by
  have hq : 0 < 1 - 4 * t * B := by linarith only [hB]
  have hb : 0 < (1 - 4 * t * B) / (4 * t) := by positivity
  have hrew (v : ℝ) : gaussDensity t v * Real.exp (B * v ^ 2) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 - 4 * t * B) / (4 * t)) * v ^ 2) := by
    unfold gaussDensity
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hrew]
  refine ⟨(integrable_exp_neg_mul_sq hb).const_mul _, ?_⟩
  rw [integral_const_mul, integral_gaussian]
  have hp : 0 < 4 * Real.pi * t := by positivity
  have hdiv : Real.pi / ((1 - 4 * t * B) / (4 * t)) = (4 * Real.pi * t) / (1 - 4 * t * B) := by
    field_simp
  rw [hdiv, Real.sqrt_div hp.le, Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  have hsp : Real.sqrt (4 * Real.pi * t) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsq : Real.sqrt (1 - 4 * t * B) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  field_simp

theorem integral_gaussDensity_mul_exp_sq {t B : ℝ} (ht : 0 < t) (hB : 4 * t * B < 1) :
    (∫ v : ℝ, gaussDensity t v * Real.exp (B * v ^ 2)) = (Real.sqrt (1 - 4 * t * B))⁻¹ :=
  (integrable_and_integral_gaussDensity_mul_exp_sq ht hB).2

theorem integrable_gaussDensity {t : ℝ} (ht : 0 < t) : Integrable (gaussDensity t) := by
  have h := (integrable_and_integral_gaussDensity_mul_exp_sq (B := 0) ht (by norm_num)).1
  simpa only [zero_mul, Real.exp_zero, mul_one] using h

theorem integral_gaussDensity_eq_one {t : ℝ} (ht : 0 < t) : (∫ v : ℝ, gaussDensity t v) = 1 := by
  have h := integral_gaussDensity_mul_exp_sq (B := 0) ht (by norm_num)
  simpa only [zero_mul, Real.exp_zero, mul_one, sub_zero, Real.sqrt_one, inv_one] using h

/-- The excess integrand of a quadratic exponent. -/
theorem integrable_gaussExcess {t B : ℝ} (ht : 0 < t) (hB : 4 * t * B < 1) :
    Integrable (fun v : ℝ => gaussDensity t v * (Real.exp (B * v ^ 2) - 1)) := by
  have h := (integrable_and_integral_gaussDensity_mul_exp_sq ht hB).1.sub (integrable_gaussDensity ht)
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **The excess of a quadratic exponent is linear in the time.** -/
theorem gaussExcess_le {t B : ℝ} (ht : 0 < t) (hB0 : 0 ≤ B) (hB : 4 * t * B ≤ 1 / 2) :
    (∫ v : ℝ, gaussDensity t v * (Real.exp (B * v ^ 2) - 1)) ≤ 8 * t * B := by
  have hq : 4 * t * B < 1 := by linarith only [hB]
  have hsplit : (∫ v : ℝ, gaussDensity t v * (Real.exp (B * v ^ 2) - 1)) =
      (∫ v : ℝ, gaussDensity t v * Real.exp (B * v ^ 2)) - ∫ v : ℝ, gaussDensity t v := by
    rw [← integral_sub (integrable_and_integral_gaussDensity_mul_exp_sq ht hq).1
      (integrable_gaussDensity ht)]
    congr 1
    funext v
    ring
  rw [hsplit, integral_gaussDensity_mul_exp_sq ht hq, integral_gaussDensity_eq_one ht]
  obtain ⟨q, hqdef⟩ : ∃ q, q = 4 * t * B := ⟨_, rfl⟩
  rw [← hqdef] at hq hB ⊢
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hsq : 1 - q ≤ Real.sqrt (1 - q) := by
    have h01 : 0 ≤ 1 - q := by linarith only [hq]
    have h1 : 1 - q ≤ 1 := by linarith only [hq0]
    rw [Real.le_sqrt h01]
    nlinarith only [h01, h1]
  have hs0 : 0 < 1 - q := by linarith only [hq]
  have hinv : (Real.sqrt (1 - q))⁻¹ ≤ (1 - q)⁻¹ := inv_anti₀ hs0 hsq
  have h2 : (1 - q)⁻¹ ≤ 1 + 2 * q := by
    rw [inv_le_comm₀ hs0 (by linarith only [hq0]), inv_le_iff_one_le_mul₀ (by linarith only [hq0])]
    nlinarith only [hq0, hB]
  have he : 8 * t * B = 2 * q := by rw [hqdef]; ring
  rw [he]
  linarith only [hinv, h2]

/-- The Gaussian tail beyond `ρ`, at the exponent `ρ²/(8τ)`. -/
theorem integral_gaussDensity_compl_le {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 ≤ ρ) :
    (∫ v in (Ioc (-ρ) ρ)ᶜ, gaussDensity τ v) ≤ 2 * Real.exp (-(ρ ^ 2 / (8 * τ))) := by
  have hBq : 4 * τ * (1 / (8 * τ)) = 1 / 2 := by field_simp; norm_num
  obtain ⟨hint, hval⟩ := integrable_and_integral_gaussDensity_mul_exp_sq (B := 1 / (8 * τ)) hτ
    (by rw [hBq]; norm_num)
  have hmono : (∫ v in (Ioc (-ρ) ρ)ᶜ, gaussDensity τ v) ≤
      ∫ v in (Ioc (-ρ) ρ)ᶜ, Real.exp (-(ρ ^ 2 / (8 * τ))) *
        (gaussDensity τ v * Real.exp (1 / (8 * τ) * v ^ 2)) := by
    refine setIntegral_mono_on (integrable_gaussDensity hτ).integrableOn
      (hint.const_mul _).integrableOn measurableSet_Ioc.compl fun v hv => ?_
    have hsq : ρ ^ 2 ≤ v ^ 2 := by
      have hv' : ¬ (-ρ < v ∧ v ≤ ρ) := hv
      by_cases h1 : -ρ < v
      · have h2 : ρ < v := lt_of_not_ge fun h => hv' ⟨h1, h⟩
        nlinarith only [hρ, h2]
      · have h2 : v ≤ -ρ := not_lt.mp h1
        nlinarith only [hρ, h2]
    have hg := (gaussDensity_pos hτ v).le
    have hexp : 1 ≤ Real.exp (-(ρ ^ 2 / (8 * τ))) * Real.exp (1 / (8 * τ) * v ^ 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have he : -(ρ ^ 2 / (8 * τ)) + 1 / (8 * τ) * v ^ 2 = (v ^ 2 - ρ ^ 2) / (8 * τ) := by
        field_simp
        ring
      rw [he]
      exact div_nonneg (by linarith only [hsq]) (by positivity)
    calc
      _ ≤ gaussDensity τ v * (Real.exp (-(ρ ^ 2 / (8 * τ))) * Real.exp (1 / (8 * τ) * v ^ 2)) :=
        le_mul_of_one_le_right hg hexp
      _ = _ := by ring
  have hall : (∫ v in (Ioc (-ρ) ρ)ᶜ, Real.exp (-(ρ ^ 2 / (8 * τ))) *
      (gaussDensity τ v * Real.exp (1 / (8 * τ) * v ^ 2))) ≤
      ∫ v : ℝ, Real.exp (-(ρ ^ 2 / (8 * τ))) *
        (gaussDensity τ v * Real.exp (1 / (8 * τ) * v ^ 2)) :=
    setIntegral_le_integral (hint.const_mul _)
      (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (gaussDensity_pos hτ v).le (Real.exp_pos _).le))
  refine hmono.trans (hall.trans ?_)
  rw [integral_const_mul, hval, hBq, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hs : (1 : ℝ) / 2 ≤ Real.sqrt (1 - 1 / 2) := by
    rw [Real.le_sqrt (by norm_num)]
    norm_num
  calc
    _ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) hs
    _ = 2 := by norm_num

/-- `|v|/(2τ) g_τ(v) ≤ (2/√τ) g_{2τ}(v)`: the first moment is paid by a wider Gaussian. -/
theorem abs_div_mul_gaussDensity_le {τ : ℝ} (hτ : 0 < τ) (v : ℝ) :
    |v| / (2 * τ) * gaussDensity τ v ≤ 2 / Real.sqrt τ * gaussDensity (2 * τ) v := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hss : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  have hp : 0 < 4 * Real.pi * τ := by positivity
  have hr : |v| / (2 * Real.sqrt τ) ≤ Real.exp (v ^ 2 / (8 * τ)) := by
    have h := Real.add_one_le_exp (v ^ 2 / (8 * τ))
    refine le_trans ?_ h
    have hv : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
    have he : |v| ^ 2 / (8 * τ) + 1 - |v| / (2 * Real.sqrt τ) =
        (|v| / (2 * Real.sqrt τ) - 1) ^ 2 / 2 + 1 / 2 := by
      have hτ' : τ = Real.sqrt τ * Real.sqrt τ := hss.symm
      rw [hτ']
      rw [Real.sqrt_mul_self hs.le]
      field_simp
      ring
    rw [hv]
    nlinarith only [he, sq_nonneg (|v| / (2 * Real.sqrt τ) - 1)]
  have hrp : (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) ≤ 2 * (4 * Real.pi * (2 * τ)) ^ (-(1 / 2 : ℝ)) := by
    have he : 4 * Real.pi * (2 * τ) = 2 * (4 * Real.pi * τ) := by ring
    rw [he, Real.mul_rpow (by norm_num) hp.le, ← mul_assoc]
    have h2 : 1 ≤ (2 : ℝ) * 2 ^ (-(1 / 2 : ℝ)) := by
      have h3 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ 2 ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_neg_one] at h3
      linarith only [h3]
    exact le_mul_of_one_le_left (by positivity) h2
  have hexp : Real.exp (-(v ^ 2 / (4 * τ))) * Real.exp (v ^ 2 / (8 * τ)) =
      Real.exp (-(v ^ 2 / (4 * (2 * τ)))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold gaussDensity
  have hkey : |v| / (2 * τ) = |v| / (2 * Real.sqrt τ) * (1 / Real.sqrt τ) := by
    nth_rewrite 1 [← hss]
    field_simp
  rw [hkey]
  calc
    _ ≤ (Real.exp (v ^ 2 / (8 * τ)) * (1 / Real.sqrt τ)) *
        ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(v ^ 2 / (4 * τ)))) := by gcongr
    _ = (1 / Real.sqrt τ) * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (-(v ^ 2 / (4 * τ))) * Real.exp (v ^ 2 / (8 * τ)))) := by ring
    _ = (1 / Real.sqrt τ) * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(v ^ 2 / (4 * (2 * τ))))) := by rw [hexp]
    _ ≤ (1 / Real.sqrt τ) * ((2 * (4 * Real.pi * (2 * τ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(v ^ 2 / (4 * (2 * τ))))) := by gcongr
    _ = _ := by ring

/-! ## Completing the square at the complex saddle -/

/-- The exponent off the window. -/
theorem gauss_source_exponent_le {τ y a δ A Bi α Λ ρ x v : ℝ} (hτ : 0 < τ) (ha : a = y + 2 * τ * A)
    (hδ : δ = 2 * τ * Bi) (hA : |A - α| ≤ Λ) (hΛ : 8 * τ * Λ ≤ ρ) (hρ : 0 ≤ ρ)
    (hv : v ^ 2 ≤ δ ^ 2) (hx : ρ ≤ |x - a|) :
    -(((x - y) ^ 2 - v ^ 2) / (4 * τ)) + (x - a) * α ≤
      -(τ * (A ^ 2 - Bi ^ 2)) - ρ ^ 2 / (8 * τ) := by
  obtain ⟨r, hr⟩ : ∃ r, r = x - a := ⟨_, rfl⟩
  rw [← hr] at hx ⊢
  have h1 : ((x - y) ^ 2 - v ^ 2) / (4 * τ) = r ^ 2 / (4 * τ) + r * A + τ * A ^ 2 - v ^ 2 / (4 * τ) := by
    have hxy : x - y = r + 2 * τ * A := by rw [hr, ha]; ring
    rw [hxy]
    field_simp
    ring
  have h2 : v ^ 2 / (4 * τ) ≤ τ * Bi ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [hδ] at hv
    nlinarith only [hv]
  have h3 : |r| * Λ ≤ r ^ 2 / (8 * τ) := by
    rw [le_div_iff₀ (by positivity), ← sq_abs r]
    have hr0 := abs_nonneg r
    nlinarith only [mul_le_mul_of_nonneg_left hΛ hr0, mul_le_mul_of_nonneg_left hx hr0]
  have h4 : ρ ^ 2 / (8 * τ) ≤ r ^ 2 / (8 * τ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← sq_abs r]
    exact pow_le_pow_left₀ hρ hx 2
  have h5 : r ^ 2 / (4 * τ) = 2 * (r ^ 2 / (8 * τ)) := by
    field_simp
    ring
  have h6 : -(r * (A - α)) ≤ |r| * Λ := by
    have h7 := neg_abs_le (r * (A - α))
    rw [abs_mul] at h7
    have h8 := mul_le_mul_of_nonneg_left hA (abs_nonneg r)
    linarith only [h7, h8]
  rw [h1]
  nlinarith only [h2, h3, h4, h5, h6]

/-- **The data of a complex saddle.** The fixed point `u = a + iδ = y + 2τℓ`, the local second-order model of `F` on
the window `|v| ≤ ρ`, and a size bound with exponential rate `α` on the rectangle over `[0, x₂]`. -/
structure SaddleData (F : ℂ → ℂ) (τ y a δ : ℝ) (ℓ : ℂ) (α Λ ρ x₂ B K : ℝ) : Prop where
  hF : Differentiable ℂ F
  hτ : 0 < τ
  hu : (a : ℂ) + (δ : ℂ) * I = (y : ℂ) + 2 * (τ : ℂ) * ℓ
  hA : |ℓ.re - α| ≤ Λ
  hΛ : 8 * τ * Λ ≤ ρ
  hρ : 0 < ρ
  hlow : ρ ≤ a
  hhigh : a + ρ ≤ x₂
  hB0 : 0 ≤ B
  hB : 8 * τ * B ≤ 1 / 2
  hK : 0 ≤ K
  hwin : ∀ v ∈ Icc (-ρ) ρ, ‖F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) -
      F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp ((v : ℂ) * ℓ)‖ ≤
    ‖F ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp (v * ℓ.re) * (Real.exp (B * v ^ 2) - 1)
  hsrc : ∀ x ∈ Icc 0 x₂, ∀ v ∈ [[(0 : ℝ), δ]], ‖F ((x : ℂ) + (v : ℂ) * I)‖ ≤
    K * ‖F ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp ((x - a) * α)

namespace SaddleData

variable {F : ℂ → ℂ} {τ y a δ : ℝ} {ℓ : ℂ} {α Λ ρ x₂ B K : ℝ}

/-- The mass of the saddle: the modulus of `F(u) e^{−τℓ²}`. -/
def mass (F : ℂ → ℂ) (τ a δ : ℝ) (ℓ : ℂ) : ℝ :=
  ‖F ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2)))

theorem mass_nonneg (F : ℂ → ℂ) (τ a δ : ℝ) (ℓ : ℂ) : 0 ≤ mass F τ a δ ℓ :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem re_eq (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) : a = y + 2 * τ * ℓ.re := by
  have := congrArg Complex.re h.hu
  simpa [Complex.mul_re] using this

theorem im_eq (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) : δ = 2 * τ * ℓ.im := by
  have := congrArg Complex.im h.hu
  simpa [Complex.mul_im] using this

theorem norm_main (F : ℂ → ℂ) (τ a δ : ℝ) (ℓ : ℂ) :
    ‖F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))‖ = mass F τ a δ ℓ := by
  have hre : (-((τ : ℂ) * ℓ ^ 2)).re = -(τ * (ℓ.re ^ 2 - ℓ.im ^ 2)) := by
    rw [Complex.neg_re, Complex.re_ofReal_mul, sq]
    simp only [Complex.mul_re]
    ring
  rw [norm_mul, Complex.norm_exp, hre, mass]

/-- **Off the window, the integrand is exponentially below the saddle mass.** -/
theorem norm_kernel_mul_le (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) {x v : ℝ} (hx : x ∈ Icc 0 x₂)
    (hv : v ∈ [[(0 : ℝ), δ]]) (hxa : ρ ≤ |x - a|) :
    ‖gaussKernel τ ((x : ℂ) + (v : ℂ) * I - (y : ℂ)) * F ((x : ℂ) + (v : ℂ) * I)‖ ≤
      mass F τ a δ ℓ * (K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(ρ ^ 2 / (8 * τ))))) := by
  have hτ := h.hτ
  have hsq : v ^ 2 ≤ δ ^ 2 := by
    rcases Set.mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith only [h1, h2]
  have hexpo := gauss_source_exponent_le hτ h.re_eq h.im_eq h.hA h.hΛ h.hρ.le hsq hxa
  have hk : (x : ℂ) + (v : ℂ) * I - (y : ℂ) = ((x - y : ℝ) : ℂ) + (v : ℂ) * I := by
    push_cast
    ring
  rw [norm_mul, hk, norm_gaussKernel hτ]
  have hN := norm_nonneg (F ((a : ℂ) + (δ : ℂ) * I))
  have hc : 0 ≤ (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc
    _ ≤ ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(((x - y) ^ 2 - v ^ 2) / (4 * τ)))) *
        (K * ‖F ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp ((x - a) * α)) :=
      mul_le_mul_of_nonneg_left (h.hsrc x hx v hv) (by positivity)
    _ = K * ‖F ((a : ℂ) + (δ : ℂ) * I)‖ * (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(((x - y) ^ 2 - v ^ 2) / (4 * τ)) + (x - a) * α) := by
      rw [Real.exp_add]
      ring
    _ ≤ K * ‖F ((a : ℂ) + (δ : ℂ) * I)‖ * (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2)) - ρ ^ 2 / (8 * τ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo)
        (mul_nonneg (mul_nonneg h.hK hN) hc)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, mass]
      ring

/-- The kernel on the line through the saddle: the exact cancellation of the exponential model. -/
theorem gaussKernel_saddle (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) (v : ℝ) :
    gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) =
      (gaussDensity τ v : ℂ) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) *
        Complex.exp (-((v : ℂ) * ℓ)) := by
  have hτ := h.hτ
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hk : (a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ) = 2 * (τ : ℂ) * ℓ + (v : ℂ) := by
    rw [h.hu]
    ring
  rw [hk, ← gaussKernel_ofReal]
  unfold gaussKernel
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- **On the window, the integrand follows the Gaussian with a quadratic relative error.** -/
theorem norm_window_sub_le (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) {v : ℝ} (hv : v ∈ Icc (-ρ) ρ) :
    ‖gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) * F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) -
        F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) * (gaussDensity τ v : ℂ)‖ ≤
      mass F τ a δ ℓ * (gaussDensity τ v * (Real.exp (B * v ^ 2) - 1)) := by
  have hτ := h.hτ
  have hg := (gaussDensity_pos hτ v).le
  have hfac : gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) -
        F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) * (gaussDensity τ v : ℂ) =
      (gaussDensity τ v : ℂ) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) * Complex.exp (-((v : ℂ) * ℓ)) *
        (F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) -
          F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp ((v : ℂ) * ℓ)) := by
    rw [h.gaussKernel_saddle v]
    have he : Complex.exp (-((v : ℂ) * ℓ)) * Complex.exp ((v : ℂ) * ℓ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination (-(gaussDensity τ v : ℂ) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) *
      F ((a : ℂ) + (δ : ℂ) * I)) * he
  have hre : (-((τ : ℂ) * ℓ ^ 2)).re = -(τ * (ℓ.re ^ 2 - ℓ.im ^ 2)) := by
    rw [Complex.neg_re, Complex.re_ofReal_mul, sq]
    simp only [Complex.mul_re]
    ring
  have hre2 : (-((v : ℂ) * ℓ)).re = -(v * ℓ.re) := by
    rw [Complex.neg_re, Complex.re_ofReal_mul]
  rw [hfac, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg,
    Complex.norm_exp, Complex.norm_exp, hre, hre2]
  have hw := h.hwin v hv
  have hexp : Real.exp (-(v * ℓ.re)) * Real.exp (v * ℓ.re) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ ≤ gaussDensity τ v * Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) * Real.exp (-(v * ℓ.re)) *
        (‖F ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp (v * ℓ.re) * (Real.exp (B * v ^ 2) - 1)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (Real.exp (-(v * ℓ.re)) * Real.exp (v * ℓ.re)) * (mass F τ a δ ℓ *
        (gaussDensity τ v * (Real.exp (B * v ^ 2) - 1))) := by
      rw [mass]
      ring
    _ = _ := by rw [hexp, one_mul]

theorem four_tau_B_le (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) : 4 * τ * B ≤ 1 / 2 := by
  have := mul_nonneg h.hτ.le h.hB0
  linarith only [h.hB, this]

/-- **The window integral.** `∫_{−ρ}^{ρ} g_τ(u + v − y) F(u + v) dv = F(u) e^{−τℓ²} (1 + small)`. -/
theorem norm_window_integral_sub_le (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K)
    (hc : Continuous fun v : ℝ => gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
      F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) :
    ‖(∫ v in (-ρ)..ρ, gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) -
      F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))‖ ≤
      mass F τ a δ ℓ * (8 * τ * B + 2 * Real.exp (-(ρ ^ 2 / (8 * τ)))) := by
  have hτ := h.hτ
  have hρ := h.hρ
  have hle : -ρ ≤ ρ := by linarith only [hρ]
  set M := F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) with hM
  have hgc : Continuous (gaussDensity τ) := by
    unfold gaussDensity
    fun_prop
  have hg1 : IntervalIntegrable (fun v : ℝ => M * (gaussDensity τ v : ℂ)) volume (-ρ) ρ :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hgc)).intervalIntegrable _ _
  have hsplit : (∫ v in (-ρ)..ρ, gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) - M =
      (∫ v in (-ρ)..ρ, (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) - M * (gaussDensity τ v : ℂ))) +
      M * (((∫ v in (-ρ)..ρ, gaussDensity τ v) - 1 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) hg1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    push_cast
    ring
  have hB4 := h.four_tau_B_le
  have hexc := integrable_gaussExcess (B := B) hτ (by linarith only [hB4])
  have h1 : ‖∫ v in (-ρ)..ρ, (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) - M * (gaussDensity τ v : ℂ))‖ ≤
      mass F τ a δ ℓ * (8 * τ * B) := by
    have hbd := intervalIntegral.norm_integral_le_of_norm_le (f := fun v : ℝ =>
        gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) - M * (gaussDensity τ v : ℂ))
      (g := fun v : ℝ => mass F τ a δ ℓ * (gaussDensity τ v * (Real.exp (B * v ^ 2) - 1)))
      (μ := volume) hle
      (Eventually.of_forall fun v hv => h.norm_window_sub_le ⟨hv.1.le, hv.2⟩)
      ((hexc.const_mul _).intervalIntegrable)
    refine hbd.trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mass_nonneg _ _ _ _ _)
    rw [intervalIntegral.integral_of_le hle]
    refine (setIntegral_le_integral hexc (Eventually.of_forall fun v => ?_)).trans
      (gaussExcess_le hτ h.hB0 hB4)
    have hb : 0 ≤ B * v ^ 2 := mul_nonneg h.hB0 (sq_nonneg v)
    exact mul_nonneg (gaussDensity_pos hτ v).le (sub_nonneg.mpr (Real.one_le_exp hb))
  have h2 : |(∫ v in (-ρ)..ρ, gaussDensity τ v) - 1| ≤ 2 * Real.exp (-(ρ ^ 2 / (8 * τ))) := by
    have hint := integrable_gaussDensity hτ
    have hadd := integral_add_compl (measurableSet_Ioc (a := -ρ) (b := ρ)) hint
    rw [integral_gaussDensity_eq_one hτ] at hadd
    rw [intervalIntegral.integral_of_le hle]
    have htail := integral_gaussDensity_compl_le hτ hρ.le
    have hnn : 0 ≤ ∫ v in (Ioc (-ρ) ρ)ᶜ, gaussDensity τ v :=
      setIntegral_nonneg measurableSet_Ioc.compl fun v _ => (gaussDensity_pos hτ v).le
    rw [abs_le]
    constructor <;> linarith only [hadd, htail, hnn]
  have hnM : ‖M‖ = mass F τ a δ ℓ := norm_main F τ a δ ℓ
  rw [hsplit]
  calc
    _ ≤ mass F τ a δ ℓ * (8 * τ * B) + ‖M‖ * |(∫ v in (-ρ)..ρ, gaussDensity τ v) - 1| := by
      refine (norm_add_le _ _).trans (add_le_add h1 ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by
      rw [hnM, mul_add]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 (mass_nonneg _ _ _ _ _))

/-- **The first moment on the window.** The Gaussian part is odd, so only the relative error remains. -/
theorem norm_window_moment_le (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K)
    (hc : Continuous fun v : ℝ => gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
      F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) :
    ‖∫ v in (-ρ)..ρ, ((v / (2 * τ) : ℝ) : ℂ) *
        (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)))‖ ≤
      mass F τ a δ ℓ * (32 * Real.sqrt τ * B) := by
  have hτ := h.hτ
  have hρ := h.hρ
  have hle : -ρ ≤ ρ := by linarith only [hρ]
  set M := F ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) with hM
  have hgc : Continuous (gaussDensity τ) := by
    unfold gaussDensity
    fun_prop
  -- The Gaussian first moment vanishes on the symmetric window.
  have hodd : (∫ v in (-ρ)..ρ, v / (2 * τ) * gaussDensity τ v) = 0 := by
    have hne : (∫ v in (-ρ)..ρ, (-v) / (2 * τ) * gaussDensity τ (-v)) =
        ∫ v in (-ρ)..ρ, v / (2 * τ) * gaussDensity τ v := by
      have := intervalIntegral.integral_comp_neg (a := -ρ) (b := ρ)
        (fun v : ℝ => v / (2 * τ) * gaussDensity τ v)
      simpa only [neg_neg] using this
    have hneg : (∫ v in (-ρ)..ρ, (-v) / (2 * τ) * gaussDensity τ (-v)) =
        -∫ v in (-ρ)..ρ, v / (2 * τ) * gaussDensity τ v := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext v
      unfold gaussDensity
      rw [neg_sq]
      ring
    linarith only [hne, hneg]
  have hc1 : Continuous fun v : ℝ => ((v / (2 * τ) : ℝ) : ℂ) *
      (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) :=
    (Complex.continuous_ofReal.comp (continuous_id.div_const _)).mul hc
  have hc2 : Continuous fun v : ℝ => M * ((v / (2 * τ) * gaussDensity τ v : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_id.div_const _).mul hgc))
  have hsplit : (∫ v in (-ρ)..ρ, ((v / (2 * τ) : ℝ) : ℂ) *
        (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)))) =
      ∫ v in (-ρ)..ρ, (((v / (2 * τ) : ℝ) : ℂ) *
        (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) -
        M * ((v / (2 * τ) * gaussDensity τ v : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hodd]
    simp
  have h2τ : 0 < 2 * τ := by positivity
  have hB2 : 4 * (2 * τ) * B ≤ 1 / 2 := by linarith only [h.hB]
  have hexc := integrable_gaussExcess (t := 2 * τ) (B := B) h2τ (by linarith only [hB2])
  have hpt (v : ℝ) (hv : v ∈ Icc (-ρ) ρ) :
      ‖((v / (2 * τ) : ℝ) : ℂ) * (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) -
        M * ((v / (2 * τ) * gaussDensity τ v : ℝ) : ℂ)‖ ≤
      mass F τ a δ ℓ * (2 / Real.sqrt τ) *
        (gaussDensity (2 * τ) v * (Real.exp (B * v ^ 2) - 1)) := by
    have he : ((v / (2 * τ) : ℝ) : ℂ) * (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) -
        M * ((v / (2 * τ) * gaussDensity τ v : ℝ) : ℂ) =
        ((v / (2 * τ) : ℝ) : ℂ) * (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
          F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) - M * (gaussDensity τ v : ℂ)) := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos h2τ]
    have hb : 0 ≤ Real.exp (B * v ^ 2) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (mul_nonneg h.hB0 (sq_nonneg v)))
    have hw := h.norm_window_sub_le hv
    have hm := mass_nonneg F τ a δ ℓ
    have hmom := abs_div_mul_gaussDensity_le hτ v
    calc
      _ ≤ |v| / (2 * τ) * (mass F τ a δ ℓ * (gaussDensity τ v * (Real.exp (B * v ^ 2) - 1))) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = mass F τ a δ ℓ * (Real.exp (B * v ^ 2) - 1) * (|v| / (2 * τ) * gaussDensity τ v) := by ring
      _ ≤ mass F τ a δ ℓ * (Real.exp (B * v ^ 2) - 1) *
          (2 / Real.sqrt τ * gaussDensity (2 * τ) v) :=
        mul_le_mul_of_nonneg_left hmom (mul_nonneg hm hb)
      _ = _ := by ring
  rw [hsplit]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hle
    (Eventually.of_forall fun v hv => hpt v ⟨hv.1.le, hv.2⟩)
    ((hexc.const_mul (mass F τ a δ ℓ * (2 / Real.sqrt τ))).intervalIntegrable)
  refine hbd.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hle]
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hss : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  have hE : (∫ v in Ioc (-ρ) ρ, gaussDensity (2 * τ) v * (Real.exp (B * v ^ 2) - 1)) ≤ 8 * (2 * τ) * B := by
    refine (setIntegral_le_integral hexc (Eventually.of_forall fun v => ?_)).trans
      (gaussExcess_le h2τ h.hB0 hB2)
    have hb : 0 ≤ B * v ^ 2 := mul_nonneg h.hB0 (sq_nonneg v)
    exact mul_nonneg (gaussDensity_pos h2τ v).le (sub_nonneg.mpr (Real.one_le_exp hb))
  have hm := mass_nonneg F τ a δ ℓ
  calc
    _ ≤ mass F τ a δ ℓ * (2 / Real.sqrt τ) * (8 * (2 * τ) * B) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = mass F τ a δ ℓ * (32 * (τ / Real.sqrt τ) * B) := by ring
    _ = _ := by
      have : τ / Real.sqrt τ = Real.sqrt τ := by
        nth_rewrite 1 [← hss]
        field_simp
      rw [this]

/-- **The contour shift, with a weight.** Away from the window, every piece of the rectangle is below the mass. -/
theorem norm_sub_window_le (h : SaddleData F τ y a δ ℓ α Λ ρ x₂ B K) {ω : ℂ → ℂ} {Ω : ℝ}
    (hω : Differentiable ℂ ω) (hΩ : 0 ≤ Ω)
    (hΩb : ∀ x ∈ Icc 0 x₂, ∀ v ∈ [[(0 : ℝ), δ]], ‖ω ((x : ℂ) + (v : ℂ) * I)‖ ≤ Ω) :
    ‖(∫ x in (0 : ℝ)..x₂, ω (x : ℂ) * (gaussKernel τ ((x : ℂ) - (y : ℂ)) * F (x : ℂ))) -
        ∫ v in (-ρ)..ρ, ω ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) *
          (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
            F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)))‖ ≤
      mass F τ a δ ℓ * (Ω * (K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(ρ ^ 2 / (8 * τ))))) * (x₂ + 2 * |δ|)) := by
  have hρ := h.hρ
  have hlow := h.hlow
  have hhigh := h.hhigh
  set Bd := mass F τ a δ ℓ * (Ω * (K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(ρ ^ 2 / (8 * τ)))))) with hBd
  let G : ℂ → ℂ := fun z => ω z * (gaussKernel τ (z - (y : ℂ)) * F z)
  have hG : Differentiable ℂ G := hω.mul
    (((differentiable_gaussKernel τ).comp (differentiable_id.sub_const _)).mul h.hF)
  have hGc : Continuous G := hG.continuous
  -- The pointwise bound off the window.
  have hpt : ∀ x ∈ Icc 0 x₂, ∀ v ∈ [[(0 : ℝ), δ]], ρ ≤ |x - a| →
      ‖G ((x : ℂ) + (v : ℂ) * I)‖ ≤ Bd := by
    intro x hx v hv hxa
    have h1 := h.norm_kernel_mul_le hx hv hxa
    have h2 := hΩb x hx v hv
    have hc : 0 ≤ mass F τ a δ ℓ * (K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(ρ ^ 2 / (8 * τ))))) :=
      mul_nonneg (mass_nonneg _ _ _ _ _) (mul_nonneg h.hK (by positivity))
    change ‖ω _ * (gaussKernel τ (_ - _) * F _)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ Ω * (mass F τ a δ ℓ * (K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(ρ ^ 2 / (8 * τ)))))) :=
        mul_le_mul h2 h1 (norm_nonneg _) hΩ
      _ = Bd := by rw [hBd]; ring
  have hshift := integral_eq_shift_add_edges hG 0 x₂ δ
  have hx₂ : 0 ≤ x₂ := by linarith only [hρ, hlow, hhigh]
  have hδmem : δ ∈ [[(0 : ℝ), δ]] := Set.right_mem_uIcc
  -- Three pieces of the line at height `δ`.
  have hint (A B : ℝ) : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + (δ : ℂ) * I)) volume A B :=
    (hGc.comp (by fun_prop)).intervalIntegrable _ _
  have hadd : (∫ x in (0 : ℝ)..x₂, G ((x : ℂ) + (δ : ℂ) * I)) =
      (∫ x in (0 : ℝ)..(a - ρ), G ((x : ℂ) + (δ : ℂ) * I)) +
      (∫ x in (a - ρ)..(a + ρ), G ((x : ℂ) + (δ : ℂ) * I)) +
      (∫ x in (a + ρ)..x₂, G ((x : ℂ) + (δ : ℂ) * I)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmid : (∫ x in (a - ρ)..(a + ρ), G ((x : ℂ) + (δ : ℂ) * I)) =
      ∫ v in (-ρ)..ρ, G ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) := by
    have hs := intervalIntegral.integral_comp_add_left (a := -ρ) (b := ρ)
      (fun x : ℝ => G ((x : ℂ) + (δ : ℂ) * I)) a
    rw [show a + -ρ = a - ρ by ring] at hs
    rw [← hs]
    refine intervalIntegral.integral_congr fun v _ => ?_
    dsimp only
    congr 1
    push_cast
    ring
  have hreal : (∫ x in (0 : ℝ)..x₂, ω (x : ℂ) * (gaussKernel τ ((x : ℂ) - (y : ℂ)) * F (x : ℂ))) =
      ∫ x in (0 : ℝ)..x₂, G (x : ℂ) := rfl
  have hwindow : (∫ v in (-ρ)..ρ, ω ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) *
      (gaussKernel τ ((a : ℂ) + (δ : ℂ) * I + (v : ℂ) - (y : ℂ)) *
        F ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)))) =
      ∫ v in (-ρ)..ρ, G ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) := rfl
  rw [hreal, hwindow, hshift, hadd, hmid]
  -- The four remaining pieces.
  have hBd0 : 0 ≤ Bd := mul_nonneg (mass_nonneg _ _ _ _ _) (mul_nonneg hΩ
    (mul_nonneg h.hK (by positivity)))
  have hlowp : ‖∫ x in (0 : ℝ)..(a - ρ), G ((x : ℂ) + (δ : ℂ) * I)‖ ≤ Bd * (a - ρ) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a - ρ)
      (f := fun x : ℝ => G ((x : ℂ) + (δ : ℂ) * I)) (C := Bd) (fun x hx => by
        rw [uIoc_of_le (by linarith only [hlow])] at hx
        refine hpt x ⟨hx.1.le, by linarith only [hx.2, hhigh, hρ]⟩ δ hδmem ?_
        rw [abs_of_nonpos (by linarith only [hx.2, hρ])]
        linarith only [hx.2])
    rwa [sub_zero, abs_of_nonneg (by linarith only [hlow])] at hb
  have hhighp : ‖∫ x in (a + ρ)..x₂, G ((x : ℂ) + (δ : ℂ) * I)‖ ≤ Bd * (x₂ - (a + ρ)) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a + ρ) (b := x₂)
      (f := fun x : ℝ => G ((x : ℂ) + (δ : ℂ) * I)) (C := Bd) (fun x hx => by
        rw [uIoc_of_le hhigh] at hx
        refine hpt x ⟨by linarith only [hx.1, hlow, hρ], hx.2⟩ δ hδmem ?_
        rw [abs_of_nonneg (by linarith only [hx.1, hρ])]
        linarith only [hx.1])
    rwa [abs_of_nonneg (by linarith only [hhigh])] at hb
  have hedge (x₀ : ℝ) (hx₀ : x₀ ∈ Icc 0 x₂) (hxa : ρ ≤ |x₀ - a|) :
      ‖I * ∫ v in (0 : ℝ)..δ, G ((x₀ : ℂ) + (v : ℂ) * I)‖ ≤ Bd * |δ| := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
      (f := fun v : ℝ => G ((x₀ : ℂ) + (v : ℂ) * I)) (C := Bd) (fun v hv =>
        hpt x₀ hx₀ v (Set.uIoc_subset_uIcc hv) hxa)
    rw [sub_zero] at hb
    rwa [norm_mul, Complex.norm_I, one_mul]
  have he0 := hedge 0 ⟨le_rfl, hx₂⟩ (by
    rw [zero_sub, abs_neg, abs_of_pos (by linarith only [hlow, hρ])]
    exact hlow)
  have he1 := hedge x₂ ⟨hx₂, le_rfl⟩ (by
    rw [abs_of_nonneg (by linarith only [hhigh, hρ])]
    linarith only [hhigh])
  have hmain := calc
    ‖(∫ x in (0 : ℝ)..(a - ρ), G ((x : ℂ) + (δ : ℂ) * I)) +
          (∫ v in (-ρ)..ρ, G ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))) +
          (∫ x in (a + ρ)..x₂, G ((x : ℂ) + (δ : ℂ) * I)) +
          I * (∫ v in (0 : ℝ)..δ, G (((0 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I * (∫ v in (0 : ℝ)..δ, G ((x₂ : ℂ) + (v : ℂ) * I)) -
        ∫ v in (-ρ)..ρ, G ((a : ℂ) + (δ : ℂ) * I + (v : ℂ))‖ =
      ‖(∫ x in (0 : ℝ)..(a - ρ), G ((x : ℂ) + (δ : ℂ) * I)) +
          (∫ x in (a + ρ)..x₂, G ((x : ℂ) + (δ : ℂ) * I)) +
          I * (∫ v in (0 : ℝ)..δ, G (((0 : ℝ) : ℂ) + (v : ℂ) * I)) -
          I * (∫ v in (0 : ℝ)..δ, G ((x₂ : ℂ) + (v : ℂ) * I))‖ := by
        congr 1
        ring
    _ ≤ Bd * (a - ρ) + Bd * (x₂ - (a + ρ)) + Bd * |δ| + Bd * |δ| := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ he1)
        refine (norm_add_le _ _).trans (add_le_add ?_ he0)
        exact (norm_add_le _ _).trans (add_le_add hlowp hhighp)
  refine hmain.trans ?_
  have hpos : Bd * ρ * 2 ≥ 0 := by positivity
  rw [hBd] at hpos ⊢
  nlinarith only [hpos]

end SaddleData

end

end GaloisForLFunctions.ZeroConfigurationGeometry
