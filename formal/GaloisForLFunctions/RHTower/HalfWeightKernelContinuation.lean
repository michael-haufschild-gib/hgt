import GaloisForLFunctions.RHTower.HalfWeightKernel
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# Analytic continuation of the weight-½ kernel transforms

On the real line `kerH_{y,w} = y^w h_{w+1/4, w-1/4}` with `h_{a,b}(x) = (x+iy)^{-a}(x-iy)^{-b}`
(`kerH_eq_hab`). Since `h_{a,b}' = -a h_{a+1,b} - b h_{a,b+1}` (`hasDerivAt_hab`), the Fourier
transforms satisfy, for `Re(a+b) > 1`,
`2πiξ 𝓕h_{a,b}(ξ) = -a 𝓕h_{a+1,b}(ξ) - b 𝓕h_{a,b+1}(ξ)` (`fourier_hab_rec`).

* `Gk`: the recursion `G_{k+1}(a,b) = -(a G_k(a+1,b) + b G_k(a,b+1))/(2πiξ)` started at `G_0 = 𝓕h`;
  `Gk_eq`: it equals `𝓕h_{a,b}` wherever that converges (`ξ ≠ 0`).
* `norm_Gk_le`: `|G_k(a,b)(ξ)| ≤ ((|a|+|b|+2k)/(2π|ξ|))^k e^{π(|Im a|+|Im b|)} y^{1-Re(a+b)-k}
  C_{(Re(a+b)+k)/2}`, valid for `Re(a+b) + k > 1`.
* `differentiableAt_Gk`: holomorphy along `(w+α, w+β)` for `Re(2w+α+β) > 1 - k` (base case via
  `differentiableAt_integral_of_cauchy_dominated`).
* `PhiK = y^w G_k(w+1/4, w-1/4)`: `fourier_kerH_eq_PhiK` (it continues `𝓕kerH_{y,w}(ξ)`),
  `differentiableAt_PhiK` (holomorphic on `Re w > (1-k)/2`), `PhiK_eq_PhiK` (independent of `k`),
  `norm_PhiK_le` (decay `|ξ|^{-k}`).

The non-constant Fourier coefficients of the weight-½ Eisenstein series therefore continue across
`Re w = 1/2` with decay of every polynomial order in `ξ`.
-/

open Real Complex MeasureTheory Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

/-! ### The kernel as a product of complex powers -/

/-- `h_{a,b}(x) = (x + iy)^{-a} (x - iy)^{-b}`. -/
def hab (y : ℝ) (a b : ℂ) (x : ℝ) : ℂ := ((x : ℂ) + y * I) ^ (-a) * ((x : ℂ) - y * I) ^ (-b)

variable {y : ℝ}

theorem plus_ne_zero (hy : 0 < y) (x : ℝ) : ((x : ℂ) + y * I) ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; linarith

theorem minus_ne_zero (hy : 0 < y) (x : ℝ) : ((x : ℂ) - y * I) ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; linarith

theorem plus_mem_slitPlane (hy : 0 < y) (x : ℝ) : ((x : ℂ) + y * I) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by simp; exact hy.ne'))

theorem minus_mem_slitPlane (hy : 0 < y) (x : ℝ) : ((x : ℂ) - y * I) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by simp; exact hy.ne'))

theorem minus_eq_conj (x : ℝ) : ((x : ℂ) - y * I) = starRingEnd ℂ ((x : ℂ) + y * I) := by
  simp [Complex.ext_iff]

/-- `kerH_{y,w} = y^w h_{w+1/4, w-1/4}` on the real line. -/
theorem kerH_eq_hab (hy : 0 < y) (w : ℂ) (x : ℝ) :
    kerH y w x = (y : ℂ) ^ w * hab y (w + 1 / 4) (w - 1 / 4) x := by
  set ζ : ℂ := (x : ℂ) + y * I with hζ
  have hζ0 : ζ ≠ 0 := plus_ne_zero hy x
  have hζ' : ((x : ℂ) - y * I) ≠ 0 := minus_ne_zero hy x
  have hwz : wz y x = ζ := by rw [hζ]; unfold wz; ring
  have hlogc : Complex.log ((x : ℂ) - y * I) = starRingEnd ℂ (Complex.log ζ) := by
    rw [minus_eq_conj, Complex.log_conj]
    rw [← hζ]
    intro h
    have := Complex.arg_eq_pi_iff.1 h
    have him : ζ.im = y := by rw [hζ]; simp
    linarith [this.2, hy]
  have hwt : Real.log (wt y x) = Real.log y - 2 * Real.log ‖ζ‖ := by
    unfold wt
    rw [Real.log_div hy.ne' (by positivity), show x ^ 2 + y ^ 2 = ‖ζ‖ ^ 2 by
      rw [← Complex.normSq_eq_norm_sq, hζ]; simp [Complex.normSq_apply]; ring,
      Real.log_pow]
    push_cast; ring
  have hlog : Complex.log ζ = (Real.log ‖ζ‖ : ℂ) + ((Complex.log ζ).im : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.log_re]
  unfold kerH hab argW
  rw [hwz, Complex.cpow_def_of_ne_zero hζ0, Complex.cpow_def_of_ne_zero hζ',
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), hlogc, ← Complex.exp_add,
    ← Complex.exp_add, hwt]
  congr 1
  rw [← Complex.ofReal_log hy.le]
  conv_rhs => rw [hlog]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring


/-! ### Derivative and size of `h_{a,b}` -/

theorem hasDerivAt_plus_cpow (hy : 0 < y) (a : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) + y * I) ^ (-a))
      (-a * ((x : ℂ) + y * I) ^ (-(a + 1))) x := by
  have h1 : HasDerivAt (fun z : ℂ => z + y * I) 1 (x : ℂ) := (hasDerivAt_id _).add_const _
  have h2 := h1.cpow_const (c := -a) (plus_mem_slitPlane hy x)
  have h3 := h2.comp_ofReal
  refine h3.congr_deriv ?_
  rw [show -a - 1 = -(a + 1) by ring, mul_one]

theorem hasDerivAt_minus_cpow (hy : 0 < y) (b : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) - y * I) ^ (-b))
      (-b * ((x : ℂ) - y * I) ^ (-(b + 1))) x := by
  have h1 : HasDerivAt (fun z : ℂ => z - y * I) 1 (x : ℂ) := (hasDerivAt_id _).sub_const _
  have h2 := h1.cpow_const (c := -b) (minus_mem_slitPlane hy x)
  have h3 := h2.comp_ofReal
  refine h3.congr_deriv ?_
  rw [show -b - 1 = -(b + 1) by ring, mul_one]

/-- `h_{a,b}' = -a h_{a+1,b} - b h_{a,b+1}`. -/
theorem hasDerivAt_hab (hy : 0 < y) (a b : ℂ) (x : ℝ) :
    HasDerivAt (hab y a b) (-a * hab y (a + 1) b x - b * hab y a (b + 1) x) x := by
  have h := (hasDerivAt_plus_cpow hy a x).mul (hasDerivAt_minus_cpow hy b x)
  refine h.congr_deriv ?_
  unfold hab; ring

theorem norm_cpow_le_exp (z w : ℂ) (hz : z ≠ 0) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (Real.pi * |w.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have h1 := Complex.abs_arg_le_pi z
  have h2 : |z.arg * w.im| ≤ Real.pi * |w.im| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  linarith [neg_abs_le (z.arg * w.im)]

theorem norm_plus_sq (x : ℝ) : ‖(x : ℂ) + y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring

theorem norm_minus_sq (x : ℝ) : ‖(x : ℂ) - y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring

/-- `|h_{a,b}(x)| ≤ e^{π(|Im a|+|Im b|)} (x²+y²)^{-Re(a+b)/2}`. -/
theorem norm_hab_le (hy : 0 < y) (a b : ℂ) (x : ℝ) :
    ‖hab y a b x‖ ≤ Real.exp (Real.pi * (|a.im| + |b.im|)) *
      (x ^ 2 + y ^ 2) ^ (-(a + b).re / 2) := by
  unfold hab
  rw [norm_mul]
  have h1 := norm_cpow_le_exp ((x : ℂ) + y * I) (-a) (plus_ne_zero hy x)
  have h2 := norm_cpow_le_exp ((x : ℂ) - y * I) (-b) (minus_ne_zero hy x)
  have hp : ‖(x : ℂ) + y * I‖ = (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← norm_plus_sq, Real.sqrt_sq (norm_nonneg _)]
  have hm : ‖(x : ℂ) - y * I‖ = (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← norm_minus_sq, Real.sqrt_sq (norm_nonneg _)]
  have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [hp] at h1; rw [hm] at h2
  calc _ ≤ ((x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ)) ^ (-a).re * Real.exp (Real.pi * |(-a).im|) *
        (((x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ)) ^ (-b).re * Real.exp (Real.pi * |(-b).im|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by
        rw [← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le]
        simp only [Complex.neg_re, Complex.neg_im, abs_neg, Complex.add_re]
        rw [show Real.exp (Real.pi * (|a.im| + |b.im|)) =
          Real.exp (Real.pi * |a.im|) * Real.exp (Real.pi * |b.im|) by
            rw [← Real.exp_add]; ring_nf]
        rw [show -(a.re + b.re) / 2 = 1 / 2 * -a.re + 1 / 2 * -b.re by ring,
          Real.rpow_add hpos]
        ring


/-! ### Integrability and the Fourier recursion -/

theorem continuous_hab (hy : 0 < y) (a b : ℂ) : Continuous (hab y a b) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_hab hy a b x).continuousAt

theorem rpow_sum_sq_eq (hy : 0 < y) (σ x : ℝ) :
    (x ^ 2 + y ^ 2) ^ (-σ) = y ^ (-σ) * wt y x ^ σ := by
  unfold wt
  have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [Real.div_rpow hy.le hpos.le, Real.rpow_neg hpos.le, Real.rpow_neg hy.le]
  field_simp

theorem integrable_hab (hy : 0 < y) {a b : ℂ} (hab1 : 1 < (a + b).re) : Integrable (hab y a b) := by
  have hσ : 1 / 2 < (a + b).re / 2 := by linarith
  have hI := (integrable_wt_rpow hy hσ).const_mul
    (Real.exp (Real.pi * (|a.im| + |b.im|)) * y ^ (-((a + b).re / 2)))
  refine hI.mono' (continuous_hab hy a b).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  refine (norm_hab_le hy a b x).trans (le_of_eq ?_)
  rw [show -(a + b).re / 2 = -((a + b).re / 2) by ring, rpow_sum_sq_eq hy]
  ring

theorem integrable_fourier_integrand {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun v : ℝ => ((𝐞 (-(v * ξ)) : Circle) : ℂ) * f v) := by
  have hc : Continuous (fun v : ℝ => ((𝐞 (-(v * ξ)) : Circle) : ℂ)) :=
    continuous_induced_dom.comp (Real.continuous_fourierChar.comp (by fun_prop))
  refine Integrable.mono' hf.norm (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [norm_mul, Circle.norm_coe, one_mul]

theorem fourier_linear {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c d : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x + d * g x) ξ = c * 𝓕 f ξ + d * 𝓕 g ξ := by
  simp only [Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
  have h1 := integrable_fourier_integrand hf ξ
  have h2 := integrable_fourier_integrand hg ξ
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul c) (h2.const_mul d)]
  congr 1; ext v; ring

/-- **The Fourier recursion**: `2πiξ 𝓕h_{a,b}(ξ) = -a 𝓕h_{a+1,b}(ξ) - b 𝓕h_{a,b+1}(ξ)`
for `Re(a+b) > 1`. -/
theorem fourier_hab_rec (hy : 0 < y) {a b : ℂ} (hab1 : 1 < (a + b).re) (ξ : ℝ) :
    (2 * Real.pi * I * ξ) * 𝓕 (hab y a b) ξ =
      -a * 𝓕 (hab y (a + 1) b) ξ - b * 𝓕 (hab y a (b + 1)) ξ := by
  have hint1 : Integrable (hab y (a + 1) b) := integrable_hab hy (by simp; simp at hab1; linarith)
  have hint2 : Integrable (hab y a (b + 1)) := integrable_hab hy (by simp; simp at hab1; linarith)
  have hderiv : deriv (hab y a b) = fun x => -a * hab y (a + 1) b x + -b * hab y a (b + 1) x := by
    funext x; rw [(hasDerivAt_hab hy a b x).deriv]; ring
  have hd := Real.fourier_deriv (integrable_hab hy hab1)
    (fun x => (hasDerivAt_hab hy a b x).differentiableAt) (by
      rw [hderiv]
      exact (hint1.const_mul _).add (hint2.const_mul _))
  have := congrFun hd ξ
  rw [hderiv, fourier_linear hint1 hint2] at this
  rw [smul_eq_mul] at this
  rw [← this]; ring


/-! ### The continued Fourier transforms -/

/-- `G_0(a,b)(ξ) = 𝓕h_{a,b}(ξ)` and
`G_{k+1}(a,b)(ξ) = -(a G_k(a+1,b)(ξ) + b G_k(a,b+1)(ξ)) / (2πiξ)`. -/
def Gk (y : ℝ) : ℕ → ℂ → ℂ → ℝ → ℂ
  | 0, a, b, ξ => 𝓕 (hab y a b) ξ
  | k + 1, a, b, ξ => -(a * Gk y k (a + 1) b ξ + b * Gk y k a (b + 1) ξ) / (2 * Real.pi * I * ξ)

theorem Gk_zero (a b : ℂ) (ξ : ℝ) : Gk y 0 a b ξ = 𝓕 (hab y a b) ξ := rfl

theorem Gk_succ (k : ℕ) (a b : ℂ) (ξ : ℝ) :
    Gk y (k + 1) a b ξ = -(a * Gk y k (a + 1) b ξ + b * Gk y k a (b + 1) ξ) / (2 * Real.pi * I * ξ) :=
  rfl

/-- On the region of convergence every `G_k` is the Fourier transform. -/
theorem Gk_eq (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) (k : ℕ) :
    ∀ a b : ℂ, 1 < (a + b).re → Gk y k a b ξ = 𝓕 (hab y a b) ξ := by
  induction k with
  | zero => intro a b _; rfl
  | succ k ih =>
    intro a b hab1
    rw [Gk_succ, ih (a + 1) b (by simp; simp at hab1; linarith),
      ih a (b + 1) (by simp; simp at hab1; linarith)]
    have h2 : (2 * Real.pi * I * ξ : ℂ) ≠ 0 := by
      have : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp_all
    rw [div_eq_iff h2]
    have := fourier_hab_rec hy hab1 ξ
    linear_combination -this

theorem norm_fourier_le_integral' {f : ℝ → ℂ} (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  SelbergPoincareKernel.norm_fourier_le_integral ξ

/-- `|𝓕h_{a,b}(ξ)| ≤ e^{π(|Im a|+|Im b|)} y^{1-Re(a+b)} C_{Re(a+b)/2}`. -/
theorem norm_fourier_hab_le (hy : 0 < y) {a b : ℂ} (hab1 : 1 < (a + b).re) (ξ : ℝ) :
    ‖𝓕 (hab y a b) ξ‖ ≤ Real.exp (Real.pi * (|a.im| + |b.im|)) *
      (y ^ (1 - (a + b).re) * cst ((a + b).re / 2)) := by
  refine (norm_fourier_le_integral' ξ).trans ?_
  have hσ : 1 / 2 < (a + b).re / 2 := by linarith
  have hI := (integrable_wt_rpow hy hσ).const_mul
    (Real.exp (Real.pi * (|a.im| + |b.im|)) * y ^ (-((a + b).re / 2)))
  calc ∫ x, ‖hab y a b x‖ ≤ ∫ x, Real.exp (Real.pi * (|a.im| + |b.im|)) *
        y ^ (-((a + b).re / 2)) * wt y x ^ ((a + b).re / 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hI
          (Eventually.of_forall fun x => by
            refine (norm_hab_le hy a b x).trans (le_of_eq ?_)
            rw [show -(a + b).re / 2 = -((a + b).re / 2) by ring, rpow_sum_sq_eq hy]
            ring)
    _ = _ := by
        rw [integral_const_mul, integral_wt_rpow hy]
        rw [mul_assoc, ← mul_assoc (y ^ _), ← Real.rpow_add hy]
        congr 2; ring_nf


/-- **Decay of the continued transforms**: for `ξ ≠ 0` and `Re(a+b) + k > 1`,
`|G_k(a,b)(ξ)| ≤ ((|a|+|b|+2k)/(2π|ξ|))^k e^{π(|Im a|+|Im b|)} y^{1-Re(a+b)-k} C_{(Re(a+b)+k)/2}`. -/
theorem norm_Gk_le (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) (k : ℕ) :
    ∀ a b : ℂ, 1 < (a + b).re + k →
      ‖Gk y k a b ξ‖ ≤ ((‖a‖ + ‖b‖ + 2 * k) / (2 * Real.pi * |ξ|)) ^ k *
        Real.exp (Real.pi * (|a.im| + |b.im|)) *
          (y ^ (1 - (a + b).re - k) * cst (((a + b).re + k) / 2)) := by
  have hξp : 0 < 2 * Real.pi * |ξ| := by have := abs_pos.2 hξ; positivity
  induction k with
  | zero =>
    intro a b h
    simp only [Nat.cast_zero, add_zero, pow_zero, one_mul, sub_zero] at h ⊢
    rw [Gk_zero]; exact norm_fourier_hab_le hy h ξ
  | succ k ih =>
    intro a b h
    push_cast at h ⊢
    have hre : 1 < a.re + b.re + (k + 1) := by simpa using h
    have h1 := ih (a + 1) b (by simp; linarith)
    have h2 := ih a (b + 1) (by simp; linarith)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at h1 h2
    rw [Gk_succ, norm_div, norm_neg]
    have hden : ‖(2 * Real.pi * I * ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
      simp [abs_of_pos Real.pi_pos]
    rw [hden, div_le_iff₀ hξp]
    set E := Real.exp (Real.pi * (|a.im| + |b.im|))
    set Y := y ^ (1 - (a + b).re - (k + 1)) * cst (((a + b).re + (k + 1)) / 2)
    have hY1 : y ^ (1 - (a.re + 1 + b.re) - k) * cst ((a.re + 1 + b.re + k) / 2) = Y := by
      simp only [Y, Complex.add_re]; congr 2 <;> ring
    have hY2 : y ^ (1 - (a.re + (b.re + 1)) - k) * cst ((a.re + (b.re + 1) + k) / 2) = Y := by
      simp only [Y, Complex.add_re]; congr 2 <;> ring
    have hY0 : 0 ≤ Y := by have := cst_nonneg (((a + b).re + (k + 1)) / 2); positivity
    rw [hY1] at h1; rw [hY2] at h2
    set R := (‖a‖ + ‖b‖ + 2 * (k + 1)) / (2 * Real.pi * |ξ|)
    have hR0 : 0 ≤ R := by positivity
    have hA : (‖a + 1‖ + ‖b‖ + 2 * k) / (2 * Real.pi * |ξ|) ≤ R := by
      apply div_le_div_of_nonneg_right _ hξp.le
      have := norm_add_le a 1; simp at this; linarith
    have hB : (‖a‖ + ‖b + 1‖ + 2 * k) / (2 * Real.pi * |ξ|) ≤ R := by
      apply div_le_div_of_nonneg_right _ hξp.le
      have := norm_add_le b 1; simp at this; linarith
    have hpa := pow_le_pow_left₀ (by positivity) hA k
    have hpb := pow_le_pow_left₀ (by positivity) hB k
    have hG1 : ‖Gk y k (a + 1) b ξ‖ ≤ R ^ k * E * Y :=
      h1.trans (by gcongr)
    have hG2 : ‖Gk y k a (b + 1) ξ‖ ≤ R ^ k * E * Y :=
      h2.trans (by gcongr)
    have hE0 : 0 ≤ E := by positivity
    calc ‖a * Gk y k (a + 1) b ξ + b * Gk y k a (b + 1) ξ‖
        ≤ ‖a‖ * (R ^ k * E * Y) + ‖b‖ * (R ^ k * E * Y) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hG1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hG2 (norm_nonneg _))
      _ ≤ R * (2 * Real.pi * |ξ|) * (R ^ k * E * Y) := by
          rw [← add_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simp only [R]; rw [div_mul_cancel₀ _ hξp.ne']; linarith
      _ = R ^ (k + 1) * E * Y * (2 * Real.pi * |ξ|) := by ring


/-! ### Holomorphy in the spectral variable -/

theorem rpow_neg_le_add {u s s₁ s₂ : ℝ} (hu : 0 < u) (h1 : s₁ ≤ s) (h2 : s ≤ s₂) :
    u ^ (-s) ≤ u ^ (-s₁) + u ^ (-s₂) := by
  rcases le_or_gt 1 u with hu1 | hu1
  · have : u ^ (-s) ≤ u ^ (-s₁) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have : 0 ≤ u ^ (-s₂) := by positivity
    linarith
  · have : u ^ (-s) ≤ u ^ (-s₂) := Real.rpow_le_rpow_of_exponent_ge hu hu1.le (by linarith)
    have : 0 ≤ u ^ (-s₁) := by positivity
    linarith

theorem integrable_sum_sq_rpow (hy : 0 < y) {s : ℝ} (hs : 1 < s) :
    Integrable (fun x : ℝ => (x ^ 2 + y ^ 2) ^ (-(s / 2))) := by
  have := (integrable_wt_rpow hy (show 1 / 2 < s / 2 by linarith)).const_mul (y ^ (-(s / 2)))
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [rpow_sum_sq_eq hy]

/-- The Fourier transform `w ↦ 𝓕h_{w+α, w+β}(ξ)` is holomorphic where `Re(2w+α+β) > 1`. -/
theorem differentiableAt_fourier_hab (hy : 0 < y) (α β : ℂ) (ξ : ℝ) {w₀ : ℂ}
    (h : 1 < (2 * w₀ + α + β).re) :
    DifferentiableAt ℂ (fun w => 𝓕 (hab y (w + α) (w + β)) ξ) w₀ := by
  set δ := (2 * w₀ + α + β).re - 1 with hδ
  have hδ0 : 0 < δ := by linarith
  set R := δ / 4 with hR
  have hR0 : 0 < R := by positivity
  set s₁ := 1 + δ / 2
  set s₂ := (2 * w₀ + α + β).re + δ / 2
  set E := Real.exp (Real.pi * (|(w₀ + α).im| + R + (|(w₀ + β).im| + R)))
  have hre : ∀ w ∈ Metric.ball w₀ R, s₁ ≤ (w + α + (w + β)).re ∧ (w + α + (w + β)).re ≤ s₂ := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := abs_re_le_norm (w - w₀)
    have hre' : (w + α + (w + β)).re = (2 * w₀ + α + β).re + 2 * (w - w₀).re := by
      simp; ring
    obtain ⟨hl, hr⟩ := abs_le.1 (this.trans hw.le)
    rw [hre']
    constructor
    · simp only [s₁]; linarith
    · simp only [s₂]; linarith
  have him : ∀ w ∈ Metric.ball w₀ R, |(w + α).im| + |(w + β).im| ≤
      |(w₀ + α).im| + R + (|(w₀ + β).im| + R) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := abs_im_le_norm (w - w₀)
    have e1 : (w + α).im = (w₀ + α).im + (w - w₀).im := by simp; ring
    have e2 : (w + β).im = (w₀ + β).im + (w - w₀).im := by simp; ring
    rw [e1, e2]
    have ha := abs_add_le ((w₀ + α).im) ((w - w₀).im)
    have hb := abs_add_le ((w₀ + β).im) ((w - w₀).im)
    linarith
  simp only [Real.fourier_real_eq]
  refine GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
    (bound := fun x => E * ((x ^ 2 + y ^ 2) ^ (-(s₁ / 2)) + (x ^ 2 + y ^ 2) ^ (-(s₂ / 2)))) hR0
    ?_ ?_ ?_ ?_
  · intro w _
    have hc : Continuous (fun v : ℝ => ((𝐞 (-(v * ξ)) : Circle) : ℂ)) :=
      continuous_induced_dom.comp (Real.continuous_fourierChar.comp (by fun_prop))
    exact (hc.smul (continuous_hab hy _ _)).aestronglyMeasurable
  · intro x
    refine DifferentiableOn.const_smul ?_ _
    intro w _
    unfold hab
    refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
    · exact ((differentiableAt_id.add_const α).neg).const_cpow (Or.inl (plus_ne_zero hy x))
    · exact ((differentiableAt_id.add_const β).neg).const_cpow (Or.inl (minus_ne_zero hy x))
  · intro x w hw
    rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    refine (norm_hab_le hy _ _ x).trans ?_
    obtain ⟨hs1, hs2⟩ := hre w hw
    have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
    have hE : Real.exp (Real.pi * (|(w + α).im| + |(w + β).im|)) ≤ E :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (him w hw) Real.pi_pos.le)
    have hP := rpow_neg_le_add hpos (show s₁ / 2 ≤ (w + α + (w + β)).re / 2 by linarith)
      (show (w + α + (w + β)).re / 2 ≤ s₂ / 2 by linarith)
    rw [show -(w + α + (w + β)).re / 2 = -((w + α + (w + β)).re / 2) by ring]
    exact mul_le_mul hE hP (by positivity) (by positivity)
  · have hs1 : 1 < s₁ := by simp only [s₁]; linarith
    have hs2 : 1 < s₂ := by simp only [s₂]; linarith
    exact ((integrable_sum_sq_rpow hy hs1).add (integrable_sum_sq_rpow hy hs2)).const_mul E


/-- Every `G_k` is holomorphic along `(w+α, w+β)` where `Re(2w+α+β) > 1 - k`. -/
theorem differentiableAt_Gk (hy : 0 < y) (ξ : ℝ) (k : ℕ) :
    ∀ (α β w₀ : ℂ), 1 < (2 * w₀ + α + β).re + k →
      DifferentiableAt ℂ (fun w => Gk y k (w + α) (w + β) ξ) w₀ := by
  induction k with
  | zero =>
    intro α β w₀ h
    simp only [Nat.cast_zero, add_zero] at h
    exact differentiableAt_fourier_hab hy α β ξ h
  | succ k ih =>
    intro α β w₀ h
    push_cast at h
    have h1 := ih (α + 1) β w₀ (by simp; simp at h; linarith)
    have h2 := ih α (β + 1) w₀ (by simp; simp at h; linarith)
    have e1 : (fun w => Gk y k (w + α + 1) (w + β) ξ) = fun w => Gk y k (w + (α + 1)) (w + β) ξ := by
      funext w; congr 1; ring
    have e2 : (fun w => Gk y k (w + α) (w + β + 1) ξ) = fun w => Gk y k (w + α) (w + (β + 1)) ξ := by
      funext w; congr 1; ring
    simp only [Gk_succ]
    refine (((differentiableAt_id.add_const α).mul ?_).add
      ((differentiableAt_id.add_const β).mul ?_)).neg.div_const _
    · rw [e1]; exact h1
    · rw [e2]; exact h2

/-- The continued transform of the Eisenstein kernel: `Φ_k(w)(ξ) = y^w G_k(w+1/4, w-1/4)(ξ)`. -/
def PhiK (y : ℝ) (k : ℕ) (w : ℂ) (ξ : ℝ) : ℂ :=
  (y : ℂ) ^ w * Gk y k (w + 1 / 4) (w - 1 / 4) ξ

theorem fourier_kerH_eq_PhiK (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) (k : ℕ) {w : ℂ} (hw : 1 / 2 < w.re) :
    𝓕 (kerH y w) ξ = PhiK y k w ξ := by
  have hre : 1 < (w + 1 / 4 + (w - 1 / 4)).re := by simp; linarith
  rw [PhiK, Gk_eq hy hξ k _ _ hre]
  have hk : kerH y w = fun x => (y : ℂ) ^ w * hab y (w + 1 / 4) (w - 1 / 4) x :=
    funext (kerH_eq_hab hy w)
  rw [hk]
  simp only [Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; ext v; ring

theorem differentiableAt_PhiK (hy : 0 < y) (ξ : ℝ) (k : ℕ) {w₀ : ℂ}
    (h : 1 < 2 * w₀.re + k) : DifferentiableAt ℂ (fun w => PhiK y k w ξ) w₀ := by
  unfold PhiK
  refine ((differentiableAt_id).const_cpow (Or.inl (by exact_mod_cast hy.ne'))).mul ?_
  have := differentiableAt_Gk hy ξ k (1 / 4) (-(1 / 4)) w₀ (by simp; linarith)
  simpa [sub_eq_add_neg] using this


/-- `Φ_k` does not depend on `k` where defined. -/
theorem PhiK_eq_PhiK (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) {k k' : ℕ} (hk : k ≤ k') {w : ℂ}
    (hw : 1 < 2 * w.re + k) : PhiK y k w ξ = PhiK y k' w ξ := by
  set U : Set ℂ := {w : ℂ | 1 < 2 * w.re + k} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hUc : IsPreconnected U := by
    have : Convex ℝ U := by
      have := convex_halfSpace_re_gt ((1 - k) / 2)
      convert this using 1; ext z; simp only [hU, Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
    exact this.isPreconnected
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have hdf : DifferentiableOn ℂ (fun w => PhiK y k w ξ) U :=
    fun w hw => (differentiableAt_PhiK hy ξ k hw).differentiableWithinAt
  have hdg : DifferentiableOn ℂ (fun w => PhiK y k' w ξ) U := fun w hw =>
    (differentiableAt_PhiK hy ξ k' (by simp only [hU, Set.mem_setOf_eq] at hw; linarith)).differentiableWithinAt
  have hf := hdf.analyticOnNhd hUo
  have hg := hdg.analyticOnNhd hUo
  have h1U : (1 : ℂ) ∈ U := by
    simp only [hU, Set.mem_setOf_eq, Complex.one_re]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hev : (fun w => PhiK y k w ξ) =ᶠ[nhds (1 : ℂ)] (fun w => PhiK y k' w ξ) := by
    have ho : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (by simp; norm_num)] with w hw
    rw [← fourier_kerH_eq_PhiK hy hξ k hw, ← fourier_kerH_eq_PhiK hy hξ k' hw]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h1U hev hw

/-- **Decay of the continued kernel transform**:
`|Φ_k(w)(ξ)| ≤ ((|w+1/4|+|w-1/4|+2k)/(2π|ξ|))^k e^{2π|Im w|} y^{1-Re w-k} C_{Re w + k/2}`. -/
theorem norm_PhiK_le (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) (k : ℕ) {w : ℂ} (hw : 1 < 2 * w.re + k) :
    ‖PhiK y k w ξ‖ ≤ ((‖w + 1 / 4‖ + ‖w - 1 / 4‖ + 2 * k) / (2 * Real.pi * |ξ|)) ^ k *
      Real.exp (2 * Real.pi * |w.im|) * (y ^ (1 - w.re - k) * cst ((2 * w.re + k) / 2)) := by
  unfold PhiK
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have h := norm_Gk_le hy hξ k (w + 1 / 4) (w - 1 / 4) (by simp; linarith)
  have hre : (w + 1 / 4 + (w - 1 / 4)).re = 2 * w.re := by simp; ring
  have him : |(w + 1 / 4).im| + |(w - 1 / 4).im| = 2 * |w.im| := by simp; ring
  rw [hre, him] at h
  calc y ^ w.re * ‖Gk y k (w + 1 / 4) (w - 1 / 4) ξ‖
      ≤ y ^ w.re * (((‖w + 1 / 4‖ + ‖w - 1 / 4‖ + 2 * k) / (2 * Real.pi * |ξ|)) ^ k *
          Real.exp (Real.pi * (2 * |w.im|)) *
            (y ^ (1 - 2 * w.re - k) * cst ((2 * w.re + k) / 2))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
        rw [show Real.pi * (2 * |w.im|) = 2 * Real.pi * |w.im| by ring]
        have : y ^ w.re * y ^ (1 - 2 * w.re - k) = y ^ (1 - w.re - k) := by
          rw [← Real.rpow_add hy]; congr 1; ring
        rw [← this]; ring

end

end GaloisForLFunctions.RHTower.HalfWeight
