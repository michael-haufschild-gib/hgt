import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# A Gaussian filter that removes the poles at `±i/2`

Let `g_t(w) = (4πt)^{−1/2} e^{−w²/(4t)}` (`filterGauss`, variance `2t`, moment generating function
`∫ g_t(w) e^{wc} dw = e^{tc²}`). For `K > 0` put

`ǧ_K(w) = 2 e^{−K/4} g_K(w) − e^{−K/2} g_{2K}(w)`  (`poleFilter`).

* `∫ ǧ_K(w) e^{wc} dw = 2e^{−K/4} e^{Kc²} − e^{−K/2} e^{2Kc²}` (`integral_poleFilter_mul_rexp`).
  At `c = ±½` this is `1`.
* `∫ ǧ_K(w) cos(τw) dw = 2E − E²` with `E = e^{−K(τ² + ¼)}` (`integral_poleFilter_mul_cos`).
  Hence `1 − ∫ ǧ_K cos(τ·) = (1 − E)² > 0` for every real `τ` (`one_sub_integral_poleFilter_mul_cos_pos`).
  As an analytic function of `τ`, `(1 − e^{−K(τ²+¼)})²` has double zeros at `τ = ±i/2`.
* `∫ |ǧ_K| ≤ 2e^{−K/4} + e^{−K/2}` (`integral_abs_poleFilter_le`), which tends to `0`.

So subtracting `ǧ_K ⋆ P` from an even positive-definite profile `P` multiplies its cosine transform by
the strictly positive factor `(1 − e^{−K(τ²+¼)})²`. This kills a simple pole of the transform at
`±i/2` and leaves a zero there, and the perturbation is uniformly small as `K → ∞`.
-/

open MeasureTheory Complex Set Filter

namespace RHTower

noncomputable section

/-- The normal density of variance `2t`. -/
def filterGauss (t w : ℝ) : ℝ := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-(w ^ 2 / (4 * t)))

theorem filterGauss_pos {t : ℝ} (ht : 0 < t) (w : ℝ) : 0 < filterGauss t w := by
  unfold filterGauss; positivity

theorem filterGauss_neg (t w : ℝ) : filterGauss t (-w) = filterGauss t w := by
  simp [filterGauss]

theorem continuous_filterGauss (t : ℝ) : Continuous (filterGauss t) := by
  unfold filterGauss; fun_prop

/-- The moment generating function `∫ g_t(w) e^{wx} dw = e^{tx²}`. -/
theorem integral_filterGauss_mul_exp {t : ℝ} (ht : 0 < t) (x : ℂ) :
    ∫ w : ℝ, (filterGauss t w : ℂ) * Complex.exp (w * x) = Complex.exp (t * x ^ 2) := by
  have hb : (-(1 / (4 * t) : ℂ)).re < 0 := by
    rw [Complex.neg_re, ← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_div, Complex.ofReal_re]
    have : 0 < 1 / (4 * t) := by positivity
    linarith
  have hquad := integral_cexp_quadratic hb x 0
  have hfun : ∀ w : ℝ, (filterGauss t w : ℂ) * Complex.exp (w * x) =
      ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) *
        Complex.exp (-(1 / (4 * t) : ℂ) * (w : ℂ) ^ 2 + x * w + 0) := by
    intro w
    unfold filterGauss
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

theorem integrable_filterGauss_mul_exp {t : ℝ} (ht : 0 < t) (x : ℂ) :
    Integrable (fun w : ℝ => (filterGauss t w : ℂ) * Complex.exp (w * x)) := by
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  refine ((integrable_cexp_quadratic hb x 0).const_mul
    (((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).congr (Eventually.of_forall fun w => ?_)
  unfold filterGauss
  push_cast
  rw [mul_assoc (_ : ℂ) (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
  congr 2
  ring

theorem integrable_filterGauss_mul_rexp {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable fun w : ℝ => filterGauss t w * Real.exp (w * c) := by
  refine (integrable_filterGauss_mul_exp ht c).norm.congr (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (filterGauss_pos ht _),
    ← Complex.ofReal_mul, Complex.norm_exp_ofReal]

theorem integral_filterGauss_mul_rexp {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ w : ℝ, filterGauss t w * Real.exp (w * c) = Real.exp (t * c ^ 2) := by
  have h := integral_filterGauss_mul_exp ht c
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  exact h

theorem integrable_filterGauss {t : ℝ} (ht : 0 < t) : Integrable (filterGauss t) := by
  simpa using integrable_filterGauss_mul_rexp ht 0

theorem integral_filterGauss_eq_one {t : ℝ} (ht : 0 < t) : ∫ w, filterGauss t w = 1 := by
  simpa using integral_filterGauss_mul_rexp ht 0

/-- The cosine transform of the Gaussian: `∫ g_t(w) cos(τw) dw = e^{−tτ²}`. -/
theorem integral_filterGauss_mul_cos {t : ℝ} (ht : 0 < t) (τ : ℝ) :
    ∫ w, filterGauss t w * Real.cos (τ * w) = Real.exp (-(t * τ ^ 2)) := by
  have h := integral_filterGauss_mul_exp ht ((τ : ℂ) * I)
  have hint := integrable_filterGauss_mul_exp ht ((τ : ℂ) * I)
  have e1 : ∀ w : ℝ, ((filterGauss t w : ℂ) * Complex.exp ((w : ℂ) * ((τ : ℂ) * I))).re =
      filterGauss t w * Real.cos (τ * w) := by
    intro w
    rw [show (w : ℂ) * ((τ : ℂ) * I) = ((τ * w : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have e2 : (Complex.exp ((t : ℂ) * ((τ : ℂ) * I) ^ 2)).re = Real.exp (-(t * τ ^ 2)) := by
    rw [show (t : ℂ) * ((τ : ℂ) * I) ^ 2 = ((-(t * τ ^ 2) : ℝ) : ℂ) by
      push_cast; ring_nf; rw [I_sq]; ring, ← Complex.ofReal_exp, Complex.ofReal_re]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  simp_rw [e1] at hre
  rw [hre, h, e2]

/-- The pole filter `ǧ_K(w) = 2e^{−K/4} g_K(w) − e^{−K/2} g_{2K}(w)`. -/
def poleFilter (K w : ℝ) : ℝ :=
  2 * Real.exp (-(K / 4)) * filterGauss K w - Real.exp (-(K / 2)) * filterGauss (2 * K) w

/-- The nonnegative majorant `2e^{−K/4} g_K + e^{−K/2} g_{2K}` of `|ǧ_K|`. -/
def gaussPoleMajorant (K w : ℝ) : ℝ :=
  2 * Real.exp (-(K / 4)) * filterGauss K w + Real.exp (-(K / 2)) * filterGauss (2 * K) w

theorem poleFilter_neg (K w : ℝ) : poleFilter K (-w) = poleFilter K w := by
  simp only [poleFilter, filterGauss_neg]

theorem continuous_poleFilter (K : ℝ) : Continuous (poleFilter K) := by
  unfold poleFilter filterGauss; fun_prop

theorem continuous_gaussPoleMajorant (K : ℝ) : Continuous (gaussPoleMajorant K) := by
  unfold gaussPoleMajorant filterGauss; fun_prop

theorem gaussPoleMajorant_nonneg {K : ℝ} (hK : 0 < K) (w : ℝ) : 0 ≤ gaussPoleMajorant K w := by
  unfold gaussPoleMajorant
  have h1 := filterGauss_pos hK w
  have h2 := filterGauss_pos (by positivity : 0 < 2 * K) w
  positivity

theorem abs_poleFilter_le {K : ℝ} (hK : 0 < K) (w : ℝ) :
    |poleFilter K w| ≤ gaussPoleMajorant K w := by
  unfold poleFilter gaussPoleMajorant
  have h1 := filterGauss_pos hK w
  have h2 := filterGauss_pos (by positivity : 0 < 2 * K) w
  have e1 := Real.exp_pos (-(K / 4))
  have e2 := Real.exp_pos (-(K / 2))
  rw [abs_le]
  constructor <;> nlinarith [mul_pos e1 h1, mul_pos e2 h2]

theorem integrable_gaussPoleMajorant_mul_rexp {K : ℝ} (hK : 0 < K) (c : ℝ) :
    Integrable fun w => gaussPoleMajorant K w * Real.exp (w * c) := by
  have h := ((integrable_filterGauss_mul_rexp hK c).const_mul (2 * Real.exp (-(K / 4)))).add
    ((integrable_filterGauss_mul_rexp (by positivity : 0 < 2 * K) c).const_mul
      (Real.exp (-(K / 2))))
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [gaussPoleMajorant, Pi.add_apply]; ring

theorem integrable_poleFilter_mul_rexp {K : ℝ} (hK : 0 < K) (c : ℝ) :
    Integrable fun w => poleFilter K w * Real.exp (w * c) := by
  refine (integrable_gaussPoleMajorant_mul_rexp hK c).mono'
    ((continuous_poleFilter K).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (abs_poleFilter_le hK w) (Real.exp_pos _).le

theorem integrable_poleFilter {K : ℝ} (hK : 0 < K) : Integrable (poleFilter K) := by
  simpa using integrable_poleFilter_mul_rexp hK 0

/-- `|ǧ_K(w)| e^{c|w|}` is integrable for every `c ≥ 0`. -/
theorem integrable_gaussPoleMajorant_mul_exp_abs {K : ℝ} (hK : 0 < K) (c : ℝ) :
    Integrable fun w => gaussPoleMajorant K w * Real.exp (c * |w|) := by
  refine ((integrable_gaussPoleMajorant_mul_rexp hK c).add
    (integrable_gaussPoleMajorant_mul_rexp hK (-c))).mono'
    ((continuous_gaussPoleMajorant K).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  have hm := gaussPoleMajorant_nonneg hK w
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm (Real.exp_pos _).le), ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hm
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw, mul_comm]; linarith [Real.exp_pos (w * -c)]
  · rw [abs_of_nonpos hw, show c * -w = w * -c by ring]; linarith [Real.exp_pos (w * c)]

/-- **The exponential moments of the filter.** -/
theorem integral_poleFilter_mul_rexp {K : ℝ} (hK : 0 < K) (c : ℝ) :
    ∫ w, poleFilter K w * Real.exp (w * c) =
      2 * Real.exp (-(K / 4)) * Real.exp (K * c ^ 2) -
        Real.exp (-(K / 2)) * Real.exp (2 * K * c ^ 2) := by
  have hK2 : 0 < 2 * K := by positivity
  have e : (fun w => poleFilter K w * Real.exp (w * c)) = fun w =>
      2 * Real.exp (-(K / 4)) * (filterGauss K w * Real.exp (w * c)) -
        Real.exp (-(K / 2)) * (filterGauss (2 * K) w * Real.exp (w * c)) := by
    funext w; simp only [poleFilter]; ring
  rw [e, integral_sub ((integrable_filterGauss_mul_rexp hK c).const_mul _)
    ((integrable_filterGauss_mul_rexp hK2 c).const_mul _), integral_const_mul,
    integral_const_mul, integral_filterGauss_mul_rexp hK, integral_filterGauss_mul_rexp hK2]

/-- At `c = ±½` the filter has exponential moment `1`. -/
theorem integral_poleFilter_mul_exp_half {K : ℝ} (hK : 0 < K) (σ : ℝ) (hσ : σ ^ 2 = 1 / 4) :
    ∫ w, poleFilter K w * Real.exp (w * σ) = 1 := by
  rw [integral_poleFilter_mul_rexp hK, hσ, mul_assoc, ← Real.exp_add, ← Real.exp_add,
    show -(K / 4) + K * (1 / 4) = 0 by ring, show -(K / 2) + 2 * K * (1 / 4) = 0 by ring,
    Real.exp_zero]
  norm_num

/-- **The cosine transform of the filter**: `2E − E²` with `E = e^{−K(τ² + ¼)}`. -/
theorem integral_poleFilter_mul_cos {K : ℝ} (hK : 0 < K) (τ : ℝ) :
    ∫ w, poleFilter K w * Real.cos (τ * w) =
      2 * Real.exp (-(K * (τ ^ 2 + 1 / 4))) - Real.exp (-(K * (τ ^ 2 + 1 / 4))) ^ 2 := by
  have hK2 : 0 < 2 * K := by positivity
  have hi : ∀ t, 0 < t → Integrable fun w => filterGauss t w * Real.cos (τ * w) := by
    intro t ht
    refine (integrable_filterGauss ht).mono' (by unfold filterGauss; fun_prop)
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (filterGauss_pos ht w)]
    exact mul_le_of_le_one_right (filterGauss_pos ht w).le (Real.abs_cos_le_one _)
  have e : (fun w => poleFilter K w * Real.cos (τ * w)) = fun w =>
      2 * Real.exp (-(K / 4)) * (filterGauss K w * Real.cos (τ * w)) -
        Real.exp (-(K / 2)) * (filterGauss (2 * K) w * Real.cos (τ * w)) := by
    funext w; simp only [poleFilter]; ring
  rw [e, integral_sub ((hi K hK).const_mul _) ((hi _ hK2).const_mul _), integral_const_mul,
    integral_const_mul, integral_filterGauss_mul_cos hK, integral_filterGauss_mul_cos hK2]
  have a1 : Real.exp (-(K / 4)) * Real.exp (-(K * τ ^ 2)) = Real.exp (-(K * (τ ^ 2 + 1 / 4))) := by
    rw [← Real.exp_add]; congr 1; ring
  have a2 : Real.exp (-(K / 2)) * Real.exp (-(2 * K * τ ^ 2)) =
      Real.exp (-(K * (τ ^ 2 + 1 / 4))) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_assoc, a1, a2]

/-- **The filtered spectrum is strictly positive**: `1 − ∫ ǧ_K cos(τ·) = (1 − e^{−K(τ²+¼)})² > 0`. -/
theorem one_sub_integral_poleFilter_mul_cos_pos {K : ℝ} (hK : 0 < K) (τ : ℝ) :
    0 < 1 - ∫ w, poleFilter K w * Real.cos (τ * w) := by
  rw [integral_poleFilter_mul_cos hK]
  have hlt : Real.exp (-(K * (τ ^ 2 + 1 / 4))) < 1 := by
    have : 0 < K * (τ ^ 2 + 1 / 4) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(K * (τ ^ 2 + 1 / 4)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  nlinarith [sq_pos_of_pos (sub_pos.mpr hlt)]

/-- **The filter is small in `L¹`.** -/
theorem integral_abs_poleFilter_le {K : ℝ} (hK : 0 < K) :
    ∫ w, |poleFilter K w| ≤ 2 * Real.exp (-(K / 4)) + Real.exp (-(K / 2)) := by
  have hK2 : 0 < 2 * K := by positivity
  have hmaj : ∫ w, gaussPoleMajorant K w = 2 * Real.exp (-(K / 4)) + Real.exp (-(K / 2)) := by
    unfold gaussPoleMajorant
    rw [integral_add ((integrable_filterGauss hK).const_mul _)
      ((integrable_filterGauss hK2).const_mul _), integral_const_mul, integral_const_mul,
      integral_filterGauss_eq_one hK, integral_filterGauss_eq_one hK2]
    ring
  rw [← hmaj]
  refine integral_mono (integrable_poleFilter hK).abs ?_ (abs_poleFilter_le hK)
  simpa using integrable_gaussPoleMajorant_mul_rexp hK 0

end

end RHTower
