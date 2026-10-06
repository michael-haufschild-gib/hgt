import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Gaussian spectral weight `t² e^{−(t/K)²}` and its Fourier transform

For `K > 0`,

`∫ t² e^{−(t/K)²} e^{2itw} dt = G_K(w) = (√π K³/2)(1 − 2K²w²) e^{−K²w²}`

(`integral_gaussWeight_mul_cexp`), and `G_K = 𝒢_K'` with `𝒢_K(w) = (√π K³/2) w e^{−K²w²}`
(`hasDerivAt_gaussPrim`).  The proof starts from the Gaussian integral
`∫ e^{−t²/K²} e^{2itw} dt = √π K e^{−K²w²}` and integrates by parts twice, using
`t e^{−t²/K²} = −(K²/2)(e^{−t²/K²})'`.
-/

open MeasureTheory Set Filter Complex

namespace GaloisForLFunctions.RHTower.KuznetsovGauss

noncomputable section

/-- The spectral weight `g_K(t) = t² e^{−(t/K)²}`. -/
def gaussWeight (K t : ℝ) : ℝ := t ^ 2 * Real.exp (-(t / K) ^ 2)

/-- `𝒢_K(w) = (√π K³/2) w e^{−K²w²}`. -/
def gaussPrim (K w : ℝ) : ℝ := Real.sqrt Real.pi * K ^ 3 / 2 * (w * Real.exp (-(K * w) ^ 2))

/-- `G_K(w) = (√π K³/2)(1 − 2K²w²) e^{−K²w²}`. -/
def gaussDeriv (K w : ℝ) : ℝ :=
  Real.sqrt Real.pi * K ^ 3 / 2 * ((1 - 2 * (K * w) ^ 2) * Real.exp (-(K * w) ^ 2))

theorem gaussWeight_nonneg (K t : ℝ) : 0 ≤ gaussWeight K t := by
  unfold gaussWeight; positivity

theorem hasDerivAt_gaussPrim (K w : ℝ) : HasDerivAt (gaussPrim K) (gaussDeriv K w) w := by
  have hlin : HasDerivAt (fun w : ℝ => K * w) K w := by
    simpa using (hasDerivAt_id w).const_mul K
  have hsq : HasDerivAt (fun w : ℝ => -(K * w) ^ 2) (-(2 * (K * w) * K)) w :=
    ((hlin.pow 2).neg).congr_deriv (by simp)
  have hprod := ((hasDerivAt_id' w).mul hsq.exp).const_mul (Real.sqrt Real.pi * K ^ 3 / 2)
  change HasDerivAt (fun w => Real.sqrt Real.pi * K ^ 3 / 2 * (w * Real.exp (-(K * w) ^ 2))) _ w
  exact hprod.congr_deriv (by simp only [gaussDeriv]; ring)

/-! ## Integrability of the Gaussian moments -/

theorem integrable_pow_mul_exp_neg_sq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k * Real.exp (-a * t ^ 2)) := by
  refine (integrable_rpow_mul_exp_neg_mul_sq ha (s := k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Real.rpow_natCast]

theorem integrable_pow_mul_cexp {a : ℝ} (ha : 0 < a) (k : ℕ) (w : ℝ) :
    Integrable (fun t : ℝ => ((t ^ k : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
      cexp (2 * t * w * Complex.I)) := by
  refine ((integrable_pow_mul_exp_neg_sq ha k).norm).mono' (by fun_prop) ?_
  refine Eventually.of_forall fun t => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(a : ℂ) * (t : ℂ) ^ 2).re = -a * t ^ 2 := by
    rw [show -(a : ℂ) * (t : ℂ) ^ 2 = ((-a * t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have h2 : (2 * (t : ℂ) * w * Complex.I).re = 0 := by simp
  rw [h1, h2, Real.exp_zero, mul_one, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]

/-! ## The Fourier transform -/

theorem integral_gauss_cexp {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ t : ℝ, cexp (-(a : ℂ) * (t : ℂ) ^ 2) * cexp (2 * t * w * Complex.I) =
      ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * cexp (-((w ^ 2 / a : ℝ) : ℂ)) := by
  have hb : (-(a : ℂ)).re < 0 := by simp [ha]
  have h := integral_cexp_quadratic hb (2 * w * Complex.I) 0
  simp_rw [← Complex.exp_add]
  have hpt : ∀ t : ℝ, -(a : ℂ) * (t : ℂ) ^ 2 + 2 * t * w * Complex.I =
      -(a : ℂ) * (t : ℂ) ^ 2 + 2 * w * Complex.I * t + 0 := fun t => by ring
  simp_rw [hpt, h]
  congr 1
  · rw [neg_neg, show (Real.pi : ℂ) / a = ((Real.pi / a : ℝ) : ℂ) by push_cast; rfl,
      Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  · congr 1
    have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

theorem hasDerivAt_gauss {a : ℝ} (t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (-(a : ℂ) * (t : ℂ) ^ 2))
      (-(2 * a) * (((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2))) t := by
  have h := (((hasDerivAt_id t).ofReal_comp).pow 2).const_mul (-(a : ℂ))
  refine h.cexp.congr_deriv ?_
  simp
  ring

theorem hasDerivAt_cexp_line (w t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (2 * t * w * Complex.I))
      (2 * w * Complex.I * cexp (2 * t * w * Complex.I)) t := by
  have hf : (fun t : ℝ => cexp (2 * t * w * Complex.I)) =
      fun t : ℝ => cexp ((2 * w * Complex.I) * (t : ℂ)) := by
    funext t; ring_nf
  rw [hf]
  exact (((hasDerivAt_id (t : ℂ)).const_mul (2 * w * Complex.I)).comp_ofReal.cexp).congr_deriv
    (by simp; ring_nf)

/-- `∫ t e^{−at²} e^{2itw} dt = (iw/a) ∫ e^{−at²} e^{2itw} dt`. -/
theorem integral_mul_gauss_cexp {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ t : ℝ, ((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) * cexp (2 * t * w * Complex.I) =
      w * Complex.I / a * ∫ t : ℝ, ((t ^ 0 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I) := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => cexp (2 * t * w * Complex.I))
    (u' := fun t : ℝ => 2 * w * Complex.I * cexp (2 * t * w * Complex.I))
    (v := fun t : ℝ => cexp (-(a : ℂ) * (t : ℂ) ^ 2))
    (v' := fun t : ℝ => -(2 * a) * (((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2)))
    (fun t _ => hasDerivAt_cexp_line w t) (fun t _ => hasDerivAt_gauss t)
    (((integrable_pow_mul_cexp ha 1 w).const_mul (-(2 * a : ℂ))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; ring))
    (((integrable_pow_mul_cexp ha 0 w).const_mul (2 * w * Complex.I)).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
    ((integrable_pow_mul_cexp ha 0 w).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have h1 : ∫ t : ℝ, cexp (2 * t * w * Complex.I) *
      (-(2 * a) * (((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2))) =
      -(2 * a) * ∫ t : ℝ, ((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have h2 : ∫ t : ℝ, 2 * w * Complex.I * cexp (2 * t * w * Complex.I) *
      cexp (-(a : ℂ) * (t : ℂ) ^ 2) =
      2 * w * Complex.I * ∫ t : ℝ, ((t ^ 0 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I) := by
    rw [← integral_const_mul]; congr 1; funext t; push_cast; ring
  rw [h1, h2] at h
  rw [div_mul_eq_mul_div, eq_div_iff hac]
  linear_combination (-1 / 2 : ℂ) * h

/-- `∫ t² e^{−at²} e^{2itw} dt = (1 − 2w²/a)/(2a) ∫ e^{−at²} e^{2itw} dt`. -/
theorem integral_sq_mul_gauss_cexp {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ t : ℝ, ((t ^ 2 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) * cexp (2 * t * w * Complex.I) =
      (1 - 2 * w ^ 2 / a) / (2 * a) * ∫ t : ℝ, ((t ^ 0 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I) := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => (t : ℂ) * cexp (2 * t * w * Complex.I))
    (u' := fun t : ℝ => cexp (2 * t * w * Complex.I) +
      (t : ℂ) * (2 * w * Complex.I * cexp (2 * t * w * Complex.I)))
    (v := fun t : ℝ => cexp (-(a : ℂ) * (t : ℂ) ^ 2))
    (v' := fun t : ℝ => -(2 * a) * (((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2)))
    (fun t _ => (((hasDerivAt_id t).ofReal_comp).mul (hasDerivAt_cexp_line w t)).congr_deriv
      (by simp))
    (fun t _ => hasDerivAt_gauss t)
    (((integrable_pow_mul_cexp ha 2 w).const_mul (-(2 * a : ℂ))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
    ((((integrable_pow_mul_cexp ha 0 w)).add
      ((integrable_pow_mul_cexp ha 1 w).const_mul (2 * w * Complex.I))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply, Pi.add_apply]; push_cast; ring))
    ((integrable_pow_mul_cexp ha 1 w).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have h1 : ∫ t : ℝ, (t : ℂ) * cexp (2 * t * w * Complex.I) *
      (-(2 * a) * (((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2))) =
      -(2 * a) * ∫ t : ℝ, ((t ^ 2 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I) := by
    rw [← integral_const_mul]; congr 1; funext t; push_cast; ring
  have h2 : ∫ t : ℝ, (cexp (2 * t * w * Complex.I) +
      (t : ℂ) * (2 * w * Complex.I * cexp (2 * t * w * Complex.I))) *
      cexp (-(a : ℂ) * (t : ℂ) ^ 2) =
      (∫ t : ℝ, ((t ^ 0 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I)) + 2 * w * Complex.I *
      ∫ t : ℝ, ((t ^ 1 : ℝ) : ℂ) * cexp (-(a : ℂ) * (t : ℂ) ^ 2) * cexp (2 * t * w * Complex.I) := by
    rw [← integral_const_mul, ← integral_add (integrable_pow_mul_cexp ha 0 w)
      ((integrable_pow_mul_cexp ha 1 w).const_mul _)]
    congr 1; funext t; push_cast; ring
  rw [h1, h2, integral_mul_gauss_cexp ha w] at h
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero two_ne_zero hac)]
  linear_combination (-1 : ℂ) * h + (2 * (w : ℂ) ^ 2 / a * ∫ t : ℝ, ((t ^ 0 : ℝ) : ℂ) *
    cexp (-(a : ℂ) * (t : ℂ) ^ 2) * cexp (2 * t * w * Complex.I)) * Complex.I_sq

/-- **The Fourier transform of the weight**: `∫ g_K(t) e^{2itw} dt = G_K(w)`. -/
theorem integral_gaussWeight_mul_cexp {K : ℝ} (hK : 0 < K) (w : ℝ) :
    ∫ t : ℝ, (gaussWeight K t : ℂ) * cexp (2 * t * w * Complex.I) = gaussDeriv K w := by
  have ha : (0 : ℝ) < (K ^ 2)⁻¹ := by positivity
  have hpt : ∀ t : ℝ, (gaussWeight K t : ℂ) * cexp (2 * t * w * Complex.I) =
      ((t ^ 2 : ℝ) : ℂ) * cexp (-(((K ^ 2)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2) *
        cexp (2 * t * w * Complex.I) := fun t => by
    rw [gaussWeight, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 3
    push_cast
    field_simp
  simp_rw [hpt]
  rw [integral_sq_mul_gauss_cexp ha w]
  have h0 : ∀ t : ℝ, ((t ^ 0 : ℝ) : ℂ) * cexp (-(((K ^ 2)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2) *
      cexp (2 * t * w * Complex.I) =
      cexp (-(((K ^ 2)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2) * cexp (2 * t * w * Complex.I) := fun t => by
    simp
  simp_rw [h0]
  rw [integral_gauss_cexp ha w, gaussDeriv, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ (K ^ 2)⁻¹),
    Real.sqrt_inv, Real.sqrt_sq hK.le]
  have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  push_cast
  have he : -((w : ℂ) ^ 2 / ((K : ℂ) ^ 2)⁻¹) = -((K : ℂ) * w) ^ 2 := by field_simp
  rw [he]
  field_simp

end

end GaloisForLFunctions.RHTower.KuznetsovGauss
