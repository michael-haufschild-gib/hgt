import GaloisForLFunctions.RHTower.KuznetsovSameSignWeightOfOdd
import GaloisForLFunctions.RHTower.KuznetsovBesselIdentity
import GaloisForLFunctions.HTGeometry.SechComplexFourierTransform
import GaloisForLFunctions.HTGeometry.FourierIteratedDerivDecay

/-!
# The same-sign spectral weights as `sech`-kernel integrals

The Whittaker–Mellin square is elementary on the real line: by the reflection formulas,

`t W(1+it, ν) W(1−it, ν) = π² sinh(πt) / (cos 2πν + cosh 2πt)`   (`mul_whittMellin_one_add_eq`)

for `|Re ν| < ½`.  The right side is `(2i)⁻¹` times the Fourier transform of the kernel

`k_ν(w) = (π / sin πν) sinh(2νw) / cosh w`   (`k_0(w) = 2w / cosh w`)

(`integral_sechKernel_mul_cexp`), by `∫ e^{aw}/cosh w dw = π/cos(πa/2)`.  Since the same-sign weight
of an odd profile `G` is `h(t) = (2it/π) Ĝ(t)`, Fubini and Fourier inversion give the exact identity

`∫ h(t) |W(1+it, ν)|² dt = ∫ G(w) k_ν(w) dw`   (`specWeight_eq_integral_sechKernel`).

For `ν = iκ` the kernel is `π sin(2κw)/(sinh(πκ) cosh w)`, for real `ν ∈ [0, ½)` it is
`(π/sin πν) sinh(2νw)/cosh w ≤ π|w| cosh(2νw)/cosh w`: the decay `e^{−πκ}` and the exceptional growth
`e^{2ν|w|}` are explicit.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-! ## The elementary form of `|W(1+it, ν)|²` -/

/-- `Φ̃_ν(t) = π² sinh(πt) / (cos 2πν + cosh 2πt)`. -/
def sechProfile (ν : ℂ) (t : ℝ) : ℂ :=
  (Real.pi : ℂ) ^ 2 * Complex.sinh (Real.pi * t) /
    (Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t))

theorem Gamma_half_add_mul_Gamma_half_sub (u : ℂ) :
    Complex.Gamma (1 / 2 + u) * Complex.Gamma (1 / 2 - u) = Real.pi / Complex.cos (Real.pi * u) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + u)
  rw [show (1 : ℂ) - (1 / 2 + u) = 1 / 2 - u by ring,
    show (Real.pi : ℂ) * (1 / 2 + u) = Real.pi / 2 + Real.pi * u by ring, Complex.sin_add,
    Complex.sin_pi_div_two, Complex.cos_pi_div_two, zero_mul, add_zero, one_mul] at h
  exact h

theorem Gamma_one_add_mul_Gamma_one_sub {t : ℝ} (ht : t ≠ 0) :
    Complex.Gamma (1 + t * Complex.I) * Complex.Gamma (1 - t * Complex.I) =
      Real.pi * t / Complex.sinh (Real.pi * t) := by
  have htI : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have h := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * Complex.I)
  rw [show (1 : ℂ) + t * Complex.I = t * Complex.I + 1 by ring, Complex.Gamma_add_one _ htI,
    mul_assoc, h, show (Real.pi : ℂ) * (t * Complex.I) = (Real.pi * t) * Complex.I by ring,
    Complex.sin_mul_I]
  have hs : Complex.sinh (Real.pi * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast fun h => mul_ne_zero Real.pi_ne_zero ht (Real.sinh_eq_zero.1 h)
  field_simp

theorem cos_pi_mul_ne_zero {u : ℂ} (hu : |u.re| < 1 / 2) : Complex.cos (Real.pi * u) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 h
  have hre := congrArg Complex.re hk
  simp at hre
  have hπ := Real.pi_pos
  have : u.re = (2 * k + 1) / 2 := by
    field_simp at hre ⊢; nlinarith
  rw [this] at hu
  rcases abs_lt.1 hu with ⟨h1, h2⟩
  have hk1 : (k : ℝ) < 0 := by linarith
  have hk2 : (-1 : ℝ) < k := by linarith
  have : k < 0 := by exact_mod_cast hk1
  have : -1 < k := by exact_mod_cast hk2
  omega

/-- **`t W(1+it,ν) W(1−it,ν) = π² sinh(πt)/(cos 2πν + cosh 2πt)`** for `|Re ν| < ½`. -/
theorem mul_whittMellin_one_add_eq {ν : ℂ} (hν : |ν.re| < 1 / 2) {t : ℝ} (ht : t ≠ 0) :
    (t : ℂ) * (whittMellin (1 + t * Complex.I) ν * whittMellin (1 - t * Complex.I) ν) =
      sechProfile ν t := by
  have hb1 : 1 / 2 < ((1 : ℂ) + t * Complex.I).re := by simp; norm_num
  have hb2 : 1 / 2 < ((1 : ℂ) - t * Complex.I).re := by simp; norm_num
  rw [whittMellin_eq hb1, whittMellin_eq hb2]
  have e1 : (1 : ℂ) + t * Complex.I - 1 / 2 + ν = 1 / 2 + (t * Complex.I + ν) := by ring
  have e2 : (1 : ℂ) + t * Complex.I - 1 / 2 - ν = 1 / 2 + (t * Complex.I - ν) := by ring
  have e3 : (1 : ℂ) - t * Complex.I - 1 / 2 + ν = 1 / 2 - (t * Complex.I - ν) := by ring
  have e4 : (1 : ℂ) - t * Complex.I - 1 / 2 - ν = 1 / 2 - (t * Complex.I + ν) := by ring
  rw [e1, e2, e3, e4]
  have hA := Gamma_half_add_mul_Gamma_half_sub ((t : ℂ) * Complex.I + ν)
  have hB := Gamma_half_add_mul_Gamma_half_sub ((t : ℂ) * Complex.I - ν)
  have hC := Gamma_one_add_mul_Gamma_one_sub ht
  have h2 : (2 : ℂ) ^ (-((1 : ℂ) + t * Complex.I - 1 / 2)) * (2 : ℂ) ^ (-((1 : ℂ) - t * Complex.I - 1 / 2))
      = 1 / 2 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -((1 : ℂ) + t * Complex.I - 1 / 2) +
      -((1 : ℂ) - t * Complex.I - 1 / 2) = -1 by ring, Complex.cpow_neg_one]
    ring
  have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) = Real.pi := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hcA : Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν)) ≠ 0 :=
    cos_pi_mul_ne_zero (by simpa using hν)
  have hcB : Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν)) ≠ 0 :=
    cos_pi_mul_ne_zero (by simpa using hν)
  have hs : Complex.sinh (Real.pi * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast fun h => mul_ne_zero Real.pi_ne_zero ht (Real.sinh_eq_zero.1 h)
  have hG1 : Complex.Gamma (1 + t * Complex.I) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp)
  have hG2 : Complex.Gamma (1 - t * Complex.I) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp)
  have hprod : Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν)) *
      Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν)) =
      (Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t)) / 2 := by
    rw [show (Real.pi : ℂ) * ((t : ℂ) * Complex.I + ν) = (Real.pi * t) * Complex.I + Real.pi * ν by ring,
      show (Real.pi : ℂ) * ((t : ℂ) * Complex.I - ν) = (Real.pi * t) * Complex.I - Real.pi * ν by ring,
      Complex.cos_add, Complex.cos_sub, Complex.cos_mul_I, Complex.sin_mul_I,
      show (2 : ℂ) * Real.pi * ν = 2 * (Real.pi * ν) by ring, Complex.cos_two_mul,
      show (2 : ℂ) * Real.pi * t = 2 * (Real.pi * t) by ring, Complex.cosh_two_mul]
    have hc := Complex.cos_sq_add_sin_sq ((Real.pi : ℂ) * ν)
    have hh := Complex.cosh_sq_sub_sinh_sq ((Real.pi : ℂ) * t)
    linear_combination (Complex.cosh ((Real.pi : ℂ) * t) ^ 2 - 1) * hc +
      (1 / 2 - Complex.sin ((Real.pi : ℂ) * ν) ^ 2) * hh +
      (-(Complex.sinh ((Real.pi : ℂ) * t)) ^ 2 * Complex.sin ((Real.pi : ℂ) * ν) ^ 2) * Complex.I_sq
  have hden : Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hprod; exact mul_ne_zero hcA hcB hprod
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  set gA := Complex.Gamma (1 / 2 + ((t : ℂ) * Complex.I + ν))
  set gA' := Complex.Gamma (1 / 2 - ((t : ℂ) * Complex.I + ν))
  set gB := Complex.Gamma (1 / 2 + ((t : ℂ) * Complex.I - ν))
  set gB' := Complex.Gamma (1 / 2 - ((t : ℂ) * Complex.I - ν))
  set p₁ := (2 : ℂ) ^ (-((1 : ℂ) + t * Complex.I - 1 / 2))
  set p₂ := (2 : ℂ) ^ (-((1 : ℂ) - t * Complex.I - 1 / 2))
  calc (t : ℂ) * ((Real.sqrt Real.pi : ℂ) * p₁ * gA * gB / Complex.Gamma (1 + t * Complex.I) *
        ((Real.sqrt Real.pi : ℂ) * p₂ * gB' * gA' / Complex.Gamma (1 - t * Complex.I)))
      = (t : ℂ) * (((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ)) * (p₁ * p₂) *
          (gA * gA') * (gB * gB') /
          (Complex.Gamma (1 + t * Complex.I) * Complex.Gamma (1 - t * Complex.I)) := by
        field_simp
    _ = (t : ℂ) * Real.pi * (1 / 2) * (Real.pi / Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν))) *
          (Real.pi / Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν))) /
          (Real.pi * t / Complex.sinh (Real.pi * t)) := by
        rw [hsq, h2, hA, hB, hC]
    _ = (Real.pi : ℂ) ^ 2 * Complex.sinh (Real.pi * t) /
          (2 * (Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν)) *
            Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν)))) := by
        field_simp
    _ = _ := by rw [hprod, sechProfile]; field_simp


/-! ## The Fourier transform of the `sech` kernel -/

theorem cosh_ne_zero_of_abs_im_lt {u : ℂ} (hu : |u.im| < Real.pi / 2) : Complex.cosh u ≠ 0 := by
  rw [← Complex.cos_mul_I]
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 h
  have hre := congrArg Complex.re hk
  simp at hre
  have hπ := Real.pi_pos
  rcases abs_lt.1 hu with ⟨h1, h2⟩
  have hk1 : (k : ℝ) < 0 := by nlinarith
  have hk2 : (-1 : ℝ) < k := by nlinarith
  have : k < 0 := by exact_mod_cast hk1
  have : -1 < k := by exact_mod_cast hk2
  omega

theorem norm_cexp_mul_I_div_cosh (z : ℂ) (w : ℝ) :
    ‖Complex.exp (-(z * (w : ℂ)) * Complex.I) / (Real.cosh w : ℂ)‖ =
      Real.exp (z.im * w) / Real.cosh w := by
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos w).le]
  congr 2
  simp

theorem exp_mul_div_cosh_le (a w : ℝ) :
    Real.exp (a * w) / Real.cosh w ≤ 2 * Real.exp (-((1 - |a|) * |w|)) := by
  have hc := Real.cosh_pos w
  rw [div_le_iff₀ hc]
  have h1 : Real.exp |w| ≤ 2 * Real.cosh w := by
    rw [Real.cosh_eq]
    rcases le_total 0 w with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-w)]
    · rw [abs_of_nonpos h]; linarith [Real.exp_pos w]
  have h2 : Real.exp (a * w) ≤ Real.exp (|a| * |w|) :=
    Real.exp_le_exp.2 (by rw [← abs_mul]; exact le_abs_self _)
  have h3 : Real.exp (|a| * |w|) = Real.exp (-((1 - |a|) * |w|)) * Real.exp |w| := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (a * w) ≤ Real.exp (-((1 - |a|) * |w|)) * Real.exp |w| := h2.trans h3.le
    _ ≤ Real.exp (-((1 - |a|) * |w|)) * (2 * Real.cosh w) := by gcongr
    _ = _ := by ring

theorem integrable_exp_neg_mul_abs' {c : ℝ} (hc : 0 < c) : Integrable fun w : ℝ => Real.exp (-(c * |w|)) := by
  have h := integrable_exp_neg_abs'.comp_mul_left' hc.ne'
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [abs_mul, abs_of_pos hc]

theorem integrable_cexp_div_cosh {z : ℂ} (hz : |z.im| < 1) :
    Integrable fun w : ℝ => Complex.exp (-(z * (w : ℂ)) * Complex.I) / (Real.cosh w : ℂ) := by
  refine ((integrable_exp_neg_mul_abs' (c := 1 - |z.im|) (by linarith)).const_mul 2).mono'
    (Continuous.aestronglyMeasurable (Continuous.div (by fun_prop) (by fun_prop)
      fun w => by exact_mod_cast (Real.cosh_pos w).ne')) (Eventually.of_forall fun w => ?_)
  rw [norm_cexp_mul_I_div_cosh]
  exact exp_mul_div_cosh_le _ _

/-- **`∫ sinh(2νw)/cosh w · e^{2itw} dw = 2πi sin(πν) sinh(πt)/(cos 2πν + cosh 2πt)`.** -/
theorem integral_sinh_div_cosh_mul_cexp {ν : ℂ} (hν : |ν.re| < 1 / 2) (t : ℝ) :
    ∫ w : ℝ, Complex.sinh (2 * ν * w) / (Real.cosh w : ℂ) * Complex.exp (2 * t * w * Complex.I) =
      2 * Real.pi * Complex.I * Complex.sin (Real.pi * ν) * Complex.sinh (Real.pi * t) /
        (Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t)) := by
  set z₁ : ℂ := 2 * ν * Complex.I - 2 * t
  set z₂ : ℂ := -2 * ν * Complex.I - 2 * t
  have hz₁ : |z₁.im| < 1 := by simp [z₁]; linarith
  have hz₂ : |z₂.im| < 1 := by simp [z₂]; linarith
  have hpt : ∀ w : ℝ, Complex.sinh (2 * ν * w) / (Real.cosh w : ℂ) * Complex.exp (2 * t * w * Complex.I) =
      (1 / 2) * (Complex.exp (-(z₁ * (w : ℂ)) * Complex.I) / (Real.cosh w : ℂ)) -
        (1 / 2) * (Complex.exp (-(z₂ * (w : ℂ)) * Complex.I) / (Real.cosh w : ℂ)) := fun w => by
    rw [Complex.sinh, show -(z₁ * (w : ℂ)) * Complex.I = 2 * ν * w + 2 * t * w * Complex.I by
        simp only [z₁]; ring_nf; rw [Complex.I_sq]; ring,
      show -(z₂ * (w : ℂ)) * Complex.I = -(2 * ν * w) + 2 * t * w * Complex.I by
        simp only [z₂]; ring_nf; rw [Complex.I_sq]; ring,
      Complex.exp_add, Complex.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_sub ((integrable_cexp_div_cosh hz₁).const_mul _) ((integrable_cexp_div_cosh hz₂).const_mul _),
    integral_const_mul, integral_const_mul, HTGeometry.integral_cexp_div_cosh hz₁,
    HTGeometry.integral_cexp_div_cosh hz₂]
  have e₁ : (Real.pi : ℂ) * z₁ / 2 = (Real.pi * ν) * Complex.I - Real.pi * t := by simp only [z₁]; ring
  have e₂ : (Real.pi : ℂ) * z₂ / 2 = -((Real.pi * ν) * Complex.I + Real.pi * t) := by simp only [z₂]; ring
  rw [e₁, e₂, Complex.cosh_neg, Complex.cosh_sub, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  set c := Complex.cos (Real.pi * ν) * Complex.cosh (Real.pi * t)
  set d := Complex.sin (Real.pi * ν) * Complex.sinh (Real.pi * t)
  have hcd : c ^ 2 + d ^ 2 = (Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t)) / 2 := by
    simp only [c, d]
    rw [show (2 : ℂ) * Real.pi * ν = 2 * (Real.pi * ν) by ring, Complex.cos_two_mul,
      show (2 : ℂ) * Real.pi * t = 2 * (Real.pi * t) by ring, Complex.cosh_two_mul]
    have hc := Complex.cos_sq_add_sin_sq ((Real.pi : ℂ) * ν)
    have hh := Complex.cosh_sq_sub_sinh_sq ((Real.pi : ℂ) * t)
    linear_combination (Complex.cosh ((Real.pi : ℂ) * t) ^ 2 - 1) * hc +
      (1 / 2 - Complex.sin ((Real.pi : ℂ) * ν) ^ 2) * hh
  have hne₁ : Complex.cosh ((Real.pi * ν) * Complex.I - Real.pi * t) ≠ 0 := by
    refine cosh_ne_zero_of_abs_im_lt ?_
    simp
    rw [abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hne₂ : Complex.cosh ((Real.pi * ν) * Complex.I + Real.pi * t) ≠ 0 := by
    refine cosh_ne_zero_of_abs_im_lt ?_
    simp
    rw [abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I] at hne₁
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I] at hne₂
  have hden : Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t) ≠ 0 := by
    intro h0
    have h1 : c ^ 2 + d ^ 2 = 0 := by rw [hcd, h0, zero_div]
    have h2 : (c - Complex.sin (Real.pi * ν) * Complex.I * Complex.sinh (Real.pi * t)) *
        (c + Complex.sin (Real.pi * ν) * Complex.I * Complex.sinh (Real.pi * t)) = 0 := by
      have : (c - d * Complex.I) * (c + d * Complex.I) = c ^ 2 + d ^ 2 := by
        ring_nf; rw [Complex.I_sq]; ring
      rw [← h1, ← this]; simp only [d]; ring
    rcases mul_eq_zero.1 h2 with h | h
    · exact hne₁ (by simp only [c] at h ⊢; linear_combination h)
    · exact hne₂ (by simp only [c] at h ⊢; linear_combination h)
  have hD : Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t) = 2 * (c ^ 2 + d ^ 2) := by
    rw [hcd]; ring
  have hcd0 : c ^ 2 + d ^ 2 ≠ 0 := by
    intro h0; apply hden; rw [hD, h0, mul_zero]
  rw [hD]
  have hm : (c - d * Complex.I) * (c + d * Complex.I) = c ^ 2 + d ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  have hne₁' : c - d * Complex.I ≠ 0 := fun h => hcd0 (by rw [← hm, h, zero_mul])
  have hne₂' : c + d * Complex.I ≠ 0 := fun h => hcd0 (by rw [← hm, h, mul_zero])
  rw [show Complex.cos (Real.pi * ν) * Complex.cosh (Real.pi * t) -
      Complex.sin (Real.pi * ν) * Complex.I * Complex.sinh (Real.pi * t) = c - d * Complex.I by
        simp only [c, d]; ring,
    show Complex.cos (Real.pi * ν) * Complex.cosh (Real.pi * t) +
      Complex.sin (Real.pi * ν) * Complex.I * Complex.sinh (Real.pi * t) = c + d * Complex.I by
        simp only [c, d]; ring]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * Complex.sin (Real.pi * ν) * Complex.sinh (Real.pi * t) =
    2 * Real.pi * Complex.I * d by simp only [d]; ring, ← hm]
  field_simp
  ring

/-- The kernel `k_ν(w) = (π/sin πν) sinh(2νw)/cosh w`, `k_0(w) = 2w/cosh w`. -/
def sechKernel (ν : ℂ) (w : ℝ) : ℂ :=
  if ν = 0 then 2 * w / (Real.cosh w : ℂ)
  else (Real.pi : ℂ) / Complex.sin (Real.pi * ν) * Complex.sinh (2 * ν * w) / (Real.cosh w : ℂ)


theorem integral_cexp_div_cosh_real (t : ℝ) :
    ∫ w : ℝ, Complex.exp (2 * t * w * Complex.I) / (Real.cosh w : ℂ) =
      ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  have h := HTGeometry.integral_cexp_div_cosh (z := -2 * (t : ℂ)) (by simp)
  have e : (fun w : ℝ => Complex.exp (-((-2 * (t : ℂ)) * (w : ℂ)) * Complex.I) / (Real.cosh w : ℂ)) =
      fun w : ℝ => Complex.exp (2 * t * w * Complex.I) / (Real.cosh w : ℂ) := by
    funext w; congr 2; ring
  rw [e] at h
  rw [h, show (Real.pi : ℂ) * (-2 * (t : ℂ)) / 2 = -((Real.pi * t : ℝ) : ℂ) by push_cast; ring,
    Complex.cosh_neg, ← Complex.ofReal_cosh]
  push_cast; ring

theorem integrable_abs_mul_div_cosh : Integrable fun w : ℝ => |w| / Real.cosh w := by
  refine ((integrable_exp_neg_mul_abs' (c := 1 / 2) (by norm_num)).const_mul 4).mono'
    (Continuous.aestronglyMeasurable (Continuous.div (by fun_prop) (by fun_prop)
      fun w => (Real.cosh_pos w).ne')) (Eventually.of_forall fun w => ?_)
  have hc := Real.cosh_pos w
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hc]
  have h1 : Real.exp |w| ≤ 2 * Real.cosh w := by
    rw [Real.cosh_eq]
    rcases le_total 0 w with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-w)]
    · rw [abs_of_nonpos h]; linarith [Real.exp_pos w]
  have h2 : |w| ≤ 2 * Real.exp (|w| / 2) := by
    have := Real.add_one_le_exp (|w| / 2)
    nlinarith [abs_nonneg w, Real.exp_pos (|w| / 2)]
  calc |w| ≤ 2 * Real.exp (|w| / 2) := h2
    _ = 2 * Real.exp (|w| / 2) * (Real.exp (-(1 / 2 * |w|)) * Real.exp |w|) * Real.exp (-(|w| / 2)) := by
        rw [show Real.exp (-(1 / 2 * |w|)) * Real.exp |w| = Real.exp (|w| / 2) by
          rw [← Real.exp_add]; ring_nf]
        rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ ≤ 2 * Real.exp (|w| / 2) * (Real.exp (-(1 / 2 * |w|)) * (2 * Real.cosh w)) *
        Real.exp (-(|w| / 2)) := by gcongr
    _ = 4 * Real.exp (-(1 / 2 * |w|)) * Real.cosh w * (Real.exp (|w| / 2) * Real.exp (-(|w| / 2))) := by
        ring
    _ = 4 * Real.exp (-(1 / 2 * |w|)) * Real.cosh w := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- **`∫ (2w/cosh w) e^{2itw} dw = 2i Φ̃_0(t)`**, by differentiating `∫ e^{2itw}/cosh w = π/cosh πt`. -/
theorem integral_two_mul_div_cosh_mul_cexp (t : ℝ) :
    ∫ w : ℝ, 2 * (w : ℂ) / (Real.cosh w : ℂ) * Complex.exp (2 * t * w * Complex.I) =
      2 * Complex.I * sechProfile 0 t := by
  set F : ℝ → ℝ → ℂ := fun t w => Complex.exp (2 * t * w * Complex.I) / (Real.cosh w : ℂ)
  set F' : ℝ → ℝ → ℂ := fun t w => (2 * w * Complex.I) * Complex.exp (2 * t * w * Complex.I) /
    (Real.cosh w : ℂ)
  have hcont : ∀ s : ℝ, Continuous (F s) := fun s =>
    Continuous.div (by fun_prop) (by fun_prop) fun w => by exact_mod_cast (Real.cosh_pos w).ne'
  have hnormF : ∀ s w, ‖F s w‖ = 1 / Real.cosh w := fun s w => by
    simp only [F]
    rw [norm_div, show 2 * (s : ℂ) * w * Complex.I = ((2 * s * w : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos w).le]
  have hint1 : Integrable fun w : ℝ => 1 / Real.cosh w := by
    have := integrable_cexp_div_cosh (z := 0) (by simp)
    refine this.norm.congr (Eventually.of_forall fun w => ?_)
    dsimp only
    rw [norm_cexp_mul_I_div_cosh]; simp
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (x₀ := t)
    (bound := fun w => 2 * (|w| / Real.cosh w)) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    (hint1.mono' (hcont t).aestronglyMeasurable (Eventually.of_forall fun w => (hnormF t w).le))
    (F' := F') (Continuous.aestronglyMeasurable (Continuous.div (by fun_prop) (by fun_prop)
      fun w => by exact_mod_cast (Real.cosh_pos w).ne'))
    (Eventually.of_forall fun w s _ => by
      simp only [F']
      rw [norm_div, norm_mul, show 2 * (s : ℂ) * w * Complex.I = ((2 * s * w : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_real, Complex.norm_ofNat, mul_one, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_of_nonneg (Real.cosh_pos w).le]
      ring_nf; exact le_rfl)
    (integrable_abs_mul_div_cosh.const_mul 2)
    (Eventually.of_forall fun w s _ => by
      simp only [F, F']
      have h1 : HasDerivAt (fun s : ℝ => (2 * (s : ℂ) * w * Complex.I)) (2 * w * Complex.I) s := by
        have := ((hasDerivAt_id s).ofReal_comp).const_mul (2 * (w : ℂ) * Complex.I)
        simpa [mul_comm, mul_assoc, mul_left_comm] using this
      exact (h1.cexp.div_const _).congr_deriv (by ring))
  have hR : HasDerivAt (fun s : ℝ => ((Real.pi / Real.cosh (Real.pi * s) : ℝ) : ℂ))
      (((-(Real.pi * (Real.pi * Real.sinh (Real.pi * t))) / Real.cosh (Real.pi * t) ^ 2 : ℝ) : ℂ)) t := by
    have h1 : HasDerivAt (fun s : ℝ => Real.cosh (Real.pi * s)) (Real.sinh (Real.pi * t) * Real.pi) t :=
      (Real.hasDerivAt_cosh _).comp t ((hasDerivAt_id t).const_mul Real.pi |>.congr_deriv (by ring))
    have h2 := (hasDerivAt_const t Real.pi).div h1 (Real.cosh_pos _).ne'
    refine (h2.ofReal_comp).congr_deriv ?_
    push_cast; ring
  have hfun : (fun s : ℝ => ∫ w : ℝ, F s w) = fun s => ((Real.pi / Real.cosh (Real.pi * s) : ℝ) : ℂ) :=
    funext fun s => integral_cexp_div_cosh_real s
  rw [hfun] at hd
  have huniq := hd.2.unique hR
  have e : (fun w : ℝ => 2 * (w : ℂ) / (Real.cosh w : ℂ) * Complex.exp (2 * t * w * Complex.I)) =
      fun w => (-Complex.I) * F' t w := by
    funext w; simp only [F']; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e, integral_const_mul, huniq, sechProfile]
  have hc := Real.cosh_pos (Real.pi * t)
  have hc' : Complex.cosh ((Real.pi : ℂ) * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]; exact_mod_cast hc.ne'
  rw [show (2 : ℂ) * Real.pi * (0 : ℂ) = 0 by ring, Complex.cos_zero,
    show (2 : ℂ) * Real.pi * t = 2 * (Real.pi * t) by ring, Complex.cosh_two_mul]
  have hh := Complex.cosh_sq_sub_sinh_sq ((Real.pi : ℂ) * t)
  have hden : (1 : ℂ) + (Complex.cosh (Real.pi * t) ^ 2 + Complex.sinh (Real.pi * t) ^ 2) =
      2 * Complex.cosh (Real.pi * t) ^ 2 := by linear_combination -hh
  rw [hden]
  push_cast
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh] at *
  field_simp


theorem sin_pi_mul_ne_zero {ν : ℂ} (hν : |ν.re| < 1 / 2) (h0 : ν ≠ 0) :
    Complex.sin (Real.pi * ν) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hνk : ν = k := by
    have := hk; field_simp at this; linear_combination this
  have hre : ν.re = k := by rw [hνk]; simp
  rw [hre] at hν
  have hk0 : k = 0 := by
    rcases abs_lt.1 hν with ⟨h1, h2⟩
    have : (k : ℝ) < 1 := by linarith
    have : (-1 : ℝ) < k := by linarith
    have : k < 1 := by exact_mod_cast ‹(k : ℝ) < 1›
    have : -1 < k := by exact_mod_cast ‹(-1 : ℝ) < k›
    omega
  exact h0 (by rw [hνk, hk0]; simp)

/-- **`∫ k_ν(w) e^{2itw} dw = 2i Φ̃_ν(t)`** for `|Re ν| < ½`. -/
theorem integral_sechKernel_mul_cexp {ν : ℂ} (hν : |ν.re| < 1 / 2) (t : ℝ) :
    ∫ w : ℝ, sechKernel ν w * Complex.exp (2 * t * w * Complex.I) = 2 * Complex.I * sechProfile ν t := by
  by_cases h0 : ν = 0
  · subst h0
    simp only [sechKernel, if_true]
    exact integral_two_mul_div_cosh_mul_cexp t
  · simp only [sechKernel, if_neg h0]
    have hs := sin_pi_mul_ne_zero hν h0
    have e : (fun w : ℝ => (Real.pi : ℂ) / Complex.sin (Real.pi * ν) * Complex.sinh (2 * ν * w) /
        (Real.cosh w : ℂ) * Complex.exp (2 * t * w * Complex.I)) =
        fun w : ℝ => ((Real.pi : ℂ) / Complex.sin (Real.pi * ν)) *
          (Complex.sinh (2 * ν * w) / (Real.cosh w : ℂ) * Complex.exp (2 * t * w * Complex.I)) := by
      funext w; ring
    rw [e, integral_const_mul, integral_sinh_div_cosh_mul_cexp hν t, sechProfile]
    field_simp

/-! ## Size of the kernel and of the profile -/

theorem norm_sinh_le_cosh_re (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  rw [Complex.sinh, Real.cosh_eq, norm_div, Complex.norm_ofNat]
  gcongr
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

theorem continuous_sechKernel (ν : ℂ) : Continuous (sechKernel ν) := by
  unfold sechKernel
  split_ifs
  · exact Continuous.div (by fun_prop) (by fun_prop) fun w => by exact_mod_cast (Real.cosh_pos w).ne'
  · exact Continuous.div (by fun_prop) (by fun_prop) fun w => by exact_mod_cast (Real.cosh_pos w).ne'

theorem norm_sechKernel_le {ν : ℂ} (h0 : ν ≠ 0) (w : ℝ) :
    ‖sechKernel ν w‖ ≤ ‖(Real.pi : ℂ) / Complex.sin (Real.pi * ν)‖ *
      (2 * Real.exp (-((1 - |2 * ν.re|) * |w|))) := by
  simp only [sechKernel, if_neg h0]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos w).le, mul_div_assoc]
  gcongr
  refine (div_le_div_of_nonneg_right (norm_sinh_le_cosh_re _) (Real.cosh_pos w).le).trans ?_
  have hre : (2 * ν * (w : ℂ)).re = 2 * ν.re * w := by simp
  rw [hre]
  have h1 : Real.cosh (2 * ν.re * w) ≤ Real.exp (|2 * ν.re| * |w|) := by
    rw [← abs_mul]
    rw [Real.cosh_eq]
    rcases le_total 0 (2 * ν.re * w) with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_le_exp.2 (show -(2 * ν.re * w) ≤ 2 * ν.re * w by linarith)]
    · rw [abs_of_nonpos h]; linarith [Real.exp_le_exp.2 (show 2 * ν.re * w ≤ -(2 * ν.re * w) by linarith)]
  have h2 := exp_mul_div_cosh_le (|2 * ν.re|) w
  rw [abs_abs] at h2
  calc Real.cosh (2 * ν.re * w) / Real.cosh w ≤ Real.exp (|2 * ν.re| * |w|) / Real.cosh w := by
        gcongr
    _ ≤ Real.exp (|2 * ν.re| * w) / Real.cosh w * Real.exp (|2 * ν.re| * (|w| - w)) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]; ring_nf; exact le_rfl
    _ ≤ _ := by
        rcases le_total 0 w with hw | hw
        · rw [abs_of_nonneg hw, sub_self, mul_zero, Real.exp_zero, mul_one]
          have := exp_mul_div_cosh_le (|2 * ν.re|) w
          rwa [abs_abs, abs_of_nonneg hw] at this
        · have := exp_mul_div_cosh_le (-|2 * ν.re|) w
          rw [abs_neg, abs_abs] at this
          calc Real.exp (|2 * ν.re| * w) / Real.cosh w * Real.exp (|2 * ν.re| * (|w| - w))
              = Real.exp (-|2 * ν.re| * w) / Real.cosh w := by
                rw [abs_of_nonpos hw, div_mul_eq_mul_div, ← Real.exp_add]; ring_nf
            _ ≤ _ := this

theorem integrable_sechKernel {ν : ℂ} (hν : |ν.re| < 1 / 2) : Integrable (sechKernel ν) := by
  by_cases h0 : ν = 0
  · subst h0
    refine (integrable_abs_mul_div_cosh.const_mul 2).mono' (continuous_sechKernel 0).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    simp only [sechKernel, if_true]
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.cosh_pos w).le]
    ring_nf; exact le_rfl
  · have hc : 0 < 1 - |2 * ν.re| := by rw [abs_mul, abs_two]; linarith
    exact (((integrable_exp_neg_mul_abs' hc).const_mul 2).const_mul
      ‖(Real.pi : ℂ) / Complex.sin (Real.pi * ν)‖).mono'
      (continuous_sechKernel ν).aestronglyMeasurable
      (Eventually.of_forall fun w => norm_sechKernel_le h0 w)

theorem abs_cos_mul_cosh_le_norm_cos (x y : ℝ) :
    |Real.cos x| * Real.cosh y ≤ ‖Complex.cos ((x : ℂ) + y * Complex.I)‖ := by
  have hre : (Complex.cos ((x : ℂ) + y * Complex.I)).re = Real.cos x * Real.cosh y := by
    simp only [Complex.cos_add_mul_I, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  calc |Real.cos x| * Real.cosh y = |Real.cos x * Real.cosh y| := by
        rw [abs_mul, abs_of_pos (Real.cosh_pos y)]
    _ = |(Complex.cos ((x : ℂ) + y * Complex.I)).re| := by rw [hre]
    _ ≤ _ := Complex.abs_re_le_norm _

theorem cosh_sq_le_cosh_add_mul_cosh_sub (a b : ℝ) : Real.cosh a ^ 2 ≤ Real.cosh (a + b) * Real.cosh (a - b) := by
  rw [Real.cosh_add, Real.cosh_sub]
  have := Real.cosh_sq_sub_sinh_sq b
  nlinarith [sq_nonneg (Real.sinh a), sq_nonneg (Real.sinh b), Real.cosh_sq_sub_sinh_sq a]

theorem cos_two_pi_add_cosh_two_pi_eq (ν : ℂ) (t : ℝ) :
    Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t) =
      2 * (Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν)) *
        Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν))) := by
  rw [show (Real.pi : ℂ) * ((t : ℂ) * Complex.I + ν) = (Real.pi * t) * Complex.I + Real.pi * ν by ring,
    show (Real.pi : ℂ) * ((t : ℂ) * Complex.I - ν) = (Real.pi * t) * Complex.I - Real.pi * ν by ring,
    Complex.cos_add, Complex.cos_sub, Complex.cos_mul_I, Complex.sin_mul_I,
    show (2 : ℂ) * Real.pi * ν = 2 * (Real.pi * ν) by ring, Complex.cos_two_mul,
    show (2 : ℂ) * Real.pi * t = 2 * (Real.pi * t) by ring, Complex.cosh_two_mul]
  have hc := Complex.cos_sq_add_sin_sq ((Real.pi : ℂ) * ν)
  have hh := Complex.cosh_sq_sub_sinh_sq ((Real.pi : ℂ) * t)
  linear_combination (-2) * ((Complex.cosh ((Real.pi : ℂ) * t) ^ 2 - 1) * hc +
    (1 / 2 - Complex.sin ((Real.pi : ℂ) * ν) ^ 2) * hh +
    (-(Complex.sinh ((Real.pi : ℂ) * t)) ^ 2 * Complex.sin ((Real.pi : ℂ) * ν) ^ 2) * Complex.I_sq)

/-- **Decay of the profile**: `|Φ̃_ν(t)| ≤ π² e^{−π|t|} / cos²(π Re ν)`. -/
theorem norm_sechProfile_le {ν : ℂ} (hν : |ν.re| < 1 / 2) (t : ℝ) :
    ‖sechProfile ν t‖ ≤ Real.pi ^ 2 / Real.cos (Real.pi * ν.re) ^ 2 * Real.exp (-(Real.pi * |t|)) := by
  have hcos : 0 < Real.cos (Real.pi * ν.re) := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;>
      nlinarith [abs_lt.1 hν, Real.pi_pos]
  have hA : |Real.cos (Real.pi * ν.re)| * Real.cosh (Real.pi * (t + ν.im)) ≤
      ‖Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν))‖ := by
    have eA : (Real.pi : ℂ) * ((t : ℂ) * Complex.I + ν) =
        ((Real.pi * ν.re : ℝ) : ℂ) + ((Real.pi * (t + ν.im) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [eA]; exact abs_cos_mul_cosh_le_norm_cos _ _
  have hB : |Real.cos (Real.pi * ν.re)| * Real.cosh (Real.pi * (t - ν.im)) ≤
      ‖Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν))‖ := by
    have eB : (Real.pi : ℂ) * ((t : ℂ) * Complex.I - ν) =
        ((-(Real.pi * ν.re) : ℝ) : ℂ) + ((Real.pi * (t - ν.im) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have := abs_cos_mul_cosh_le_norm_cos (-(Real.pi * ν.re)) (Real.pi * (t - ν.im))
    rw [Real.cos_neg] at this
    rw [eB]; exact this
  have hC := cosh_sq_le_cosh_add_mul_cosh_sub (Real.pi * t) (Real.pi * ν.im)
  rw [show Real.pi * t + Real.pi * ν.im = Real.pi * (t + ν.im) by ring,
    show Real.pi * t - Real.pi * ν.im = Real.pi * (t - ν.im) by ring] at hC
  have hD : 2 * Real.cos (Real.pi * ν.re) ^ 2 * Real.cosh (Real.pi * t) ^ 2 ≤
      ‖Complex.cos (2 * Real.pi * ν) + Complex.cosh (2 * Real.pi * t)‖ := by
    rw [cos_two_pi_add_cosh_two_pi_eq, norm_mul, Complex.norm_ofNat, norm_mul]
    rw [abs_of_pos hcos] at hA hB
    have h0 : 0 ≤ Real.cos (Real.pi * ν.re) := hcos.le
    calc 2 * Real.cos (Real.pi * ν.re) ^ 2 * Real.cosh (Real.pi * t) ^ 2
        ≤ 2 * Real.cos (Real.pi * ν.re) ^ 2 * (Real.cosh (Real.pi * (t + ν.im)) *
          Real.cosh (Real.pi * (t - ν.im))) := by gcongr
      _ = 2 * ((Real.cos (Real.pi * ν.re) * Real.cosh (Real.pi * (t + ν.im))) *
          (Real.cos (Real.pi * ν.re) * Real.cosh (Real.pi * (t - ν.im)))) := by ring
      _ ≤ _ := by gcongr
  have hch := Real.cosh_pos (Real.pi * t)
  have hD0 : 0 < 2 * Real.cos (Real.pi * ν.re) ^ 2 * Real.cosh (Real.pi * t) ^ 2 := by positivity
  rw [sechProfile, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    div_le_iff₀ (hD0.trans_le hD)]
  have hsinh : ‖Complex.sinh (Real.pi * t)‖ ≤ Real.cosh (Real.pi * t) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq (Real.pi * t), Real.sinh_sq (Real.pi * t),
      sq_nonneg (Real.cosh (Real.pi * t) + Real.sinh (Real.pi * t)),
      sq_nonneg (Real.cosh (Real.pi * t) - Real.sinh (Real.pi * t))]
  have hexp : 1 ≤ 2 * Real.cosh (Real.pi * t) * Real.exp (-(Real.pi * |t|)) := by
    have : Real.exp |Real.pi * t| ≤ 2 * Real.cosh (Real.pi * t) := by
      rw [Real.cosh_eq]
      rcases le_total 0 (Real.pi * t) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(Real.pi * t))]
      · rw [abs_of_nonpos h]; linarith [Real.exp_pos (Real.pi * t)]
    rw [abs_mul, abs_of_pos Real.pi_pos] at this
    have h2 : Real.exp (Real.pi * |t|) * Real.exp (-(Real.pi * |t|)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(Real.pi * |t|))]
  calc Real.pi ^ 2 * ‖Complex.sinh (Real.pi * t)‖
      ≤ Real.pi ^ 2 * Real.cosh (Real.pi * t) := by gcongr
    _ ≤ Real.pi ^ 2 * Real.cosh (Real.pi * t) * (2 * Real.cosh (Real.pi * t) * Real.exp (-(Real.pi * |t|))) :=
        le_mul_of_one_le_right (by positivity) hexp
    _ = Real.pi ^ 2 / Real.cos (Real.pi * ν.re) ^ 2 * Real.exp (-(Real.pi * |t|)) *
          (2 * Real.cos (Real.pi * ν.re) ^ 2 * Real.cosh (Real.pi * t) ^ 2) := by
        field_simp
    _ ≤ _ := by gcongr

theorem continuous_sechProfile {ν : ℂ} (hν : |ν.re| < 1 / 2) : Continuous (sechProfile ν) := by
  unfold sechProfile
  refine Continuous.div (by fun_prop) (by fun_prop) fun t h => ?_
  have hD := cos_two_pi_add_cosh_two_pi_eq ν t
  rw [h] at hD
  have hA : Complex.cos (Real.pi * ((t : ℂ) * Complex.I + ν)) ≠ 0 :=
    cos_pi_mul_ne_zero (by simpa using hν)
  have hB : Complex.cos (Real.pi * ((t : ℂ) * Complex.I - ν)) ≠ 0 :=
    cos_pi_mul_ne_zero (by simpa using hν)
  exact mul_ne_zero two_ne_zero (mul_ne_zero hA hB) hD.symm

theorem integrable_sechProfile {ν : ℂ} (hν : |ν.re| < 1 / 2) : Integrable (sechProfile ν) :=
  ((integrable_exp_neg_mul_abs' Real.pi_pos).const_mul _).mono'
    (continuous_sechProfile hν).aestronglyMeasurable (Eventually.of_forall (norm_sechProfile_le hν))


/-! ## The spectral weight as a `sech`-kernel integral -/

theorem ofReal_norm_whittMellin_sq {ν : ℂ} (hν : conj ν = ν ∨ conj ν = -ν) (t : ℝ) :
    ((‖whittMellin (((1 : ℝ) : ℂ) + t * Complex.I) ν‖ ^ 2 : ℝ) : ℂ) =
      whittMellin (1 + t * Complex.I) ν * whittMellin (1 - t * Complex.I) ν := by
  have hc : conj (whittMellin (((1 : ℝ) : ℂ) + t * Complex.I) ν) = whittMellin (1 - t * Complex.I) ν := by
    rw [conj_whittMellin]
    have hb : conj (((1 : ℝ) : ℂ) + t * Complex.I) = 1 - (t : ℂ) * Complex.I := by
      simp [map_add, Complex.conj_ofReal]; ring
    rw [hb]
    rcases hν with h | h
    · rw [h]
    · rw [h, whittMellin_neg]
  rw [Complex.ofReal_pow, ← Complex.mul_conj', hc]
  push_cast
  ring_nf

theorem h_eq_fourier (P : OddDecayProfile) (t : ℝ) :
    P.h t = 2 * (t : ℂ) * Complex.I / Real.pi * 𝓕 P.G (t / Real.pi) := by
  have hf := Real.fourier_iteratedDeriv (f := P.G) (N := ((1 : ℕ) : ℕ∞)) (n := 1)
    (by exact_mod_cast P.contDiff 1) (fun n _ => P.integrable_iteratedDeriv n) le_rfl
  rw [iteratedDeriv_one] at hf
  rw [OddDecayProfile.h, hf]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [pow_one, smul_eq_mul]
  push_cast
  field_simp

/-- **The same-sign spectral weight of an odd profile**:
`∫ h(t) |W(1+it, ν)|² dt = ∫ G(w) k_ν(w) dw` for `ν̄ = ±ν`, `|Re ν| < ½`. -/
theorem specWeight_eq_integral_sechKernel (P : OddDecayProfile) {ν : ℂ}
    (hν : conj ν = ν ∨ conj ν = -ν) (hνre : |ν.re| < 1 / 2) :
    specWeight P.toWeight 1 ν = ∫ w : ℝ, P.G w * sechKernel ν w := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set K : ℝ → ℂ := fun t => 2 * Complex.I * sechProfile ν t with hK
  have hKcont : Continuous K := continuous_const.mul (continuous_sechProfile hνre)
  have hKint : Integrable K := (integrable_sechProfile hνre).const_mul _
  -- the integrand
  have hpt : ∀ t : ℝ, P.toWeight.h t * ((‖whittMellin (((1 : ℝ) : ℂ) + t * Complex.I) ν‖ ^ 2 : ℝ) : ℂ) =
      (Real.pi : ℂ)⁻¹ * (𝓕 P.G (t / Real.pi) * K t) := fun t => by
    show P.h t * _ = _
    rw [ofReal_norm_whittMellin_sq hν, h_eq_fourier]
    rcases eq_or_ne t 0 with rfl | ht
    · simp [K, sechProfile]
    · have hW := mul_whittMellin_one_add_eq hνre ht
      simp only [K]
      rw [← hW]
      field_simp
  rw [specWeight]
  simp_rw [hpt]
  rw [integral_const_mul]
  -- `𝓕G(t/π) = ∫ e^{−2itv} G(v) dv` and Fubini
  have hF : ∀ t : ℝ, 𝓕 P.G (t / Real.pi) * K t =
      ∫ v : ℝ, P.G v * (K t * Complex.exp (-(2 * t * v) * Complex.I)) := fun t => by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_mul_const]
    congr 1; funext v
    rw [smul_eq_mul, show (((-2 * Real.pi * v * (t / Real.pi)) : ℝ) : ℂ) * Complex.I =
      -(2 * t * v) * Complex.I by push_cast; field_simp]
    ring
  simp_rw [hF]
  have hGc : Continuous P.G := by
    have := P.continuous_iteratedDeriv 0; rwa [iteratedDeriv_zero] at this
  have hGi : Integrable P.G := by
    have := P.integrable_iteratedDeriv 0; rwa [iteratedDeriv_zero] at this
  have hprod : Integrable (Function.uncurry fun (t v : ℝ) =>
      P.G v * (K t * Complex.exp (-(2 * t * v) * Complex.I))) ((volume : Measure ℝ).prod volume) := by
    refine (hKint.norm.mul_prod hGi.norm).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact Continuous.aestronglyMeasurable ((hGc.comp continuous_snd).mul
        ((hKcont.comp continuous_fst).mul (by fun_prop)))
    · simp only [Function.uncurry]
      rw [norm_mul, norm_mul, show -(2 * (z.1 : ℂ) * z.2) * Complex.I =
        ((-(2 * z.1 * z.2)) : ℝ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one,
        mul_comm]
  rw [integral_integral_swap hprod]
  -- Fourier inversion for the kernel
  have hkc := continuous_sechKernel ν
  have hki := integrable_sechKernel hνre
  have hFk : ∀ ξ : ℝ, 𝓕 (sechKernel ν) ξ = K (-(Real.pi * ξ)) := fun ξ => by
    simp only [K]
    rw [← integral_sechKernel_mul_cexp hνre, Real.fourier_real_eq_integral_exp_smul]
    congr 1; funext w
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast; ring
  have hFki : Integrable (𝓕 (sechKernel ν)) := by
    refine (hKint.comp_mul_left' (show -Real.pi ≠ 0 by simp [Real.pi_ne_zero])).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only [hFk]; ring_nf
  have hinv := congrFun (hkc.fourierInv_fourier_eq hki hFki)
  have hin : ∀ v : ℝ, ∫ t : ℝ, K t * Complex.exp (-(2 * t * v) * Complex.I) =
      Real.pi * sechKernel ν v := fun v => by
    have hsub := MeasureTheory.Measure.integral_comp_mul_left
      (fun t : ℝ => K t * Complex.exp (-(2 * t * v) * Complex.I)) (-Real.pi)
    rw [abs_inv, abs_neg, abs_of_pos Real.pi_pos, Complex.real_smul] at hsub
    have e : (fun ξ : ℝ => K (-Real.pi * ξ) * Complex.exp (-(2 * ((-Real.pi * ξ : ℝ) : ℂ) * v) * Complex.I)) =
        fun ξ => Complex.exp (((-2 * Real.pi * ξ * -v : ℝ) : ℂ) * Complex.I) • 𝓕 (sechKernel ν) ξ := by
      funext ξ
      rw [hFk, smul_eq_mul, mul_comm, show -(Real.pi * ξ) = -Real.pi * ξ by ring]
      congr 2
      push_cast; ring
    rw [e] at hsub
    have h2 := hinv v
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h2
    rw [h2] at hsub
    rw [hsub]
    push_cast
    field_simp
    congr 1; funext t; ring_nf
  simp_rw [integral_const_mul, hin]
  rw [← integral_const_mul]
  congr 1; funext w
  field_simp


/-! ## Bounds for the kernel and for the spectral weights -/

theorem abs_sinh_le_abs_mul_cosh (x : ℝ) : |Real.sinh x| ≤ |x| * Real.cosh x := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.sinh y ≤ y * Real.cosh y := fun y hy => by
    rcases hy.eq_or_lt with rfl | hy
    · simp
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hy
      Real.continuous_sinh.continuousOn (fun x _ => Real.hasDerivAt_sinh x)
    rw [Real.sinh_zero, sub_zero, sub_zero] at hcd
    have hcy : Real.cosh c ≤ Real.cosh y := Real.cosh_le_cosh.2 (by
      rw [abs_of_pos hc.1, abs_of_pos (hc.1.trans hc.2)]; exact hc.2.le)
    rw [eq_div_iff hy.ne'] at hcd
    nlinarith
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.2 h)]; exact key x h
  · have := key (-x) (by linarith)
    rw [Real.sinh_neg, Real.cosh_neg] at this
    rw [abs_of_nonpos h, abs_of_nonpos (Real.sinh_nonpos_iff.2 h)]; linarith

theorem sechKernel_ofReal_pos {ν : ℝ} (hν : ν ≠ 0) (w : ℝ) :
    sechKernel ν w = (((Real.pi / Real.sin (Real.pi * ν) * Real.sinh (2 * ν * w) / Real.cosh w) : ℝ) : ℂ) := by
  have h0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  simp only [sechKernel, if_neg h0]
  push_cast; ring

/-- **`|k_ν(w)| ≤ π |w| cosh(2νw)/cosh w`** for real `0 ≤ ν < ½`. -/
theorem norm_sechKernel_real_le {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν < 1 / 2) (w : ℝ) :
    ‖sechKernel ν w‖ ≤ Real.pi * |w| * Real.cosh (2 * ν * w) / Real.cosh w := by
  have hc := Real.cosh_pos w
  rcases h0.eq_or_lt with rfl | hν
  · simp only [Complex.ofReal_zero, sechKernel, if_true]
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg hc.le, mul_zero, zero_mul, Real.cosh_zero, mul_one]
    gcongr
    linarith [Real.pi_gt_three]
  · rw [sechKernel_ofReal_pos hν.ne', Complex.norm_real, Real.norm_eq_abs]
    have hs : 2 * ν ≤ Real.sin (Real.pi * ν) := by
      have := Real.mul_le_sin (x := Real.pi * ν) (by positivity) (by nlinarith [Real.pi_pos])
      rw [show 2 / Real.pi * (Real.pi * ν) = 2 * ν by field_simp] at this
      exact this
    have hs0 : 0 < Real.sin (Real.pi * ν) := by linarith
    rw [abs_div, abs_mul, abs_div, abs_of_pos Real.pi_pos, abs_of_pos hs0, abs_of_pos hc]
    have h2 := abs_sinh_le_abs_mul_cosh (2 * ν * w)
    rw [abs_mul, abs_mul, abs_two, abs_of_pos hν] at h2
    rw [div_le_div_iff_of_pos_right hc, div_mul_eq_mul_div, div_le_iff₀ hs0]
    calc Real.pi * |Real.sinh (2 * ν * w)| ≤ Real.pi * (2 * ν * |w| * Real.cosh (2 * ν * w)) := by gcongr
      _ = Real.pi * |w| * Real.cosh (2 * ν * w) * (2 * ν) := by ring
      _ ≤ Real.pi * |w| * Real.cosh (2 * ν * w) * Real.sin (Real.pi * ν) := by gcongr

theorem sechKernel_imag {κ : ℝ} (hκ : κ ≠ 0) (w : ℝ) :
    sechKernel ((κ : ℂ) * Complex.I) w =
      (((Real.pi * Real.sin (2 * κ * w) / (Real.sinh (Real.pi * κ) * Real.cosh w)) : ℝ) : ℂ) := by
  have h0 : (κ : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hκ) Complex.I_ne_zero
  simp only [sechKernel, if_neg h0]
  rw [show (Real.pi : ℂ) * ((κ : ℂ) * Complex.I) = (Real.pi * κ : ℂ) * Complex.I by ring,
    show (2 : ℂ) * ((κ : ℂ) * Complex.I) * w = (2 * κ * w : ℂ) * Complex.I by ring,
    Complex.sin_mul_I, Complex.sinh_mul_I]
  have hs : Complex.sinh ((Real.pi : ℂ) * κ) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast fun h => mul_ne_zero Real.pi_ne_zero hκ (Real.sinh_eq_zero.1 h)
  have hc : (Real.cosh w : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos w).ne'
  push_cast
  field_simp

/-- **`|k_{iκ}(w)| ≤ 2|w|/cosh w`** for every real `κ`. -/
theorem norm_sechKernel_imag_le (κ w : ℝ) :
    ‖sechKernel ((κ : ℂ) * Complex.I) w‖ ≤ 2 * |w| / Real.cosh w := by
  have hc := Real.cosh_pos w
  rcases eq_or_ne κ 0 with rfl | hκ
  · simp only [Complex.ofReal_zero, zero_mul, sechKernel, if_true]
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg hc.le]
  · rw [sechKernel_imag hκ, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos hc]
    have hs : Real.pi * |κ| ≤ |Real.sinh (Real.pi * κ)| := by
      have h := Real.self_le_sinh_iff.2 (by positivity : 0 ≤ Real.pi * |κ|)
      rcases le_total 0 κ with hk | hk
      · rw [abs_of_nonneg hk] at h ⊢
        rw [abs_of_nonneg (Real.sinh_nonneg_iff.2 (by positivity))]; exact h
      · rw [abs_of_nonpos hk] at h ⊢
        rw [abs_of_nonpos (Real.sinh_nonpos_iff.2 (by nlinarith [Real.pi_pos])), ← Real.sinh_neg]
        rw [show -(Real.pi * κ) = Real.pi * -κ by ring]; exact h
    have hs0 : 0 < |Real.sinh (Real.pi * κ)| := lt_of_lt_of_le (by positivity) hs
    have h2 : |Real.sin (2 * κ * w)| ≤ 2 * |κ| * |w| := by
      have := Real.abs_sin_le_abs (x := 2 * κ * w)
      rwa [abs_mul, abs_mul, abs_two] at this
    rw [div_le_div_iff₀ (by positivity) hc]
    calc Real.pi * |Real.sin (2 * κ * w)| * Real.cosh w ≤ Real.pi * (2 * |κ| * |w|) * Real.cosh w := by gcongr
      _ = 2 * |w| * (Real.pi * |κ| * Real.cosh w) := by ring
      _ ≤ 2 * |w| * (|Real.sinh (Real.pi * κ)| * Real.cosh w) := by gcongr

/-- **`|k_{iκ}(w)| ≤ π/(|sinh πκ| cosh w)`** for `κ ≠ 0`. -/
theorem norm_sechKernel_imag_le' {κ : ℝ} (hκ : κ ≠ 0) (w : ℝ) :
    ‖sechKernel ((κ : ℂ) * Complex.I) w‖ ≤ Real.pi / (|Real.sinh (Real.pi * κ)| * Real.cosh w) := by
  have hc := Real.cosh_pos w
  rw [sechKernel_imag hκ, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos hc]
  gcongr
  calc Real.pi * |Real.sin (2 * κ * w)| ≤ Real.pi * 1 := by gcongr; exact Real.abs_sin_le_one _
    _ = Real.pi := mul_one _

theorem cosh_le_exp_abs'' (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_le_exp.2 (show -x ≤ x by linarith)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_le_exp.2 (show x ≤ -x by linarith)]

theorem continuous_G (P : OddDecayProfile) : Continuous P.G := by
  have := P.continuous_iteratedDeriv 0; rwa [iteratedDeriv_zero] at this

theorem integrable_norm_G_mul_abs_cosh (P : OddDecayProfile) {ν : ℝ} (hν : |ν| ≤ 1 / 2) :
    Integrable fun w : ℝ => ‖P.G w‖ * (|w| * Real.cosh (2 * ν * w) / Real.cosh w) := by
  obtain ⟨C, hC, hb⟩ := P.exists_bound 0
  refine ((integrable_abs_mul_div_cosh).const_mul C).mono'
    (Continuous.aestronglyMeasurable ((continuous_G P).norm.mul (Continuous.div (by fun_prop)
      (by fun_prop) fun w => (Real.cosh_pos w).ne'))) (Eventually.of_forall fun w => ?_)
  have hc := Real.cosh_pos w
  have hG := hb w
  rw [iteratedDeriv_zero] at hG
  rw [Real.norm_of_nonneg (by positivity)]
  have hcosh : Real.cosh (2 * ν * w) ≤ Real.exp |w| := (cosh_le_exp_abs'' _).trans
    (Real.exp_le_exp.2 (by rw [abs_mul, abs_mul, abs_two]; nlinarith [abs_nonneg w]))
  have he : Real.exp (-(2 * |w|)) * Real.exp |w| ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.2 (by linarith [abs_nonneg w])
  calc ‖P.G w‖ * (|w| * Real.cosh (2 * ν * w) / Real.cosh w)
      ≤ (C * Real.exp (-(2 * |w|))) * (|w| * Real.exp |w| / Real.cosh w) := by gcongr
    _ = C * (|w| / Real.cosh w) * (Real.exp (-(2 * |w|)) * Real.exp |w|) := by ring
    _ ≤ C * (|w| / Real.cosh w) * 1 := by gcongr
    _ = _ := mul_one _

/-- **The exceptional and the bottom weights**: for real `0 ≤ ν < ½`,
`|∫ h |W(1+it, ν)|²| ≤ π ∫ |G(w)| |w| cosh(2νw)/cosh w dw`. -/
theorem norm_specWeight_real_le (P : OddDecayProfile) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν < 1 / 2) :
    ‖specWeight P.toWeight 1 ν‖ ≤
      Real.pi * ∫ w : ℝ, ‖P.G w‖ * (|w| * Real.cosh (2 * ν * w) / Real.cosh w) := by
  rw [specWeight_eq_integral_sechKernel P (Or.inl (Complex.conj_ofReal ν))
    (by simp; rw [abs_of_nonneg h0]; linarith), ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_norm_G_mul_abs_cosh P
    (by rw [abs_of_nonneg h0]; linarith)).const_mul _) (Eventually.of_forall fun w => ?_)
  rw [norm_mul]
  have := norm_sechKernel_real_le h0 h1 w
  calc ‖P.G w‖ * ‖sechKernel (ν : ℂ) w‖ ≤ ‖P.G w‖ * (Real.pi * |w| * Real.cosh (2 * ν * w) / Real.cosh w) := by
        gcongr
    _ = _ := by ring

/-- **The tempered weights, uniformly**: `|∫ h |W(1+it, iκ)|²| ≤ 2 ∫ |G(w)| |w|/cosh w dw`. -/
theorem norm_specWeight_imag_le (P : OddDecayProfile) (κ : ℝ) :
    ‖specWeight P.toWeight 1 ((κ : ℂ) * Complex.I)‖ ≤
      2 * ∫ w : ℝ, ‖P.G w‖ * (|w| * Real.cosh (2 * 0 * w) / Real.cosh w) := by
  rw [specWeight_eq_integral_sechKernel P (Or.inr (by simp)) (by simp), ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_norm_G_mul_abs_cosh P (by norm_num)).const_mul _)
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul, mul_zero, zero_mul, Real.cosh_zero, mul_one]
  have := norm_sechKernel_imag_le κ w
  calc ‖P.G w‖ * ‖sechKernel ((κ : ℂ) * Complex.I) w‖ ≤ ‖P.G w‖ * (2 * |w| / Real.cosh w) := by gcongr
    _ = _ := by ring

theorem specWeight_imag_eq (P : OddDecayProfile) {κ : ℝ} (hκ : κ ≠ 0) :
    specWeight P.toWeight 1 ((κ : ℂ) * Complex.I) =
      (((Real.pi / Real.sinh (Real.pi * κ)) : ℝ) : ℂ) *
        ∫ w : ℝ, P.G w / (Real.cosh w : ℂ) * (Real.sin (2 * κ * w) : ℂ) := by
  rw [specWeight_eq_integral_sechKernel P (Or.inr (by simp)) (by simp), ← integral_const_mul]
  congr 1; funext w
  rw [sechKernel_imag hκ]
  have hc : (Real.cosh w : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos w).ne'
  have hs : (Real.sinh (Real.pi * κ) : ℂ) ≠ 0 := by
    exact_mod_cast fun h => mul_ne_zero Real.pi_ne_zero hκ (Real.sinh_eq_zero.1 h)
  push_cast
  field_simp

/-- **Decay of the tempered weights**: if `Q = G/cosh` is `C^K` with integrable derivatives, then
`|∫ h |W(1+it, iκ)|²| ≤ (π/|sinh πκ|) ‖Q^{(K)}‖₁ / |2κ|^K`. -/
theorem norm_specWeight_imag_le_of_iteratedDeriv (P : OddDecayProfile) {κ : ℝ} (hκ : κ ≠ 0) (K : ℕ)
    (hQ : ContDiff ℝ K (fun w : ℝ => P.G w / (Real.cosh w : ℂ)))
    (hQi : ∀ n : ℕ, n ≤ K → Integrable (iteratedDeriv n (fun w : ℝ => P.G w / (Real.cosh w : ℂ)))) :
    ‖specWeight P.toWeight 1 ((κ : ℂ) * Complex.I)‖ ≤
      Real.pi / |Real.sinh (Real.pi * κ)| *
        ((∫ w : ℝ, ‖iteratedDeriv K (fun w : ℝ => P.G w / (Real.cosh w : ℂ)) w‖) / |2 * κ| ^ K) := by
  have h2κ : 2 * κ ≠ 0 := mul_ne_zero two_ne_zero hκ
  have hm2κ : -(2 * κ) ≠ 0 := neg_ne_zero.2 h2κ
  have hA := HTGeometry.norm_integral_mul_cexp_le_of_iteratedDeriv K hQ hQi h2κ
  have hB := HTGeometry.norm_integral_mul_cexp_le_of_iteratedDeriv K hQ hQi hm2κ
  rw [abs_neg] at hB
  have hQint : Integrable fun w : ℝ => P.G w / (Real.cosh w : ℂ) := by simpa using hQi 0 (Nat.zero_le _)
  have hsin : ∀ w : ℝ, P.G w / (Real.cosh w : ℂ) * (Real.sin (2 * κ * w) : ℂ) =
      (Complex.I / 2) * (P.G w / (Real.cosh w : ℂ) * Complex.exp (-((2 * κ : ℝ) * w) * Complex.I)) -
        (Complex.I / 2) * (P.G w / (Real.cosh w : ℂ) *
          Complex.exp (-((-(2 * κ) : ℝ) * w) * Complex.I)) := fun w => by
    rw [Complex.ofReal_sin, Complex.sin]
    push_cast
    ring_nf
  have hi : ∀ ξ : ℝ, Integrable fun w : ℝ =>
      P.G w / (Real.cosh w : ℂ) * Complex.exp (-(ξ * w) * Complex.I) := fun ξ =>
    hQint.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun w => by
        rw [show -((ξ : ℂ) * w) * Complex.I = ((-(ξ * w) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact (Complex.norm_exp_ofReal_mul_I _).le)
  rw [specWeight_imag_eq P hκ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos Real.pi_pos]
  gcongr
  simp_rw [hsin]
  rw [integral_sub ((hi _).const_mul _) ((hi _).const_mul _), integral_const_mul, integral_const_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_div, Complex.norm_I, Complex.norm_ofNat]
  linarith

end

end GaloisForLFunctions.RHTower.DeckPointPair
