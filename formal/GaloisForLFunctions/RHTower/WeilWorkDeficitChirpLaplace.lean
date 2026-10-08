import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Complex Laplace transform of the normalized signed saddle profile

The normalized real part of a complex Gaussian has an absolutely convergent
complex Laplace transform. Its critical positive tilt has zero mass, and the
associated Fourier multiplier has exactly one real zero, with an explicit
nonzero derivative there.

This module supplies a classical Gaussian bridge for the Weil-work deficit
research. Identifying this profile with the actual Xi-kernel saddle limit,
controlling the coefficient tails, and constructing exact cancellation blocks
remain separate obligations. No spectral-deficit producer is asserted here.
-/

noncomputable section
open Complex MeasureTheory
namespace RHTower.WeilWorkDeficitChirp

private def rate : ℂ := (2 * (2 / (Real.pi : ℂ) + I))⁻¹

private theorem rate_re_pos : 0 < rate.re := by
  have hp : 0 < (2 * (2 / (Real.pi : ℂ) + I)).re := by
    norm_num [mul_re, div_ofReal_re, div_ofReal_im]
    positivity
  have hn : (2 * (2 / (Real.pi : ℂ) + I)) ≠ 0 := by
    intro h
    rw [h] at hp
    exact (lt_irrefl 0) hp
  change 0 < (2 * (2 / (Real.pi : ℂ) + I))⁻¹.re
  rw [Complex.inv_re]
  exact div_pos hp (Complex.normSq_pos.mpr hn)

private def gaussian (b : ℂ) (x : ℝ) : ℂ :=
  exp (-b * (x : ℂ)^2) / (∫ y : ℝ, exp (-b * (y : ℂ)^2))

/-- The normalized signed Gaussian-chirp profile from the integer saddle. -/
def profile (x : ℝ) : ℝ := (gaussian rate x).re

/-- Fourier symbol of the critically tilted profile, extended to complex frequency. -/
def criticalSymbol (z : ℂ) : ℂ :=
  ∫ x : ℝ, exp (((Real.sqrt Real.pi : ℂ)-I*z)*x) * (profile x : ℂ)

private theorem gaussian_conj (b : ℂ) (x : ℝ) :
    gaussian (starRingEnd ℂ b) x = starRingEnd ℂ (gaussian b x) := by
  unfold gaussian
  rw [map_div₀]
  congr 1
  · simp [← exp_conj]
  · rw [← integral_conj]
    congr 1
    funext y
    simp [← exp_conj]

private theorem profile_pair (x : ℝ) :
    (profile x : ℂ) = (gaussian rate x + gaussian (starRingEnd ℂ rate) x) / 2 := by
  rw [gaussian_conj]
  exact Complex.re_eq_add_conj _

private theorem integrable_gaussian_tilt (b z : ℂ) (hb : 0 < b.re) :
    Integrable (fun x : ℝ => exp (z * x) * gaussian b x) := by
  have h := (integrable_cexp_quadratic hb z 0).div_const
    (∫ y : ℝ, exp (-b * (y : ℂ)^2))
  convert h using 1
  funext x
  dsimp [gaussian]
  rw [← mul_div_assoc, ← exp_add]
  congr 2
  ring_nf

private theorem integral_gaussian_tilt (b z : ℂ) (hb : 0 < b.re) :
    (∫ x : ℝ, exp (z * x) * gaussian b x) = exp (z^2 / (4*b)) := by
  have hbn : b ≠ 0 := by intro h; subst b; simp at hb
  have hn : ((Real.pi : ℂ)/b)^(1/2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hbn))
  have he : (fun x : ℝ => exp (z*x) * gaussian b x) =
      fun x : ℝ => exp (-b*(x:ℂ)^2+z*x+0) /
        (∫ y : ℝ, exp (-b * (y : ℂ)^2)) := by
    funext x
    dsimp [gaussian]
    rw [← mul_div_assoc, ← exp_add]
    congr 2
    ring_nf
  rw [he, integral_div, integral_cexp_quadratic (by simpa using neg_neg_of_pos hb),
    integral_gaussian_complex hb]
  simp only [neg_neg, zero_sub, mul_neg, div_neg, neg_neg]
  exact mul_div_cancel_left₀ _ hn

private theorem rate_exponent (z : ℂ) :
    z^2 / (4*rate) = z^2/(Real.pi:ℂ) + z^2/2*I := by
  unfold rate
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring_nf

private theorem conj_rate_exponent (z : ℂ) :
    z^2 / (4*starRingEnd ℂ rate) = z^2/(Real.pi:ℂ) - z^2/2*I := by
  unfold rate
  simp only [map_inv₀, map_mul, map_ofNat, map_add, map_div₀, conj_ofReal, conj_I]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring_nf

/-- Every complex exponential tilt is absolutely integrable. -/
theorem integrable_profile_tilt (z : ℂ) :
    Integrable (fun x : ℝ => exp (z*x) * (profile x : ℂ)) := by
  have h := ((integrable_gaussian_tilt rate z rate_re_pos).add
    (integrable_gaussian_tilt (starRingEnd ℂ rate) z
      (by simpa only [conj_re] using rate_re_pos))).div_const 2
  convert h using 1
  funext x
  rw [profile_pair]
  dsimp only [Pi.add_apply]
  ring_nf

/-- Exact bilateral Laplace transform, retaining the signed quadratic phase. -/
theorem integral_profile_tilt (z : ℂ) :
    (∫ x : ℝ, exp (z*x) * (profile x : ℂ)) =
      exp (z^2/(Real.pi:ℂ)) * cos (z^2/2) := by
  have he : (fun x : ℝ => exp (z*x) * (profile x : ℂ)) =
      fun x : ℝ => (exp (z*x)*gaussian rate x +
        exp (z*x)*gaussian (starRingEnd ℂ rate) x)/2 := by
    funext x
    rw [profile_pair]
    ring_nf
  rw [he, integral_div, integral_add
    (integrable_gaussian_tilt rate z rate_re_pos)
    (integrable_gaussian_tilt (starRingEnd ℂ rate) z
      (by simpa only [conj_re] using rate_re_pos)),
    integral_gaussian_tilt rate z rate_re_pos,
    integral_gaussian_tilt (starRingEnd ℂ rate) z
      (by simpa only [conj_re] using rate_re_pos),
    rate_exponent, conj_rate_exponent]
  rw [sub_eq_add_neg, exp_add, exp_add, Complex.cos]
  ring_nf

theorem integral_profile : (∫ x : ℝ, (profile x : ℂ)) = 1 := by
  simpa using integral_profile_tilt 0

/-- The critical tilt has exactly zero mass although the unweighted mass is one. -/
theorem integral_profile_critical_tilt :
    (∫ x : ℝ, exp ((Real.sqrt Real.pi : ℂ)*x) * (profile x : ℂ)) = 0 := by
  have hs : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi:ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  rw [integral_profile_tilt, hs, Complex.cos_pi_div_two, mul_zero]

/-- The phase factor in the stretched-exponential coefficient-tail law. -/
theorem integral_profile_root_tilt (τ : ℝ) :
    (∫ x : ℝ, exp (((τ*Real.sqrt Real.pi/4 : ℝ):ℂ)*x) * (profile x : ℂ)) =
      ((Real.exp (τ^2/16) * Real.cos (Real.pi*τ^2/32) : ℝ):ℂ) := by
  rw [integral_profile_tilt]
  have hs : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi:ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  have h1 : ((τ:ℂ)*(Real.sqrt Real.pi:ℂ)/4)^2/(Real.pi:ℂ) = (τ:ℂ)^2/16 := by
    rw [div_pow, mul_pow, hs]
    field_simp
    ring_nf
  have h2 : ((τ:ℂ)*(Real.sqrt Real.pi:ℂ)/4)^2/2 = (Real.pi:ℂ)*(τ:ℂ)^2/32 := by
    rw [div_pow, mul_pow, hs]
    ring_nf
  rw [h1, h2]

/-- The critical profile has exactly one zero on the real frequency axis. -/
theorem criticalSymbol_real_zero_iff (ξ : ℝ) : criticalSymbol ξ = 0 ↔ ξ = 0 := by
  rw [criticalSymbol, integral_profile_tilt, mul_eq_zero,
    or_iff_right (Complex.exp_ne_zero _)]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
    have hi := congrArg Complex.im hk
    norm_num [pow_two, mul_re, mul_im, div_ofReal_im] at hi
    have hs := Real.sqrt_pos.mpr Real.pi_pos
    nlinarith
  · intro h
    subst ξ
    have hs : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi:ℂ) := by
      exact_mod_cast Real.sq_sqrt Real.pi_pos.le
    simp [hs]

/-- The sole real-frequency zero is simple, with its exact normalized derivative. -/
theorem hasDerivAt_criticalSymbol_zero :
    HasDerivAt criticalSymbol (I*(Real.sqrt Real.pi:ℂ)*exp 1) 0 := by
  let l : ℂ := (Real.sqrt Real.pi : ℂ)
  have hl : l^2 = (Real.pi:ℂ) := by
    change (Real.sqrt Real.pi : ℂ)^2 = (Real.pi:ℂ)
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : HasDerivAt (fun z : ℂ => l-I*z) (-I) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_mul I).const_sub l
  have h := ((hd.pow 2).div_const (Real.pi:ℂ)).cexp.mul
    ((hd.pow 2).div_const 2).ccos
  simp only [Pi.pow_apply] at h
  convert! h using 1
  · funext z
    exact integral_profile_tilt (l-I*z)
  · simp only [mul_zero, sub_zero, hl, div_self hp, Complex.cos_pi_div_two,
      Complex.sin_pi_div_two]
    dsimp [l]
    ring_nf

end RHTower.WeilWorkDeficitChirp
