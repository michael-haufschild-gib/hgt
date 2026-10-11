import GaloisForLFunctions.RHTower.XiSliceHusimiPositivity

/-!
# Husimi positivity is blind to real-rootedness

The abstract Husimi identity `exp_mul_heightAverage_eq` holds for every even real source with all
exponential moments.  This file exhibits such a source whose slice at height `0` has a negative
Taylor coefficient, and whose transform has a non-real zero.

**Example.**  `f(u) = e^{−u²} cos 2u`.  Its transform is
`F(z) = ∫ e^{−izu} f(u) du = (√π/2)(e^{−(z−2)²/4} + e^{−(z+2)²/4})` (`sourceFL_gaussCos`).  Hence
`F(iπ/2) = 0`, a non-real zero, and the height-`0` slice `S(x) = F(−ix)F(ix)` vanishes at the real
point `x = π/2` while `S(0) = π e^{−2} > 0`.  A function with only nonnegative Taylor coefficients
cannot do that, so some coefficient of `S` is negative (`exists_not_nonneg_taylorCoeff_gaussCos_slice`).

**Meaning for WD.**  Husimi positivity of the height-averaged slice, at every resolution and every
height, is strictly weaker than slice positivity.  It holds for sources whose transforms have
non-real zeros.  Together with `not_nonneg_smoothing_eq_husimi`, the averaged positivity side of WD
carries no information about real-rootedness; any producer must use the arithmetic of the theta
source.
-/

open Complex MeasureTheory Real
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The source `e^{−u²} cos 2u`. -/
def gaussCos (u : ℝ) : ℝ := Real.exp (-u ^ 2) * Real.cos (2 * u)

theorem gaussCos_neg (u : ℝ) : gaussCos (-u) = gaussCos u := by
  simp [gaussCos, mul_neg, Real.cos_neg]

theorem continuous_gaussCos : Continuous gaussCos := by
  unfold gaussCos; fun_prop

theorem integrable_exp_mul_gaussCos (b : ℝ) :
    Integrable (fun u => Real.exp (b * u) * gaussCos u) := by
  have hq := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (b : ℂ) 0
  refine hq.norm.mono' ((by unfold gaussCos; fun_prop :
    Continuous fun u : ℝ => Real.exp (b * u) * gaussCos u).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Complex.norm_exp, Real.norm_eq_abs]
  have hre : (-(1 : ℂ) * (u : ℂ) ^ 2 + (b : ℂ) * u + 0).re = b * u - u ^ 2 := by
    simp [pow_two]; ring
  rw [hre]
  unfold gaussCos
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    ← mul_assoc, ← Real.exp_add]
  calc Real.exp (b * u + -u ^ 2) * |Real.cos (2 * u)| ≤ Real.exp (b * u + -u ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ = Real.exp (b * u - u ^ 2) := by ring_nf

/-- **The transform of `e^{−u²} cos 2u`.** -/
theorem sourceFL_gaussCos (z : ℂ) :
    sourceFL gaussCos z =
      (Real.sqrt π / 2 : ℝ) * (cexp (-(z - 2) ^ 2 / 4) + cexp (-(z + 2) ^ 2 / 4)) := by
  have hb : ((-1 : ℂ)).re < 0 := by norm_num
  have h1 := integral_cexp_quadratic hb (-I * z + 2 * I) 0
  have h2 := integral_cexp_quadratic hb (-I * z - 2 * I) 0
  have hi1 := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (-I * z + 2 * I) 0
  have hi2 := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (-I * z - 2 * I) 0
  have hpt : ∀ u : ℝ, cexp (-I * z * u) * (gaussCos u : ℂ) =
      (1 / 2 : ℂ) * (cexp (-1 * (u : ℂ) ^ 2 + (-I * z + 2 * I) * u + 0) +
        cexp (-1 * (u : ℂ) ^ 2 + (-I * z - 2 * I) * u + 0)) := by
    intro u
    unfold gaussCos
    push_cast
    rw [Complex.cos, show ((2 : ℂ) * u * I) = 2 * u * I from rfl]
    rw [show cexp (-1 * (u : ℂ) ^ 2 + (-I * z + 2 * I) * u + 0) =
        cexp (-I * z * u) * cexp (-(u : ℂ) ^ 2) * cexp (2 * u * I) by
          rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf,
      show cexp (-1 * (u : ℂ) ^ 2 + (-I * z - 2 * I) * u + 0) =
        cexp (-I * z * u) * cexp (-(u : ℂ) ^ 2) * cexp (-(2 * u * I)) by
          rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf]
    ring
  unfold sourceFL
  simp_rw [hpt]
  rw [integral_const_mul, integral_add (by simpa using hi1) (by simpa using hi2)]
  have e1 : ∫ u : ℝ, cexp (-1 * (u : ℂ) ^ 2 + (-I * z + 2 * I) * u + 0) =
      (Real.sqrt π : ℂ) * cexp (-(z - 2) ^ 2 / 4) := by
    rw [h1]
    congr 1
    · rw [neg_neg, div_one, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
    · congr 1
      ring_nf
      rw [I_sq]
      ring
  have e2 : ∫ u : ℝ, cexp (-1 * (u : ℂ) ^ 2 + (-I * z - 2 * I) * u + 0) =
      (Real.sqrt π : ℂ) * cexp (-(z + 2) ^ 2 / 4) := by
    rw [h2]
    congr 1
    · rw [neg_neg, div_one, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
    · congr 1
      ring_nf
      rw [I_sq]
      ring
  rw [e1, e2]
  push_cast
  ring

/-- The transform of `e^{−u²} cos 2u` has the non-real zero `iπ/2`. -/
theorem sourceFL_gaussCos_I_pi_div_two :
    sourceFL gaussCos (I * ((Real.pi / 2 : ℝ) : ℂ)) = 0 := by
  rw [sourceFL_gaussCos]
  have e1 : -(I * ((Real.pi / 2 : ℝ) : ℂ) - 2) ^ 2 / 4 =
      ((Real.pi ^ 2 / 16 - 1 : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e2 : -(I * ((Real.pi / 2 : ℝ) : ℂ) + 2) ^ 2 / 4 =
      ((Real.pi ^ 2 / 16 - 1 : ℝ) : ℂ) + -((Real.pi / 2 : ℝ) : ℂ) * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add, ← mul_add]
  have hcos : cexp (((Real.pi / 2 : ℝ) : ℂ) * I) + cexp (-((Real.pi / 2 : ℝ) : ℂ) * I) = 0 := by
    have h := Complex.cos.eq_def (((Real.pi / 2 : ℝ) : ℂ))
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two, ofReal_zero] at h
    have h' : (cexp ((((Real.pi / 2 : ℝ) : ℂ)) * I) + cexp (-(((Real.pi / 2 : ℝ) : ℂ)) * I)) / 2
        = 0 := h.symm
    rw [div_eq_zero_iff] at h'
    exact h'.resolve_right two_ne_zero
  rw [hcos, mul_zero, mul_zero]

theorem expMomentSource_gaussCos : ExpMomentSource (fun u => (gaussCos u : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp continuous_gaussCos, fun c => ?_⟩
  have h := (integrable_exp_mul_gaussCos c).norm.add (integrable_exp_mul_gaussCos (-c)).norm
  refine h.mono' ((by unfold gaussCos; fun_prop : Continuous fun u : ℝ =>
    Real.exp (c * |u|) * ‖(gaussCos u : ℂ)‖).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)),
    Complex.norm_real]
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    nlinarith [abs_nonneg (gaussCos u), Real.exp_pos (-c * u)]
  · rw [abs_of_nonpos hu, show c * -u = -c * u by ring]
    nlinarith [abs_nonneg (gaussCos u), Real.exp_pos (c * u)]

/-- **A Husimi-positive source with a non-positive slice.**  The height-`0` slice of
`e^{−u²} cos 2u` has a Taylor coefficient that is not a nonnegative real. -/
theorem exists_not_nonneg_taylorCoeff_gaussCos_slice :
    ∃ n : ℕ, ¬ (0 ≤ ((n.factorial : ℂ))⁻¹ * iteratedDeriv n
      (fun x : ℂ => sourceFL gaussCos (-(I * x)) * sourceFL gaussCos (I * x)) 0) := by
  classical
  by_contra hall
  push Not at hall
  set S : ℂ → ℂ := fun x => sourceFL gaussCos (-(I * x)) * sourceFL gaussCos (I * x) with hS
  have hd : Differentiable ℂ (sourceFL gaussCos) :=
    expMomentSource_gaussCos.differentiable_sourceTransform
  have hSd : Differentiable ℂ S := by
    simp only [hS]
    exact (hd.comp (by fun_prop)).mul (hd.comp (by fun_prop))
  set δ : ℝ := Real.pi / 2 with hδ
  have hzero : S (δ : ℂ) = 0 := by
    simp only [hS, hδ]
    rw [show I * ((Real.pi / 2 : ℝ) : ℂ) = I * ((Real.pi / 2 : ℝ) : ℂ) from rfl,
      sourceFL_gaussCos_I_pi_div_two, mul_zero]
  have hS0 : S 0 = ((Real.pi * Real.exp (-2) : ℝ) : ℂ) := by
    simp only [hS, mul_zero, neg_zero, sourceFL_gaussCos]
    have e : (-(0 - 2 : ℂ) ^ 2 / 4) = ((-1 : ℝ) : ℂ) := by push_cast; ring
    have e' : (-(0 + 2 : ℂ) ^ 2 / 4) = ((-1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, e', ← ofReal_exp]
    push_cast
    have hpi : (Real.sqrt π : ℂ) ^ 2 = (π : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
    have hexp : cexp (-1) * cexp (-1) = cexp (-2) := by rw [← Complex.exp_add]; norm_num
    calc (Real.sqrt π / 2 : ℂ) * (cexp (-1) + cexp (-1)) *
          ((Real.sqrt π / 2 : ℂ) * (cexp (-1) + cexp (-1)))
        = (Real.sqrt π : ℂ) ^ 2 * (cexp (-1) * cexp (-1)) := by ring
      _ = _ := by rw [hpi, hexp]
  -- the Taylor series at the real zero `δ`
  have hsum := hasSum_taylorSeries_of_entire hSd 0 (δ : ℂ)
  rw [hzero] at hsum
  have hre := hasSum_re hsum
  simp only [sub_zero, smul_eq_mul, zero_re] at hre
  have hterm : ∀ n, 0 ≤ (((n.factorial : ℂ))⁻¹ * ((δ : ℂ) ^ n * iteratedDeriv n S 0)).re := by
    intro n
    have hn := hall n
    have hδn : (δ : ℂ) ^ n = ((δ ^ n : ℝ) : ℂ) := by push_cast; ring
    rw [show ((n.factorial : ℂ))⁻¹ * ((δ : ℂ) ^ n * iteratedDeriv n S 0) =
        ((δ ^ n : ℝ) : ℂ) * (((n.factorial : ℂ))⁻¹ * iteratedDeriv n S 0) by rw [hδn]; ring,
      Complex.re_ofReal_mul]
    exact mul_nonneg (pow_nonneg (by positivity) n) (Complex.nonneg_iff.mp hn).1
  have h0 := le_hasSum hre 0 (fun n _ => hterm n)
  have hc0 : (((0 : ℕ).factorial : ℂ)⁻¹ * ((δ : ℂ) ^ 0 * iteratedDeriv 0 S 0)).re =
      Real.pi * Real.exp (-2) := by
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, iteratedDeriv_zero,
      hS0, ofReal_re]
  rw [hc0] at h0
  have : 0 < Real.pi * Real.exp (-2) := by positivity
  linarith

end

end RHTower
