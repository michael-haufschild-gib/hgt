import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage
import GaloisForLFunctions.RHTower.HeatGaussianTiltedMoments
import GaloisForLFunctions.RHTower.KiKimLeeRelativeBounds

/-!
# A Gaussian average with quadratic local error

A function close to one on a fixed interval has a Gaussian average close
to one. A quadratic exponential controls the local error; a linear
exponential envelope pays for the complete complementary tail.
-/

open Complex MeasureTheory Filter Set

namespace RHTower.DeBruijn

noncomputable section

private def quadraticErrorTail (t r u : ℝ) : ℝ :=
  (Iic (-r)).indicator (gaussDensity (2 * t)) u +
    (Ici r).indicator (gaussDensity (2 * t)) u

private theorem integrable_gaussDensity_real {t : ℝ} (ht : 0 < t) :
    Integrable (gaussDensity t) := by
  simpa only [sub_zero, mul_zero, Real.exp_zero, mul_one] using
    integrable_gaussDensity_sub_mul_rexp ht 0 0

private theorem quadraticErrorTail_nonneg {t : ℝ} (ht : 0 < t) (r u : ℝ) :
    0 ≤ quadraticErrorTail t r u := by
  apply add_nonneg
  · by_cases h : u ∈ Iic (-r)
    · simp only [indicator_of_mem h]
      exact (gaussDensity_pos (by positivity) u).le
    · simp only [indicator_of_notMem h, le_refl]
  · by_cases h : u ∈ Ici r
    · simp only [indicator_of_mem h]
      exact (gaussDensity_pos (by positivity) u).le
    · simp only [indicator_of_notMem h, le_refl]

private theorem gaussDensity_le_quadraticErrorTail {t r u : ℝ} (ht : 0 < t)
    (hu : r ≤ |u|) : gaussDensity (2 * t) u ≤ quadraticErrorTail t r u := by
  have hg := (gaussDensity_pos (by positivity : 0 < 2 * t) u).le
  rcases le_total 0 u with hpos | hneg
  · have hmem : u ∈ Ici r := by simpa only [mem_Ici, abs_of_nonneg hpos] using hu
    unfold quadraticErrorTail
    rw [indicator_of_mem hmem]
    by_cases h : u ∈ Iic (-r)
    · rw [indicator_of_mem h]
      linarith only [hg]
    · rw [indicator_of_notMem h, zero_add]
  · have hmem : u ∈ Iic (-r) := by
      rw [abs_of_nonpos hneg] at hu
      show u ≤ -r
      linarith only [hu]
    unfold quadraticErrorTail
    rw [indicator_of_mem hmem]
    by_cases h : u ∈ Ici r
    · rw [indicator_of_mem h]
      linarith only [hg]
    · rw [indicator_of_notMem h, add_zero]

private theorem integral_quadraticErrorTail_le {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (∫ u, quadraticErrorTail t r u) ≤ 2 * Real.exp (-(r ^ 2 / (8 * t))) := by
  have ht2 : 0 < 2 * t := by positivity
  have hi := integrable_gaussDensity_real ht2
  have hlo := setIntegral_Iic_gaussDensity_sub_mul_rexp_le ht2 0 0 (-r) (r / (4 * t))
    (by positivity)
  have hhi := setIntegral_Ici_gaussDensity_sub_mul_rexp_le ht2 0 0 r (r / (4 * t))
    (by positivity)
  simp only [sub_zero, mul_zero, Real.exp_zero, mul_one, zero_sub, zero_add,
    zero_mul, add_zero] at hlo hhi
  have elo : r / (4 * t) * -r + 2 * t * (-(r / (4 * t))) ^ 2 = -(r ^ 2 / (8 * t)) := by
    field_simp
    ring
  have ehi : -(r / (4 * t) * r) + 2 * t * (r / (4 * t)) ^ 2 = -(r ^ 2 / (8 * t)) := by
    field_simp
    ring
  rw [elo] at hlo
  rw [ehi] at hhi
  unfold quadraticErrorTail
  rw [integral_add (hi.indicator measurableSet_Iic) (hi.indicator measurableSet_Ici),
    integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ici]
  linarith only [hlo, hhi]

private theorem exp_sub_one_le_mul_exp (v : ℝ) :
    Real.exp v - 1 ≤ v * Real.exp v := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-v)) (Real.exp_pos v).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith only [h]

private theorem gaussDensity_mul_quadratic_error_le {t K : ℝ} (ht : 0 < t)
    (hK : 0 ≤ K) (htK : t * K ≤ 1 / 8) (u : ℝ) :
    gaussDensity t u * (Real.exp (K * u ^ 2) - 1) ≤
      (2 * K) * (gaussDensity (2 * t) u * u ^ 2) := by
  have hexp : K * u ^ 2 ≤ u ^ 2 / (8 * t) := by
    rw [le_div_iff₀ (by positivity : 0 < 8 * t)]
    have h := mul_le_mul_of_nonneg_right htK (sq_nonneg u)
    nlinarith only [h]
  calc
    _ ≤ gaussDensity t u * ((K * u ^ 2) * Real.exp (K * u ^ 2)) :=
      mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp _) (gaussDensity_pos ht u).le
    _ = (K * u ^ 2) * (gaussDensity t u * Real.exp (K * u ^ 2)) := by ring
    _ ≤ (K * u ^ 2) * (gaussDensity t u * Real.exp (u ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (gaussDensity_pos ht u).le)
        (by positivity)
    _ ≤ (K * u ^ 2) * (2 * gaussDensity (2 * t) u) :=
      mul_le_mul_of_nonneg_left (gaussDensity_mul_exp_le ht u) (by positivity)
    _ = _ := by ring

/-- A complete Gaussian error bound from a quadratic local estimate and a
linear exponential global envelope. Both the average and its error are integrable. -/
theorem integral_gaussDensity_quadratic_error_le {t r K E D : ℝ} {F : ℝ → ℂ}
    (ht : 0 < t) (hr : 0 < r) (hK : 0 ≤ K) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (htK : t * K ≤ 1 / 8) (htD : t * D ≤ r / 8) (hF : Continuous F)
    (hlocal : ∀ u : ℝ, |u| ≤ r → ‖F u - 1‖ ≤ Real.exp (K * u ^ 2) - 1)
    (hglobal : ∀ u : ℝ, ‖F u‖ ≤ Real.exp (E + D * |u|)) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * F u) ∧
      ‖(∫ u : ℝ, (gaussDensity t u : ℂ) * F u) - 1‖ ≤
        8 * t * K + 8 * Real.exp (E - r ^ 2 / (8 * t)) := by
  let W : ℝ → ℝ := fun u =>
    (2 * K) * (gaussDensity (2 * t) u * u ^ 2) +
      (4 * Real.exp E) * quadraticErrorTail t r u
  have ht2 : 0 < 2 * t := by positivity
  have hg := integrable_gaussDensity_real ht2
  have hitail : Integrable (quadraticErrorTail t r) :=
    (hg.indicator measurableSet_Iic).add (hg.indicator measurableSet_Ici)
  have hiW : Integrable W := ((integrable_gaussDensity_mul_pow ht2 2).const_mul _).add
    (hitail.const_mul _)
  have hpoint : ∀ u : ℝ, ‖(gaussDensity t u : ℂ) * (F u - 1)‖ ≤ W u := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht u)]
    have hloc0 : 0 ≤ (2 * K) * (gaussDensity (2 * t) u * u ^ 2) := by
      exact mul_nonneg (by positivity)
        (mul_nonneg (gaussDensity_pos ht2 u).le (sq_nonneg u))
    have htail0 : 0 ≤ (4 * Real.exp E) * quadraticErrorTail t r u :=
      mul_nonneg (by positivity) (quadraticErrorTail_nonneg ht r u)
    by_cases hu : |u| ≤ r
    · have h := (mul_le_mul_of_nonneg_left (hlocal u hu) (gaussDensity_pos ht u).le).trans
        (gaussDensity_mul_quadratic_error_le ht hK htK u)
      exact h.trans (by dsimp [W]; linarith only [htail0])
    · have hur : r ≤ |u| := (lt_of_not_ge hu).le
      have hexp : D * |u| ≤ u ^ 2 / (8 * t) := by
        rw [le_div_iff₀ (by positivity : 0 < 8 * t)]
        have h1 := mul_le_mul_of_nonneg_right htD (abs_nonneg u)
        have h2 := mul_le_mul_of_nonneg_right hur (abs_nonneg u)
        nlinarith only [h1, h2, sq_abs u]
      have hnorm : ‖F u - 1‖ ≤ 2 * Real.exp (E + D * |u|) := by
        have htri := norm_sub_le (F u) (1 : ℂ)
        rw [norm_one] at htri
        have he1 : 1 ≤ Real.exp (E + D * |u|) := Real.one_le_exp (by positivity)
        linarith only [htri, hglobal u, he1]
      have htail : gaussDensity t u * ‖F u - 1‖ ≤
          (4 * Real.exp E) * quadraticErrorTail t r u := by
        calc
          _ ≤ gaussDensity t u * (2 * Real.exp (E + D * |u|)) :=
            mul_le_mul_of_nonneg_left hnorm (gaussDensity_pos ht u).le
          _ = (2 * Real.exp E) * (gaussDensity t u * Real.exp (D * |u|)) := by
            rw [Real.exp_add]
            ring
          _ ≤ (2 * Real.exp E) * (gaussDensity t u * Real.exp (u ^ 2 / (8 * t))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (gaussDensity_pos ht u).le)
              (by positivity)
          _ ≤ (2 * Real.exp E) * (2 * gaussDensity (2 * t) u) :=
            mul_le_mul_of_nonneg_left (gaussDensity_mul_exp_le ht u) (by positivity)
          _ = (4 * Real.exp E) * gaussDensity (2 * t) u := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (gaussDensity_le_quadraticErrorTail ht hur)
            (by positivity)
      exact htail.trans (by dsimp [W]; linarith only [hloc0])
  have hgcont : Continuous (fun u : ℝ => (gaussDensity t u : ℂ)) := by
    unfold gaussDensity
    fun_prop
  have herror : Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * (F u - 1)) :=
    hiW.mono' (hgcont.mul (hF.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall hpoint)
  have hig : Integrable (fun u : ℝ => (gaussDensity t u : ℂ)) :=
    (integrable_gaussDensity_real ht).ofReal
  have hsplit : (fun u : ℝ => (gaussDensity t u : ℂ) * F u) =
      fun u => (gaussDensity t u : ℂ) * (F u - 1) + (gaussDensity t u : ℂ) := by
    funext u
    ring
  have hmass : (∫ u : ℝ, (gaussDensity t u : ℂ)) = 1 := by
    simpa only [mul_zero, Complex.exp_zero, mul_one, zero_pow two_ne_zero] using
      integral_gaussDensity_mul_exp ht 0
  have hbound : (∫ u, W u) ≤ 8 * t * K + 8 * Real.exp (E - r ^ 2 / (8 * t)) := by
    have hm : (∫ u : ℝ, gaussDensity (2 * t) u * u ^ 2) = 4 * t := by
      have h := integral_gaussDensity_mul_pow_even ht2 1
      norm_num [Nat.factorial] at h
      linarith only [h]
    have htail := integral_quadraticErrorTail_le ht hr.le
    dsimp [W]
    rw [integral_add ((integrable_gaussDensity_mul_pow ht2 2).const_mul _)
      (hitail.const_mul _), integral_const_mul, integral_const_mul, hm]
    calc
      _ ≤ (2 * K) * (4 * t) + (4 * Real.exp E) *
          (2 * Real.exp (-(r ^ 2 / (8 * t)))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left htail
          (by positivity : 0 ≤ 4 * Real.exp E))
      _ = _ := by
        rw [show E - r ^ 2 / (8 * t) = E + -(r ^ 2 / (8 * t)) by ring, Real.exp_add]
        ring
  refine ⟨by rw [hsplit]; exact herror.add hig, ?_⟩
  rw [hsplit, integral_add herror hig, hmass, add_sub_cancel_right]
  exact (norm_integral_le_integral_norm _).trans
    ((integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hiW
      (Eventually.of_forall hpoint)).trans hbound)

end

end RHTower.DeBruijn
