import Mathlib

/-!
# The exponential window integral

`expInt L T U = ∫_T^{T+U} e^{iLt} dt` is the elementary primitive behind every mean-value theorem
for Dirichlet polynomials: it is `U` on the diagonal `L = 0` and at most `2/|L|` off it.  The
real-part specialisation is the corpus's `cosInt`; the complex form is what a *twisted* mean value
needs, since a twist `(h/k)^{-it}` shifts the frequency `L` rather than preserving the cosine.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `∫_T^{T+U} e^{iLt} dt`. -/
def expInt (L T U : ℝ) : ℂ := ∫ t in T..(T + U), Complex.exp (((L * t : ℝ) : ℂ) * I)

theorem expInt_zero (T U : ℝ) : expInt 0 T U = (U : ℂ) := by
  unfold expInt
  simp

theorem hasDerivAt_expLin {L : ℝ} (hL : L ≠ 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (((L * u : ℝ) : ℂ) * I) / ((L : ℂ) * I))
      (Complex.exp (((L * t : ℝ) : ℂ) * I)) t := by
  have hLC : ((L : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hL) Complex.I_ne_zero
  have hlin : HasDerivAt (fun u : ℝ => ((L * u : ℝ) : ℂ) * I) ((L : ℂ) * I) t := by
    have h : HasDerivAt (fun u : ℝ => ((L * u : ℝ) : ℂ)) (L : ℂ) t := by
      have h0 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h1 := h0.const_mul ((L : ℂ))
      refine h1.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · ring
      · filter_upwards with u
        push_cast
        ring
    simpa using h.mul_const I
  have hexp := hlin.cexp
  have hres : HasDerivAt (fun u : ℝ => Complex.exp (((L * u : ℝ) : ℂ) * I) / ((L : ℂ) * I))
      (Complex.exp (((L * t : ℝ) : ℂ) * I) * ((L : ℂ) * I) / ((L : ℂ) * I)) t :=
    hexp.div_const _
  refine hres.congr_deriv ?_
  rw [mul_div_assoc, div_self hLC, mul_one]

theorem expInt_eq {L : ℝ} (hL : L ≠ 0) (T U : ℝ) :
    expInt L T U
      = (Complex.exp (((L * (T + U) : ℝ) : ℂ) * I) - Complex.exp (((L * T : ℝ) : ℂ) * I))
        / ((L : ℂ) * I) := by
  unfold expInt
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (((L * t : ℝ) : ℂ) * I))
      volume T (T + U) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_expLin hL t) hint]
  ring

theorem norm_expInt_le {L : ℝ} (hL : L ≠ 0) (T U : ℝ) : ‖expInt L T U‖ ≤ 2 / |L| := by
  have hLabs : (0 : ℝ) < |L| := abs_pos.mpr hL
  rw [expInt_eq hL]
  have hden : ‖(L : ℂ) * I‖ = |L| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnum : ‖Complex.exp (((L * (T + U) : ℝ) : ℂ) * I)
      - Complex.exp (((L * T : ℝ) : ℂ) * I)‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [norm_div, hden, div_le_div_iff₀ hLabs hLabs]
  nlinarith [hnum, hLabs]

theorem norm_expInt_le_length (L T U : ℝ) (hU : 0 ≤ U) : ‖expInt L T U‖ ≤ U := by
  unfold expInt
  have hbnd : ∀ t ∈ Set.uIoc T (T + U),
      ‖Complex.exp (((L * t : ℝ) : ℂ) * I)‖ ≤ 1 := by
    intro t _
    rw [Complex.norm_exp_ofReal_mul_I]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  have habs : |T + U - T| = U := by
    rw [show T + U - T = U by ring, abs_of_nonneg hU]
  rw [habs] at h
  linarith

end GaloisForLFunctions.HTGeometry

end
