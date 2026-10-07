import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorWeightedIntegral
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorLogMoments

/-!
# Spatial smoothness of every polynomial Poisson mode

Normalizing the real integration parameter onto the unit circle separates a
fixed integrable weight from a smooth kernel with compact parameter range.
This proves C∞ regularity at every logarithmic order, without derivative cutoffs.
-/

noncomputable section

open Complex Set Filter MeasureTheory Topology Metric Polynomial
open scoped ContDiff ComplexConjugate

namespace RHTower.WeilHigherDenominator

/-- Compactification of the real integration parameter. -/
def polarParameter (t : ℝ) : ℂ := (I - (t : ℂ)) / (‖I - (t : ℂ)‖ : ℂ)

private lemma polarParameter_den_ne (t : ℝ) : ‖I - (t : ℂ)‖ ≠ 0 := by
  apply norm_ne_zero_iff.mpr
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem continuous_polarParameter : Continuous polarParameter := by
  apply (continuous_const.sub Complex.continuous_ofReal).div
    (Complex.continuous_ofReal.comp (continuous_const.sub Complex.continuous_ofReal).norm)
  intro t
  change (‖I - (t : ℂ)‖ : ℂ) ≠ 0
  exact_mod_cast polarParameter_den_ne t

theorem norm_polarParameter (t : ℝ) : ‖polarParameter t‖ = 1 := by
  simp only [polarParameter, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (polarParameter_den_ne t)

/-- Squared projective denominator, expressed as a real polynomial. -/
def projectivePoissonDenom (z c : ℂ) : ℝ :=
  (z.re * c.im + c.re) ^ 2 + (z.im * c.im) ^ 2

/-- The projective half-power kernel; spatial points are in the upper half-plane. -/
def projectivePoissonKernel (z c : ℂ) : ℝ := projectivePoissonDenom z c ^ (-1 / 2 : ℝ)

theorem projectivePoissonDenom_pos {z c : ℂ} (hz : 0 < z.im) (hc : c ≠ 0) :
    0 < projectivePoissonDenom z c := by
  by_cases hi : c.im = 0
  · have hr : c.re ≠ 0 := by
      intro hr
      apply hc
      exact Complex.ext (by simpa using hr) (by simpa using hi)
    simpa [projectivePoissonDenom, hi] using sq_pos_of_ne_zero hr
  · have hp : z.im * c.im ≠ 0 := mul_ne_zero hz.ne' hi
    dsimp [projectivePoissonDenom]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hp)

theorem projectivePoissonKernel_eq_norm_inv (z c : ℂ) :
    projectivePoissonKernel z c = ‖z * (c.im : ℂ) + (c.re : ℂ)‖⁻¹ := by
  have hq : projectivePoissonDenom z c = ‖z * (c.im : ℂ) + (c.re : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [projectivePoissonDenom, Complex.normSq_apply, pow_two]
  rw [projectivePoissonKernel, hq, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

/-- Joint smoothness includes both ends of the compactified integration line. -/
theorem contDiffOn_projectivePoissonKernel :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => projectivePoissonKernel p.1 p.2)
      ({z : ℂ | 0 < z.im} ×ˢ {c : ℂ | c ≠ 0}) := by
  intro p hp
  have hq : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => projectivePoissonDenom q.1 q.2) p := by
    have hr₁ : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1.re) p :=
      reCLM.contDiff.contDiffAt.comp p contDiffAt_fst
    have hi₁ : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1.im) p :=
      imCLM.contDiff.contDiffAt.comp p contDiffAt_fst
    have hr₂ : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.2.re) p :=
      reCLM.contDiff.contDiffAt.comp p contDiffAt_snd
    have hi₂ : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.2.im) p :=
      imCLM.contDiff.contDiffAt.comp p contDiffAt_snd
    exact (((hr₁.mul hi₂).add hr₂).pow 2).add ((hi₁.mul hi₂).pow 2)
  exact (hq.rpow_const_of_ne (projectivePoissonDenom_pos hp.1 hp.2).ne').contDiffWithinAt

/-- The compactified kernel is exactly the ratio to the fixed imaginary-axis kernel. -/
theorem projectivePoissonKernel_polarParameter (z : ℂ) (t : ℝ) :
    projectivePoissonKernel z (polarParameter t) = ‖I - (t : ℂ)‖ / ‖z - (t : ℂ)‖ := by
  have hv : z * ((polarParameter t).im : ℂ) + ((polarParameter t).re : ℂ) =
      (z - (t : ℂ)) / (‖I - (t : ℂ)‖ : ℂ) := by
    simp only [polarParameter, div_ofReal_im, div_ofReal_re, sub_im, I_im, ofReal_im,
      sub_re, I_re, ofReal_re, sub_zero, zero_sub]
    push_cast
    ring
  rw [projectivePoissonKernel_eq_norm_inv, hv, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_div]

/-- The actual weighted kernel factors through the fixed axis and compact parameter. -/
theorem polynomial_polarKernel_projective (ρ z : ℂ) (P : ℂ[X]) (hz : 0 < z.im) (t : ℝ) :
    P.eval (Real.log |t| : ℂ) * polarKernel ρ z t =
      (P.eval (Real.log |t| : ℂ) * polarKernel ρ I t) *
        (projectivePoissonKernel z (polarParameter t) : ℂ) := by
  have hr : (‖I - (t : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast polarParameter_den_ne t
  have hd : (‖z - (t : ℂ)‖ : ℂ) ≠ 0 := by
    apply ofReal_ne_zero.mpr
    apply norm_ne_zero_iff.mpr
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, ofReal_im, sub_zero, zero_im] at hi
    exact hz.ne' hi
  rw [projectivePoissonKernel_polarParameter, ofReal_div]
  simp only [polarKernel]
  field_simp

private lemma smooth_weighted_projective {w : ℝ → ℝ} (hw : Integrable w) :
    ContDiffOn ℝ ∞ (fun z => ∫ t : ℝ, w t * projectivePoissonKernel z (polarParameter t))
      {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hV : IsOpen {c : ℂ | c ≠ 0} := isOpen_ne
  have hKV : sphere (0 : ℂ) 1 ⊆ {c : ℂ | c ≠ 0} := by
    intro c hc hz
    simp [hz] at hc
  have hγK : ∀ t : ℝ, polarParameter t ∈ sphere (0 : ℂ) 1 := by
    intro t
    simpa only [mem_sphere, dist_zero_right] using norm_polarParameter t
  simpa only [smul_eq_mul] using contDiffOn_weighted_compact_parameter_infty
    hU hV (isCompact_sphere (0 : ℂ) 1) hKV continuous_polarParameter hγK hw
    contDiffOn_projectivePoissonKernel

/-- All actual polynomial Poisson modes are smooth throughout the upper half-plane. -/
theorem contDiffOn_polynomialPolarMode {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (P : ℂ[X]) : ContDiffOn ℝ ∞ (polynomialPolarMode ρ P) {z : ℂ | 0 < z.im} := by
  let W : ℝ → ℂ := fun t => P.eval (Real.log |t| : ℂ) * polarKernel ρ I t
  have hW : Integrable W := integrable_polynomial_polarKernel hρ₀ hρ₁ (by simp) P
  let J : (ℝ → ℝ) → ℂ → ℝ := fun w z => ∫ t : ℝ, w t * projectivePoissonKernel z (polarParameter t)
  have hR : ContDiffOn ℝ ∞ (J fun t => (W t).re) {z : ℂ | 0 < z.im} :=
    smooth_weighted_projective hW.re
  have hI : ContDiffOn ℝ ∞ (J fun t => (W t).im) {z : ℂ | 0 < z.im} :=
    smooth_weighted_projective hW.im
  have hint : ContDiffOn ℝ ∞ (fun z => ∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ z t)
      {z : ℂ | 0 < z.im} := by
    have hh : ContDiffOn ℝ ∞ (fun z => ((J (fun t => (W t).re) z : ℝ) : ℂ) +
        ((J (fun t => (W t).im) z : ℝ) : ℂ) * I) {z : ℂ | 0 < z.im} :=
      (ofRealCLM.contDiff.comp_contDiffOn hR).add
        ((ofRealCLM.contDiff.comp_contDiffOn hI).mul contDiffOn_const)
    apply hh.congr
    intro z hz
    have heq : (fun t => P.eval (Real.log |t| : ℂ) * polarKernel ρ z t) =
        (fun t => W t * (projectivePoissonKernel z (polarParameter t) : ℂ)) :=
      funext (polynomial_polarKernel_projective ρ z P hz)
    have hzt := integrable_polynomial_polarKernel hρ₀ hρ₁ hz P
    rw [heq] at hzt ⊢
    simpa [J, Complex.mul_re, Complex.mul_im] using (integral_re_add_im hzt).symm
  have hs : ContDiffOn ℝ ∞ (fun z : ℂ => (Real.sqrt z.im : ℂ)) {z : ℂ | 0 < z.im} := by
    intro z hz
    rw [show (fun z : ℂ => (Real.sqrt z.im : ℂ)) =
      (fun z : ℂ => ((z.im ^ (1 / 2 : ℝ) : ℝ) : ℂ)) by funext z; rw [Real.sqrt_eq_rpow]]
    exact (ofRealCLM.contDiff.contDiffAt.comp z
      (imCLM.contDiff.contDiffAt.rpow_const_of_ne hz.ne')).contDiffWithinAt
  exact hs.mul hint

/-- Polynomial logarithmic weights preserve horizontal evenness. -/
theorem polynomialPolarMode_reflect (ρ : ℂ) (P : ℂ[X]) (z : ℂ) :
    polynomialPolarMode ρ P (-conj z) = polynomialPolarMode ρ P z := by
  simp only [polynomialPolarMode, neg_im, conj_im, neg_neg, polarKernel_reflect]
  congr 1
  simpa using Measure.integral_comp_mul_left
    (fun t : ℝ => P.eval (Real.log |t| : ℂ) * polarKernel ρ z t) (-1)

end RHTower.WeilHigherDenominator
