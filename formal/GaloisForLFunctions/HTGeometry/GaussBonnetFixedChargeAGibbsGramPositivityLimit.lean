import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsGramForms

/-!
# Suppression of nonpositive responses in actual Gibbs Gram forms

The imaginary part of each actual finite quadratic response is o(d).
Its negative real part is also o(d), because the exact critical form
is nonnegative. These are quantified asymptotic positivity statements
with no finite-state Hermitian or positivity premise.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsGramForm_re_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    Tendsto (fun τ => ((egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).re -
      (egbFixedChargeACriticalGramForm n x z).re) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (egbFixedChargeAGibbsGramForm_first_zero_limit w φ l₁ l₂ n x z)
  simpa only [Function.comp_def, Complex.div_ofReal_re, Complex.sub_re, Complex.zero_re] using h

theorem egbFixedChargeAGibbsGramForm_im_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).im /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp
    (egbFixedChargeAGibbsGramForm_first_zero_limit w φ l₁ l₂ n x z)
  simpa only [Function.comp_def, Complex.div_ofReal_im, Complex.sub_im, Complex.zero_im,
    egbFixedChargeACriticalGramForm_im_zero, sub_zero] using h

theorem egbFixedChargeAGibbsGramForm_negative_part_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    Tendsto (fun τ => max 0 (-(egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).re) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendsto_nhds.mp
    (egbFixedChargeAGibbsGramForm_re_first_zero_limit w φ l₁ l₂ n x z)) ε hε
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hk := egbFixedChargeACriticalGramForm_re_nonneg n x z
  have hm : 0 ≤ max 0 (-(egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).re) := le_max_left _ _
  have hb : max 0 (-(egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).re) ≤
      |(egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).re - (egbFixedChargeACriticalGramForm n x z).re| := by
    apply max_le (abs_nonneg _)
    have ha := neg_le_abs ((egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z).re -
      (egbFixedChargeACriticalGramForm n x z).re)
    linarith
  have hdiv := div_le_div_of_nonneg_right hb hd.le
  simp only [Real.dist_eq, sub_zero, abs_div, abs_of_pos hd] at hτ
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hm hd.le)]
  exact hdiv.trans_lt hτ

end GaloisForLFunctions.HTGeometry
