import GaloisForLFunctions.RHTower.Sieve.PerronCompareSharp

/-!
# The comparison kernel at low frequency
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **All three branches of the comparison kernel.** -/
theorem norm_perronCompareKernel_le_min3 {x h h₁ t : ℝ} (hx : 0 < x) (hh : 0 < h) (hh₁ : 0 < h₁)
    (hle : h ≤ h₁) (ht : t ≠ 0) :
    ‖perronCompareKernel x h h₁ t‖
      ≤ min (min (2 * h) (2 * |t| * h * h₁ / x)) (4 * (x + h₁) / |t|) :=
  le_min (le_min (norm_perronCompareKernel_le_length hx hh hh₁ t)
      (norm_perronCompareKernel_le_sharp hx hh hh₁ hle))
    (norm_perronCompareKernel_le_div hx hh hh₁ hle ht)

/-- **The comparison kernel is uniformly small below the transition height.**  For
`|t| ≤ δ·x/h₁` the two windows agree to within `2hδ`: this is the statement that the window
comparison of Lemma 3.1 sees nothing below height `x/h₁`. -/
theorem norm_perronCompareKernel_le_of_low {x h h₁ t δ : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hh₁ : 0 < h₁) (hle : h ≤ h₁) (hlow : |t| ≤ δ * x / h₁) :
    ‖perronCompareKernel x h h₁ t‖ ≤ 2 * h * δ := by
  refine le_trans (norm_perronCompareKernel_le_sharp hx hh hh₁ hle) ?_
  have hstep : 2 * |t| * h * h₁ / x ≤ 2 * (δ * x / h₁) * h * h₁ / x := by
    have hnum : 2 * |t| * h * h₁ ≤ 2 * (δ * x / h₁) * h * h₁ := by
      have h1 : 2 * |t| ≤ 2 * (δ * x / h₁) := by linarith
      have h2 : (0 : ℝ) ≤ h * h₁ := by positivity
      nlinarith [h1, h2]
    exact div_le_div_of_nonneg_right hnum hx.le
  refine le_trans hstep (le_of_eq ?_)
  field_simp

end

end RHTower.Sieve
