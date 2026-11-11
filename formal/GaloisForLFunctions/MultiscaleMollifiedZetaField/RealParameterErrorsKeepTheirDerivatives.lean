import GaloisForLFunctions.HTGeometry.BoundedSolutionDerivative

/-!
# Recovering derivatives from uniform real-parameter errors

A short-interval Landau estimate transfers a small value bound to the first
and second derivatives when higher derivatives have polynomial bounds.
Two different step sizes avoid assuming a differentiated remainder formula.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Rescaling the unit-interval Landau estimate keeps the value and curvature
costs separate. -/
theorem abs_deriv_le_of_short_interval {f g q : ℝ → ℝ} {x h E M : ℝ}
    (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + h), HasDerivAt f (g y) y)
    (hg : ∀ y ∈ Icc x (x + h), HasDerivAt g (q y) y)
    (hq : ContinuousOn q (Icc x (x + h)))
    (hE : ∀ y ∈ Icc x (x + h), |f y| ≤ E)
    (hM : ∀ y ∈ Icc x (x + h), |q y| ≤ M) :
    |g x| ≤ 2 * E / h + M * h / 2 := by
  have hmem {s : ℝ} (hs : s ∈ Icc 0 1) : x + h * s ∈ Icc x (x + h) := by
    constructor <;> nlinarith only [hs.1, hs.2, hh]
  have hF (s : ℝ) (hs : s ∈ Icc 0 1) :
      HasDerivAt (fun z => f (x + h * z)) (h * g (x + h * s)) s := by
    have he := (hf _ (hmem hs)).comp s
      (((hasDerivAt_id s).const_mul h).const_add x)
    exact he.congr_deriv (by ring)
  have hG (s : ℝ) (hs : s ∈ Icc 0 1) :
      HasDerivAt (fun z => h * g (x + h * z)) (h ^ 2 * q (x + h * s)) s := by
    have he := ((hg _ (hmem hs)).comp s
      (((hasDerivAt_id s).const_mul h).const_add x)).const_mul h
    exact he.congr_deriv (by ring)
  have hQ : ContinuousOn (fun s => h ^ 2 * q (x + h * s)) (Icc 0 1) :=
    continuousOn_const.mul (hq.comp (by fun_prop) (fun _ hs => hmem hs))
  have hb := HTGeometry.abs_deriv_le_of_bounded (u := 0) (C := E) (M := h ^ 2 * M)
    (by simpa only [zero_add] using hF)
    (by simpa only [zero_add] using hG)
    (by simpa only [zero_add] using hQ)
    (fun s hs => hE _ (hmem (by simpa only [zero_add] using hs)))
    (fun s hs => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
      exact mul_le_mul_of_nonneg_left
        (hM _ (hmem (by simpa only [zero_add] using hs))) (sq_nonneg h))
  simp only [mul_zero, add_zero, abs_mul, abs_of_pos hh] at hb
  calc
    |g x| ≤ (2 * E + h ^ 2 * M / 2) / h :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hb)
    _ = 2 * E / h + M * h / 2 := by field_simp

/-- A smaller inner step first bounds the first derivative throughout the
outer interval; a second Landau estimate then bounds the second derivative. -/
theorem abs_second_deriv_le_of_two_steps {f g q r : ℝ → ℝ} {x h k E M₂ M₃ : ℝ}
    (hh : 0 < h) (hk : 0 < k)
    (hf : ∀ y ∈ Icc x (x + h + k), HasDerivAt f (g y) y)
    (hg : ∀ y ∈ Icc x (x + h + k), HasDerivAt g (q y) y)
    (hq : ∀ y ∈ Icc x (x + h + k), HasDerivAt q (r y) y)
    (hqc : ContinuousOn q (Icc x (x + h + k)))
    (hrc : ContinuousOn r (Icc x (x + h + k)))
    (hE : ∀ y ∈ Icc x (x + h + k), |f y| ≤ E)
    (hM₂ : ∀ y ∈ Icc x (x + h + k), |q y| ≤ M₂)
    (hM₃ : ∀ y ∈ Icc x (x + h + k), |r y| ≤ M₃) :
    |q x| ≤ 4 * E / (h * k) + M₂ * k / h + M₃ * h / 2 := by
  have hout : Icc x (x + h) ⊆ Icc x (x + h + k) :=
    Icc_subset_Icc_right (by linarith only [hk])
  have hfirst (y : ℝ) (hy : y ∈ Icc x (x + h)) :
      |g y| ≤ 2 * E / k + M₂ * k / 2 := by
    have hsub : Icc y (y + k) ⊆ Icc x (x + h + k) :=
      Icc_subset_Icc hy.1 (by linarith only [hy.2])
    exact abs_deriv_le_of_short_interval hk
      (fun z hz => hf z (hsub hz)) (fun z hz => hg z (hsub hz))
      (hqc.mono hsub) (fun z hz => hE z (hsub hz)) (fun z hz => hM₂ z (hsub hz))
  have hb := abs_deriv_le_of_short_interval hh
    (fun y hy => hg y (hout hy)) (fun y hy => hq y (hout hy))
    (hrc.mono hout) hfirst (fun y hy => hM₃ y (hout hy))
  refine hb.trans_eq ?_
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
