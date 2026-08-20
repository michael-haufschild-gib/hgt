import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A simple pole sitting on the left edge of a rectangle

The argument principle on a rectangle expresses the phase advance along the left edge through the
advance along the other three edges and the enclosed zero count.  When a zero sits *on* the left
edge the identity has to be corrected, and the correction is computed here in its cleanest form:
for `s₀ = c + iτ` with `T₁ < τ < T₂`, the combination

```text
∫_{T₁}^{T₂} Re (s - s₀)⁻¹|_{s = d+it} dt + ∫_c^d Im (s - s₀)⁻¹|_{s = x+iT₁} dx
  - ∫_c^d Im (s - s₀)⁻¹|_{s = x+iT₂} dx
```

is exactly `π` — half of the full turn `2π` an interior pole would produce.  The three integrals are
elementary arctangents and the identity `arctan u + arctan u⁻¹ = π/2` collapses their sum.
-/

open Complex intervalIntegral

noncomputable section

namespace RHTower

/-- **A simple pole on the left edge contributes exactly `π` to the three remaining edges.**
For `s₀ = c + iτ` with `T₁ < τ < T₂` and `c < d`, the argument-variation combination
`(right) + (bottom) − (top)` of `(s − s₀)⁻¹` over the rectangle `[c,d]×[T₁,T₂]` equals `π`:
half a turn, the pole sitting on the boundary. -/
theorem simplePole_three_edge_variation {c d τ T₁ T₂ : ℝ} (hcd : c < d)
    (h1 : T₁ < τ) (h2 : τ < T₂) :
    (∫ t in T₁..T₂, ((((d : ℂ) + (t : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).re)
      + (∫ x in c..d, ((((x : ℂ) + (T₁ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).im)
      - (∫ x in c..d, ((((x : ℂ) + (T₂ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).im)
      = Real.pi := by
  set a : ℝ := d - c with ha
  have hapos : 0 < a := by simp only [ha]; linarith
  set p : ℝ := τ - T₁ with hp
  have hppos : 0 < p := by simp only [hp]; linarith
  set q : ℝ := T₂ - τ with hq
  have hqpos : 0 < q := by simp only [hq]; linarith
  -- the right edge
  have hright : (∫ t in T₁..T₂, ((((d : ℂ) + (t : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).re)
      = Real.arctan (q / a) + Real.arctan (p / a) := by
    have hpt : ∀ t : ℝ,
        ((((d : ℂ) + (t : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).re
          = a / (a ^ 2 + (t - τ) ^ 2) := by
      intro t
      rw [Complex.inv_re]
      have hre : (((d : ℂ) + (t : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I))).re = a := by
        simp [ha]
      have hns : Complex.normSq (((d : ℂ) + (t : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))
          = a ^ 2 + (t - τ) ^ 2 := by
        rw [Complex.normSq_apply]
        simp [ha]
        ring
      rw [hre, hns]
    simp_rw [hpt]
    rw [show (fun t : ℝ => a / (a ^ 2 + (t - τ) ^ 2))
        = (fun t : ℝ => (fun u : ℝ => a / (a ^ 2 + u ^ 2)) (t - τ)) from rfl,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => a / (a ^ 2 + u ^ 2)) τ,
      integral_div_sq_add_sq]
    have : (T₁ - τ) / a = -(p / a) := by simp only [hp]; ring_nf
    rw [this, Real.arctan_neg]
    have : (T₂ - τ) / a = q / a := by simp only [hq]
    rw [this]
    ring
  -- the bottom edge
  have hbot : (∫ x in c..d, ((((x : ℂ) + (T₁ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).im)
      = Real.arctan (a / p) := by
    have hpt : ∀ x : ℝ,
        ((((x : ℂ) + (T₁ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).im
          = p / (p ^ 2 + (x - c) ^ 2) := by
      intro x
      rw [Complex.inv_im]
      have him : (((x : ℂ) + (T₁ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I))).im = -p := by
        simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, hp]
        ring
      have hns : Complex.normSq (((x : ℂ) + (T₁ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))
          = p ^ 2 + (x - c) ^ 2 := by
        rw [Complex.normSq_apply]
        simp [hp]
        ring
      rw [him, hns]
      ring
    simp_rw [hpt]
    rw [show (fun x : ℝ => p / (p ^ 2 + (x - c) ^ 2))
        = (fun x : ℝ => (fun u : ℝ => p / (p ^ 2 + u ^ 2)) (x - c)) from rfl,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => p / (p ^ 2 + u ^ 2)) c,
      integral_div_sq_add_sq]
    have h0 : (c - c) / p = 0 := by simp
    have h1' : (d - c) / p = a / p := by simp only [ha]
    rw [h0, h1', Real.arctan_zero, sub_zero]
  -- the top edge
  have htop : (∫ x in c..d, ((((x : ℂ) + (T₂ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).im)
      = -Real.arctan (a / q) := by
    have hpt : ∀ x : ℝ,
        ((((x : ℂ) + (T₂ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))⁻¹).im
          = -(q / (q ^ 2 + (x - c) ^ 2)) := by
      intro x
      rw [Complex.inv_im]
      have him : (((x : ℂ) + (T₂ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I))).im = q := by
        simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, hq]
        ring
      have hns : Complex.normSq (((x : ℂ) + (T₂ : ℂ) * I) - (((c : ℂ) + (τ : ℂ) * I)))
          = q ^ 2 + (x - c) ^ 2 := by
        rw [Complex.normSq_apply]
        simp [hq]
        ring
      rw [him, hns, neg_div]
    simp_rw [hpt]
    rw [intervalIntegral.integral_neg]
    congr 1
    rw [show (fun x : ℝ => q / (q ^ 2 + (x - c) ^ 2))
        = (fun x : ℝ => (fun u : ℝ => q / (q ^ 2 + u ^ 2)) (x - c)) from rfl,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => q / (q ^ 2 + u ^ 2)) c,
      integral_div_sq_add_sq]
    have h0 : (c - c) / q = 0 := by simp
    have h1' : (d - c) / q = a / q := by simp only [ha]
    rw [h0, h1', Real.arctan_zero, sub_zero]
  rw [hright, hbot, htop]
  have hpa : Real.arctan (a / p) = Real.pi / 2 - Real.arctan (p / a) := by
    have : a / p = (p / a)⁻¹ := by
      field_simp
    rw [this, Real.arctan_inv_of_pos (by positivity)]
  have hqa : Real.arctan (a / q) = Real.pi / 2 - Real.arctan (q / a) := by
    have : a / q = (q / a)⁻¹ := by
      field_simp
    rw [this, Real.arctan_inv_of_pos (by positivity)]
  rw [hpa, hqa]
  ring

end RHTower

end
