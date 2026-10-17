import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Translation-averaged densities are blind to the depth of a zero

Let `f` be entire with `|f(x+iy)| ≤ C_K (1+x²)⁻¹` on every horizontal strip `|y| ≤ K`.  For any
point `ρ = β + iγ` and scale `L > 0`,
`∫ f((γ - τ + i(β - ½)) L) dτ = L⁻¹ ∫ f(x) dx`,
independently of `β`: the horizontal contour shift by `(β - ½) L` costs nothing, in either
direction.  Translation-averaged one-level densities therefore cannot see whether a zero lies on
the critical line.
-/

noncomputable section
namespace RHTower

open Complex MeasureTheory

/-- A horizontal shift of the contour, up or down, leaves the integral unchanged. -/
theorem integral_shift_of_strip_decay {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hdecay : ∀ K : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ K → ‖f z‖ ≤ C*(1+z.re^(2:ℕ))⁻¹) (c : ℝ) :
    (∫ x : ℝ, f ((x : ℂ)+(c : ℂ)*I))=∫ x : ℝ, f (x : ℂ) := by
  obtain ⟨C, hC⟩ := hdecay |c|
  rcases le_total 0 c with hc | hc
  · exact integral_horizontal_shift_of_upper_inv_one_add_sq_decay hc
      (fun z _ _ => hf z) (fun z h0 h1 => hC z (by rw [abs_le]; constructor <;> linarith [le_abs_self c]))
  · set G : ℂ → ℂ := fun z => f (z+(c : ℂ)*I) with hG
    have hGd : Differentiable ℂ G := hf.comp (differentiable_id.add_const _)
    have hcc : 0≤-c := by linarith
    have hGb : ∀ z : ℂ, 0≤z.im → z.im≤-c → ‖G z‖≤C*(1+z.re^(2:ℕ))⁻¹ := by
      intro z h0 h1
      have hz := hC (z+(c : ℂ)*I) (by
        simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        rw [abs_le, abs_of_nonpos hc]
        constructor <;> linarith)
      simpa [hG] using hz
    have hs := integral_horizontal_shift_of_upper_inv_one_add_sq_decay hcc (fun z _ _ => hGd z) hGb
    have h1 : (fun x : ℝ => G ((x : ℂ)+((-c : ℝ) : ℂ)*I))=fun x : ℝ => f (x : ℂ) := by
      funext x
      simp only [hG]
      congr 1
      push_cast
      ring
    rw [h1] at hs
    exact hs.symm

/-- **Depth blindness.**  For every `β, γ` and `L > 0`,
`∫ f((γ - τ + i(β - ½)) L) dτ = L⁻¹ ∫ f(x) dx`. -/
theorem integral_translationAveraged_depth_blind {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hdecay : ∀ K : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ K → ‖f z‖ ≤ C*(1+z.re^(2:ℕ))⁻¹)
    (β γ L : ℝ) (hL : 0<L) :
    (∫ τ : ℝ, f ((((γ-τ : ℝ) : ℂ)+((β-1/2 : ℝ) : ℂ)*I)*(L : ℂ)))=
      L⁻¹*∫ x : ℝ, f (x : ℂ) := by
  set g : ℝ → ℂ := fun u => f ((u : ℂ)+(((β-1/2)*L : ℝ) : ℂ)*I) with hg
  have hpt : (fun τ : ℝ => f ((((γ-τ : ℝ) : ℂ)+((β-1/2 : ℝ) : ℂ)*I)*(L : ℂ)))=
      fun τ : ℝ => (fun u : ℝ => g (u+γ*L)) ((-L)*τ) := by
    funext τ
    simp only [hg]
    congr 1
    push_cast
    ring
  rw [hpt, Measure.integral_comp_mul_left (fun u : ℝ => g (u+γ*L)) (-L),
    integral_add_right_eq_self g (γ*L), hg, integral_shift_of_strip_decay hf hdecay]
  rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hL), real_smul, ofReal_inv]

end RHTower
