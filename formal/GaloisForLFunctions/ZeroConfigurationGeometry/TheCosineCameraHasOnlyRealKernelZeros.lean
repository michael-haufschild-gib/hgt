import GaloisForLFunctions.IncommensurableGaborPinching.CosineKernelAdditiveRigidity

/-!
# The cosine camera has only real kernel zeros

The proportion engine of `IncommensurableGaborPinching` uses the cosine window
`v*(s) = cos(2θs)` on `[−½, ½]`, `θ = λ/√2`, and its kernel `K(Δ) = ∫ v*(s) cos(2πΔs) ds`
(`mtKernelNum`). Two zero vectors at heights `γ, γ'` overlap through `K(γ − γ')`; for a tilted
point the gap is complex. Kernel design (question Q5 of the field) asks for windows whose
complexified kernel excludes tilted points next to real ones.

* **Closed form at complex frequency** (`cosineWindowTransform_closed_form`).
  `((πζ)² − θ²) K(ζ) = πζ sin(πζ) cos θ − θ sin θ cos(πζ)` for every `ζ ∈ ℂ`.
* **Only real zeros** (`im_eq_zero_of_cosineWindowTransform_eq_zero`). For `0 < θ < π/2` every
  complex zero of `K` is real. The zeros solve `z sin z = C cos z`, `z = πζ`, `C = θ tan θ > 0`,
  and for `z = u + iv` this forces `(u² + v²) sinh v cosh v = −C v |cos z|²`, impossible for
  `v ≠ 0` (`im_eq_zero_of_mul_sin_eq`).
* **Complex additive rigidity** (`no_complex_additive_zero_triple`). For `0 < θ < π/2` there are no
  complex `ζ₁, ζ₂` with `K(ζ₁) = K(ζ₂) = K(ζ₁ + ζ₂) = 0`: the complex question reduces to the real
  one, `mtKernel_no_additive_zero_triple`. This extends `mtKernel_additive_zero_triple_iff` to complex
  arguments over the range `0 < λ < π/√2`, which contains the shape parameter `4/3`.

So under the cosine camera a tilted point is orthogonal to no real point, and no three points, real
or tilted, are mutually orthogonal through additive gaps.
-/

open Complex MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open IncommensurableGaborPinching

/-- **Roots of `z sin z = C cos z` with `C > 0` are real.** -/
theorem im_eq_zero_of_mul_sin_eq {C : ℝ} (hC : 0 < C) {z : ℂ}
    (hz : z * Complex.sin z = C * Complex.cos z) : z.im = 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, z = u + v * I := ⟨z.re, z.im, (Complex.re_add_im z).symm⟩
  rw [Complex.sin_add_mul_I, Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, mul_one, zero_add, zero_sub] at hre him
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  -- the imaginary part of `|z|² sin z · conj(cos z)`
  have hsc := Real.sin_sq_add_cos_sq u
  have hT : (u ^ 2 + v ^ 2) * (Real.sinh v * Real.cosh v) +
      C * v * ((Real.cos u * Real.cosh v) ^ 2 + (Real.sin u * Real.sinh v) ^ 2) = 0 := by
    linear_combination (-(u * -(Real.sin u * Real.sinh v) + v * (Real.cos u * Real.cosh v))) * hre +
      (u * (Real.cos u * Real.cosh v) - v * -(Real.sin u * Real.sinh v)) * him -
      (u ^ 2 + v ^ 2) * Real.sinh v * Real.cosh v * hsc
  by_contra hv
  have hvs : 0 < v * Real.sinh v := by
    rcases lt_or_gt_of_ne hv with h | h
    · exact mul_pos_of_neg_of_neg h (Real.sinh_neg_iff.mpr h)
    · exact mul_pos h (Real.sinh_pos_iff.mpr h)
  have hch : 0 < Real.cosh v := Real.cosh_pos v
  have huv : 0 < u ^ 2 + v ^ 2 := by positivity
  have h1 : 0 < (u ^ 2 + v ^ 2) * (v * Real.sinh v) * Real.cosh v := by positivity
  have h2 : 0 ≤ C * v ^ 2 * ((Real.cos u * Real.cosh v) ^ 2 + (Real.sin u * Real.sinh v) ^ 2) := by
    positivity
  have h3 : v * ((u ^ 2 + v ^ 2) * (Real.sinh v * Real.cosh v) +
      C * v * ((Real.cos u * Real.cosh v) ^ 2 + (Real.sin u * Real.sinh v) ^ 2)) = 0 := by
    rw [hT, mul_zero]
  nlinarith [h1, h2, h3]

/-- The transform of the cosine window `cos(2θs)` on `[−½, ½]` at complex frequency `ζ`. -/
def cosineWindowTransform (θ : ℝ) (ζ : ℂ) : ℂ :=
  ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ((Real.cos (2 * θ * s) : ℝ) : ℂ) * Complex.cos (2 * π * ζ * s)

/-- **The closed form at complex frequency.** -/
theorem cosineWindowTransform_closed_form (θ : ℝ) (ζ : ℂ) :
    ((π * ζ) ^ 2 - θ ^ 2) * cosineWindowTransform θ ζ =
      π * ζ * Complex.sin (π * ζ) * Real.cos θ - θ * Real.sin θ * Complex.cos (π * ζ) := by
  set b : ℂ := 2 * π * ζ
  set G : ℂ → ℂ := fun w => b * Complex.sin (b * w) * Complex.cos (2 * θ * w) -
    2 * θ * Complex.cos (b * w) * Complex.sin (2 * θ * w)
  have hG : ∀ w : ℂ, HasDerivAt G ((b ^ 2 - 4 * θ ^ 2) * (Complex.cos (2 * θ * w) *
      Complex.cos (b * w))) w := by
    intro w
    have h1 := ((hasDerivAt_id' w).const_mul b).csin
    have h2 := ((hasDerivAt_id' w).const_mul (2 * (θ : ℂ))).ccos
    have h3 := ((hasDerivAt_id' w).const_mul b).ccos
    have h4 := ((hasDerivAt_id' w).const_mul (2 * (θ : ℂ))).csin
    exact (((h1.const_mul b).mul h2).sub ((h3.const_mul (2 * (θ : ℂ))).mul h4)).congr_deriv
      (by ring)
  have hGr : ∀ s : ℝ, HasDerivAt (fun s : ℝ => G s) ((b ^ 2 - 4 * θ ^ 2) *
      (((Real.cos (2 * θ * s) : ℝ) : ℂ) * Complex.cos (2 * π * ζ * s))) s := by
    intro s
    have e1 : Complex.cos (2 * (θ : ℂ) * s) = ((Real.cos (2 * θ * s) : ℝ) : ℂ) := by
      push_cast; ring_nf
    have e2 : Complex.cos (b * s) = Complex.cos (2 * π * ζ * s) := rfl
    have := (hG s).comp_ofReal
    rwa [e1, e2] at this
  have hint : IntervalIntegrable (fun s : ℝ => (b ^ 2 - 4 * θ ^ 2) *
      (((Real.cos (2 * θ * s) : ℝ) : ℂ) * Complex.cos (2 * π * ζ * s))) volume
      (-(1 : ℝ) / 2) (1 / 2) :=
    (by fun_prop : Continuous fun s : ℝ => (b ^ 2 - 4 * θ ^ 2) *
      (((Real.cos (2 * θ * s) : ℝ) : ℂ) * Complex.cos (2 * π * ζ * s))).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hGr s) hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have hval : G ((1 / 2 : ℝ) : ℂ) - G ((-(1 : ℝ) / 2 : ℝ) : ℂ) =
      4 * (π * ζ * Complex.sin (π * ζ) * Real.cos θ - θ * Real.sin θ * Complex.cos (π * ζ)) := by
    simp only [G, b]
    push_cast
    have e1 : 2 * (π : ℂ) * ζ * (1 / 2) = π * ζ := by ring
    have e2 : 2 * (π : ℂ) * ζ * (-1 / 2) = -(π * ζ) := by ring
    have e3 : 2 * (θ : ℂ) * (1 / 2) = θ := by ring
    have e4 : 2 * (θ : ℂ) * (-1 / 2) = -θ := by ring
    rw [e1, e2, e3, e4, Complex.sin_neg, Complex.cos_neg, Complex.sin_neg, Complex.cos_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [hval] at hftc
  rw [cosineWindowTransform]
  have hb : b ^ 2 - 4 * θ ^ 2 = 4 * ((π * ζ) ^ 2 - θ ^ 2) := by simp only [b]; ring
  rw [hb] at hftc
  linear_combination hftc / 4

/-- **The cosine camera has only real kernel zeros** for `0 < θ < π/2`. -/
theorem im_eq_zero_of_cosineWindowTransform_eq_zero {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < π / 2)
    {ζ : ℂ} (hζ : cosineWindowTransform θ ζ = 0) : ζ.im = 0 := by
  have hcf := cosineWindowTransform_closed_form θ ζ
  rw [hζ, mul_zero] at hcf
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ'⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hC : 0 < θ * Real.sin θ / Real.cos θ := by positivity
  have hc : ((Real.cos θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
  have hx : (π * ζ) * Complex.sin (π * ζ) * (Real.cos θ : ℂ) =
      (θ : ℂ) * (Real.sin θ : ℂ) * Complex.cos (π * ζ) := by linear_combination -hcf
  have hz : (π * ζ) * Complex.sin (π * ζ) =
      ((θ * Real.sin θ / Real.cos θ : ℝ) : ℂ) * Complex.cos (π * ζ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, div_mul_eq_mul_div, eq_div_iff hc]
    exact hx
  have him := im_eq_zero_of_mul_sin_eq hC hz
  rw [show (π * ζ).im = π * ζ.im by simp] at him
  exact (mul_eq_zero.mp him).resolve_left Real.pi_ne_zero

/-- On real frequencies the transform is the kernel numerator of `IncommensurableGaborPinching`. -/
theorem cosineWindowTransform_ofReal (lam Δ : ℝ) :
    cosineWindowTransform (Zeta23.ThmD.theta lam) Δ = (mtKernelNum lam Δ : ℂ) := by
  rw [cosineWindowTransform, mtKernelNum, ← intervalIntegral.integral_ofReal]
  congr 1 with s
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have harg : 2 * Zeta23.ThmD.theta lam * s = Real.sqrt 2 * lam * s := by
    rw [Zeta23.ThmD.theta]
    field_simp
    rw [hs2]; ring
  rw [harg, Zeta23.ThmD.vStar]
  push_cast; ring_nf

/-- **Complex additive rigidity of the cosine camera.** For `0 < θ < π/2` no two complex zeros of
the kernel have a zero sum. -/
theorem no_complex_additive_zero_triple {lam : ℝ} (hθ : 0 < Zeta23.ThmD.theta lam)
    (hθ' : Zeta23.ThmD.theta lam < π / 2) (ζ₁ ζ₂ : ℂ) :
    ¬ (cosineWindowTransform (Zeta23.ThmD.theta lam) ζ₁ = 0 ∧
      cosineWindowTransform (Zeta23.ThmD.theta lam) ζ₂ = 0 ∧
        cosineWindowTransform (Zeta23.ThmD.theta lam) (ζ₁ + ζ₂) = 0) := by
  rintro ⟨h1, h2, h3⟩
  have hr : ∀ ζ : ℂ, cosineWindowTransform (Zeta23.ThmD.theta lam) ζ = 0 →
      ζ = (ζ.re : ℂ) ∧ mtKernel lam ζ.re = 0 := fun ζ hζ => by
    have him := im_eq_zero_of_cosineWindowTransform_eq_zero hθ hθ' hζ
    have hζr : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    refine ⟨hζr, ?_⟩
    rw [hζr, cosineWindowTransform_ofReal] at hζ
    rw [mtKernel, Complex.ofReal_eq_zero.mp hζ, zero_div]
  have hsin : Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ≠ 0 :=
    (mul_pos hθ (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos]))).ne'
  obtain ⟨-, k1⟩ := hr ζ₁ h1
  obtain ⟨-, k2⟩ := hr ζ₂ h2
  obtain ⟨-, k3⟩ := hr (ζ₁ + ζ₂) h3
  rw [Complex.add_re] at k3
  exact mtKernel_no_additive_zero_triple hsin ζ₁.re ζ₂.re ⟨k1, k2, k3⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
