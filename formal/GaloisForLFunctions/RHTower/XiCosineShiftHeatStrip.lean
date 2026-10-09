import GaloisForLFunctions.RHTower.DeBruijnNewmanCosineShift
import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound

/-!
# The de Bruijn–Newman constant of the cosine family

For `h > 0` put `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2 = cos(hD)Ξ` and let
`A_{h,t}(z) = (H_t(z + ih) + H_t(z − ih))/2` be its heat deformation (`riemannHeat`).

* `cosineShift_zeros_im_sq_le`: every zero of `A_h` has `(Im z)² ≤ max(1/4 − h², 0)`. Every zero
  of `Ξ` has `(Im z)² < 1/4`, and averaging the two vertical shifts by `±ih` contracts the zero strip
  (de Bruijn's strip shrinking, `SuperExpKernel.zeros_mul_cosh`).
* `cosineShift_heat_zeros_real`: for every `t > 0` with `1/4 − h² ≤ 2t`, all zeros of `A_{h,t}` are
  real (de Bruijn's heat contraction).

With `exists_cosineShift_negHeat_zero_im_neg` (non-real zeros at every negative heat time), the
de Bruijn–Newman constant of `A_h` lies in `[0, max(1/4 − h², 0)/2]` for every `h > 0`,
unconditionally. At `h = 0` this is de Bruijn's `Λ ≤ 1/8` in this normalization, and for `h ≥ ½`
both bounds are `0`.
-/

open Complex

namespace RHTower.DeBruijn

noncomputable section

/-- The cosine-damped kernel `Φ(x) cosh(hx)`. -/
theorem riemannKernel_mul_cosh_superExp (h : ℝ) :
    SuperExpKernel fun x => riemannKernelReal x * Real.cosh (h * x) := by
  have := riemannKernel_superExp.mul_cosh_pow h 1
  simpa using this

/-- `A_h` is the transform of `Φ(x) cosh(hx)`. -/
theorem cosTransform_riemannKernel_mul_cosh (h : ℝ) (z : ℂ) :
    cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) z =
      (XiC (z + h * I) + XiC (z - h * I)) / 2 := by
  have e := riemannKernel_superExp.cosTransform_add_shift h z
  rw [cosTransform_riemannKernel, cosTransform_riemannKernel] at e
  have hX : ∀ w : ℂ, xi (1 / 2 + I * w) = XiC w := fun w => by rw [XiC, mul_comm]
  rw [hX, hX] at e
  linear_combination (-1 / 2 : ℂ) * e

/-- **Strip shrinking.** Every zero of `cos(hD)Ξ` has `(Im z)² ≤ max(1/4 − h², 0)`. -/
theorem cosineShift_zeros_im_sq_le {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0) :
    z.im ^ 2 ≤ max (1 / 4 - h ^ 2) 0 := by
  rw [← cosTransform_riemannKernel_mul_cosh] at hz
  exact riemannKernel_superExp.zeros_mul_cosh (by norm_num) riemannKernel_zeros_im_sq_le hh z hz

/-- The heat deformation of `A_h` is the transform of `Φ(x) cosh(hx) e^{tx²}`. -/
theorem cosTransform_heat_cosh (h t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x) * Real.exp (t * x ^ 2)) z =
      (riemannHeat t (z + h * I) + riemannHeat t (z - h * I)) / 2 := by
  have e := (riemannKernel_superExp.mul_exp_sq ht).cosTransform_add_shift h z
  unfold riemannHeat
  have hfun : (fun x => riemannKernelReal x * Real.cosh (h * x) * Real.exp (t * x ^ 2)) =
      fun x => riemannKernelReal x * Real.exp (t * x ^ 2) * Real.cosh (h * x) := by
    funext x; ring
  rw [hfun]
  linear_combination (-1 / 2 : ℂ) * e

/-- **De Bruijn's bound for the cosine family.** For `h > 0` and every heat time `t > 0` with
`1/4 − h² ≤ 2t`, all zeros of `(H_t(z + ih) + H_t(z − ih))/2` are real. -/
theorem cosineShift_heat_zeros_real {h t : ℝ} (hh : 0 < h) (ht0 : 0 < t)
    (ht : 1 / 4 - h ^ 2 ≤ 2 * t) {z : ℂ}
    (hz : (riemannHeat t (z + h * I) + riemannHeat t (z - h * I)) / 2 = 0) : z.im = 0 := by
  rw [← cosTransform_heat_cosh h t ht0.le] at hz
  have hzeros : ∀ w, cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) w = 0 →
      w.im ^ 2 ≤ max (1 / 4 - h ^ 2) 0 := fun w hw =>
    riemannKernel_superExp.zeros_mul_cosh (by norm_num) riemannKernel_zeros_im_sq_le hh w hw
  exact cosTransform_heat_zeros_real (riemannKernel_mul_cosh_superExp h) hzeros
    (max_le ht (by linarith)) ht0 z hz

/-- **The de Bruijn–Newman constant of `cos(hD)Ξ` lies in `[0, max(1/4 − h², 0)/2]`.** Non-real
zeros exist at every negative heat time, and only real zeros remain from heat time
`max(1/4 − h², 0)/2` on (for `t > 0`). -/
theorem cosineShift_deBruijnNewman_bounds {h : ℝ} (hh : 0 < h) :
    (∀ τ : ℝ, 0 < τ → ∃ z : ℂ,
        riemannHeat (-τ) (z + h * I) + riemannHeat (-τ) (z - h * I) = 0 ∧ z.im < 0) ∧
      ∀ t : ℝ, 0 < t → max (1 / 4 - h ^ 2) 0 ≤ 2 * t → ∀ z : ℂ,
        (riemannHeat t (z + h * I) + riemannHeat t (z - h * I)) / 2 = 0 → z.im = 0 := by
  refine ⟨fun τ hτ => ?_, fun t ht0 ht z hz =>
    cosineShift_heat_zeros_real hh ht0 ((le_max_left _ _).trans ht) hz⟩
  obtain ⟨z, hz, him, -⟩ := exists_cosineShift_negHeat_zero_im_neg hτ hh 0
  exact ⟨z, hz, him⟩

end

end RHTower.DeBruijn
