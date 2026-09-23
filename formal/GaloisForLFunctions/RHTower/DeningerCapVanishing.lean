import GaloisForLFunctions.RHTower.DeningerPoissonFourierReflection

/-!
# Members of Meyer's space vanish to second order at the origin

An even Schwartz function has vanishing derivative at the origin, so a member of Meyer's space —
which also vanishes there — is bounded by a constant times `x²` everywhere: two applications of the
mean value inequality, with the second derivative bounded by a Schwartz seminorm.

This is the estimate that pushes the Mellin transform of a member of Meyer's space past the
imaginary axis: it converges on `Re s > −2`, which is what makes a vertical line to the left of the
critical strip available.

* `deriv_zero_of_even_schwartzMap` : an even Schwartz function has vanishing derivative at
  the origin.
* `norm_le_seminorm_mul_sq` : **`‖f x‖ ≤ p₀,₀(f'')·x²`** for such an `f`.
-/

open scoped Real SchwartzMap
open Complex GaloisForLFunctions

noncomputable section

namespace RHTower

theorem deriv_zero_of_even_schwartzMap {f : 𝓢(ℝ, ℂ)} (hf : ∀ x : ℝ, f (-x) = f x) :
    deriv (f : ℝ → ℂ) 0 = 0 := by
  have h := deriv_neg_of_even_schwartz hf 0
  rw [neg_zero] at h
  have h2 : deriv (f : ℝ → ℂ) 0 + deriv (f : ℝ → ℂ) 0 = 0 := by
    rw [h] at *
    linear_combination h
  have h3 : (2 : ℂ) * deriv (f : ℝ → ℂ) 0 = 0 := by
    linear_combination h2
  have h4 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_eq_zero.mp h3).resolve_left h4

theorem abs_le_abs_of_mem_uIcc {x y : ℝ} (hy : y ∈ Set.uIcc (0 : ℝ) x) : |y| ≤ |x| := by
  rcases abs_cases x with hx | hx
  · have hmem : y ∈ Set.Icc (0 : ℝ) x := by
      rwa [Set.uIcc_of_le hx.2] at hy
    rw [abs_of_nonneg hmem.1, hx.1]
    exact hmem.2
  · have hmem : y ∈ Set.Icc x (0 : ℝ) := by
      rwa [Set.uIcc_of_ge hx.2.le] at hy
    rw [abs_of_nonpos hmem.2, hx.1]
    linarith [hmem.1]

/-- **A member of Meyer's space vanishes to second order at the origin.** -/
theorem norm_le_seminorm_mul_sq {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x) (h0 : f 0 = 0)
    (x : ℝ) :
    ‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 (derivSCLM (derivSCLM f)) * x ^ (2 : ℕ) := by
  set M : ℝ := SchwartzMap.seminorm ℂ 0 0 (derivSCLM (derivSCLM f)) with hM
  have hMnn : 0 ≤ M := apply_nonneg _ _
  have hderiv2 : ∀ y : ℝ, ‖deriv (derivSCLM f : ℝ → ℂ) y‖ ≤ M := by
    intro y
    have hval : deriv (derivSCLM f : ℝ → ℂ) y = derivSCLM (derivSCLM f) y := by
      rw [derivSCLM_apply]
    rw [hval]
    exact SchwartzMap.norm_le_seminorm ℂ _ y
  have hderivAt : ∀ y : ℝ, HasDerivAt (derivSCLM f : ℝ → ℂ)
      (deriv (derivSCLM f : ℝ → ℂ) y) y := fun y => (derivSCLM f).hasDerivAt y
  have hstep1 : ∀ y : ℝ, ‖derivSCLM f y‖ ≤ M * |y| := by
    intro y
    have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := (derivSCLM f : ℝ → ℂ)) (f' := fun z => deriv (derivSCLM f : ℝ → ℂ) z)
      (s := Set.uIcc (0 : ℝ) y) (C := M)
      (fun z _ => ((hderivAt z).hasDerivWithinAt))
      (fun z _ => hderiv2 z) (convex_uIcc 0 y) Set.left_mem_uIcc Set.right_mem_uIcc
    have hzero : derivSCLM f 0 = 0 := by
      rw [derivSCLM_apply]
      exact deriv_zero_of_even_schwartzMap he
    rw [hzero, sub_zero, sub_zero] at hbound
    have habs : ‖y‖ = |y| := Real.norm_eq_abs y
    rw [habs] at hbound
    exact hbound
  have hderivAtf : ∀ y : ℝ, HasDerivAt (f : ℝ → ℂ) (derivSCLM f y) y := by
    intro y
    have hval : derivSCLM f y = deriv (f : ℝ → ℂ) y := by
      rw [derivSCLM_apply]
    rw [hval]
    exact f.hasDerivAt y
  have hbound2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := (f : ℝ → ℂ)) (f' := fun z => derivSCLM f z)
    (s := Set.uIcc (0 : ℝ) x) (C := M * |x|)
    (fun z _ => ((hderivAtf z).hasDerivWithinAt))
    (fun z hz => le_trans (hstep1 z)
      (mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_uIcc hz) hMnn))
    (convex_uIcc 0 x) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at hbound2
  have hsq : M * |x| * |x| = M * x ^ (2 : ℕ) := by
    rw [mul_assoc, abs_mul_abs_self]
    ring
  rw [hsq] at hbound2
  exact hbound2

end RHTower

end
