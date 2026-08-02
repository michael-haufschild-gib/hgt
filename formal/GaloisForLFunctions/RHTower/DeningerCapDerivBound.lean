import GaloisForLFunctions.RHTower.DeningerFourierWeight

/-!
# Derivatives from the Fourier side

The Fourier transform turns differentiation into multiplication by `2πiξ`, so the supremum of the
`n`-th derivative of a Schwartz function is bounded by the `L¹` norm of `(2πξ)^n` times its Fourier
transform, hence by two polynomially weighted supremum seminorms of the Fourier transform:

`p_{0,n}(f) ≤ (2π)^n · π · (p_{n,0}(𝓕f) + p_{n+2,0}(𝓕f))`.

For a member of Meyer's space the right-hand side is controlled by the radial data of its Poisson
sum, so the derivatives at the origin — the one place the dilation picture cannot see — are
controlled as well.

* `norm_le_integral_norm_fourier` : Fourier inversion as a supremum bound.
* `norm_fourier_iterate_derivSCLM` : the multiplier `(2π|ξ|)^n`.
* `seminorm_zero_deriv_le_fourier` : **`p_{0,n}(f)` bounded by two seminorms of `𝓕f`.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Two elementary Fourier bounds -/

/-- A Fourier transform is bounded by the `L¹` norm. -/
theorem norm_fourier_le_integral (g : 𝓢(ℝ, ℂ)) (w : ℝ) :
    ‖𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) w‖ ≤ ∫ v : ℝ, ‖(g : ℝ → ℂ) v‖ := by
  rw [Real.fourier_eq]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ‖(Real.fourierChar (-(inner ℝ v w)) : Circle) • (g : ℝ → ℂ) v‖ = ‖(g : ℝ → ℂ) v‖
  exact Circle.norm_smul _ _

/-- **Fourier inversion as a supremum bound**: a Schwartz function is bounded by the `L¹` norm of
its Fourier transform. -/
theorem norm_le_integral_norm_fourier (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖g x‖ ≤ ∫ ξ : ℝ, ‖𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ := by
  have hFint : Integrable (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := (fourierSCLM g).integrable
  have hinv : 𝓕⁻ (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    g.continuous.fourierInv_fourier_eq g.integrable hFint
  have hval : ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = 𝓕 (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) (-x) := by
    rw [← Real.fourierInv_eq_fourier_neg, hinv]
  have hcoe : ((fourierSCLM g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := rfl
  have hbound := norm_fourier_le_integral (fourierSCLM g) (-x)
  rw [hcoe] at hbound
  show ‖((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ≤ _
  rw [hval]
  exact hbound

/-! ## The multiplier of a derivative -/

/-- The Fourier transform of a derivative is `2πiξ` times the Fourier transform. -/
theorem norm_fourier_derivSCLM (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ‖𝓕 ((derivSCLM f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖
      = 2 * π * |ξ| * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ := by
  have hcoe : ((derivSCLM f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    funext x
    rw [derivSCLM_apply]
  have hint : Integrable (deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := by
    rw [← hcoe]
    exact (derivSCLM f).integrable
  have h := Real.fourier_deriv f.integrable f.differentiable hint
  rw [hcoe, h]
  show ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ)) • 𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ = _
  rw [norm_smul]
  congr 1
  have hpi : (0 : ℝ) ≤ π := Real.pi_pos.le
  simp [abs_of_nonneg hpi]

/-- The Fourier transform of an iterated derivative carries the multiplier `(2π|ξ|)^n`. -/
theorem norm_fourier_iterate_derivSCLM (n : ℕ) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ‖𝓕 (((derivSCLM^[n]) f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖
      = (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ := by
  induction n generalizing f with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (derivSCLM f), norm_fourier_derivSCLM f ξ]
    ring

/-! ## The supremum of a derivative -/

/-- The supremum of an iterated derivative is bounded by a weighted `L¹` norm of the Fourier
transform. -/
theorem norm_iterate_derivSCLM_le (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖((derivSCLM^[n]) f) x‖
      ≤ ∫ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ := by
  have hbound := norm_le_integral_norm_fourier ((derivSCLM^[n]) f) x
  have hcongr : (∫ ξ : ℝ, ‖𝓕 ((((derivSCLM^[n]) f) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖)
      = ∫ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
      norm_fourier_iterate_derivSCLM n f ξ)
  rw [hcongr] at hbound
  exact hbound

/-- The weighted `L¹` norm of a Fourier transform is bounded by two of its seminorms. -/
theorem integral_pow_norm_fourier_le (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖)
      ≤ (2 * π) ^ n * π * (SchwartzMap.seminorm ℂ n 0 (fourierSCLM f)
          + SchwartzMap.seminorm ℂ (n + 2) 0 (fourierSCLM f)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set F : 𝓢(ℝ, ℂ) := fourierSCLM f with hF
  set M : ℝ := SchwartzMap.seminorm ℂ n 0 F + SchwartzMap.seminorm ℂ (n + 2) 0 F with hM
  have hFcoe : ∀ ξ : ℝ, 𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ = F ξ := fun ξ => rfl
  have hpt : ∀ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖
      ≤ (2 * π) ^ n * M * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have hn := SchwartzMap.norm_pow_mul_le_seminorm ℂ F n ξ
    have hn2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ F (n + 2) ξ
    have habs : ‖ξ‖ = |ξ| := Real.norm_eq_abs ξ
    rw [habs] at hn hn2
    have hsplit : |ξ| ^ (n + 2) = |ξ| ^ n * ξ ^ 2 := by
      rw [pow_add, sq_abs]
    rw [hsplit] at hn2
    have hkey : |ξ| ^ n * ‖F ξ‖ * (1 + ξ ^ 2) ≤ M := by
      have hnn : 0 ≤ |ξ| ^ n * ‖F ξ‖ := by positivity
      nlinarith [hn, hn2]
    have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    have hstep : |ξ| ^ n * ‖F ξ‖ ≤ M * (1 + ξ ^ 2)⁻¹ := by
      calc |ξ| ^ n * ‖F ξ‖ = |ξ| ^ n * ‖F ξ‖ * (1 + ξ ^ 2) * (1 + ξ ^ 2)⁻¹ := by
            field_simp
        _ ≤ M * (1 + ξ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hkey (by positivity)
    calc (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖
        = (2 * π) ^ n * (|ξ| ^ n * ‖F ξ‖) := by
          rw [hFcoe ξ, mul_pow]
          ring
      _ ≤ (2 * π) ^ n * (M * (1 + ξ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (2 * π) ^ n * M * (1 + ξ ^ 2)⁻¹ := by ring
  have hmaj : Integrable (fun ξ : ℝ => (2 * π) ^ n * M * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ξ : ℝ => by positivity) hmaj
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hmono
  calc (∫ ξ : ℝ, (2 * π * |ξ|) ^ n * ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖)
      ≤ (2 * π) ^ n * M * π := hmono
    _ = (2 * π) ^ n * π * M := by ring

/-- **The supremum seminorms of the derivatives are bounded by two weighted supremum seminorms of
the Fourier transform.** -/
theorem seminorm_zero_deriv_le_fourier (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.seminorm ℂ 0 n f
      ≤ (2 * π) ^ n * π * (SchwartzMap.seminorm ℂ n 0 (fourierSCLM f)
          + SchwartzMap.seminorm ℂ (n + 2) 0 (fourierSCLM f)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hiter : ∀ (m : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ),
      iteratedDeriv m ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ((derivSCLM^[m]) g) x := by
    intro m
    induction m with
    | zero =>
      intro g x
      rw [iteratedDeriv_zero, Function.iterate_zero_apply]
    | succ m ih =>
      intro g x
      have hcoe : deriv ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = ((derivSCLM g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
        funext y
        rw [derivSCLM_apply]
      rw [iteratedDeriv_succ', hcoe, ih (derivSCLM g) x, Function.iterate_succ_apply]
  have hnn : 0 ≤ (2 * π) ^ n * π * (SchwartzMap.seminorm ℂ n 0 (fourierSCLM f)
      + SchwartzMap.seminorm ℂ (n + 2) 0 (fourierSCLM f)) := by
    have h1 : 0 ≤ SchwartzMap.seminorm ℂ n 0 (fourierSCLM f) := apply_nonneg _ _
    have h2 : 0 ≤ SchwartzMap.seminorm ℂ (n + 2) 0 (fourierSCLM f) := apply_nonneg _ _
    have h3 : 0 ≤ (2 * π) ^ n * π := by positivity
    exact mul_nonneg h3 (by linarith)
  refine SchwartzMap.seminorm_le_bound' ℂ 0 n f hnn fun x => ?_
  rw [pow_zero, one_mul, hiter n f x]
  exact le_trans (norm_iterate_derivSCLM_le n f x) (integral_pow_norm_fourier_le n f)

end RHTower

end
