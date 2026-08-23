import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Exact hyperbolic profiles for dispersive equations

Derivative chain for `Q = sech²`, represented algebraically as `1 - tanh²`, and for `R = Q²`.
Every identity is a genuine `HasDerivAt` theorem over `ℝ`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

noncomputable def solitonT (x : ℝ) : ℝ := Real.tanh x

noncomputable def solitonQ (x : ℝ) : ℝ := 1 - solitonT x ^ 2

noncomputable def solitonQ1 (x : ℝ) : ℝ := -2 * solitonT x * solitonQ x

noncomputable def solitonQ2 (x : ℝ) : ℝ := 4 * solitonQ x - 6 * solitonQ x ^ 2

noncomputable def solitonQ3 (x : ℝ) : ℝ :=
  -8 * solitonT x * solitonQ x + 24 * solitonT x * solitonQ x ^ 2

noncomputable def solitonQ4 (x : ℝ) : ℝ :=
  16 * solitonQ x - 120 * solitonQ x ^ 2 + 120 * solitonQ x ^ 3

noncomputable def solitonQ5 (x : ℝ) : ℝ :=
  -32 * solitonT x * solitonQ x + 480 * solitonT x * solitonQ x ^ 2
    - 720 * solitonT x * solitonQ x ^ 3

noncomputable def solitonR (x : ℝ) : ℝ := solitonQ x ^ 2

noncomputable def solitonR1 (x : ℝ) : ℝ := -4 * solitonT x * solitonQ x ^ 2

noncomputable def solitonR2 (x : ℝ) : ℝ := 16 * solitonQ x ^ 2 - 20 * solitonQ x ^ 3

noncomputable def solitonR3 (x : ℝ) : ℝ :=
  -64 * solitonT x * solitonQ x ^ 2 + 120 * solitonT x * solitonQ x ^ 3

noncomputable def solitonR4 (x : ℝ) : ℝ :=
  256 * solitonQ x ^ 2 - 1040 * solitonQ x ^ 3 + 840 * solitonQ x ^ 4

noncomputable def solitonR5 (x : ℝ) : ℝ :=
  -1024 * solitonT x * solitonQ x ^ 2 + 6240 * solitonT x * solitonQ x ^ 3
    - 6720 * solitonT x * solitonQ x ^ 4

theorem solitonQ_eq_inv_cosh_sq (x : ℝ) : solitonQ x = 1 / Real.cosh x ^ 2 := by
  exact HTGeometry.one_sub_tanh_sq x

theorem hasDerivAt_solitonT (x : ℝ) : HasDerivAt solitonT (solitonQ x) x := by
  have h := HTGeometry.hasDerivAt_tanh x
  rw [← HTGeometry.one_sub_tanh_sq x] at h
  change HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x
  exact h

theorem hasDerivAt_solitonQ (x : ℝ) : HasDerivAt solitonQ (solitonQ1 x) x := by
  have hT := hasDerivAt_solitonT x
  have h := (hasDerivAt_const x (1 : ℝ)).sub (hT.pow 2)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ]
  · simp [solitonQ, solitonQ1, solitonT]

theorem hasDerivAt_solitonQ1 (x : ℝ) : HasDerivAt solitonQ1 (solitonQ2 x) x := by
  have hT := hasDerivAt_solitonT x
  have hQ := hasDerivAt_solitonQ x
  have h := (hT.mul hQ).const_mul (-2 : ℝ)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ1]
    ring
  · simp [solitonQ, solitonQ1, solitonQ2, solitonT]
    ring

theorem hasDerivAt_solitonQ2 (x : ℝ) : HasDerivAt solitonQ2 (solitonQ3 x) x := by
  have hQ := hasDerivAt_solitonQ x
  have h := (hQ.const_mul (4 : ℝ)).sub ((hQ.pow 2).const_mul (6 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ2]
  · simp [solitonQ, solitonQ1, solitonQ3, solitonT]
    ring

theorem hasDerivAt_solitonQ3 (x : ℝ) : HasDerivAt solitonQ3 (solitonQ4 x) x := by
  have hT := hasDerivAt_solitonT x
  have hQ := hasDerivAt_solitonQ x
  have h₁ := (hT.mul hQ).const_mul (-8 : ℝ)
  have h₂ := (hT.mul (hQ.pow 2)).const_mul (24 : ℝ)
  have h := h₁.add h₂
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ3]
    ring
  · simp [solitonQ, solitonQ1, solitonQ4, solitonT]
    ring

theorem hasDerivAt_solitonQ4 (x : ℝ) : HasDerivAt solitonQ4 (solitonQ5 x) x := by
  have hQ := hasDerivAt_solitonQ x
  have h₁ := hQ.const_mul (16 : ℝ)
  have h₂ := (hQ.pow 2).const_mul (120 : ℝ)
  have h₃ := (hQ.pow 3).const_mul (120 : ℝ)
  have h := (h₁.sub h₂).add h₃
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ4]
  · simp [solitonQ, solitonQ1, solitonQ5, solitonT]
    ring

theorem hasDerivAt_solitonR (x : ℝ) : HasDerivAt solitonR (solitonR1 x) x := by
  have h := (hasDerivAt_solitonQ x).pow 2
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonR]
  · simp [solitonQ, solitonQ1, solitonR1, solitonT]
    ring

theorem hasDerivAt_solitonR1 (x : ℝ) : HasDerivAt solitonR1 (solitonR2 x) x := by
  have hT := hasDerivAt_solitonT x
  have hQ := hasDerivAt_solitonQ x
  have h := (hT.mul (hQ.pow 2)).const_mul (-4 : ℝ)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonR1]
    ring
  · simp [solitonQ, solitonQ1, solitonR2, solitonT]
    ring

theorem hasDerivAt_solitonR2 (x : ℝ) : HasDerivAt solitonR2 (solitonR3 x) x := by
  have hQ := hasDerivAt_solitonQ x
  have h := ((hQ.pow 2).const_mul (16 : ℝ)).sub ((hQ.pow 3).const_mul (20 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonR2]
  · simp [solitonQ, solitonQ1, solitonR3, solitonT]
    ring

theorem hasDerivAt_solitonR3 (x : ℝ) : HasDerivAt solitonR3 (solitonR4 x) x := by
  have hT := hasDerivAt_solitonT x
  have hQ := hasDerivAt_solitonQ x
  have h₁ := (hT.mul (hQ.pow 2)).const_mul (-64 : ℝ)
  have h₂ := (hT.mul (hQ.pow 3)).const_mul (120 : ℝ)
  have h := h₁.add h₂
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonR3]
    ring
  · simp [solitonQ, solitonQ1, solitonR4, solitonT]
    ring

theorem hasDerivAt_solitonR4 (x : ℝ) : HasDerivAt solitonR4 (solitonR5 x) x := by
  have hQ := hasDerivAt_solitonQ x
  have h₁ := (hQ.pow 2).const_mul (256 : ℝ)
  have h₂ := (hQ.pow 3).const_mul (1040 : ℝ)
  have h₃ := (hQ.pow 4).const_mul (840 : ℝ)
  have h := (h₁.sub h₂).add h₃
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonR4]
  · simp [solitonQ, solitonQ1, solitonR5, solitonT]
    ring

end GaloisForLFunctions.HTGeometry.DispersivePDE
