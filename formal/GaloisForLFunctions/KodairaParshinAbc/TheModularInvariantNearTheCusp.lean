import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfTheModularLambdaFunction
import GaloisForLFunctions.RHTower.ModularLambdaHeightBound

/-!
# The modular invariant near the cusp

The class-number step compares the height of `j` at a CM point with `exp(π √d / h')`; at the
archimedean place this is the growth `|j(τ)| ≍ exp(2π Im τ)` near the cusp, evaluated at the
points `τ = (-b + i√d)/(2a)` of the reduced forms, where `2π Im τ = π √d / a`.

For the level-one modular function `J(λ(τ))` built from the Legendre invariant this follows from
the cusp expansion of the corpus (`RHTower.ModularLambdaWinding.exists_cusp_bounds`):
`λ(τ) = u(τ) e^{iπτ}` with `|u - 16| < 8` and `|λ| ≤ 1/2` for `Im τ ≥ Y`.  Then
`|λ² - λ + 1| ∈ [1/4, 7/4]`, `|λ - 1| ∈ [1/2, 3/2]`, `|u| ∈ (8, 24)`, and

  `e^{2π Im τ} ≤ 324 |J(λ(τ))|`,   `|J(λ(τ))| ≤ 86 e^{2π Im τ}`

(`exists_cusp_bounds_lambdaInvariant`).
-/

noncomputable section

open Complex UpperHalfPlane Bottcher

namespace GaloisForLFunctions.KodairaParshinAbc

theorem norm_exp_pi_I_mul (z : ℂ) : ‖Complex.exp (Real.pi * Complex.I * z)‖ = Real.exp (-(Real.pi * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Cusp growth of `J ∘ λ`**: there is `Y` such that for `Im τ ≥ Y`,
`e^{2π Im τ} ≤ 324 |J(λ(τ))|` and `|J(λ(τ))| ≤ 86 e^{2π Im τ}`. -/
theorem exists_cusp_bounds_lambdaInvariant :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ τ : ℍ, Y ≤ τ.im →
      Real.exp (2 * Real.pi * τ.im) ≤ 324 * ‖lambdaInvariant τ‖ ∧
        ‖lambdaInvariant τ‖ ≤ 86 * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨Y, hY1, hY⟩ := RHTower.ModularLambdaWinding.exists_cusp_bounds
  refine ⟨Y, hY1, fun τ hτ => ?_⟩
  have hτ' : Y ≤ (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact hτ
  obtain ⟨hu, hL⟩ := hY τ hτ'
  obtain ⟨h0, h1⟩ := modularLambda_ne_zero_ne_one τ
  set L := modularLambda (τ : ℂ) with hLdef
  set u := L * Complex.exp (-(Real.pi * Complex.I * (τ : ℂ))) with hudef
  set E := Real.exp (Real.pi * τ.im) with hEdef
  have hE : 0 < E := Real.exp_pos _
  -- `|L| E = |u|`
  have hexp : ‖Complex.exp (-(Real.pi * Complex.I * (τ : ℂ)))‖ = E := by
    rw [Complex.norm_exp, hEdef]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, UpperHalfPlane.coe_im]
  have hLE : ‖L‖ * E = ‖u‖ := by
    rw [hudef, norm_mul, hexp]
  -- bounds on `|u|`, `|L - 1|`, `|L² - L + 1|`
  have hu_lo : 8 < ‖u‖ := by
    have := norm_sub_norm_le (16 : ℂ) u
    rw [norm_sub_rev] at this
    have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
    linarith
  have hu_hi : ‖u‖ < 24 := by
    have := norm_le_norm_add_norm_sub' u 16
    have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
    linarith
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  have hm_lo : 1 / 2 ≤ ‖L - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) L
    rw [norm_sub_rev, norm_one] at this
    linarith
  have hm_hi : ‖L - 1‖ ≤ 3 / 2 := by
    have := norm_sub_le L 1
    rw [norm_one] at this
    linarith
  have hs_lo : 1 / 4 ≤ ‖L ^ 2 - L + 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (L - L ^ 2)
    have h2 : ‖L - L ^ 2‖ ≤ ‖L‖ + ‖L‖ ^ 2 := by
      have := norm_sub_le L (L ^ 2)
      rwa [norm_pow] at this
    have e : (1 : ℂ) - (L - L ^ 2) = L ^ 2 - L + 1 := by ring
    rw [e, norm_one] at h
    nlinarith
  have hs_hi : ‖L ^ 2 - L + 1‖ ≤ 7 / 4 := by
    have h := norm_add_le (L ^ 2 - L) 1
    have h2 : ‖L ^ 2 - L‖ ≤ ‖L‖ ^ 2 + ‖L‖ := by
      have := norm_sub_le (L ^ 2) L
      rwa [norm_pow] at this
    rw [norm_one] at h
    nlinarith
  -- `|J| |u|² |L - 1|² = 256 |s|³ E²`
  have hJ : ‖lambdaInvariant τ‖ * (‖u‖ ^ 2 * ‖L - 1‖ ^ 2) = 256 * ‖L ^ 2 - L + 1‖ ^ 3 * E ^ 2 := by
    have hLn : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hL1n : ‖L - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1)
    unfold lambdaInvariant legendreInvariant
    rw [← hLdef, norm_div, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, ← hLE]
    have : ‖(256 : ℂ)‖ = 256 := by norm_num
    rw [this]
    field_simp
  have hE2 : Real.exp (2 * Real.pi * τ.im) = E ^ 2 := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hE2]
  have hu2 : 0 < ‖u‖ ^ 2 * ‖L - 1‖ ^ 2 := by positivity
  have hJ0 : 0 ≤ ‖lambdaInvariant τ‖ := norm_nonneg _
  constructor
  · -- `E² ≤ 324 |J|`
    have hlow : 256 * (1 / 4) ^ 3 * E ^ 2 ≤ ‖lambdaInvariant τ‖ * (24 ^ 2 * (3 / 2) ^ 2) := by
      calc 256 * (1 / 4) ^ 3 * E ^ 2 ≤ 256 * ‖L ^ 2 - L + 1‖ ^ 3 * E ^ 2 := by
            gcongr
        _ = ‖lambdaInvariant τ‖ * (‖u‖ ^ 2 * ‖L - 1‖ ^ 2) := hJ.symm
        _ ≤ ‖lambdaInvariant τ‖ * (24 ^ 2 * (3 / 2) ^ 2) := by
            gcongr
    nlinarith
  · -- `|J| ≤ 86 E²`
    have hup : ‖lambdaInvariant τ‖ * (8 ^ 2 * (1 / 2) ^ 2) ≤ 256 * (7 / 4) ^ 3 * E ^ 2 := by
      calc ‖lambdaInvariant τ‖ * (8 ^ 2 * (1 / 2) ^ 2)
          ≤ ‖lambdaInvariant τ‖ * (‖u‖ ^ 2 * ‖L - 1‖ ^ 2) := by gcongr
        _ = 256 * ‖L ^ 2 - L + 1‖ ^ 3 * E ^ 2 := hJ
        _ ≤ 256 * (7 / 4) ^ 3 * E ^ 2 := by gcongr
    nlinarith [sq_nonneg E]

/-- **At the point of a reduced form.**  High enough in the cusp, a point `τ = (-b + i√d)/(2a)`
satisfies `exp(π √d / a) ≤ 324 |J(λ(τ))|` and `|J(λ(τ))| ≤ 86 exp(π √d / a)`. -/
theorem exists_cusp_bounds_at_reducedForm :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ (τ : ℍ) (a d : ℝ), 0 < a → τ.im = Real.sqrt d / (2 * a) → Y ≤ τ.im →
      Real.exp (Real.pi * Real.sqrt d / a) ≤ 324 * ‖lambdaInvariant τ‖ ∧
        ‖lambdaInvariant τ‖ ≤ 86 * Real.exp (Real.pi * Real.sqrt d / a) := by
  obtain ⟨Y, hY1, hY⟩ := exists_cusp_bounds_lambdaInvariant
  refine ⟨Y, hY1, fun τ a d ha hτ hYτ => ?_⟩
  have e : 2 * Real.pi * τ.im = Real.pi * Real.sqrt d / a := by
    rw [hτ]
    field_simp
  obtain ⟨h1, h2⟩ := hY τ hYτ
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

end GaloisForLFunctions.KodairaParshinAbc
