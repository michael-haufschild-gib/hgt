import GaloisForLFunctions.RHTower.KFreeAbelSmoothedSaving

set_option autoImplicit false

/-!
# The Mellin–Abel integrands on the line `Re s = 2` with their constants supplied

The Möbius and `k`-free Abel integrands are bounded on `Re s = 2` in terms of a `Γ` (resp. `Γζ`)
decay constant and the bound for `1/ζ` on `Re s ≥ 3/2`.  The corpus proves all three bounds
(`exists_norm_Gamma_le_exp_half`, `exists_norm_Gamma_mul_zeta_le`,
`exists_norm_inv_riemannZeta_le_of_three_halves_le_re`), so one pair of constants serves every
line point and every smoothing parameter.
-/

open Complex

namespace RHTower.MoebiusAbel

/-- `‖x^{-s} Γ(s)/ζ(s)‖ ≤ x^{-2} A B e^{-|t|/2}` on `s = 2 + it`, uniformly in `x > 0` and `t`. -/
theorem abelMoebiusIntegrand_line_le_uniform :
    ∃ A Bz : ℝ, 0 ≤ A ∧ 0 ≤ Bz ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ,
      ‖abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(|t| / 2)) := by
  obtain ⟨A, hA, hΓ⟩ := exists_norm_Gamma_le_exp_half
  obtain ⟨Bz, hBz, hz⟩ := exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  exact ⟨A, Bz, hA, hBz, fun x hx t => abelMoebiusIntegrand_line_le hx hΓ hz t⟩

end RHTower.MoebiusAbel

namespace RHTower.KFreeAbel

/-- The `k`-free Abel integrand on `s = 2 + iy` decays like `t^{-2} A B e^{-|y|/4}`, uniformly in
`k ≥ 2`, `t > 0` and `y`; the `Γζ` constant is taken on the strip `1 ≤ Re s ≤ 2`. -/
theorem norm_kFree_line_le_uniform :
    ∃ A Bz : ℝ, 0 ≤ A ∧ 0 ≤ Bz ∧ ∀ k : ℕ, 2 ≤ k → ∀ t : ℝ, 0 < t → ∀ y : ℝ,
      ‖kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * |y|)) := by
  obtain ⟨A, hA, hΓζ⟩ := exists_norm_Gamma_mul_zeta_le (a := 1) one_pos
  obtain ⟨Bz, hBz, hz⟩ := exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  exact ⟨A, Bz, hA, hBz, fun k hk t ht y =>
    norm_kFree_line_le hk ht (by norm_num) hΓζ hz y⟩

end RHTower.KFreeAbel
