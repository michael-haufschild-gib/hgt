import GaloisForLFunctions.HTGeometry.HermiteSeminormGrowth
import Mathlib.Analysis.PSeries

/-!
# The Hermite expansion is absolutely summable in every Schwartz seminorm

The coefficients of a Schwartz function decay faster than any power of the eigenvalue, and the
normalized Hermite functions grow only polynomially in every Schwartz seminorm.  Choosing the decay
two orders above the growth, each term of the expansion is bounded by a constant times `(j+1)⁻²`,
whose sum converges.

So the Hermite expansion of a Schwartz function is absolutely summable in every seminorm of the
Schwartz space — the estimate that makes it converge there.

* `hermiteCoeff_decay_shift` : the coefficients decay against the shifted eigenvalue.
* `schwartzSeminorm_hermiteTerm_le` : **each term is `O((j+1)⁻²)` in every seminorm.**
* `summable_schwartzSeminorm_hermiteTerm` : **the seminorm series converges.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Decay against the shifted eigenvalue -/

theorem shifted_le_two_mul_hamiltonian (j : ℕ) :
    4 * π * ((j : ℝ) + 1) ≤ 2 * (2 * π * (2 * (j : ℝ) + 1)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem hermiteCoeff_decay_shift (M : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      (4 * π * ((j : ℝ) + 1)) ^ M * ‖hermiteCoeff f j‖ ≤ C := by
  refine ⟨2 ^ M * ‖((hamiltonianCLM^[M]) f).toLp 2 (volume : Measure ℝ)‖, by positivity,
    fun j => ?_⟩
  have hdecay := hermiteCoeff_decay M j f
  have hgrow : (4 * π * ((j : ℝ) + 1)) ^ M
      ≤ 2 ^ M * (2 * π * (2 * (j : ℝ) + 1)) ^ M := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ M
    exact shifted_le_two_mul_hamiltonian j
  calc (4 * π * ((j : ℝ) + 1)) ^ M * ‖hermiteCoeff f j‖
      ≤ (2 ^ M * (2 * π * (2 * (j : ℝ) + 1)) ^ M) * ‖hermiteCoeff f j‖ :=
        mul_le_mul_of_nonneg_right hgrow (norm_nonneg _)
    _ = 2 ^ M * ((2 * π * (2 * (j : ℝ) + 1)) ^ M * ‖hermiteCoeff f j‖) := by ring
    _ ≤ 2 ^ M * ‖((hamiltonianCLM^[M]) f).toLp 2 (volume : Measure ℝ)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hdecay

/-! ## The terms of the expansion -/

theorem four_pi_mul_pos (j : ℕ) : 0 < 4 * π * ((j : ℝ) + 1) := by
  have := Real.pi_pos
  positivity

/-- **Each term of the Hermite expansion is `O((j+1)⁻²)` in every Schwartz seminorm.** -/
theorem schwartzSeminorm_hermiteTerm_le (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      SchwartzMap.seminorm ℂ k n (hermiteCoeff f j • hermiteUnit j)
        ≤ C * ((4 * π * ((j : ℝ) + 1)) ^ 2)⁻¹ := by
  obtain ⟨C₁, hC₁, hgrow⟩ := schwartzSeminorm_hermiteUnit_le k n
  obtain ⟨C₂, hC₂, hdecay⟩ := hermiteCoeff_decay_shift (k + n + 4) f
  refine ⟨C₁ * C₂, by positivity, fun j => ?_⟩
  have hpos := four_pi_mul_pos j
  have hsmul : SchwartzMap.seminorm ℂ k n (hermiteCoeff f j • hermiteUnit j)
      = ‖hermiteCoeff f j‖ * SchwartzMap.seminorm ℂ k n (hermiteUnit j) :=
    map_smul_eq_mul _ _ _
  rw [hsmul]
  have hbound : ‖hermiteCoeff f j‖ * SchwartzMap.seminorm ℂ k n (hermiteUnit j)
      ≤ ‖hermiteCoeff f j‖ * (C₁ * (4 * π * ((j : ℝ) + 1)) ^ (k + n + 2)) :=
    mul_le_mul_of_nonneg_left (hgrow j) (norm_nonneg _)
  refine le_trans hbound ?_
  have hdec : ‖hermiteCoeff f j‖ ≤ C₂ * ((4 * π * ((j : ℝ) + 1)) ^ (k + n + 4))⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    have h := hdecay j
    linarith [h]
  calc ‖hermiteCoeff f j‖ * (C₁ * (4 * π * ((j : ℝ) + 1)) ^ (k + n + 2))
      ≤ (C₂ * ((4 * π * ((j : ℝ) + 1)) ^ (k + n + 4))⁻¹)
        * (C₁ * (4 * π * ((j : ℝ) + 1)) ^ (k + n + 2)) := by
        refine mul_le_mul_of_nonneg_right hdec (by positivity)
    _ = C₁ * C₂ * ((4 * π * ((j : ℝ) + 1)) ^ 2)⁻¹ := by
        rw [show k + n + 4 = (k + n + 2) + 2 by omega, pow_add]
        field_simp

/-- **The seminorm series of the Hermite expansion converges.** -/
theorem summable_schwartzSeminorm_hermiteTerm (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    Summable fun j : ℕ =>
      SchwartzMap.seminorm ℂ k n (hermiteCoeff f j • hermiteUnit j) := by
  obtain ⟨C, hC, hbound⟩ := schwartzSeminorm_hermiteTerm_le k n f
  refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound ?_
  have h1 : Summable fun j : ℕ => 1 / ((j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h2 : Summable fun j : ℕ => 1 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := (summable_nat_add_iff 1).mpr h1
  have hfun : (fun j : ℕ => C * ((4 * π * ((j : ℝ) + 1)) ^ 2)⁻¹)
      = fun j : ℕ => (C * ((4 * π) ^ 2)⁻¹) * (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext j
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
  rw [hfun]
  exact h2.mul_left _

end GaloisForLFunctions

end
