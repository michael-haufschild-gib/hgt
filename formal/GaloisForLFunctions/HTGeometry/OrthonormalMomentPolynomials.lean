import GaloisForLFunctions.HTGeometry.OrthogonalMomentPolynomials

/-!
# Orthonormal polynomials of a moment sequence

Normalization of the monic family of `OrthogonalMomentPolynomials` by its moment norm.  For a
positive definite moment form the resulting family `orthonormalPoly s n` satisfies

`⟪orthonormalPoly s m, orthonormalPoly s n⟫_s = if m = n then 1 else 0`

and has exact degree `n` with strictly positive leading coefficient — the classical normalization of
orthonormal polynomials on the real line.

This is the family whose complex evaluations control indeterminacy of the Hamburger problem through
the convergence of `∑ |P n z| ^ 2`.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The moment norm of the monic orthogonal polynomial of index `n`. -/
noncomputable def monicOrthoNorm (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (momentInner s (monicOrtho s n) (monicOrtho s n))

theorem monicOrthoNorm_pos (h : PositiveMomentForm s) (n : ℕ) : 0 < monicOrthoNorm s n :=
  Real.sqrt_pos.mpr (monicOrtho_inner_self_pos h n)

theorem monicOrthoNorm_ne_zero (h : PositiveMomentForm s) (n : ℕ) : monicOrthoNorm s n ≠ 0 :=
  ne_of_gt (monicOrthoNorm_pos h n)

theorem monicOrthoNorm_sq (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoNorm s n ^ 2 = momentInner s (monicOrtho s n) (monicOrtho s n) :=
  Real.sq_sqrt (monicOrtho_inner_self_pos h n).le

/-- The **orthonormal polynomials** of the moment sequence. -/
noncomputable def orthonormalPoly (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  (monicOrthoNorm s n)⁻¹ • monicOrtho s n

theorem orthonormalPoly_degree (h : PositiveMomentForm s) (n : ℕ) :
    (orthonormalPoly s n).degree = (n : WithBot ℕ) := by
  rw [orthonormalPoly, Polynomial.smul_eq_C_mul, Polynomial.degree_mul,
    Polynomial.degree_C (inv_ne_zero (monicOrthoNorm_ne_zero h n)), zero_add,
    monicOrtho_degree]

theorem orthonormalPoly_ne_zero (h : PositiveMomentForm s) (n : ℕ) :
    orthonormalPoly s n ≠ 0 := by
  intro hzero
  have := orthonormalPoly_degree h n
  rw [hzero, Polynomial.degree_zero] at this
  exact (WithBot.bot_ne_coe) this

/-- Normalization: each orthonormal polynomial has moment norm one. -/
theorem orthonormalPoly_inner_self (h : PositiveMomentForm s) (n : ℕ) :
    momentInner s (orthonormalPoly s n) (orthonormalPoly s n) = 1 := by
  have hne := monicOrthoNorm_ne_zero h n
  rw [orthonormalPoly, momentInner_smul_left, momentInner_smul_right, ← monicOrthoNorm_sq h n]
  field_simp

/-- Distinct orthonormal polynomials are orthogonal. -/
theorem orthonormalPoly_inner_eq_zero (h : PositiveMomentForm s) {m n : ℕ} (hmn : m ≠ n) :
    momentInner s (orthonormalPoly s m) (orthonormalPoly s n) = 0 := by
  rw [orthonormalPoly, orthonormalPoly, momentInner_smul_left, momentInner_smul_right,
    monicOrtho_inner_eq_zero h hmn, mul_zero, mul_zero]

/-- **The orthonormality relation.** -/
theorem orthonormalPoly_inner (h : PositiveMomentForm s) (m n : ℕ) :
    momentInner s (orthonormalPoly s m) (orthonormalPoly s n) = if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [orthonormalPoly_inner_self h]
  · simp [hmn, orthonormalPoly_inner_eq_zero h hmn]

/-- The leading coefficient is the reciprocal moment norm, hence strictly positive: this is the
classical sign normalization of orthonormal polynomials on the real line. -/
theorem orthonormalPoly_leadingCoeff (n : ℕ) :
    (orthonormalPoly s n).leadingCoeff = (monicOrthoNorm s n)⁻¹ := by
  rw [orthonormalPoly, Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C, (monicOrtho_monic s n).leadingCoeff, mul_one]

theorem orthonormalPoly_leadingCoeff_pos (h : PositiveMomentForm s) (n : ℕ) :
    0 < (orthonormalPoly s n).leadingCoeff := by
  rw [orthonormalPoly_leadingCoeff]
  exact inv_pos.mpr (monicOrthoNorm_pos h n)

/-- Orthogonality to every polynomial of strictly smaller degree is inherited from the monic
family. -/
theorem orthonormalPoly_inner_eq_zero_of_degree_lt (h : PositiveMomentForm s) (n : ℕ)
    (p : Polynomial ℝ) (hp : p.degree < (n : WithBot ℕ)) :
    momentInner s (orthonormalPoly s n) p = 0 := by
  rw [orthonormalPoly, momentInner_smul_left,
    monicOrtho_inner_eq_zero_of_degree_lt h n n le_rfl p hp, mul_zero]

end HTGeometry
