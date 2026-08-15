import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Exact degree-one Dirichlet-character reduction for Selberg C2

For two complex Dirichlet characters represented at one common selected level `q`, their
finite prime-harmonic cross sum is exactly the prime-harmonic sum of `χ * ψ⁻¹`.  This uses
conjugation-as-inversion for the finite character group and remains valid at primes dividing
`q`, where both sides vanish.

Consequently, distinct characters at that common level give a nontrivial quotient character.
This is an algebraic reduction only.  It does **not** claim the analytic Mertens theorem needed
to prove convergence of the resulting ordered prime sum, hence does not claim Selberg C2.

Characters initially given at different levels must be transported to a common level before
using these statements.  Equality here is literal equality in `DirichletCharacter ℂ q`; this
module deliberately makes no unsupported identification of selected level with conductor.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Ordered finite prime-harmonic sum of one complex Dirichlet character at its selected level. -/
def dirichletCharacterPrimeHarmonic {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 N,
    if n.Prime then χ (n : ZMod q) / (n : ℂ) else 0

/-- Ordered finite prime-harmonic cross sum of two complex Dirichlet characters at one selected
level. -/
def dirichletCharacterPrimeHarmonicCross {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 N,
    if n.Prime then χ (n : ZMod q) * starRingEnd ℂ (ψ (n : ZMod q)) / (n : ℂ) else 0

/-- The exact finite-cutoff reduction of a Dirichlet-character C2 cross sum to its quotient
character.  No primitivity or analytic hypothesis is used. -/
theorem dirichletCharacterPrimeHarmonicCross_eq_quotient {q N : ℕ}
    (χ ψ : DirichletCharacter ℂ q) :
    dirichletCharacterPrimeHarmonicCross χ ψ N =
      dirichletCharacterPrimeHarmonic (χ * ψ⁻¹) N := by
  unfold dirichletCharacterPrimeHarmonicCross dirichletCharacterPrimeHarmonic
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, MulChar.mul_apply]
    rw [show starRingEnd ℂ (ψ (n : ZMod q)) = ψ⁻¹ (n : ZMod q) by
      simpa only [starRingEnd_apply] using MulChar.star_apply' ψ (n : ZMod q)]
  · simp [hp]

/-- At a fixed selected level, the quotient character is trivial exactly when the two characters
are equal.  This is the precise distinctness condition in the finite C2 reduction. -/
theorem dirichletCharacterQuotient_eq_one_iff {q : ℕ} (χ ψ : DirichletCharacter ℂ q) :
    χ * ψ⁻¹ = 1 ↔ χ = ψ := by
  constructor
  · intro h
    calc
      χ = (χ * ψ⁻¹) * ψ := by rw [mul_assoc, MulChar.inv_mul, MulChar.mul_one]
      _ = 1 * ψ := by rw [h]
      _ = ψ := one_mul _
  · intro h
    subst χ
    exact mul_inv_cancel ψ

/-- Distinct characters at one selected level have a nontrivial quotient character. -/
theorem dirichletCharacterQuotient_ne_one_of_ne {q : ℕ} (χ ψ : DirichletCharacter ℂ q)
    (hχψ : χ ≠ ψ) : χ * ψ⁻¹ ≠ 1 := by
  intro h
  exact hχψ (dirichletCharacterQuotient_eq_one_iff χ ψ |>.mp h)

end

end RHTower
