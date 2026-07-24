import GaloisForLFunctions.HTGeometry.ClockEigenvectorHomogeneous

/-!
# A clock eigenvalue is `λ^k`

A clock eigenvector is weighted-homogeneous of some weight `k` (`isWeightedHomogeneous_of_clock_eigenvector`),
and the clock scales such a polynomial by exactly `λ^k`.  Hence the eigenvalue of any clock eigenvector
is the monomial `χ(λ) = λ^k`: the concrete jet-scaling clock has purely polynomial characters.  This is
the algebraicity of the concrete cocharacter, realized on ring eigenvectors.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- **A clock eigenvalue is a monomial.**  If `ρ_λ(p) = χ(λ)·p` for all nonzero `λ` (with `p ≠ 0`),
then `χ(λ) = λ^k` for a fixed `k` (the weight of `p`). -/
theorem clock_eigenvalue_pow [Infinite C] {p : DifferentialPolynomial Unit C} (hp0 : p ≠ 0)
    {χ : C → C}
    (heig : ∀ lam : C, lam ≠ 0 → clockDilationAlgHom lam p = MvPolynomial.C (χ lam) * p) :
    ∃ k : ℕ, ∀ lam : C, lam ≠ 0 → χ lam = lam ^ k := by
  obtain ⟨k, hk⟩ := isWeightedHomogeneous_of_clock_eigenvector hp0 heig
  refine ⟨k, fun lam hlam => ?_⟩
  have h := (heig lam hlam).symm.trans (clockDilationAlgHom_isWeightedHomogeneous lam hk)
  exact MvPolynomial.C_injective _ _ (mul_right_cancel₀ hp0 h)

end

end GaloisForLFunctions
