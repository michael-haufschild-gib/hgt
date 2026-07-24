import GaloisForLFunctions.HTGeometry.ClockFieldEigenvaluePow
import GaloisForLFunctions.HTGeometry.ScalarDifferentialFieldGenerator

/-!
# The differential jets are the canonical clock eigenvectors

The `n`-th differential jet `y^(n)` of the canonical generator `y = X_{(),0}` of `C⟨y⟩` equals the free
jet variable `X_{(),n}`, which is weighted-homogeneous of jet-weight `n`.  Hence the concrete
jet-scaling clock scales it by exactly `λ^n`:

`ρ_λ(y^(n)) = λ^n · y^(n)`.

So each jet is a field clock eigenvector with the purely polynomial character `X^n`, and for `n ≥ 1` a
*charged* one (`k > 0`).  These are the canonical witnesses that the field eigenvalue theorem
`clock_field_eigenvalue_pow` is non-vacuous in the charged regime of the clock-character law: the
eigenvalue extracted from a jet is its order.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- **The `n`-th differential jet is a clock eigenvector of character `λ^n`.**
`ρ_λ(y^(n)) = λ^n · y^(n)`. -/
theorem clockDilationFieldEquiv_differentialJet (lam : C) (hlam : lam ≠ 0) (n : ℕ) :
    clockDilationFieldEquiv lam hlam (differentialJet n (scalarDifferentialGenerator C))
      = algebraMap C (ScalarDifferentialField C) (lam ^ n)
        * differentialJet n (scalarDifferentialGenerator C) := by
  rw [differentialJet_scalarDifferentialGenerator, clockDilationFieldEquiv_algebraMap,
    clockDilationAlgHom_isWeightedHomogeneous lam (MvPolynomial.isWeightedHomogeneous_X _ _ _),
    map_mul, IsScalarTower.algebraMap_apply C (DifferentialPolynomial Unit C)
      (ScalarDifferentialField C) (lam ^ n), MvPolynomial.algebraMap_eq]

/-- Every differential jet of the generator is nonzero. -/
theorem differentialJet_scalarDifferentialGenerator_ne_zero (n : ℕ) :
    differentialJet n (scalarDifferentialGenerator C) ≠ 0 := by
  rw [differentialJet_scalarDifferentialGenerator]
  exact fun h => MvPolynomial.X_ne_zero _ (IsFractionRing.to_map_eq_zero_iff.mp h)

/-- **The field eigenvalue theorem fires on the jets.**  The `n`-th jet is a nonzero field clock
eigenvector, so `clock_field_eigenvalue_pow` returns its weight: `λ^n · λ^{k_b} = λ^{k_a}` for fixed
`k_a, k_b` (here `k_a = n`, `k_b = 0`). -/
theorem clock_field_eigenvalue_differentialJet (n : ℕ) :
    ∃ ka kb : ℕ, ∀ lam : C, lam ≠ 0 → lam ^ n * lam ^ kb = lam ^ ka :=
  clock_field_eigenvalue_pow (differentialJet_scalarDifferentialGenerator_ne_zero n)
    (fun lam hlam => clockDilationFieldEquiv_differentialJet lam hlam n)

end

end GaloisForLFunctions
