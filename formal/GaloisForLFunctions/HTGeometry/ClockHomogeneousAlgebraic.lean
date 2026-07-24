import GaloisForLFunctions.HTGeometry.ClockHomogeneousScalingField

/-!
# A homogeneous generator has the polynomial clock character `X^k`

The homogeneous eigenvalue laws (`ρ_λ(p) = λ^k·p` on the ring, `ρ_λ(p/q) = λ^{a-b}·(p/q)` on the field)
say exactly that a weighted-homogeneous generator has the *polynomial* clock character `P = X^k` in
the form `ρ_λ(q) = P(λ)·q` required by the charged clock-character law (`persistent_core_dichotomy_from_algebraic`).
This discharges the algebraicity input for the concrete jet-scaling clock on a homogeneous generator.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- Ring form: a weighted-homogeneous polynomial has polynomial clock character `X^k`. -/
theorem clockDilationAlgHom_isWeightedHomogeneous_eval (lam : C)
    {p : DifferentialPolynomial Unit C} {k : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous (fun r : Unit × ℕ => r.2) p k) :
    clockDilationAlgHom lam p = MvPolynomial.C ((Polynomial.X ^ k).eval lam) * p := by
  rw [Polynomial.eval_pow, Polynomial.eval_X, clockDilationAlgHom_isWeightedHomogeneous lam hp]

/-- **Field form: the polynomial clock character of a homogeneous ratio.**  A ratio of
weighted-homogeneous polynomials (jet-weights `a ≥ b`) has the polynomial clock character `X^{a-b}` in
the exact `ρ_λ(q) = P(λ)·q` form of the charged clock-character law. -/
theorem clockDilationFieldEquiv_homogeneous_character
    {p q : DifferentialPolynomial Unit C} {a b : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous (fun r : Unit × ℕ => r.2) p a)
    (hq : MvPolynomial.IsWeightedHomogeneous (fun r : Unit × ℕ => r.2) q b)
    (hab : b ≤ a) :
    ∀ lam : C, (hlam : lam ≠ 0) →
      clockDilationFieldEquiv lam hlam
          (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) p
            / algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) q)
        = algebraMap C (ScalarDifferentialField C) ((Polynomial.X ^ (a - b)).eval lam)
          * (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) p
            / algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) q) := by
  intro lam hlam
  rw [Polynomial.eval_pow, Polynomial.eval_X,
    clockDilationFieldEquiv_homogeneous_ratio lam hlam hp hq hab]

end

end GaloisForLFunctions
