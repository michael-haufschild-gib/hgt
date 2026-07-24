import GaloisForLFunctions.HTGeometry.ClockHomogeneousScaling
import GaloisForLFunctions.HTGeometry.JetScalingClockField

/-!
# The field clock scales a homogeneous ratio by `λ^{a−b}`

Extending the ring-level homogeneous eigenvalue law to the field `C⟨y⟩`.  A ratio of
weighted-homogeneous polynomials `p/q` (jet-weights `a ≥ b`) is a clock eigenvector on the fraction
field with eigenvalue `λ^{a−b}`:

`ρ_λ(p/q) = λ^{a−b} · (p/q)`.

This realizes equation (2) of the clock-character law at the field level: a homogeneous generator of
the persistent core has the polynomial character `X^{a−b}`, discharging the algebraicity input for the
concrete jet-scaling clock on `C⟨y⟩`.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- **The field clock scales a homogeneous ratio by `λ^{a−b}`.** -/
theorem clockDilationFieldEquiv_homogeneous_ratio (lam : C) (hlam : lam ≠ 0)
    {p q : DifferentialPolynomial Unit C} {a b : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous (fun r : Unit × ℕ => r.2) p a)
    (hq : MvPolynomial.IsWeightedHomogeneous (fun r : Unit × ℕ => r.2) q b)
    (hab : b ≤ a) :
    clockDilationFieldEquiv lam hlam
        (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) p
          / algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) q)
      = algebraMap C (ScalarDifferentialField C) (lam ^ (a - b))
        * (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) p
          / algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) q) := by
  have hcoe : ∀ r : C,
      algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) (MvPolynomial.C r)
        = algebraMap C (ScalarDifferentialField C) r := fun r => by
    rw [IsScalarTower.algebraMap_apply C (DifferentialPolynomial Unit C) (ScalarDifferentialField C),
      MvPolynomial.algebraMap_eq]
  have hpowC : lam ^ a / lam ^ b = lam ^ (a - b) := by
    rw [div_eq_mul_inv, ← pow_sub₀ lam hlam hab]
  rw [map_div₀, clockDilationFieldEquiv_algebraMap, clockDilationFieldEquiv_algebraMap,
    clockDilationAlgHom_isWeightedHomogeneous lam hp,
    clockDilationAlgHom_isWeightedHomogeneous lam hq, map_mul, map_mul, hcoe, hcoe,
    mul_div_mul_comm, ← map_div₀, hpowC]

end

end GaloisForLFunctions
