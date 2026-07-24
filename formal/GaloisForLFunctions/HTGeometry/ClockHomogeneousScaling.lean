import GaloisForLFunctions.HTGeometry.JetScalingClock
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The jet-scaling clock scales weighted-homogeneous polynomials by `λ^k`

The clock dilation `ρ_λ(X_(i,n)) = λ^n·X_(i,n)` acts on a monomial by the jet-weight `λ^{Σ n_i}`, so a
polynomial that is weighted-homogeneous of weight `k` (all monomials of jet-weight `k`) is scaled
uniformly by `λ^k`:

`ρ_λ(p) = λ^k · p`   (`p` weighted-homogeneous of weight `k`).

This is the concrete realization of equation (2) of the clock-character law: a homogeneous generator
of the persistent core has the polynomial character `P = X^k`, discharging the algebraicity input for
the concrete jet-scaling clock.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [CommRing C]

/-- The clock scales a single monomial by `λ` to its jet-weight. -/
theorem clockDilationAlgHom_monomial (lam : C) (s : (Unit × ℕ) →₀ ℕ) (c : C) :
    clockDilationAlgHom lam (MvPolynomial.monomial s c)
      = MvPolynomial.C (lam ^ (Finsupp.weight (fun p : Unit × ℕ => p.2) s))
        * MvPolynomial.monomial s c := by
  rw [clockDilationAlgHom, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  simp only [mul_pow, ← MvPolynomial.C_pow, ← pow_mul, Finset.prod_mul_distrib, Finsupp.prod]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, MvPolynomial.prod_X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial, MvPolynomial.C_mul_monomial, MvPolynomial.C_mul_monomial]
  have hA : (∑ x ∈ s.support, x.2 * s x) = Finsupp.weight (fun p : Unit × ℕ => p.2) s := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl (fun x _ => by rw [smul_eq_mul, mul_comm])
  rw [hA]
  congr 1
  ring

/-- **The clock scales a weighted-homogeneous polynomial by `λ^k`.**  A weighted-homogeneous
polynomial of jet-weight `k` is an eigenvector of the clock dilation with eigenvalue `λ^k`. -/
theorem clockDilationAlgHom_isWeightedHomogeneous (lam : C)
    {p : DifferentialPolynomial Unit C} {k : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous (fun q : Unit × ℕ => q.2) p k) :
    clockDilationAlgHom lam p = MvPolynomial.C (lam ^ k) * p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [clockDilationAlgHom_monomial, hp (MvPolynomial.mem_support_iff.mp hs)]

end

end GaloisForLFunctions
