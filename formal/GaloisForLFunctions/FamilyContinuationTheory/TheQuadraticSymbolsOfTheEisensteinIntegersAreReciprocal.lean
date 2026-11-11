import GaloisForLFunctions.FamilyContinuationTheory.TheGaussSumOfAPrimePowerLivesOnOneLayer
import GaloisForLFunctions.MetaplecticMobiusDescent.TheQuadraticGaussPhaseLivesModuloFour

/-!
# The quadratic symbols of the Eisenstein integers are reciprocal

For `c ∈ O = ℤ[ω]`, `c ≠ 0`, let `Γ(c) = |c|⁻¹ Σ_{x mod c} ψ_c(x²)` with the trace character
`ψ_c(x) = exp(2πi Tr(x/(cλ)))`; it is `(1 + i^{−b} + i^a + i^{b−a})/2` for `c = a + bω` and depends
only on `c mod 4` (`normalizedQuadraticTraceGauss_formula`). For two odd primes `p, q` of `O` with
quadratic residue characters `η_p, η_q`:

* `sum_traceChar_mul_sq`: `Σ_{x mod p} ψ_p(ux²) = η_p(u) G(η_p)` for `p ∤ u` (square roots are
  counted by `1 + η_p`);
* `quadraticTraceGauss_mul`: for coprime `c, d`, the sum over `x mod cd` splits along
  `x = dx₁ + cx₂` into `Σ_{x₁} ψ_c(dx₁²) · Σ_{x₂} ψ_d(cx₂²)`, because the cross term `2x₁x₂` is
  integral and the trace character is trivial on integers (`traceChar_integral`);
* `quadratic_reciprocity`: `η_p(q) η_q(p) Γ(p) Γ(q) = Γ(pq)`.

So `η_p(q) η_q(p)` is a function of `p, q mod 4`: the quadratic part of sextic reciprocity, which
turns the cross phases of the cubic-theta probe into a fixed ray bicharacter.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein

/-- The trace character is trivial on integers: `exp(2πi Tr(z/λ)) = 1` for `z ∈ O`. -/
theorem traceChar_integral (z : O) :
    Complex.exp ((Algebra.trace ℚ K
      ((algebraMap O K z) / (algebraMap O K traceLambda * algebraMap O K 1)) : ℂ) *
        (2 * Real.pi * Complex.I)) = 1 := by
  rw [← principalTraceChar_apply 1 one_ne_zero z]
  have h : Ideal.Quotient.mk (Ideal.span {(1 : O)}) z = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_one]
    trivial
  rw [h, AddChar.map_zero_eq_one]

/-- **The CRT phase.** For `x = dx₁ + cx₂`, `ψ_{cd}(x²) = ψ_c(dx₁²) ψ_d(cx₂²)`. -/
theorem traceChar_crt_sq (c d : O) [NeZero c] [NeZero d] (x y : O) :
    principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
        (Ideal.Quotient.mk _ ((d * x + c * y) ^ 2)) =
      principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ (d * x ^ 2)) *
        principalTraceChar d (NeZero.ne d) (Ideal.Quotient.mk _ (c * y ^ 2)) := by
  rw [principalTraceChar_apply, principalTraceChar_apply, principalTraceChar_apply,
    ← Complex.exp_add]
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hc : algebraMap O K c ≠ 0 := fun h => NeZero.ne c (hinj (by rw [h, map_zero]))
  have hd : algebraMap O K d ≠ 0 := fun h => NeZero.ne d (hinj (by rw [h, map_zero]))
  have hl : algebraMap O K traceLambda ≠ 0 := fun h => traceLambda_ne_zero
    (hinj (by rw [h, map_zero]))
  have hsplit : (algebraMap O K ((d * x + c * y) ^ 2)) /
      (algebraMap O K traceLambda * algebraMap O K (c * d)) =
      (algebraMap O K (d * x ^ 2)) / (algebraMap O K traceLambda * algebraMap O K c) +
        (algebraMap O K (c * y ^ 2)) / (algebraMap O K traceLambda * algebraMap O K d) +
          (algebraMap O K (2 * x * y)) / (algebraMap O K traceLambda * algebraMap O K 1) := by
    simp only [map_mul, map_pow, map_add, map_one, map_ofNat]
    field_simp
    ring
  have h1 := traceChar_integral (2 * x * y)
  rw [hsplit, map_add, map_add, Rat.cast_add, Rat.cast_add, add_mul, add_mul, Complex.exp_add, h1,
    mul_one]

end GaloisForLFunctions.FamilyContinuationTheory
