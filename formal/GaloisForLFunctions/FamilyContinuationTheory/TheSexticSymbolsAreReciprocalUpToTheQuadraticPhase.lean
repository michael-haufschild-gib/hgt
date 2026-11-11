import GaloisForLFunctions.FamilyContinuationTheory.TheQuadraticSymbolsOfTheEisensteinIntegersAreReciprocal
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicReciprocityAtACommonCharacteristic

/-!
# The sextic symbols are reciprocal up to the quadratic phase

The sextic residue character of a prime `p ∤ 6` of `O = ℤ[ω]` is `χ_p = c_p² η_p`, `c_p` the cubic
and `η_p` the quadratic character. For primary coprime primes `p, q` the cubic parts are
reciprocal (`cubic_reciprocity_primary`) and the quadratic parts are reciprocal up to
`Γ(pq)/(Γ(p)Γ(q))` (`quadratic_reciprocity`), where `Γ(c) = |c|⁻¹ Σ_{x mod c} ψ_c(x²)` depends only
on `c mod 4`. Hence

`χ_q(p) Γ(p) Γ(q) = Γ(pq) χ_p(q)`   (`sextic_reciprocity`):

the cross phase `χ_q(p)/χ_p(q)` between two good primes is a function of their residues modulo
four. This is the law that turns the pair phases of the Poisson coefficients of the cubic-theta
probe into a fixed ray bicharacter.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein

/-- The sextic character is the square of the cubic times the quadratic character. -/
theorem complexSexticChar_apply (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O ⧸ P) :
    complexSexticChar P hgood x = complexCubicChar P hgood x ^ 2 * complexQuadraticChar P x := by
  rw [complexSexticChar, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.pow_apply' _ two_ne_zero]

/-- **Sextic reciprocity at two primes.** For primary coprime primes `p, q ∤ 6`,
`χ_q(p) Γ(p) Γ(q) = Γ(pq) χ_p(q)`. -/
theorem sextic_reciprocity (p q : O) [NeZero p] [NeZero q] [(Ideal.span {p}).IsMaximal]
    [(Ideal.span {q}).IsMaximal] (hpl : lambda ∉ Ideal.span {p}) (hql : lambda ∉ Ideal.span {q})
    (hp2 : (2 : O) ∉ Ideal.span {p}) (hq2 : (2 : O) ∉ Ideal.span {q})
    (hpprim : lambda ^ 2 ∣ p - 1) (hqprim : lambda ^ 2 ∣ q - 1) (hpq : IsCoprime p q) :
    complexSexticChar (Ideal.span {q}) hql (Ideal.Quotient.mk _ p) *
        normalizedQuadraticTraceGauss p (NeZero.ne p) *
          normalizedQuadraticTraceGauss q (NeZero.ne q) =
      normalizedQuadraticTraceGauss (p * q) (mul_ne_zero (NeZero.ne p) (NeZero.ne q)) *
        complexSexticChar (Ideal.span {p}) hpl (Ideal.Quotient.mk _ q) := by
  -- the cubic parts are reciprocal
  have hcub : complexCubicChar (Ideal.span {q}) hql (Ideal.Quotient.mk _ p) =
      complexCubicChar (Ideal.span {p}) hpl (Ideal.Quotient.mk _ q) := by
    simp only [complexCubicChar, MulChar.ringHomComp_apply]
    rw [cubic_reciprocity_primary (Ideal.span {p}) (Ideal.span {q}) hpl hql p q rfl rfl hpprim
      hqprim]
  -- the quadratic value at `q` is a sign
  have hqp : Ideal.Quotient.mk (Ideal.span {p}) q ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    intro h
    exact (inferInstance : (Ideal.span {p}).IsMaximal).ne_top
      (Ideal.span_singleton_eq_top.mpr (hpq.isUnit_of_dvd' (dvd_refl p) h))
  have hsq : complexQuadraticChar (Ideal.span {p}) (Ideal.Quotient.mk _ q) ^ 2 = 1 := by
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    simp only [complexQuadraticChar, MulChar.ringHomComp_apply, eq_intCast]
    rw [← Int.cast_pow, quadraticChar_sq_one hqp, Int.cast_one]
  have hquad := quadratic_reciprocity p q hp2 hq2 hpq
  rw [complexSexticChar_apply, complexSexticChar_apply, hcub, ← hquad]
  linear_combination (-(complexCubicChar (Ideal.span {p}) hpl (Ideal.Quotient.mk _ q) ^ 2 *
    complexQuadraticChar (Ideal.span {q}) (Ideal.Quotient.mk _ p) *
      normalizedQuadraticTraceGauss p (NeZero.ne p) *
        normalizedQuadraticTraceGauss q (NeZero.ne q))) * hsq

end GaloisForLFunctions.FamilyContinuationTheory
