import GaloisForLFunctions.FamilyContinuationTheory.TheThetaCoefficientCancelsThePairPhases

/-!
# The prime Gauss identities fix the local phases

At a primary prime `π ∤ 6` of `O = ℤ[ω]` with residue field of `Q` elements, sextic residue
character `χ` and trace character `ψ = ψ_π`, write `G_r = Σ_{x mod π} χ(x)^r ψ(x)`. The local
factors of the cubic-theta probe are read with:

* `sexticSymbol_prime`, `sexticSymbol_prime_pow`: the composite symbol at `π^t` is `χ^t`;
* `gaussSum_mul_gaussSum_inv`: `G₁ G₅ = χ(−1) Q`;
* `gamma_sq_eq`: `Γ(π)² = η(−1)` for the quadratic phase `Γ`, so `r(π, π) = χ(−1)`
  (`quadraticPhase_self`);
* `sextic_gauss_product`: `χ(4) G₁ G₂ = −π G₃` (the relation of `MetaplecticMobiusDescent`):
  normalized, `γ₁ γ₂ = −α(π) G(π)` with `G(π) = \overline{χ(4)} Γ(π)`.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

theorem prime_of_isMaximal_span : Prime π :=
  (Ideal.span_singleton_prime (NeZero.ne π)).mp hP.isPrime

include h2 hprim in
/-- The composite sextic symbol at a primary prime is the sextic residue character. -/
theorem sexticSymbol_prime (x : O) :
    sexticSymbol x π = complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ x) := by
  rw [complexSexticChar_apply, sexticSymbol, quadSymbol_prime π h2,
    CubicJacobi.symbol_prime π (prime_of_isMaximal_span π) hprim, CubicJacobi.primeValue_eq _ hlam]
  rfl

theorem sexticSymbol_one_denominator (x : O) : sexticSymbol x 1 = 1 := by
  rw [sexticSymbol, CubicJacobi.symbol_one, map_one, one_pow, quadSymbol_one_denominator, one_mul]

include h2 hprim in
/-- At a prime power the composite symbol is the power of the residue character. -/
theorem sexticSymbol_prime_pow (x : O) (t : ℕ) :
    sexticSymbol x (π ^ t) =
      complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ x) ^ t := by
  induction t with
  | zero => rw [pow_zero, pow_zero, sexticSymbol_one_denominator]
  | succ t ih => rw [pow_succ, sexticSymbol_mul_denominator, ih,
      sexticSymbol_prime π hlam h2 hprim, pow_succ]

end Prime

/-! ### Gauss identities at a prime -/

include hprim in
/-- The canonical primary generator of `(π)` is `π`. -/
theorem primaryGenerator_eq : primaryGenerator (Ideal.span {π}) hlam = π :=
  (primaryGenerator_unique _ hlam π rfl hprim).symm

/-- `χ(−1)² = 1`. -/
theorem mulChar_neg_one_sq {R : Type*} [CommRing R] (χ : MulChar R ℂ) : χ (-1) ^ 2 = 1 := by
  rw [sq, ← map_mul, neg_one_mul, neg_neg, MulChar.map_one]

/-- **`G₁ G₅ = χ(−1) Q`.** -/
theorem gaussSum_mul_gaussSum_inv :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π)) *
        gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 5) (principalTraceChar π (NeZero.ne π)) =
      complexSexticChar (Ideal.span {π}) hlam (-1) *
        (Fintype.card (O ⧸ Ideal.span {π}) : ℂ) := by
  set χ := complexSexticChar (Ideal.span {π}) hlam
  set ψ := principalTraceChar π (NeZero.ne π)
  have h6 := (complexSexticChar_powers (Ideal.span {π}) hlam).2.2
  have hinv : χ ^ 5 = χ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h6])
  have hcard := gaussSum_mul_gaussSum_eq_card (complexSexticChar_ne_one (Ideal.span {π}) hlam)
    (principalTraceChar_primitive π (NeZero.ne π))
  have hflip := mul_gaussSum_inv_eq_gaussSum (χ ^ 5) ψ
  have hval : (χ ^ 5) (-1) = χ (-1) := by
    rw [MulChar.pow_apply' _ (by norm_num), show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ,
      pow_mul, mulChar_neg_one_sq, one_pow, one_mul]
  rw [← hflip, hval, hinv]
  rw [← hinv] at hcard ⊢
  linear_combination χ (-1) * hcard

end GaloisForLFunctions.FamilyContinuationTheory
