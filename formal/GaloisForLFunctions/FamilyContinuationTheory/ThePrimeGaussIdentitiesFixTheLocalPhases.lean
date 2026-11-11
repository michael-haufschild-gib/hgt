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

/-! ### Gauss identities at a prime -/

omit [NeZero π] in
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

include hlam hprim in
/-- `|π|² = Q`. -/
theorem norm_sq_ringComplex :
    (‖ringComplex π‖ : ℂ) ^ 2 = (Fintype.card (O ⧸ Ideal.span {π}) : ℂ) := by
  have h := norm_primaryGenerator (Ideal.span {π}) hlam
  rw [primaryGenerator_eq π hlam hprim] at h
  rw [h, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_cast

include h2 hlam hprim in
/-- **`Γ(π)² = η(−1)`.** -/
theorem gamma_sq_eq :
    fixedDualAverage π ^ 2 = complexQuadraticChar (Ideal.span {π}) (-1) := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  set η := complexQuadraticChar (Ideal.span {π})
  set ψ := principalTraceChar π (NeZero.ne π)
  have hη1 : η ≠ 1 := complexQuadraticChar_ne_one _ (ringChar_ne_two π h2)
  have hηq : η.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hsq := gaussSum_sq hη1 hηq (principalTraceChar_primitive π (NeZero.ne π))
  have htr : quadraticTraceGauss π (NeZero.ne π) = gaussSum η ψ := by
    have h := sum_traceChar_mul_sq π h2 (u := 1) one_ne_zero
    simp only [one_mul, MulChar.map_one] at h
    rw [quadraticTraceGauss_eq_sum, h]
  have hn := norm_sq_ringComplex π hlam hprim
  have hn0 : (‖ringComplex π‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne π (ringComplex_injective
      (by rw [h, map_zero]))
  rw [← normalizedQuadraticTraceGauss_eq_fixedDualAverage π (NeZero.ne π),
    normalizedQuadraticTraceGauss, htr, div_pow, hsq, hn]
  have hc : (Fintype.card (O ⧸ Ideal.span {π}) : ℂ) ≠ 0 := by
    rw [← hn]; exact pow_ne_zero 2 hn0
  field_simp

include h2 in
/-- A prime `π ∤ 2` is odd. -/
theorem prime_odd : π ∉ Ideal.span {(2 : O)} := by
  intro h
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp h
  rcases (prime_of_isMaximal_span π).dvd_or_dvd (show π ∣ k * 2 from ⟨1, by rw [hk, mul_one]⟩)
    with h' | h'
  · obtain ⟨k', rfl⟩ := h'
    apply two_not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨k', mul_right_cancel₀ (NeZero.ne π) ?_⟩
    calc 2 * k' * π = π * k' * 2 := by ring
      _ = π := hk
      _ = 1 * π := (one_mul π).symm
  · exact h2 (Ideal.mem_span_singleton.mpr h')

omit [NeZero π] in
/-- The cubic character is trivial at `−1`. -/
theorem complexCubicChar_neg_one : complexCubicChar (Ideal.span {π}) hlam (-1) = 1 := by
  have h3 : complexCubicChar (Ideal.span {π}) hlam (-1) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), complexCubicChar_pow_three,
      MulChar.one_apply isUnit_one.neg]
  have h2' := mulChar_neg_one_sq (complexCubicChar (Ideal.span {π}) hlam)
  rw [pow_succ, h2', one_mul] at h3
  exact h3

include h2 hlam hprim in
/-- **`r(π, π) = χ(−1)`.** -/
theorem quadraticPhase_self :
    quadraticPhase π π = complexSexticChar (Ideal.span {π}) hlam (-1) := by
  have hodd := prime_odd π h2
  have h1 : (1 : O) ∉ Ideal.span {(2 : O)} := not_mem_two_of_isCoprime isCoprime_one_left
  rw [complexSexticChar_apply, complexCubicChar_neg_one, one_pow, one_mul, quadraticPhase,
    show π * π = 1 * π ^ 2 by ring, gamma_mul_sq h1 hodd, fixedDualAverage_one, ← sq,
    gamma_sq_eq π hlam h2 hprim]
  have hsq := mulChar_neg_one_sq (complexQuadraticChar (Ideal.span {π}))
  have hne : complexQuadraticChar (Ideal.span {π}) (-1) ≠ 0 := by
    intro h0; rw [h0] at hsq; norm_num at hsq
  field_simp
  linear_combination (-1 : ℂ) * hsq

include h2 hprim in
/-- **The sextic Gauss product.** `χ(4) G₁ G₂ = −π G₃`. -/
theorem sextic_gauss_product :
    complexSexticChar (Ideal.span {π}) hlam 4 *
        gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π)) *
          gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 2)
            (principalTraceChar π (NeZero.ne π)) =
      -ringComplex π * gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 3)
        (principalTraceChar π (NeZero.ne π)) := by
  obtain ⟨hc2, hc3, -⟩ := complexSexticChar_powers (Ideal.span {π}) hlam
  have h := sextic_cubic_gauss_product (Ideal.span {π}) hlam (ringChar_ne_two π h2) _
    (principalTraceChar_primitive π (NeZero.ne π))
  rw [primaryGenerator_eq π hlam hprim] at h
  rw [hc2, hc3]
  exact h

end Prime

end GaloisForLFunctions.FamilyContinuationTheory
