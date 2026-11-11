import GaloisForLFunctions.FamilyContinuationTheory.ThePoissonCoefficientOfAPrimePowerIsExplicit

/-!
# The local factor of the Poisson series is explicit

At a primary prime `π ∤ 6` with `N(π) = Q`, `|π| = N`, `α = π/N`, sextic residue character `χ`,
`ε = χ(−1)`, `c₄ = χ(4)`, Gauss sums `G_r` and quadratic phase `Γ = Γ(π)`, the Gauss sums obey

* `G₁ G₅ = ε Q`, `G₂ G₄ = Q`, `G₃ = N Γ`, `Γ² = ε`, `c₄³ = 1`, `c₄ G₁ G₂ = −π G₃`.

The local term of the Poisson series of the cubic-theta probe (`localTerm`) at the exponents
`(e, l, k, m)` (squarefree part, cube part, row twist, sixth-power part of the frequency
`H = u π^{j+6m}`, `π ∤ u`, `ρ = χ(u)`) is
`(ᾱ η_π)^t K(π^k, π^e, π^l; H) (X/N)^e (X³/Q)^l (Y/Q)^k V^m`, `t = e + 3l`,
with `X = Q^{−x}`, `Y = Q^{−w}`, `V = Q^{−6z}`. On each family of exponents it is geometric in
`R = (ᾱη_π)⁶ Q⁴ X⁶ V` (`localTerm_*`), and the local series sums to the closed form of the scalar
Euler identity.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- `G(φ) G(φ⁻¹) = φ(−1) #F` for a nontrivial character and a primitive additive character. -/
theorem gaussSum_mul_gaussSum_inv_char {F : Type*} [Field F] [Fintype F] {φ : MulChar F ℂ}
    (hφ : φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum φ ψ * gaussSum φ⁻¹ ψ = φ (-1) * Fintype.card F := by
  rw [← mul_gaussSum_inv_eq_gaussSum φ⁻¹, mul_left_comm, gaussSum_mul_gaussSum_eq_card hφ hψ,
    MulChar.inv_apply', inv_neg_one]

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

/-! ### The prime constants -/

omit [NeZero π] in
/-- `χ^r = χ^{r mod 6}`. -/
theorem complexSexticChar_pow_mod (r : ℕ) :
    complexSexticChar (Ideal.span {π}) hlam ^ r =
      complexSexticChar (Ideal.span {π}) hlam ^ (r % 6) := by
  conv_lhs => rw [← Nat.mod_add_div r 6, pow_add, pow_mul,
    (complexSexticChar_powers (Ideal.span {π}) hlam).2.2, one_pow, mul_one]

omit hP in
/-- `#(O/(π)) = Q`. -/
theorem card_quot_eq_absNorm :
    (Fintype.card (O ⧸ Ideal.span {π}) : ℂ) = (Ideal.absNorm (Ideal.span {π}) : ℂ) :=
  card_quot_span π

include hlam hprim in
/-- `|π|² = Q`. -/
theorem norm_sq_eq_absNorm :
    (‖ringComplex π‖ : ℂ) ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℂ) := by
  rw [norm_sq_ringComplex π hlam hprim, card_quot_eq_absNorm]

omit hP in
theorem norm_ringComplex_ne_zero : (‖ringComplex π‖ : ℂ) ≠ 0 := by
  exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne π (ringComplex_injective
    (by rw [h, map_zero]))

/-- `ᾱ π = |π|` for `α = π/|π|`. -/
theorem conj_alpha_mul :
    conj (ringComplex π / (‖ringComplex π‖ : ℂ)) * ringComplex π = (‖ringComplex π‖ : ℂ) := by
  have hN := norm_ringComplex_ne_zero π
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow, sq, mul_div_assoc, div_self hN, mul_one]

include h2 in
/-- **`G₁ G₅ = ε Q`, `G₂ G₄ = Q`, `G₃² = ε Q`**: `G_r G_{6−r} = χ^r(−1) Q` for `6 ∤ r`. -/
theorem gauss_mul_gauss_compl (r : ℕ) (hr : ¬ 6 ∣ r) (hr6 : r ≤ 6) :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ r) (principalTraceChar π (NeZero.ne π)) *
      gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ (6 - r))
        (principalTraceChar π (NeZero.ne π)) =
      complexSexticChar (Ideal.span {π}) hlam (-1) ^ r * (Ideal.absNorm (Ideal.span {π}) : ℂ) := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  set χ := complexSexticChar (Ideal.span {π}) hlam
  have h6 := (complexSexticChar_powers (Ideal.span {π}) hlam).2.2
  have hne : χ ^ r ≠ 1 := fun h => hr ((complexSexticChar_pow_eq_one_iff π hlam h2 r).mp h)
  have hinv : χ ^ (6 - r) = (χ ^ r)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.sub_add_cancel hr6, h6])
  rw [hinv, gaussSum_mul_gaussSum_inv_char hne (principalTraceChar_primitive π (NeZero.ne π)),
    card_quot_eq_absNorm, MulChar.pow_apply' χ (show r ≠ 0 by rintro rfl; exact hr (dvd_zero 6))]

include h2 in
/-- **`G₃ = N Γ`.** -/
theorem gauss_three_eq :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 3) (principalTraceChar π (NeZero.ne π)) =
      (‖ringComplex π‖ : ℂ) * fixedDualAverage π := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have htr : quadraticTraceGauss π (NeZero.ne π) =
      gaussSum (complexQuadraticChar (Ideal.span {π})) (principalTraceChar π (NeZero.ne π)) := by
    have h := sum_traceChar_mul_sq π h2 (u := 1) one_ne_zero
    simp only [one_mul, MulChar.map_one] at h
    rw [quadraticTraceGauss_eq_sum, h]
  rw [(complexSexticChar_powers (Ideal.span {π}) hlam).2.1, ← htr,
    ← normalizedQuadraticTraceGauss_eq_fixedDualAverage π (NeZero.ne π),
    normalizedQuadraticTraceGauss, mul_div_cancel₀ _ (norm_ringComplex_ne_zero π)]

include h2 hprim in
/-- **`Γ² = ε`.** -/
theorem gamma_sq_eq_sextic :
    fixedDualAverage π ^ 2 = complexSexticChar (Ideal.span {π}) hlam (-1) := by
  rw [gamma_sq_eq π hlam h2 hprim, ← (complexSexticChar_powers (Ideal.span {π}) hlam).2.1,
    MulChar.pow_apply' _ (by norm_num), pow_succ, mulChar_neg_one_sq, one_mul]

include h2 in
/-- **`c₄³ = 1`**: `4` is a square. -/
theorem sexticChar_four_pow_three :
    complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4) ^ 3 = 1 := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have h20 : Ideal.Quotient.mk (Ideal.span {π}) 2 ≠ 0 := fun h =>
    h2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [← MulChar.pow_apply' _ (by norm_num), (complexSexticChar_powers (Ideal.span {π}) hlam).2.1,
    show (4 : O) = 2 ^ 2 by norm_num, map_pow, complexQuadraticChar, MulChar.ringHomComp_apply,
    quadraticChar_sq_one' h20, map_one]

omit [NeZero π] in
/-- A unit residue has a sixth root of unity as character value. -/
theorem sexticChar_pow_six (x : O ⧸ Ideal.span {π}) (hx : IsUnit x) :
    complexSexticChar (Ideal.span {π}) hlam x ^ 6 = 1 := by
  rw [← MulChar.pow_apply' _ (by norm_num), (complexSexticChar_powers (Ideal.span {π}) hlam).2.2,
    MulChar.one_apply hx]

omit [NeZero π] in
theorem sexticChar_ne_zero (x : O ⧸ Ideal.span {π}) (hx : IsUnit x) :
    complexSexticChar (Ideal.span {π}) hlam x ≠ 0 :=
  (hx.map _).ne_zero

end Prime

end GaloisForLFunctions.FamilyContinuationTheory
