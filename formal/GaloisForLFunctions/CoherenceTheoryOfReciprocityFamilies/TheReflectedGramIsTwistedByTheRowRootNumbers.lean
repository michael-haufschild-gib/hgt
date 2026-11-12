import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheGramOfTwoRowsIsACompletedSum
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberIsTheSquareOfTheThetaCoefficient

/-!
# The reflected Gram is twisted by the root numbers of the rows

`gramEntry_eq_completedSum` writes the Gram entry of two coprime rows `u₁, u₂` as a completed sum
over the dual frequencies `h mod u₁u₂` with coefficient
`C(h) = χ_{u₁}(u₂) χ_{u₂}(u₁)⁵ g_{u₁}^{(1)}(−h) g_{u₂}^{(5)}(−h)`. For `h` prime to `u₁u₂`
(`gramCoeff_eq`):

`C(h) = r(u₂, u₁) χ_{u₂}(−1) · \overline{χ_{u₁}(−h)} χ_{u₂}(−h) · g_{u₁}^{(1)}(1) \overline{g_{u₂}^{(1)}(1)}`.

The reciprocity factor is the quadratic bicharacter `r` of the residues modulo four (sextic
reciprocity), the frequency enters through the column `\overline{χ_{u₁}(−h)} χ_{u₂}(−h)` of the same
kernel, and the rows enter through their root numbers, rank one (`g^{(5)} = χ(−1) \overline{g^{(1)}}`,
`sexticGaussPow_one_mul_five`). For rows that are products of distinct primary primes the root
numbers are `|u| G(u) γ₂(u)²` (`gramCoeff_eq_thetaSquares`). So the reflection of the sextic Gram of
amplitudes `α(u)` is the sextic Gram of the amplitudes `α(u) G(u) γ₂(u)²` against the dual columns,
weighted by `r`. At a sixth power `−h = k⁶` every row character is `1` and the coefficient is
`r(u₂, u₁) χ_{u₂}(−1) |u₁||u₂| Φ(u₁) \overline{Φ(u₂)}`, `Φ = G γ₂²`
(`gramCoeff_sixthPower`): the principal dual frequencies are coherent, with the root-number-twisted
amplitudes as matched phases.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### Unimodular symbols and the dual twist -/

/-- `\overline{χ_c(x)} χ_c(x) = 1` for `c ≠ 0` primary, prime to `2`, and `x` prime to `c`. -/
theorem conj_sexticSymbol_mul_self {x c : O} (hc0 : c ≠ 0) (hc : lambda ^ 2 ∣ c - 1)
    (hc2 : IsCoprime c 2) (hxc : IsCoprime x c) : conj (sexticSymbol x c) * sexticSymbol x c = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sexticSymbol_eq_one hc0 hc hc2 hxc]
  norm_num

/-- `\overline{χ_c(x)} = χ_c(x)⁵`. -/
theorem conj_sexticSymbol_eq_pow_five {x c : O} (hc0 : c ≠ 0) (hc : lambda ^ 2 ∣ c - 1)
    (hc2 : IsCoprime c 2) (hxc : IsCoprime x c) : conj (sexticSymbol x c) = sexticSymbol x c ^ 5 := by
  have h1 := conj_sexticSymbol_mul_self hc0 hc hc2 hxc
  have h6 := sexticSymbol_pow_six hc hc2 hxc
  linear_combination sexticSymbol x c ^ 5 * h1 - conj (sexticSymbol x c) * h6

/-- **The dual twist.** `g_c^{(j)}(x) = \overline{χ_c(x)}^j g_c^{(j)}(1)` for `x` prime to `c`. -/
theorem sexticGaussPow_eq_conj_mul {c : O} [NeZero c] (hc : lambda ^ 2 ∣ c - 1) (hc2 : IsCoprime c 2)
    {x : O} (hxc : IsCoprime x c) (j : ℕ) :
    sexticGaussPow j c x = conj (sexticSymbol x c) ^ j * sexticGaussPow j c 1 := by
  have h := sexticSymbol_pow_mul_sexticGaussPow j c hxc 1
  rw [mul_one] at h
  rw [← h, ← mul_assoc, ← mul_pow, conj_sexticSymbol_mul_self (NeZero.ne c) hc hc2 hxc, one_pow,
    one_mul]

/-! ### `g^{(1)} g^{(5)} = χ(−1) N` -/

/-- At a prime: `G₁ G₅ = χ(−1) N(π)`. -/
theorem sexticGaussPow_one_mul_five_prime (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal]
    (hlam : lambda ∉ Ideal.span {π}) (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1) :
    sexticGaussPow 1 π 1 * sexticGaussPow 5 π 1 =
      sexticSymbol (-1) π * (Complex.normSq (ringComplex π) : ℂ) := by
  rw [sexticGaussPow_prime π hlam h2 hprim one_ne_zero,
    sexticGaussPow_prime π hlam h2 hprim (by norm_num : (5 : ℕ) ≠ 0), pow_one,
    sexticSymbol_prime π hlam h2 hprim, map_neg, map_one, normSq_ringComplex_eq_card π hlam hprim]
  exact gaussSum_mul_gaussSum_inv π hlam

/-- **`g^{(1)} g^{(5)} = χ_c(−1) N(c)`** for a product of distinct primary primes `π ∤ 6`: the cross
factors contribute `X · X⁵ = X⁶ = 1`. -/
theorem sexticGaussPow_one_mul_five (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)] :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 * sexticGaussPow 5 (∏ π ∈ s, π) 1 =
      sexticSymbol (-1) (∏ π ∈ s, π) * (Complex.normSq (ringComplex (∏ π ∈ s, π)) : ℂ) := by
  induction s using Finset.induction_on generalizing hne with
  | empty =>
    have h1 : (∏ π ∈ (∅ : Finset O), π) = 1 := Finset.prod_empty
    haveI : NeZero (1 : O) := ⟨one_ne_zero⟩
    rw [sexticGaussPow_congr 1 h1, sexticGaussPow_congr 5 h1, h1, sexticGaussPow_one_modulus,
      sexticGaussPow_one_modulus, sexticSymbol_one_denominator]
    simp
  | insert π t hπt ih =>
    have hπ : π ∈ insert π t := Finset.mem_insert_self π t
    haveI : (Ideal.span {π}).IsMaximal := hmax π hπ
    haveI : NeZero π := ⟨hnz π hπ⟩
    have hsub : ∀ x ∈ t, x ∈ insert π t := fun x hx => Finset.mem_insert_of_mem hx
    have ht0 : ∏ x ∈ t, x ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx => hnz x (hsub x hx)
    haveI : NeZero (∏ x ∈ t, x) := ⟨ht0⟩
    have hnz' := fun x hx => hnz x (hsub x hx)
    have hmax' := fun x hx => hmax x (hsub x hx)
    have hlam' := fun x hx => hlam x (hsub x hx)
    have h2' := fun x hx => h2 x (hsub x hx)
    have hprim' := fun x hx => hprim x (hsub x hx)
    have hcop' := hcop.mono (by intro x hx; exact hsub x hx)
    have Ht := ih hnz' hmax' hlam' h2' hprim' hcop'
    obtain ⟨-, hPt, h2t⟩ := normSq_sexticGaussPow_prod t hnz' hmax' hlam' h2' hprim' hcop'
      (j := 1) one_ne_zero (by norm_num)
    have hcopπ : IsCoprime π (∏ x ∈ t, x) :=
      IsCoprime.prod_right fun x hx => hcop hπ (hsub x hx) (fun h => hπt (h ▸ hx))
    have hπ2 : IsCoprime π 2 := isCoprime_two_of_prime (prime_of_isMaximal_span π) (h2 π hπ)
    have Hπ := sexticGaussPow_one_mul_five_prime π (hlam π hπ) (h2 π hπ) (hprim π hπ)
    have hX6 : (sexticSymbol (∏ x ∈ t, x) π * sexticSymbol π (∏ x ∈ t, x)) ^ 6 = 1 := by
      rw [mul_pow, sexticSymbol_pow_six (hprim π hπ) hπ2 hcopπ.symm,
        sexticSymbol_pow_six hPt h2t hcopπ, one_mul]
    have he : ∏ x ∈ insert π t, x = π * ∏ x ∈ t, x := Finset.prod_insert hπt
    haveI : NeZero (π * ∏ x ∈ t, x) := ⟨mul_ne_zero (hnz π hπ) ht0⟩
    rw [sexticGaussPow_congr 1 he, sexticGaussPow_congr 5 he, he,
      sexticGaussPow_mul 1 π (∏ x ∈ t, x) hcopπ 1, sexticGaussPow_mul 5 π (∏ x ∈ t, x) hcopπ 1,
      sexticSymbol_mul_denominator]
    simp only [map_mul, Complex.ofReal_mul]
    linear_combination
      (sexticGaussPow 1 π 1 * sexticGaussPow 5 π 1 *
        (sexticGaussPow 1 (∏ x ∈ t, x) 1 * sexticGaussPow 5 (∏ x ∈ t, x) 1)) * hX6 +
      (sexticGaussPow 1 (∏ x ∈ t, x) 1 * sexticGaussPow 5 (∏ x ∈ t, x) 1) * Hπ +
      (sexticSymbol (-1) π * (Complex.normSq (ringComplex π) : ℂ)) * Ht

/-! ### The coefficient of the completed sum -/

/-- **The reflected coefficient.** For coprime primary `u₁, u₂` prime to `2` with
`g_{u₂}^{(1)} g_{u₂}^{(5)} = χ_{u₂}(−1) N(u₂)` and `|g_{u₂}^{(1)}|² = N(u₂)`, and `x` prime to
`u₁u₂`, the coefficient of `gramEntry_eq_completedSum` at the frequency `x` is
`r(u₂, u₁) χ_{u₂}(−1) \overline{χ_{u₁}(−x)} χ_{u₂}(−x) g_{u₁}^{(1)}(1) \overline{g_{u₂}^{(1)}(1)}`. -/
theorem gramCoeff_eq (u₁ u₂ : O) [NeZero u₁] [NeZero u₂] (hcop : IsCoprime u₁ u₂)
    (hp₁ : lambda ^ 2 ∣ u₁ - 1) (hp₂ : lambda ^ 2 ∣ u₂ - 1) (h2₁ : IsCoprime u₁ 2)
    (h2₂ : IsCoprime u₂ 2)
    (H₂ : sexticGaussPow 1 u₂ 1 * sexticGaussPow 5 u₂ 1 =
      sexticSymbol (-1) u₂ * (Complex.normSq (ringComplex u₂) : ℂ))
    (N₂ : Complex.normSq (sexticGaussPow 1 u₂ 1) = Complex.normSq (ringComplex u₂))
    {x : O} (hx₁ : IsCoprime x u₁) (hx₂ : IsCoprime x u₂) :
    sexticSymbol u₂ u₁ * sexticSymbol u₁ u₂ ^ 5 * sexticGaussPow 1 u₁ (-x) *
        sexticGaussPow 5 u₂ (-x) =
      quadraticPhase u₂ u₁ * sexticSymbol (-1) u₂ *
        (conj (sexticSymbol (-x) u₁) * sexticSymbol (-x) u₂) *
          (sexticGaussPow 1 u₁ 1 * conj (sexticGaussPow 1 u₂ 1)) := by
  have hx₁' : IsCoprime (-x) u₁ := hx₁.neg_left
  have hx₂' : IsCoprime (-x) u₂ := hx₂.neg_left
  have hrec : sexticSymbol u₂ u₁ = quadraticPhase u₂ u₁ * sexticSymbol u₁ u₂ :=
    sexticSymbol_reciprocity hp₂ hp₁ h2₂ h2₁ hcop.symm
  have hZ6 : sexticSymbol u₁ u₂ ^ 6 = 1 := sexticSymbol_pow_six hp₂ h2₂ hcop
  -- `\overline{χ_{u₂}(−x)}⁵ = χ_{u₂}(−x)`
  have hb5 : conj (sexticSymbol (-x) u₂) ^ 5 = sexticSymbol (-x) u₂ := by
    rw [conj_sexticSymbol_eq_pow_five (NeZero.ne u₂) hp₂ h2₂ hx₂', ← pow_mul,
      show 5 * 5 = 6 * 4 + 1 by norm_num, pow_succ, pow_mul, sexticSymbol_pow_six hp₂ h2₂ hx₂',
      one_pow, one_mul]
  -- `g^{(5)} = χ(−1) \overline{g^{(1)}}`
  have hk5 : sexticGaussPow 5 u₂ 1 = sexticSymbol (-1) u₂ * conj (sexticGaussPow 1 u₂ 1) := by
    have hk0 : sexticGaussPow 1 u₂ 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at N₂
      exact NeZero.ne u₂ (ringComplex_injective (by
        rw [map_zero]; exact (Complex.normSq_eq_zero.mp N₂.symm)))
    have hmc := Complex.mul_conj (sexticGaussPow 1 u₂ 1)
    have hNc : (Complex.normSq (sexticGaussPow 1 u₂ 1) : ℂ) = Complex.normSq (ringComplex u₂) := by
      rw [N₂]
    refine mul_left_cancel₀ hk0 ?_
    linear_combination H₂ - sexticSymbol (-1) u₂ * hmc - sexticSymbol (-1) u₂ * hNc
  rw [sexticGaussPow_eq_conj_mul hp₁ h2₁ hx₁' 1, sexticGaussPow_eq_conj_mul hp₂ h2₂ hx₂' 5]
  linear_combination
    (sexticSymbol u₁ u₂ ^ 5 * (conj (sexticSymbol (-x) u₁) ^ 1 * sexticGaussPow 1 u₁ 1) *
      (conj (sexticSymbol (-x) u₂) ^ 5 * sexticGaussPow 5 u₂ 1)) * hrec +
    (quadraticPhase u₂ u₁ * conj (sexticSymbol (-x) u₁) * sexticGaussPow 1 u₁ 1 *
      conj (sexticSymbol (-x) u₂) ^ 5 * sexticGaussPow 5 u₂ 1) * hZ6 +
    (quadraticPhase u₂ u₁ * conj (sexticSymbol (-x) u₁) * sexticGaussPow 1 u₁ 1 *
      sexticGaussPow 5 u₂ 1) * hb5 +
    (quadraticPhase u₂ u₁ * conj (sexticSymbol (-x) u₁) * sexticGaussPow 1 u₁ 1 *
      sexticSymbol (-x) u₂) * hk5

/-! ### Rows that are products of distinct primes -/

section Rows

variable (s₁ s₂ : Finset O)
  (hnz₁ : ∀ π ∈ s₁, π ≠ 0) (hmax₁ : ∀ π ∈ s₁, (Ideal.span {π}).IsMaximal)
  (hlam₁ : ∀ π ∈ s₁, lambda ∉ Ideal.span {π}) (h2₁ : ∀ π ∈ s₁, (2 : O) ∉ Ideal.span {π})
  (hprim₁ : ∀ π ∈ s₁, lambda ^ 2 ∣ π - 1) (hcop₁ : (s₁ : Set O).Pairwise IsCoprime)
  (hnz₂ : ∀ π ∈ s₂, π ≠ 0) (hmax₂ : ∀ π ∈ s₂, (Ideal.span {π}).IsMaximal)
  (hlam₂ : ∀ π ∈ s₂, lambda ∉ Ideal.span {π}) (h2₂ : ∀ π ∈ s₂, (2 : O) ∉ Ideal.span {π})
  (hprim₂ : ∀ π ∈ s₂, lambda ^ 2 ∣ π - 1) (hcop₂ : (s₂ : Set O).Pairwise IsCoprime)
  [NeZero (∏ π ∈ s₁, π)] [NeZero (∏ π ∈ s₂, π)]
  (hcop : IsCoprime (∏ π ∈ s₁, π) (∏ π ∈ s₂, π))

include hnz₁ hmax₁ hlam₁ h2₁ hprim₁ hcop₁ hnz₂ hmax₂ hlam₂ h2₂ hprim₂ hcop₂ hcop

/-- **The reflected Gram is twisted by the squares of the theta coefficients.** For rows
`u_i = Π_{π ∈ s_i} π` and `x` prime to `u₁u₂`, the coefficient of the completed sum is
`r(u₂, u₁) χ_{u₂}(−1) \overline{χ_{u₁}(−x)} χ_{u₂}(−x) |u₁||u₂| Φ(u₁) \overline{Φ(u₂)}`, with
`Φ(u) = G(u) γ₂(u)²`. -/
theorem gramCoeff_eq_thetaSquares {x : O} (hx₁ : IsCoprime x (∏ π ∈ s₁, π))
    (hx₂ : IsCoprime x (∏ π ∈ s₂, π)) :
    sexticSymbol (∏ π ∈ s₂, π) (∏ π ∈ s₁, π) * sexticSymbol (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) ^ 5 *
        sexticGaussPow 1 (∏ π ∈ s₁, π) (-x) * sexticGaussPow 5 (∏ π ∈ s₂, π) (-x) =
      quadraticPhase (∏ π ∈ s₂, π) (∏ π ∈ s₁, π) * sexticSymbol (-1) (∏ π ∈ s₂, π) *
        (conj (sexticSymbol (-x) (∏ π ∈ s₁, π)) * sexticSymbol (-x) (∏ π ∈ s₂, π)) *
          ((‖ringComplex (∏ π ∈ s₁, π)‖ : ℂ) * (‖ringComplex (∏ π ∈ s₂, π)‖ : ℂ) *
            ((thetaPhase (∏ π ∈ s₁, π) * thetaGauss (∏ π ∈ s₁, π) ^ 2) *
              conj (thetaPhase (∏ π ∈ s₂, π) * thetaGauss (∏ π ∈ s₂, π) ^ 2))) := by
  obtain ⟨-, hp₁, h2c₁⟩ := normSq_sexticGaussPow_prod s₁ hnz₁ hmax₁ hlam₁ h2₁ hprim₁ hcop₁
    (j := 1) one_ne_zero (by norm_num)
  obtain ⟨N₂, hp₂, h2c₂⟩ := normSq_sexticGaussPow_prod s₂ hnz₂ hmax₂ hlam₂ h2₂ hprim₂ hcop₂
    (j := 1) one_ne_zero (by norm_num)
  have H₂ := sexticGaussPow_one_mul_five s₂ hnz₂ hmax₂ hlam₂ h2₂ hprim₂ hcop₂
  rw [gramCoeff_eq _ _ hcop hp₁ hp₂ h2c₁ h2c₂ H₂ N₂ hx₁ hx₂]
  have R₁ := rowRootNumber_eq_thetaPhase_mul_sq s₁ hnz₁ hmax₁ hlam₁ h2₁ hprim₁ hcop₁
  have R₂ := rowRootNumber_eq_thetaPhase_mul_sq s₂ hnz₂ hmax₂ hlam₂ h2₂ hprim₂ hcop₂
  obtain ⟨a₁, -, -⟩ := row_norm_facts s₁ hnz₁ hmax₁ hlam₁ h2₁ hprim₁ hcop₁
  obtain ⟨a₂, -, -⟩ := row_norm_facts s₂ hnz₂ hmax₂ hlam₂ h2₂ hprim₂ hcop₂
  rw [← R₁, ← R₂, map_div₀, Complex.conj_ofReal]
  field_simp

/-- **The sixth powers are coherent.** At the dual frequency `−x = k⁶`, `k` prime to `u₁u₂`, every row
character is `1` and the coefficient is `r(u₂, u₁) χ_{u₂}(−1) |u₁||u₂| Φ(u₁) \overline{Φ(u₂)}`: rank
one in the root-number-twisted rows. -/
theorem gramCoeff_sixthPower {k : O} (hk₁ : IsCoprime k (∏ π ∈ s₁, π))
    (hk₂ : IsCoprime k (∏ π ∈ s₂, π)) :
    sexticSymbol (∏ π ∈ s₂, π) (∏ π ∈ s₁, π) * sexticSymbol (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) ^ 5 *
        sexticGaussPow 1 (∏ π ∈ s₁, π) (k ^ 6) * sexticGaussPow 5 (∏ π ∈ s₂, π) (k ^ 6) =
      quadraticPhase (∏ π ∈ s₂, π) (∏ π ∈ s₁, π) * sexticSymbol (-1) (∏ π ∈ s₂, π) *
          ((‖ringComplex (∏ π ∈ s₁, π)‖ : ℂ) * (‖ringComplex (∏ π ∈ s₂, π)‖ : ℂ) *
            ((thetaPhase (∏ π ∈ s₁, π) * thetaGauss (∏ π ∈ s₁, π) ^ 2) *
              conj (thetaPhase (∏ π ∈ s₂, π) * thetaGauss (∏ π ∈ s₂, π) ^ 2))) := by
  obtain ⟨-, hp₁, h2c₁⟩ := normSq_sexticGaussPow_prod s₁ hnz₁ hmax₁ hlam₁ h2₁ hprim₁ hcop₁
    (j := 1) one_ne_zero (by norm_num)
  obtain ⟨-, hp₂, h2c₂⟩ := normSq_sexticGaussPow_prod s₂ hnz₂ hmax₂ hlam₂ h2₂ hprim₂ hcop₂
    (j := 1) one_ne_zero (by norm_num)
  have hx₁ : IsCoprime (-k ^ 6) (∏ π ∈ s₁, π) := (hk₁.pow_left).neg_left
  have hx₂ : IsCoprime (-k ^ 6) (∏ π ∈ s₂, π) := (hk₂.pow_left).neg_left
  have h := gramCoeff_eq_thetaSquares s₁ s₂ hnz₁ hmax₁ hlam₁ h2₁ hprim₁ hcop₁ hnz₂ hmax₂ hlam₂
    h2₂ hprim₂ hcop₂ hcop hx₁ hx₂
  -- `χ_u(k⁶) = χ_u(k)⁶ = 1`
  have hsix : ∀ u : O, lambda ^ 2 ∣ u - 1 → IsCoprime u 2 → IsCoprime k u →
      sexticSymbol (k ^ 6) u = 1 := by
    intro u hu hu2 hku
    rw [show k ^ 6 = (k * k) ^ 3 by ring, sexticSymbol_cube_numerator, sexticSymbol_mul_numerator,
      ← sq, ← pow_mul]
    exact sexticSymbol_pow_six hu hu2 hku
  rw [neg_neg, hsix _ hp₁ h2c₁ hk₁, hsix _ hp₂ h2c₂ hk₂, map_one] at h
  linear_combination h

end Rows

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
