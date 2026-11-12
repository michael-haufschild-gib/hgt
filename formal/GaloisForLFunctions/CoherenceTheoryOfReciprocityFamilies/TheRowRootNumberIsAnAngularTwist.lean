import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberCarriesTheMoebiusSign
import GaloisForLFunctions.FamilyContinuationTheory.TheLocalFactorOfThePoissonSeriesIsExplicit

/-!
# The root number of a row is an angular twist of a conjugate cubic Gauss sum

For a squarefree `c = π₁ ⋯ π_r` of distinct primary primes `πᵢ ∤ 6`, the three composite Gauss sums
`g^{(j)} = g_c^{(j)}(1)` of the sextic, cubic and quadratic symbols of `c` have modulus `|c|`
(`normSq_sexticGaussPow_prod`): at a prime `|G(χ^j)|² = N(π)`, and the cross factors of the
twisted multiplicativity are unimodular. With the row Gauss identity
`χ_c(4) g^{(1)} g^{(2)} = μ(c) c g^{(3)}` this gives (`rowRootNumber_eq_angularTwist`)

`g^{(1)}/|c| = μ(c) · (c/|c|) · \overline{χ_c(4)} · (g^{(3)}/|c|) · \overline{g^{(2)}/|c|}`.

The normalized sextic Gauss sum of the row modulus — the root number of the row — is the Möbius
value, times the angular character `c ↦ c/|c|` of infinity type one, times the conjugate normalized
cubic Gauss sum, times unimodular factors of bounded conductor (`χ_c(4)` and the normalized
quadratic Gauss sum). The long columns of the floor bin are therefore sums of Möbius-signed
conjugate cubic Gauss sums twisted by an angular character of infinity type one.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### Norms at a prime -/

/-- **`|G(χ^j)|² = N(π)` at a prime** for `j` not divisible by `6`. -/
theorem normSq_sexticGaussPow_prime (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal]
    (hlam : lambda ∉ Ideal.span {π}) (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : ¬ 6 ∣ j) :
    Complex.normSq (sexticGaussPow j π 1) = Complex.normSq (ringComplex π) := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hχ : complexSexticChar (Ideal.span {π}) hlam ^ j ≠ 1 := fun h =>
    hj6 ((complexSexticChar_pow_eq_one_iff π hlam h2 j).mp h)
  have hψ := principalTraceChar_primitive π (NeZero.ne π)
  rw [sexticGaussPow_prime π hlam h2 hprim hj0]
  have hcard := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at hcard
  have hN : (Complex.normSq (gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ j)
      (principalTraceChar π (NeZero.ne π))) : ℂ) =
      Fintype.card (O ⧸ Ideal.span {π}) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    exact hcard
  have hπ : (Complex.normSq (ringComplex π) : ℂ) = Fintype.card (O ⧸ Ideal.span {π}) := by
    rw [card_quot_eq_absNorm π, ← norm_sq_eq_absNorm π hlam hprim, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast hN.trans hπ.symm

/-! ### Unimodular symbols -/

theorem isCoprime_two_of_prime {π : O} (hπ : Prime π) (h2 : (2 : O) ∉ Ideal.span {π}) :
    IsCoprime π 2 :=
  (Irreducible.coprime_iff_not_dvd hπ.irreducible).mpr fun h =>
    h2 (Ideal.mem_span_singleton.mpr h)

/-- `|χ_a(x)| = 1` for `a ≠ 0` primary, prime to `2`, and `x` prime to `a`. -/
theorem norm_sexticSymbol_eq_one {x a : O} (ha0 : a ≠ 0) (ha : lambda ^ 2 ∣ a - 1)
    (ha2 : IsCoprime a 2) (hxa : IsCoprime x a) : ‖sexticSymbol x a‖ = 1 := by
  have hq := quadSymbol_sq ha0 ha2 hxa
  have hqn : ‖quadSymbol x a‖ = 1 := by
    have : ‖quadSymbol x a‖ ^ 2 = 1 := by rw [← norm_pow, hq, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  rw [sexticSymbol, norm_mul, norm_pow, CubicJacobi.symbol_norm_one x a ha hxa, hqn]
  norm_num

/-- Products of primary elements are primary. -/
theorem primary_mul {a b : O} (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1) :
    lambda ^ 2 ∣ a * b - 1 := by
  have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left ha b) hb

/-- The Gauss sums of equal moduli agree, whatever the `NeZero` instances. -/
theorem sexticGaussPow_congr (j : ℕ) {c c' : O} [NeZero c] [NeZero c'] (h : c = c') :
    sexticGaussPow j c 1 = sexticGaussPow j c' 1 := by
  subst h
  rfl

theorem sexticGaussPow_one_modulus (j : ℕ) [NeZero (1 : O)] : sexticGaussPow j (1 : O) 1 = 1 := by
  unfold sexticGaussPow
  haveI : Subsingleton (O ⧸ Ideal.span {(1 : O)}) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  have hres : sexticResidue 1 0 = 1 := by
    unfold sexticResidue
    exact sexticSymbol_one_denominator _
  rw [Fintype.sum_subsingleton _ 0, mul_zero, AddChar.map_zero_eq_one, hres, one_pow, mul_one]

/-! ### Norms of the composite Gauss sums -/

/-- **`|g_c^{(j)}(1)|² = |c|²`** for a squarefree product of distinct primary primes, `6 ∤ j`,
together with the primary and parity properties of the product. -/
theorem normSq_sexticGaussPow_prod (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)]
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : ¬ 6 ∣ j) :
    Complex.normSq (sexticGaussPow j (∏ π ∈ s, π) 1) =
        Complex.normSq (ringComplex (∏ π ∈ s, π)) ∧
      lambda ^ 2 ∣ (∏ π ∈ s, π) - 1 ∧ IsCoprime (∏ π ∈ s, π) 2 := by
  induction s using Finset.induction_on generalizing hne with
  | empty =>
    have h1 : (∏ π ∈ (∅ : Finset O), π) = 1 := Finset.prod_empty
    haveI : NeZero (1 : O) := ⟨one_ne_zero⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [sexticGaussPow_congr j h1, sexticGaussPow_one_modulus, h1, map_one]
      simp
    · rw [h1, sub_self]; exact dvd_zero _
    · rw [h1]; exact isCoprime_one_left
  | insert π t hπt ih =>
    have hπ : π ∈ insert π t := Finset.mem_insert_self π t
    haveI : (Ideal.span {π}).IsMaximal := hmax π hπ
    haveI : NeZero π := ⟨hnz π hπ⟩
    have hsub : ∀ x ∈ t, x ∈ insert π t := fun x hx => Finset.mem_insert_of_mem hx
    have ht0 : ∏ x ∈ t, x ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx => hnz x (hsub x hx)
    haveI : NeZero (∏ x ∈ t, x) := ⟨ht0⟩
    obtain ⟨ihN, ihP, ih2⟩ := ih (fun x hx => hnz x (hsub x hx))
      (fun x hx => hmax x (hsub x hx)) (fun x hx => hlam x (hsub x hx))
      (fun x hx => h2 x (hsub x hx)) (fun x hx => hprim x (hsub x hx))
      (hcop.mono (by intro x hx; exact hsub x hx))
    have hcopπ : IsCoprime π (∏ x ∈ t, x) :=
      IsCoprime.prod_right fun x hx => hcop hπ (hsub x hx) (fun h => hπt (h ▸ hx))
    have hπ2 : IsCoprime π 2 := isCoprime_two_of_prime (prime_of_isMaximal_span π) (h2 π hπ)
    have he : ∏ x ∈ insert π t, x = π * ∏ x ∈ t, x := Finset.prod_insert hπt
    haveI : NeZero (π * ∏ x ∈ t, x) := ⟨mul_ne_zero (hnz π hπ) ht0⟩
    -- the cross factor is unimodular
    have hX1 : ‖sexticSymbol (∏ x ∈ t, x) π‖ = 1 :=
      norm_sexticSymbol_eq_one (hnz π hπ) (hprim π hπ) hπ2 hcopπ.symm
    have hX2 : ‖sexticSymbol π (∏ x ∈ t, x)‖ = 1 :=
      norm_sexticSymbol_eq_one ht0 ihP ih2 hcopπ
    have hX1n : Complex.normSq (sexticSymbol (∏ x ∈ t, x) π) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hX1]; norm_num
    have hX2n : Complex.normSq (sexticSymbol π (∏ x ∈ t, x)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hX2]; norm_num
    refine ⟨?_, ?_, ?_⟩
    · rw [sexticGaussPow_congr j he, sexticGaussPow_mul j π (∏ x ∈ t, x) hcopπ 1]
      simp only [map_mul, map_pow, hX1n, hX2n, one_pow, one_mul, mul_one]
      rw [normSq_sexticGaussPow_prime π (hlam π hπ) (h2 π hπ) (hprim π hπ) hj0 hj6, ihN, he,
        map_mul, map_mul]
    · rw [he]; exact primary_mul (hprim π hπ) ihP
    · rw [he]; exact hπ2.mul_left ih2

/-! ### The root number -/

/-- **The root number of a row is an angular twist.** For `c = Π_{π ∈ s} π` as in
`rowGauss_product`, with `|c| = ‖c‖`:
`g^{(1)}/|c| = (−1)^{|s|} (c/|c|) \overline{χ_c(4)} (g^{(3)}/|c|) \overline{(g^{(2)}/|c|)}`. -/
theorem rowRootNumber_eq_angularTwist (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)] :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) =
      (-1) ^ s.card * (ringComplex (∏ π ∈ s, π) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
        conj (sexticSymbol 4 (∏ π ∈ s, π)) *
          (sexticGaussPow 3 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
            conj (sexticGaussPow 2 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) := by
  set c := ∏ π ∈ s, π with hcdef
  have hid := rowGauss_product s hnz hmax hlam h2 hprim hcop
  obtain ⟨hN2, hP, hc2⟩ := normSq_sexticGaussPow_prod s hnz hmax hlam h2 hprim hcop
    (j := 2) (by norm_num) (by norm_num)
  unfold rowGaussProduct at hid
  set g1 := sexticGaussPow 1 c 1
  set g2 := sexticGaussPow 2 c 1
  set g3 := sexticGaussPow 3 c 1
  set A := ringComplex c
  set χ4 := sexticSymbol 4 c
  have hc0 : c ≠ 0 := hne.ne
  have hA0 : A ≠ 0 := by
    intro h
    exact hc0 (ringComplex_injective (by rw [map_zero]; exact h))
  set a : ℝ := ‖A‖
  have ha0 : (a : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hA0)
  -- `|χ_c(4)| = 1`
  have h4 : IsCoprime (4 : O) c := by
    have : IsCoprime c ((2 : O) ^ 2) := hc2.pow_right
    exact (by norm_num : ((2 : O) ^ 2) = 4) ▸ this.symm
  have hχ : ‖χ4‖ = 1 := norm_sexticSymbol_eq_one hc0 hP hc2 h4
  have hχc : conj χ4 * χ4 = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]
    norm_num
  -- `g₂ \overline{g₂} = |c|²`
  have hg2 : g2 * conj g2 = (a : ℂ) ^ 2 := by
    rw [Complex.mul_conj, hN2, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hconj_div : conj (g2 / (a : ℂ)) = conj g2 / (a : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal]
  rw [hconj_div]
  -- solve the identity for `g₁`
  have hsign : ((-1 : ℂ) ^ s.card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  calc g1 / (a : ℂ) = g1 * (conj χ4 * χ4) * (g2 * conj g2) / (a : ℂ) ^ 3 := by
        rw [hχc, hg2, mul_one]
        field_simp
    _ = conj χ4 * (χ4 * g1 * g2) * conj g2 / (a : ℂ) ^ 3 := by ring
    _ = conj χ4 * ((-1) ^ s.card * A * g3) * conj g2 / (a : ℂ) ^ 3 := by rw [hid]
    _ = _ := by
        field_simp

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
