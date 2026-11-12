import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberIsAnAngularTwist

/-!
# The root number of a row is the square of the theta coefficient

Let `c = π₁ ⋯ π_r` be a product of distinct primary primes `πᵢ ∤ 6`, `g^{(j)} = g_c^{(j)}(1)` the
Gauss sums of the powers of its sextic symbol, `N(c) = |c|²`, `γ₂(c) = g^{(2)}/|c|` the theta
coefficient of the cubic-theta probe at `c` (`thetaGauss`), `Γ(c)` the quadratic phase (a function
of `c mod 4`) and `G(c) = \overline{χ_c(4)} Γ(c)` (`thetaPhase`). Then

* `sexticGaussPow_three_eq`: `g^{(3)} = |c| Γ(c)`: the cross factor of the quadratic Gauss sums is
  `(χ_c(d)χ_d(c))³ = r(c, d)`, the same bicharacter that defines `Γ(cd)/(Γ(c)Γ(d))`;
* `rowHasseDavenport`: `χ_c(4) N(c) g^{(1)} = g^{(3)} (g^{(2)})²`. At a prime this is
  `χ(4)G₁G₂ = −πG₃` combined with `G₂³ = −πN(π)`; the cross factors `X` and `X³·X⁴` agree because
  `X⁶ = 1`;
* `rowRootNumber_eq_thetaPhase_mul_sq`: `g^{(1)}/|c| = G(c) γ₂(c)²`;
* `thetaGauss_cube`: `γ₂(c)³ = μ(c) c/|c|`, and `moebius_angular_mul_conj_thetaGauss`:
  `μ(c) (c/|c|) \overline{γ₂(c)} = γ₂(c)²`.

So the Möbius sign and the angular character of infinity type one in
`rowRootNumber_eq_angularTwist` are the cube of the theta coefficient, not independent twists: the
root number of a row is a phase of bounded conductor times the square of the theta coefficient of
the probe at the row modulus. The long columns of the floor bin are first moments over the rows of
`G(u) γ₂(u)²`, the normalized sextic Gauss sums of the row moduli.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### At a prime -/

section Prime

variable (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

include hlam hprim in
/-- `|π|² = N(π)`. -/
theorem normSq_ringComplex_eq_card :
    (Complex.normSq (ringComplex π) : ℂ) = Fintype.card (O ⧸ Ideal.span {π}) := by
  rw [card_quot_eq_absNorm π, ← norm_sq_eq_absNorm π hlam hprim, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

include hlam h2 hprim in
/-- **The cube at a prime.** `G₂³ = −π N(π)`. -/
theorem sexticGaussPow_two_cube_prime :
    sexticGaussPow 2 π 1 ^ 3 = -ringComplex π * (Complex.normSq (ringComplex π) : ℂ) := by
  rw [sexticGaussPow_prime π hlam h2 hprim two_ne_zero,
    (complexSexticChar_powers (Ideal.span {π}) hlam).1, normSq_ringComplex_eq_card π hlam hprim,
    ← Nat.card_eq_fintype_card]
  convert cubicGauss_cube ringComplex ringComplex_injective (Ideal.span {π}) hlam π rfl hprim _
    (principalTraceChar_primitive π (NeZero.ne π)) using 3 <;> rfl

include hlam h2 hprim in
/-- **Hasse–Davenport at a prime.** `χ(4) N(π) G₁ = G₃ G₂²`: multiply `χ(4)G₁G₂ = −πG₃` by `G₂²`
and use `G₂³ = −πN(π)`. -/
theorem rowHasseDavenport_prime :
    sexticSymbol 4 π * (Complex.normSq (ringComplex π) : ℂ) * sexticGaussPow 1 π 1 =
      sexticGaussPow 3 π 1 * sexticGaussPow 2 π 1 ^ 2 := by
  have hp := rowGauss_product_prime π hlam h2 hprim
  unfold rowGaussProduct at hp
  have hc := sexticGaussPow_two_cube_prime π hlam h2 hprim
  refine mul_left_cancel₀ (FamilyContinuationTheory.ringComplex_ne_zero π) ?_
  linear_combination (sexticSymbol 4 π * sexticGaussPow 1 π 1) * hc -
    sexticGaussPow 2 π 1 ^ 2 * hp

include hlam h2 hprim in
/-- **The quadratic Gauss sum at a prime.** `G₃ = |π| Γ(π)`. -/
theorem sexticGaussPow_three_prime :
    sexticGaussPow 3 π 1 = (‖ringComplex π‖ : ℂ) * fixedDualAverage π := by
  rw [sexticGaussPow_prime π hlam h2 hprim three_ne_zero]
  exact gauss_three_eq π hlam h2

end Prime

/-! ### The composite step -/

/-- **The step.** For coprime primary `c, d` prime to `2`, Hasse–Davenport and the quadratic
evaluation pass from `c` and `d` to `cd`. The cross factor `X = χ_c(d)χ_d(c)` enters as `X` on the
left and `X³X⁴ = X⁷ = X` on the right (`X⁶ = 1`); `X³ = r(c, d)` by reciprocity, the bicharacter
with `Γ(cd) = r(c, d)Γ(c)Γ(d)`. -/
theorem rowTheta_mul (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d)
    (hc : lambda ^ 2 ∣ c - 1) (hd : lambda ^ 2 ∣ d - 1) (hc2 : IsCoprime c 2) (hd2 : IsCoprime d 2)
    (Hc : sexticSymbol 4 c * (Complex.normSq (ringComplex c) : ℂ) * sexticGaussPow 1 c 1 =
      sexticGaussPow 3 c 1 * sexticGaussPow 2 c 1 ^ 2)
    (Hd : sexticSymbol 4 d * (Complex.normSq (ringComplex d) : ℂ) * sexticGaussPow 1 d 1 =
      sexticGaussPow 3 d 1 * sexticGaussPow 2 d 1 ^ 2)
    (Qc : sexticGaussPow 3 c 1 = (‖ringComplex c‖ : ℂ) * fixedDualAverage c)
    (Qd : sexticGaussPow 3 d 1 = (‖ringComplex d‖ : ℂ) * fixedDualAverage d) :
    haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
    (sexticSymbol 4 (c * d) * (Complex.normSq (ringComplex (c * d)) : ℂ) *
        sexticGaussPow 1 (c * d) 1 =
      sexticGaussPow 3 (c * d) 1 * sexticGaussPow 2 (c * d) 1 ^ 2) ∧
    sexticGaussPow 3 (c * d) 1 = (‖ringComplex (c * d)‖ : ℂ) * fixedDualAverage (c * d) := by
  haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
  have hc2' := not_mem_two_of_isCoprime hc2
  have hd2' := not_mem_two_of_isCoprime hd2
  have hrec : sexticSymbol c d = quadraticPhase c d * sexticSymbol d c :=
    sexticSymbol_reciprocity hc hd hc2 hd2 hcd
  have hY6 : sexticSymbol d c ^ 6 = 1 := sexticSymbol_pow_six hc hc2 hcd.symm
  have hZ6 : sexticSymbol c d ^ 6 = 1 := sexticSymbol_pow_six hd hd2 hcd
  have hr2 : quadraticPhase c d ^ 2 = 1 := quadraticPhase_sq hc2' hd2'
  have hX6 : (sexticSymbol d c * sexticSymbol c d) ^ 6 = 1 := by rw [mul_pow, hY6, hZ6, one_mul]
  have hΓ : fixedDualAverage (c * d) =
      quadraticPhase c d * fixedDualAverage c * fixedDualAverage d := by
    have h1 := gamma_ne_zero hc2'
    have h2 := gamma_ne_zero hd2'
    rw [quadraticPhase]
    field_simp
  rw [sexticGaussPow_mul 1 c d hcd 1, sexticGaussPow_mul 2 c d hcd 1,
    sexticGaussPow_mul 3 c d hcd 1, sexticSymbol_mul_denominator]
  simp only [map_mul, norm_mul, Complex.ofReal_mul]
  rw [hΓ]
  refine ⟨?_, ?_⟩
  · linear_combination
      (-(sexticSymbol d c * sexticSymbol c d *
          (sexticSymbol 4 c * (Complex.normSq (ringComplex c) : ℂ) * sexticGaussPow 1 c 1) *
          (sexticSymbol 4 d * (Complex.normSq (ringComplex d) : ℂ) * sexticGaussPow 1 d 1))) * hX6 +
      (sexticSymbol d c * sexticSymbol c d) ^ 7 * sexticGaussPow 3 d 1 * sexticGaussPow 2 d 1 ^ 2 *
        Hc +
      (sexticSymbol d c * sexticSymbol c d) ^ 7 *
        (sexticSymbol 4 c * (Complex.normSq (ringComplex c) : ℂ) * sexticGaussPow 1 c 1) * Hd
  · rw [Qc, Qd, hrec]
    linear_combination
      ((‖ringComplex c‖ : ℂ) * fixedDualAverage c * (‖ringComplex d‖ : ℂ) * fixedDualAverage d) *
        (quadraticPhase c d ^ 3 * hY6 + quadraticPhase c d * hr2)

/-! ### Products of distinct primes -/

/-- **Hasse–Davenport and the quadratic evaluation for a row.** For a finite set `s` of pairwise
coprime nonzero primary primes `π ∤ 6` and `c = Π_{π ∈ s} π`:
`χ_c(4) N(c) g^{(1)} = g^{(3)} (g^{(2)})²` and `g^{(3)} = |c| Γ(c)`. -/
theorem rowHasseDavenport (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)] :
    (sexticSymbol 4 (∏ π ∈ s, π) * (Complex.normSq (ringComplex (∏ π ∈ s, π)) : ℂ) *
        sexticGaussPow 1 (∏ π ∈ s, π) 1 =
      sexticGaussPow 3 (∏ π ∈ s, π) 1 * sexticGaussPow 2 (∏ π ∈ s, π) 1 ^ 2) ∧
    sexticGaussPow 3 (∏ π ∈ s, π) 1 =
      (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) * fixedDualAverage (∏ π ∈ s, π) := by
  induction s using Finset.induction_on generalizing hne with
  | empty =>
    have h1 : (∏ π ∈ (∅ : Finset O), π) = 1 := Finset.prod_empty
    haveI : NeZero (1 : O) := ⟨one_ne_zero⟩
    rw [sexticGaussPow_congr 1 h1, sexticGaussPow_congr 2 h1, sexticGaussPow_congr 3 h1, h1,
      sexticGaussPow_one_modulus, sexticGaussPow_one_modulus, sexticGaussPow_one_modulus,
      sexticSymbol_one_denominator, fixedDualAverage_one]
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
    obtain ⟨Ht, Qt⟩ := ih hnz' hmax' hlam' h2' hprim' hcop'
    obtain ⟨-, hPt, h2t⟩ := normSq_sexticGaussPow_prod t hnz' hmax' hlam' h2' hprim' hcop'
      (j := 1) one_ne_zero (by norm_num)
    have hcopπ : IsCoprime π (∏ x ∈ t, x) :=
      IsCoprime.prod_right fun x hx => hcop hπ (hsub x hx) (fun h => hπt (h ▸ hx))
    have hπ2 : IsCoprime π 2 := isCoprime_two_of_prime (prime_of_isMaximal_span π) (h2 π hπ)
    obtain ⟨H, Q⟩ := rowTheta_mul π (∏ x ∈ t, x) hcopπ (hprim π hπ) hPt hπ2 h2t
      (rowHasseDavenport_prime π (hlam π hπ) (h2 π hπ) (hprim π hπ)) Ht
      (sexticGaussPow_three_prime π (hlam π hπ) (h2 π hπ) (hprim π hπ)) Qt
    have he : ∏ x ∈ insert π t, x = π * ∏ x ∈ t, x := Finset.prod_insert hπt
    haveI : NeZero (π * ∏ x ∈ t, x) := ⟨mul_ne_zero (hnz π hπ) ht0⟩
    rw [sexticGaussPow_congr 1 he, sexticGaussPow_congr 2 he, sexticGaussPow_congr 3 he, he]
    exact ⟨H, Q⟩

/-! ### The root number and the cube of the theta coefficient -/

section Row

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop

/-- `|c| ≠ 0`, `N(c) = |c|²` and `\overline{χ_c(4)} χ_c(4) = 1`. -/
theorem row_norm_facts :
    (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) ≠ 0 ∧
      (Complex.normSq (ringComplex (∏ π ∈ s, π)) : ℂ) = (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) ^ 2 ∧
      conj (sexticSymbol 4 (∏ π ∈ s, π)) * sexticSymbol 4 (∏ π ∈ s, π) = 1 := by
  obtain ⟨-, hP, hc2⟩ := normSq_sexticGaussPow_prod s hnz hmax hlam h2 hprim hcop
    (j := 1) one_ne_zero (by norm_num)
  set c := ∏ π ∈ s, π
  have hc0 : c ≠ 0 := NeZero.ne c
  have hA0 : ringComplex c ≠ 0 := fun h => hc0 (ringComplex_injective (by rw [h, map_zero]))
  have h4 : IsCoprime (4 : O) c := by
    have : IsCoprime c ((2 : O) ^ 2) := hc2.pow_right
    exact (by norm_num : ((2 : O) ^ 2) = 4) ▸ this.symm
  have hχ : ‖sexticSymbol 4 c‖ = 1 := norm_sexticSymbol_eq_one hc0 hP hc2 h4
  refine ⟨by exact_mod_cast norm_ne_zero_iff.mpr hA0, ?_, ?_⟩
  · rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  · rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]
    norm_num

/-- **The root number of a row is the square of the theta coefficient.**
`g^{(1)}/|c| = G(c) γ₂(c)²`, `G(c) = \overline{χ_c(4)} Γ(c)`, `γ₂(c) = g^{(2)}/|c|`. -/
theorem rowRootNumber_eq_thetaPhase_mul_sq :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) =
      thetaPhase (∏ π ∈ s, π) * thetaGauss (∏ π ∈ s, π) ^ 2 := by
  obtain ⟨H, Q⟩ := rowHasseDavenport s hnz hmax hlam h2 hprim hcop
  obtain ⟨ha0, hN, hχ⟩ := row_norm_facts s hnz hmax hlam h2 hprim hcop
  set c := ∏ π ∈ s, π
  rw [Q, hN] at H
  unfold thetaPhase thetaGauss
  set a : ℂ := (‖ringComplex c‖ : ℂ)
  -- `g₁ |c| = \overline{χ(4)} Γ g₂²`
  have key : sexticGaussPow 1 c 1 * a =
      conj (sexticSymbol 4 c) * fixedDualAverage c * sexticGaussPow 2 c 1 ^ 2 := by
    refine mul_left_cancel₀ ha0 ?_
    linear_combination conj (sexticSymbol 4 c) * H - a ^ 2 * sexticGaussPow 1 c 1 * hχ
  have e : conj (sexticSymbol 4 c) * fixedDualAverage c * (sexticGaussPow 2 c 1 / a) ^ 2 =
      conj (sexticSymbol 4 c) * fixedDualAverage c * sexticGaussPow 2 c 1 ^ 2 / a ^ 2 := by
    rw [div_pow, mul_div_assoc]
  rw [e, ← key, sq, mul_div_mul_right _ _ ha0]

/-- **The cube of the theta coefficient.** `γ₂(c)³ = μ(c) c/|c|` with `μ(c) = (−1)^{|s|}`:
multiply the row Gauss identity `χ_c(4)g¹g² = μ(c)c g³` by `N(c)` and insert Hasse–Davenport. -/
theorem thetaGauss_cube :
    thetaGauss (∏ π ∈ s, π) ^ 3 =
      (-1) ^ s.card * (ringComplex (∏ π ∈ s, π) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) := by
  obtain ⟨H, -⟩ := rowHasseDavenport s hnz hmax hlam h2 hprim hcop
  have hR := rowGauss_product s hnz hmax hlam h2 hprim hcop
  unfold rowGaussProduct at hR
  obtain ⟨ha0, hN, -⟩ := row_norm_facts s hnz hmax hlam h2 hprim hcop
  obtain ⟨hN3, -, -⟩ := normSq_sexticGaussPow_prod s hnz hmax hlam h2 hprim hcop
    (j := 3) three_ne_zero (by norm_num)
  have hA0 : ringComplex (∏ π ∈ s, π) ≠ 0 := fun h =>
    NeZero.ne (∏ π ∈ s, π) (ringComplex_injective (by rw [h, map_zero]))
  have hg3 : sexticGaussPow 3 (∏ π ∈ s, π) 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN3
    exact hA0 (Complex.normSq_eq_zero.mp hN3.symm)
  have hcube : sexticGaussPow 2 (∏ π ∈ s, π) 1 ^ 3 = (-1) ^ s.card * ringComplex (∏ π ∈ s, π) *
      (Complex.normSq (ringComplex (∏ π ∈ s, π)) : ℂ) := by
    refine mul_left_cancel₀ hg3 ?_
    linear_combination (-sexticGaussPow 2 (∏ π ∈ s, π) 1) * H +
      (Complex.normSq (ringComplex (∏ π ∈ s, π)) : ℂ) * hR
  unfold thetaGauss
  rw [div_pow, hcube, hN]
  field_simp

/-- **The Möbius sign and the angular twist are the cube of the theta coefficient.**
`μ(c) (c/|c|) \overline{γ₂(c)} = γ₂(c)²`. -/
theorem moebius_angular_mul_conj_thetaGauss :
    (-1) ^ s.card * (ringComplex (∏ π ∈ s, π) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
        conj (thetaGauss (∏ π ∈ s, π)) =
      thetaGauss (∏ π ∈ s, π) ^ 2 := by
  obtain ⟨hN2, -, -⟩ := normSq_sexticGaussPow_prod s hnz hmax hlam h2 hprim hcop
    (j := 2) two_ne_zero (by norm_num)
  obtain ⟨ha0, hN, -⟩ := row_norm_facts s hnz hmax hlam h2 hprim hcop
  rw [← thetaGauss_cube s hnz hmax hlam h2 hprim hcop]
  set c := ∏ π ∈ s, π
  have hu : thetaGauss c * conj (thetaGauss c) = 1 := by
    unfold thetaGauss
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, hN2, hN, ← sq,
      div_self (pow_ne_zero 2 ha0)]
  linear_combination thetaGauss c ^ 2 * hu

end Row

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
