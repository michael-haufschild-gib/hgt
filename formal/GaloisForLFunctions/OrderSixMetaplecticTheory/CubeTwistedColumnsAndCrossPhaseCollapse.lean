import GaloisForLFunctions.OrderSixMetaplecticTheory.TheColumnsAreShiftedThetaProducts

/-!
# Mod-4 phase cancellation in column Hasse–Davenport, cube-twisted columns, and cubic cross-phase collapse

Three exact simplifications govern the column dictionary of the order-six metaplectic family:

* **Phase-free column Hasse–Davenport (`conj_quadraticPhase`,
  `column_quadraticPhase_cancel`, `rowRoot_column_hasseDavenport_clean`).** On odd classes `x, c`,
  `r(x, c) ∈ {±1}`, so `\overline{r(n₁ n₂² k³, c)} · r(n₁ k, c) = r(n₁ k, c)² = 1` identically.
  Consequently `rowRoot_column_hasseDavenport` simplifies with **zero** mod-4 Weil phase:
  `(g_c^{(1)}(n₁ n₂² k³) / |c|) · G̃(-2 n₁ n₂) G̃(n₁) = (g_c^{(3)}(n₁ k) / |c|) · G̃(-2 n₁ n₂ c) G̃(n₁ c)`.
* **Conjugate-symbol absorption and cube-multiplied column shift
  (`conj_sexticSymbol_mul_rowRootNumber`, `sexticGauss_mul_cube`,
  `orderB_coupled_column_collapse`).** Multiplying `Φ(c)` by `\overline{χ_c(a)}` shifts to column `a`,
  and multiplying `g_c^{(1)}(a)` by `(d/c)₂` shifts `a ↦ a d³` (`g_c^{(1)}(a d³) = (d/c)₂ g_c^{(1)}(a)`),
  collapsing `\overline{χ_c(n₁ n₂² k³)} (c/d)₂ Φ(c) G̃(-2 n₁ n₂) G̃(n₁)` directly to
  `r(d, c) (g_c^{(3)}(n₁ k d) / |c|) G̃(-2 n₁ n₂ c) G̃(n₁ c)`.
* **Symmetric prime-product Gauss factorization and cubic cross-phase collapse
  (`sexticGaussPow_prod_eq`, `sexticGauss_mul_quadGauss_prod_cubic_cross`).** Across `c = ∏_{π ∈ s} π`,
  `g_c^{(j)}(1) = (∏_{π ∈ s} ∏_{q ∈ s \setminus \{π\}} χ_π(q)^j) ∏_{π ∈ s} g_π^{(j)}(1)`, so the
  product `g_c^{(1)}(1) g_c^{(3)}(1)` carries the purely cubic cross-phase
  `∏_{π ∈ s} ∏_{q ∈ s \setminus \{π\}} (q/π)₃²`.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory CoherenceTheoryOfReciprocityFamilies MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  MetaplecticMobiusDescent.CubicJacobi

/-! ### Part 1: Mod-4 Weil phase cancellation in `rowRoot_column_hasseDavenport` -/

/-- On odd Eisenstein integers (`IsCoprime · 2`), `quadraticPhase` is `±1`-valued and therefore
real (`\overline{r(a, c)} = r(a, c)`). -/
theorem conj_quadraticPhase {a c : O} (ha2 : IsCoprime a 2) (hc2 : IsCoprime c 2) :
    starRingEnd ℂ (quadraticPhase a c) = quadraticPhase a c := by
  have hsq : quadraticPhase a c ^ 2 = 1 :=
    quadraticPhase_sq (not_mem_two_of_isCoprime ha2) (not_mem_two_of_isCoprime hc2)
  have hfac : (quadraticPhase a c - 1) * (quadraticPhase a c + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rw [sub_eq_zero.mp h1, map_one]
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_one]

/-- Exact cancellation `\overline{r(n₁ n₂² k³, c)} · r(n₁ k, c) = 1` on odd classes. -/
theorem column_quadraticPhase_cancel {n₁ n₂ k c : O} (h12 : IsCoprime n₁ 2)
    (h22 : IsCoprime n₂ 2) (hk2 : IsCoprime k 2) (hc2 : IsCoprime c 2) :
    starRingEnd ℂ (quadraticPhase (n₁ * n₂ ^ 2 * k ^ 3) c) * quadraticPhase (n₁ * k) c = 1 := by
  have ho1 := not_mem_two_of_isCoprime h12
  have ho2 := not_mem_two_of_isCoprime h22
  have hok := not_mem_two_of_isCoprime hk2
  have hoc := not_mem_two_of_isCoprime hc2
  have hn2_odd : (n₁ * n₂ ^ 2 * k ^ 3) ∉ Ideal.span {(2 : O)} :=
    not_mem_two_of_isCoprime ((h12.mul_left h22.pow_left).mul_left hk2.pow_left)
  rw [conj_quadraticPhase ((h12.mul_left h22.pow_left).mul_left hk2.pow_left) hc2]
  have hm_all : quadraticPhase (n₁ * n₂ ^ 2 * k ^ 3) c =
      quadraticPhase n₁ c * quadraticPhase n₂ c ^ 2 * quadraticPhase k c ^ 3 := by
    rw [quadraticPhase_mul_left (odd_mul ho1 (by simpa [sq] using odd_mul ho2 ho2))
        (by rw [show k ^ 3 = k * (k * k) by ring]; exact odd_mul hok (odd_mul hok hok)) hoc,
      quadraticPhase_mul_left ho1 (by simpa [sq] using odd_mul ho2 ho2) hoc,
      show n₂ ^ 2 = n₂ * n₂ from sq n₂, quadraticPhase_mul_left ho2 ho2 hoc,
      show k ^ 3 = k * (k * k) by ring, quadraticPhase_mul_left hok (odd_mul hok hok) hoc,
      quadraticPhase_mul_left hok hok hoc]
    ring
  have hm_nk : quadraticPhase (n₁ * k) c = quadraticPhase n₁ c * quadraticPhase k c :=
    quadraticPhase_mul_left ho1 hok hoc
  have hs1 := quadraticPhase_sq ho1 hoc
  have hs2 := quadraticPhase_sq ho2 hoc
  have hsk := quadraticPhase_sq hok hoc
  rw [hm_all, hm_nk]
  linear_combination
    (quadraticPhase n₁ c ^ 2 * quadraticPhase k c ^ 4) * hs2 +
    (quadraticPhase n₁ c ^ 2 * (quadraticPhase k c ^ 2 + 1)) * hsk + hs1

section Row

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop in
/-- **Phase-free Hasse–Davenport at every column.** At `n = n₁ n₂² k³`, the mod-4 Weil phases cancel
identically:
`(g_c^{(1)}(n₁ n₂² k³) / |c|) · G̃(-2 n₁ n₂) G̃(n₁) = (g_c^{(3)}(n₁ k) / |c|) · G̃(-2 n₁ n₂ c) G̃(n₁ c)`. -/
theorem rowRoot_column_hasseDavenport_clean (n₁ n₂ k : O) (h1 : lambda ^ 2 ∣ n₁ - 1)
    (h2' : lambda ^ 2 ∣ n₂ - 1) (hk : lambda ^ 2 ∣ k - 1) (h12 : IsCoprime n₁ 2)
    (h22 : IsCoprime n₂ 2) (hk2 : IsCoprime k 2) (hc1 : IsCoprime n₁ (∏ π ∈ s, π))
    (hc2 : IsCoprime n₂ (∏ π ∈ s, π)) (hck : IsCoprime k (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) (n₁ * n₂ ^ 2 * k ^ 3) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) *
        (normalizedCubicUnitGauss (n₁ * (-2 * n₂)) * normalizedCubicUnitGauss n₁) =
      (sexticGaussPow 3 (∏ π ∈ s, π) (n₁ * k) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
        (normalizedCubicUnitGauss (n₁ * (-2 * n₂) * ∏ π ∈ s, π) *
          normalizedCubicUnitGauss (n₁ * ∏ π ∈ s, π)) := by
  obtain ⟨_, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  rw [rowRoot_column_hasseDavenport s hnz hmax hlam h2 hprim hcop n₁ n₂ k
      h1 h2' hk h12 h22 hk2 hc1 hc2 hck,
    column_quadraticPhase_cancel h12 h22 hk2 hc2', one_mul]

end Row

/-! ### Part 2: Conjugate-symbol absorption and cube-multiplied column shift -/

/-- Multiplying the row root number `g_c^{(1)}(1) / |c|` by `\overline{χ_c(a)}` shifts to column `a`. -/
theorem conj_sexticSymbol_mul_rowRootNumber {a c : O} [NeZero c] (hc : lambda ^ 2 ∣ c - 1)
    (hc2 : IsCoprime c 2) (hac : IsCoprime a c) :
    starRingEnd ℂ (sexticSymbol a c) * (sexticGaussPow 1 c 1 / (‖ringComplex c‖ : ℂ)) =
      sexticGaussPow 1 c a / (‖ringComplex c‖ : ℂ) := by
  have ht := sexticSymbol_mul_sexticGauss c hac 1
  rw [mul_one] at ht
  have hχ : starRingEnd ℂ (sexticSymbol a c) * sexticSymbol a c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_sexticSymbol_eq_one (NeZero.ne c) hc hc2 hac]
    norm_num
  have hg : starRingEnd ℂ (sexticSymbol a c) * sexticGaussPow 1 c 1 = sexticGaussPow 1 c a := by
    change starRingEnd ℂ (sexticSymbol a c) * sexticGauss c 1 = sexticGauss c a
    rw [← ht, ← mul_assoc, hχ, one_mul]
  rw [← mul_div_assoc, hg]

/-- **Cube-multiplied column shift.** For primary `c ≠ 0` prime to `2`, any `a ∈ O`, and `d` prime
to `c`, `g_c^{(1)}(a d³) = (d/c)₂ · g_c^{(1)}(a)`. -/
theorem sexticGauss_mul_cube {c : O} [NeZero c] (hc : lambda ^ 2 ∣ c - 1) (hc2 : IsCoprime c 2)
    (a : O) {d : O} (hdc : IsCoprime d c) :
    sexticGaussPow 1 c (a * d ^ 3) = quadSymbol d c * sexticGaussPow 1 c a := by
  have hc0 : c ≠ 0 := NeZero.ne c
  have ht := sexticSymbol_mul_sexticGauss c (hdc.pow_left (m := 3)) a
  rw [mul_comm (d ^ 3) a] at ht
  have hd3 : sexticSymbol (d ^ 3) c = quadSymbol d c := by
    have hpow : sexticSymbol (d ^ 3) c = sexticSymbol d c ^ 3 := by
      rw [show d ^ 3 = d * (d * d) by ring, sexticSymbol_mul_numerator, sexticSymbol_mul_numerator]
      ring
    have hcube : ringComplex (symbol d c) ^ 3 = 1 := symbol_cube hc hdc
    have hq2 : quadSymbol d c ^ 2 = 1 := quadSymbol_sq hc0 hc2 hdc
    rw [hpow, sexticSymbol]
    linear_combination
      (ringComplex (symbol d c) ^ 3 + 1) * quadSymbol d c ^ 3 * hcube + quadSymbol d c * hq2
  have hq2 : quadSymbol d c ^ 2 = 1 := quadSymbol_sq hc0 hc2 hdc
  rw [hd3] at ht
  change sexticGauss c (a * d ^ 3) = quadSymbol d c * sexticGauss c a
  linear_combination -quadSymbol d c * ht + sexticGauss c (a * d ^ 3) * hq2

section CoupledRow

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop in
/-- **Coupled order-B column collapse.** Twisting a reflected column `\overline{χ_c(n₁ n₂² k³)} Φ(c)`
by an external quadratic symbol `(c/d)₂` merges `d` into the cube slot `k ↦ k d`:
`\overline{χ_c(n₁ n₂² k³)} (c/d)₂ Φ(c) G̃(-2 n₁ n₂) G̃(n₁) = r(d, c) (g_c^{(3)}(n₁ k d)/|c|) G̃(-2 n₁ n₂ c) G̃(n₁ c)`. -/
theorem orderB_coupled_column_collapse (n₁ n₂ k d : O) (h1 : lambda ^ 2 ∣ n₁ - 1)
    (h2' : lambda ^ 2 ∣ n₂ - 1) (hk : lambda ^ 2 ∣ k - 1) (hd : lambda ^ 2 ∣ d - 1)
    (h12 : IsCoprime n₁ 2) (h22 : IsCoprime n₂ 2) (hk2 : IsCoprime k 2) (hd2 : IsCoprime d 2)
    (hc1 : IsCoprime n₁ (∏ π ∈ s, π)) (hc2 : IsCoprime n₂ (∏ π ∈ s, π))
    (hck : IsCoprime k (∏ π ∈ s, π)) (hcd : IsCoprime d (∏ π ∈ s, π)) :
    starRingEnd ℂ (sexticSymbol (n₁ * n₂ ^ 2 * k ^ 3) (∏ π ∈ s, π)) * quadSymbol (∏ π ∈ s, π) d *
        (sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
        (normalizedCubicUnitGauss (n₁ * (-2 * n₂)) * normalizedCubicUnitGauss n₁) =
      quadraticPhase d (∏ π ∈ s, π) *
        (sexticGaussPow 3 (∏ π ∈ s, π) (n₁ * k * d) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
        (normalizedCubicUnitGauss (n₁ * (-2 * n₂) * ∏ π ∈ s, π) *
          normalizedCubicUnitGauss (n₁ * ∏ π ∈ s, π)) := by
  obtain ⟨hP, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  set c := ∏ π ∈ s, π
  have hnc : IsCoprime (n₁ * n₂ ^ 2 * k ^ 3) c := (hc1.mul_left hc2.pow_left).mul_left hck.pow_left
  have habs := conj_sexticSymbol_mul_rowRootNumber hP hc2' hnc
  have hrec : quadSymbol c d = quadraticPhase d c * quadSymbol d c := by
    have hr := quadSymbol_reciprocity hd hP hd2 hc2' hcd
    have hsq := quadSymbol_sq (NeZero.ne c) hc2' hcd
    have hr2 := quadraticPhase_sq (not_mem_two_of_isCoprime hd2) (not_mem_two_of_isCoprime hc2')
    linear_combination quadraticPhase d c * hr - quadSymbol c d * hr2
  have hcube := sexticGauss_mul_cube hP hc2' (n₁ * n₂ ^ 2 * k ^ 3) hcd
  have hrew_arg : n₁ * n₂ ^ 2 * k ^ 3 * d ^ 3 = n₁ * n₂ ^ 2 * (k * d) ^ 3 := by ring
  rw [hrew_arg] at hcube
  have hhd := rowRoot_column_hasseDavenport_clean s hnz hmax hlam h2 hprim hcop
    n₁ n₂ (k * d) h1 h2' (primary_mul hk hd) h12 h22 (hk2.mul_left hd2) hc1 hc2 (hck.mul_left hcd)
  have hstep1 :
      starRingEnd ℂ (sexticSymbol (n₁ * n₂ ^ 2 * k ^ 3) c) * quadSymbol c d *
          (sexticGaussPow 1 c 1 / (‖ringComplex c‖ : ℂ)) =
        quadraticPhase d c *
          (sexticGaussPow 1 c (n₁ * n₂ ^ 2 * (k * d) ^ 3) / (‖ringComplex c‖ : ℂ)) := by
    calc starRingEnd ℂ (sexticSymbol (n₁ * n₂ ^ 2 * k ^ 3) c) * quadSymbol c d *
            (sexticGaussPow 1 c 1 / (‖ringComplex c‖ : ℂ))
        = quadSymbol c d * (starRingEnd ℂ (sexticSymbol (n₁ * n₂ ^ 2 * k ^ 3) c) *
            (sexticGaussPow 1 c 1 / (‖ringComplex c‖ : ℂ))) := by ring
      _ = (quadraticPhase d c * quadSymbol d c) *
            (sexticGaussPow 1 c (n₁ * n₂ ^ 2 * k ^ 3) / (‖ringComplex c‖ : ℂ)) := by rw [habs, hrec]
      _ = quadraticPhase d c *
            ((quadSymbol d c * sexticGaussPow 1 c (n₁ * n₂ ^ 2 * k ^ 3)) / (‖ringComplex c‖ : ℂ)) := by
          ring
      _ = quadraticPhase d c *
            (sexticGaussPow 1 c (n₁ * n₂ ^ 2 * (k * d) ^ 3) / (‖ringComplex c‖ : ℂ)) := by
          rw [← hcube]
  rw [hstep1, mul_assoc (quadraticPhase d c), hhd, show n₁ * (k * d) = n₁ * k * d by ring]
  ring

end CoupledRow

/-! ### Part 3: Symmetric prime-product Gauss factorization and cubic cross-phase collapse -/

private lemma sexticSymbol_prod_numerator (t : Finset O) {π : O} [NeZero π]
    [(Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π}) (h2 : (2 : O) ∉ Ideal.span {π})
    (hprim : lambda ^ 2 ∣ π - 1) :
    sexticSymbol (∏ q ∈ t, q) π = ∏ q ∈ t, sexticSymbol q π := by
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, sexticSymbol_prime π hlam h2 hprim, map_one, map_one]
  | insert q r hqr ih =>
    rw [Finset.prod_insert hqr, Finset.prod_insert hqr, sexticSymbol_mul_numerator, ih]

private lemma sexticSymbol_prod_denominator (x : O) (t : Finset O) :
    sexticSymbol x (∏ q ∈ t, q) = ∏ q ∈ t, sexticSymbol x q := by
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, sexticSymbol_one_denominator]
  | insert q r hqr ih =>
    rw [Finset.prod_insert hqr, Finset.prod_insert hqr, sexticSymbol_mul_denominator, ih]

/-- **Ordered-pair prime factorization of `sexticGaussPow`.** For any finite set `s` of pairwise
coprime primary primes `π ∤ 6` and any `j : ℕ`,
`g_{∏_s π}^{(j)}(1) = (∏_{π ∈ s} ∏_{q ∈ s \setminus \{π\}} χ_π(q)^j) · ∏_{π ∈ s} g_π^{(j)}(1)`. -/
theorem sexticGaussPow_prod_eq (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)] (j : ℕ) :
    sexticGaussPow j (∏ π ∈ s, π) 1 =
      (∏ π ∈ s, ∏ q ∈ s.erase π, sexticSymbol q π ^ j) *
        ∏ π ∈ s, @sexticGaussPow j π ⟨if h : π ∈ s then hnz π h else one_ne_zero⟩ 1 := by
  induction s using Finset.induction_on generalizing hne with
  | empty =>
    have h1 : (∏ π ∈ (∅ : Finset O), π) = 1 := Finset.prod_empty
    haveI : NeZero (1 : O) := ⟨one_ne_zero⟩
    rw [sexticGaussPow_congr j h1, sexticGaussPow_one_modulus j, Finset.prod_empty,
      Finset.prod_empty, mul_one]
  | insert π t hπt ih =>
    have hπ : π ∈ insert π t := Finset.mem_insert_self π t
    haveI : NeZero π := ⟨hnz π hπ⟩
    haveI : (Ideal.span {π}).IsMaximal := hmax π hπ
    have hsub : ∀ x ∈ t, x ∈ insert π t := fun x hx => Finset.mem_insert_of_mem hx
    have ht0 : ∏ x ∈ t, x ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx => hnz x (hsub x hx)
    haveI : NeZero (∏ x ∈ t, x) := ⟨ht0⟩
    have hcopπ : IsCoprime π (∏ x ∈ t, x) :=
      IsCoprime.prod_right fun x hx => hcop hπ (hsub x hx) (fun h => hπt (h ▸ hx))
    have he : ∏ x ∈ insert π t, x = π * ∏ x ∈ t, x := Finset.prod_insert hπt
    haveI : NeZero (π * ∏ x ∈ t, x) := ⟨mul_ne_zero (hnz π hπ) ht0⟩
    have Ht := ih (fun x hx => hnz x (hsub x hx)) (fun x hx => hmax x (hsub x hx))
      (fun x hx => hlam x (hsub x hx)) (fun x hx => h2 x (hsub x hx))
      (fun x hx => hprim x (hsub x hx)) (hcop.mono fun x hx => hsub x hx)
    rw [sexticGaussPow_congr j he, sexticGaussPow_mul j π (∏ x ∈ t, x) hcopπ 1, Ht,
      sexticSymbol_prod_numerator t (hlam π hπ) (h2 π hπ) (hprim π hπ),
      sexticSymbol_prod_denominator π t, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    have hcross :
        (∏ x ∈ insert π t, ∏ y ∈ (insert π t).erase x, sexticSymbol y x ^ j) =
          (∏ q ∈ t, sexticSymbol q π ^ j) * (∏ q ∈ t, sexticSymbol π q ^ j) *
            (∏ x ∈ t, ∏ y ∈ t.erase x, sexticSymbol y x ^ j) := by
      rw [Finset.prod_insert hπt, Finset.erase_insert hπt]
      have hrest :
          (∏ x ∈ t, ∏ y ∈ (insert π t).erase x, sexticSymbol y x ^ j) =
            (∏ q ∈ t, sexticSymbol π q ^ j) * (∏ x ∈ t, ∏ y ∈ t.erase x, sexticSymbol y x ^ j) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q hq => ?_
        have hqne : q ≠ π := fun h => hπt (h ▸ hq)
        rw [Finset.erase_insert_of_ne _ hqne,
          Finset.prod_insert (fun hm => hπt (Finset.mem_of_mem_erase hm))]
      rw [hrest]
      ring
    have hlocal :
        (∏ x ∈ insert π t,
            @sexticGaussPow j x ⟨if h : x ∈ insert π t then hnz x h else one_ne_zero⟩ 1) =
          sexticGaussPow j π 1 *
            ∏ x ∈ t, @sexticGaussPow j x ⟨if h : x ∈ t then hnz x (hsub x h) else one_ne_zero⟩ 1 := by
      rw [Finset.prod_insert hπt]
      congr 1
      · exact sexticGaussPow_congr j rfl
      · refine Finset.prod_congr rfl fun x hx => sexticGaussPow_congr j rfl
    rw [hcross, hlocal]
    ring

/-- **Purely cubic cross-phase collapse of `g_c^{(1)}(1) g_c^{(3)}(1)`.** Multiplying the sextic
and quadratic Gauss sums across `c = ∏_{π ∈ s} π` cancels all quadratic cross-signs (`1 + 3 = 4`),
leaving the purely cubic cross-factor `∏_{π ∈ s} ∏_{q ∈ s \setminus \{π\}} (q/π)₃²`. -/
theorem sexticGauss_mul_quadGauss_prod_cubic_cross (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)] :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 * sexticGaussPow 3 (∏ π ∈ s, π) 1 =
      (∏ π ∈ s, ∏ q ∈ s.erase π, ringComplex (symbol q π) ^ 2) *
        ∏ π ∈ s,
          (@sexticGaussPow 1 π ⟨if h : π ∈ s then hnz π h else one_ne_zero⟩ 1 *
            @sexticGaussPow 3 π ⟨if h : π ∈ s then hnz π h else one_ne_zero⟩ 1) := by
  rw [sexticGaussPow_prod_eq s hnz hmax hlam h2 hprim hcop 1,
    sexticGaussPow_prod_eq s hnz hmax hlam h2 hprim hcop 3]
  have hcross :
      (∏ π ∈ s, ∏ q ∈ s.erase π, sexticSymbol q π ^ 1) *
          (∏ π ∈ s, ∏ q ∈ s.erase π, sexticSymbol q π ^ 3) =
        ∏ π ∈ s, ∏ q ∈ s.erase π, ringComplex (symbol q π) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun π hπ => ?_
    haveI : NeZero π := ⟨hnz π hπ⟩
    haveI : (Ideal.span {π}).IsMaximal := hmax π hπ
    have hπ2 : IsCoprime π 2 := isCoprime_two_of_prime (prime_of_isMaximal_span π) (h2 π hπ)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    have h4 : sexticSymbol q π ^ 1 * sexticSymbol q π ^ 3 = (sexticSymbol q π ^ 2) ^ 2 := by ring
    rw [h4, sexticSymbol_sq_eq q π (hprim π hπ) hπ2]
  rw [Finset.prod_mul_distrib]
  linear_combination
    (∏ x ∈ s, @sexticGaussPow 1 x ⟨if h : x ∈ s then hnz x h else one_ne_zero⟩ 1) *
      (∏ x ∈ s, @sexticGaussPow 3 x ⟨if h : x ∈ s then hnz x h else one_ne_zero⟩ 1) * hcross

#print axioms conj_quadraticPhase
#print axioms column_quadraticPhase_cancel
#print axioms rowRoot_column_hasseDavenport_clean
#print axioms conj_sexticSymbol_mul_rowRootNumber
#print axioms sexticGauss_mul_cube
#print axioms orderB_coupled_column_collapse
#print axioms sexticGaussPow_prod_eq
#print axioms sexticGauss_mul_quadGauss_prod_cubic_cross

end GaloisForLFunctions.OrderSixMetaplecticTheory
