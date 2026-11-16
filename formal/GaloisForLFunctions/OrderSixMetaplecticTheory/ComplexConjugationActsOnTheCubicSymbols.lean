import GaloisForLFunctions.OrderSixMetaplecticTheory.TheColumnsAreShiftedThetaProducts

/-!
# Complex conjugation acts on the cubic symbols

The nontrivial automorphism `conjO` of `ℤ[ω]` (`ω ↦ ω²`, complex conjugation) maps prime ideals to prime
ideals and transports Euler's criterion. So it acts on the cubic residue symbols by conjugating the
values (`symbol_conjO`):

`(x̄/c̄)₃ = \overline{(x/c)₃}`.

At a prime `P` both `χ_{P̄}(x̄)` and `\overline{χ_P(x)}` are cube roots of unity (or `0`) with the same reduction
`x̄^{(N P − 1)/3}` modulo `P̄`, and reduction modulo a prime away from `λ` is injective on `{0, 1, ω, ω²}`
(`cubicChar_conj`). Composite symbols follow from the factorization of `(c̄) = \overline{(c)}`
(`normalizedFactors_conjIdeal`).
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein UniqueFactorizationMonoid

/-! ### Conjugation on `ℤ[ω]` -/

theorem conjO_conjO (x : O) : conjO (conjO x) = x := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  simp only [map_add, map_mul, map_intCast, map_pow, conjO_omega]
  rw [← pow_mul, show omega ^ (2 * 2) = omega ^ 3 * omega by ring, omega_primitive.pow_eq_one, one_mul]

theorem ringComplex_conjO (x : O) : ringComplex (conjO x) = star (ringComplex x) := by
  have hz : star (ringComplex omega) = ringComplex omega ^ 2 := by
    have hz3 : ringComplex omega ^ 3 = 1 := by
      rw [← map_pow, omega_primitive.pow_eq_one, map_one]
    exact conj_eq_sq_of_cube hz3
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  simp only [map_add, map_mul, map_intCast, conjO_omega, star_add, star_mul, star_intCast, map_pow, hz]
  ring

/-- `λ̄ = λ(ω + 1)`, a unit multiple of `λ`. -/
theorem conjO_lambda : conjO lambda = lambda * (omega + 1) := by
  unfold lambda
  rw [map_sub, conjO_omega, map_one]
  ring

theorem omega_sq_add : omega ^ 2 + omega + 1 = 0 := by
  have hne : omega ≠ 1 := omega_primitive.ne_one (by norm_num)
  have : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    rw [show (omega - 1) * (omega ^ 2 + omega + 1) = omega ^ 3 - 1 by ring, omega_primitive.pow_eq_one,
      sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- The conjugate ideal `Ī = {x : x̄ ∈ I}`. -/
def conjIdeal (I : Ideal O) : Ideal O := Ideal.comap conjO I

theorem mem_conjIdeal {I : Ideal O} {x : O} : x ∈ conjIdeal I ↔ conjO x ∈ I := Iff.rfl

theorem conjIdeal_conjIdeal (I : Ideal O) : conjIdeal (conjIdeal I) = I := by
  ext x
  rw [mem_conjIdeal, mem_conjIdeal, conjO_conjO]

theorem span_conjO (c : O) : Ideal.span {conjO c} = conjIdeal (Ideal.span {c}) := by
  ext x
  rw [mem_conjIdeal, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨conjO d, by rw [map_mul, conjO_conjO]⟩
  · rintro ⟨d, hd⟩
    refine ⟨conjO d, ?_⟩
    rw [← conjO_conjO x, hd, map_mul]

theorem conjIdeal_isMaximal (P : Ideal O) [P.IsMaximal] : (conjIdeal P).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ conjO.surjective

theorem conjIdeal_good {P : Ideal O} (hgood : lambda ∉ P) : lambda ∉ conjIdeal P := by
  intro h
  rw [mem_conjIdeal, conjO_lambda] at h
  have hu : (omega + 1) * (-omega) = 1 := by linear_combination -omega_sq_add
  have : lambda = lambda * (omega + 1) * (-omega) := by rw [mul_assoc, hu, mul_one]
  exact hgood (this ▸ Ideal.mul_mem_right _ _ h)

theorem conjIdeal_eq_zero {I : Ideal O} : conjIdeal I = 0 ↔ I = 0 := by
  constructor
  · intro h
    rw [← conjIdeal_conjIdeal I, h]
    ext x
    rw [mem_conjIdeal, Submodule.zero_eq_bot, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ conjO.injective]
  · intro h
    rw [h]
    ext x
    rw [mem_conjIdeal, Submodule.zero_eq_bot, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ conjO.injective]

/-! ### Euler's criterion under conjugation -/

/-- The residue fields of `P` and `P̄`. -/
def conjQuotient (P : Ideal O) : O ⧸ P ≃+* O ⧸ conjIdeal P :=
  Ideal.quotientEquiv P (conjIdeal P) conjO.symm (by
    ext x
    rw [mem_conjIdeal, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_symm])

theorem conjQuotient_mk (P : Ideal O) (x : O) :
    conjQuotient P (Ideal.Quotient.mk P x) = Ideal.Quotient.mk (conjIdeal P) (conjO x) := by
  rw [conjQuotient, Ideal.quotientEquiv_mk]
  congr 1
  apply conjO.injective
  rw [RingEquiv.apply_symm_apply, conjO_conjO]

/-- The values of the cubic character are `0` or cube roots of unity. -/
theorem cubicChar_values (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O ⧸ P) :
    cubicChar P hgood x = 0 ∨ ∃ j : ℕ, j < 3 ∧ cubicChar P hgood x = omega ^ j := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  by_cases hx : x = 0
  · left
    rw [hx, MulChar.map_zero]
  · right
    have h3 : cubicChar P hgood x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    obtain ⟨j, hj, hjeq⟩ := omega_primitive.eq_pow_of_pow_eq_one h3
    exact ⟨j, hj, hjeq.symm⟩

theorem conjO_values {a : O} (ha : a = 0 ∨ ∃ j : ℕ, j < 3 ∧ a = omega ^ j) :
    conjO a = 0 ∨ ∃ j : ℕ, j < 3 ∧ conjO a = omega ^ j := by
  rcases ha with rfl | ⟨j, -, rfl⟩
  · left
    exact map_zero _
  · right
    refine ⟨(2 * j) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [map_pow, conjO_omega, ← pow_mul]
    conv_lhs => rw [← Nat.div_add_mod (2 * j) 3]
    rw [pow_add, pow_mul, omega_primitive.pow_eq_one, one_pow, one_mul]

/-- Reduction modulo a prime away from `λ` is injective on `{0, 1, ω, ω²}`. -/
theorem reduce_injective_on_roots (Q : Ideal O) [Q.IsMaximal] (hgood : lambda ∉ Q) {a b : O}
    (ha : a = 0 ∨ ∃ j : ℕ, j < 3 ∧ a = omega ^ j) (hb : b = 0 ∨ ∃ j : ℕ, j < 3 ∧ b = omega ^ j)
    (h : Ideal.Quotient.mk Q a = Ideal.Quotient.mk Q b) : a = b := by
  letI : Field (O ⧸ Q) := Ideal.Quotient.field Q
  have hζ := omega_reduced_primitive Q hgood
  have hne : ∀ j : ℕ, Ideal.Quotient.mk Q (omega ^ j) ≠ 0 := fun j => by
    rw [map_pow]
    exact pow_ne_zero _ (hζ.ne_zero (by norm_num))
  rcases ha with rfl | ⟨i, hi, rfl⟩ <;> rcases hb with rfl | ⟨j, hj, rfl⟩
  · rfl
  · exact absurd (h.symm.trans (map_zero _)) (hne j)
  · exact absurd (h.trans (map_zero _)) (hne i)
  · rw [map_pow, map_pow] at h
    rw [hζ.pow_inj hi hj h]

/-- **Euler's criterion under conjugation.** `χ_{P̄}(x̄) = \overline{χ_P(x)}`. -/
theorem cubicChar_conj (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O) :
    haveI := conjIdeal_isMaximal P
    cubicChar (conjIdeal P) (conjIdeal_good hgood) (Ideal.Quotient.mk _ (conjO x)) =
      conjO (cubicChar P hgood (Ideal.Quotient.mk P x)) := by
  haveI := conjIdeal_isMaximal P
  have hcard : Nat.card (O ⧸ conjIdeal P) = Nat.card (O ⧸ P) :=
    (Nat.card_congr (conjQuotient P).toEquiv).symm
  apply reduce_injective_on_roots (conjIdeal P) (conjIdeal_good hgood)
    (cubicChar_values _ _ _) (conjO_values (cubicChar_values _ _ _))
  rw [cubicChar_reduce, ← conjQuotient_mk P (cubicChar P hgood (Ideal.Quotient.mk P x)), cubicChar_reduce,
    map_pow, conjQuotient_mk, hcard]

/-- The prime value under conjugation. -/
theorem primeValue_conj (P : Ideal O) (x : O) :
    primeValue (conjIdeal P) (conjO x) = conjO (primeValue P x) := by
  by_cases h : P.IsMaximal ∧ lambda ∉ P
  · obtain ⟨hm, hg⟩ := h
    haveI := hm
    haveI := conjIdeal_isMaximal P
    rw [primeValue_eq (conjIdeal P) (conjIdeal_good hg), primeValue_eq P hg, cubicChar_conj]
  · have h' : ¬ ((conjIdeal P).IsMaximal ∧ lambda ∉ conjIdeal P) := by
      rintro ⟨hm', hg'⟩
      apply h
      haveI := hm'
      refine ⟨?_, ?_⟩
      · rw [← conjIdeal_conjIdeal P]
        exact conjIdeal_isMaximal _
      · have := conjIdeal_good hg'
        rwa [conjIdeal_conjIdeal] at this
    simp only [primeValue, dif_neg h, dif_neg h', map_zero]

/-! ### Composite symbols -/

theorem conjIdeal_eq_map (I : Ideal O) : conjIdeal I = Ideal.map conjO.symm I :=
  (Ideal.map_symm conjO).symm

theorem conjIdeal_mul (I J : Ideal O) : conjIdeal (I * J) = conjIdeal I * conjIdeal J := by
  simp only [conjIdeal_eq_map, Ideal.map_mul]

theorem conjIdeal_top : conjIdeal ⊤ = ⊤ := Ideal.comap_top

theorem conjIdeal_prime {P : Ideal O} (hP : Prime P) : Prime (conjIdeal P) := by
  have hne : conjIdeal P ≠ ⊥ := fun h => hP.ne_zero (conjIdeal_eq_zero.mp h)
  haveI : P.IsPrime := Ideal.isPrime_of_prime hP
  exact Ideal.prime_of_isPrime hne (Ideal.comap_isPrime conjO P)

theorem idealSymbol_of_prime {P : Ideal O} (hP : Prime P) (x : O) :
    idealSymbol P x = primeValue P x := by
  rw [idealSymbol, if_neg hP.ne_zero, normalizedFactors_irreducible hP.irreducible]
  simp

/-- **Conjugation on ideal symbols.** `(x̄/Ī)₃ = \overline{(x/I)₃}`. -/
theorem idealSymbol_conj (I : Ideal O) (x : O) :
    idealSymbol (conjIdeal I) (conjO x) = conjO (idealSymbol I x) := by
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · rw [show conjIdeal 0 = 0 from conjIdeal_eq_zero.mpr rfl, idealSymbol_zero, idealSymbol_zero, map_zero]
  · intro J hJ
    rw [Ideal.isUnit_iff.mp hJ, conjIdeal_top, idealSymbol_top, idealSymbol_top, map_one]
  · intro J P _ hP ih
    rw [conjIdeal_mul, idealSymbol_mul, idealSymbol_mul, map_mul, ih, idealSymbol_of_prime hP,
      idealSymbol_of_prime (conjIdeal_prime hP), primeValue_conj]

/-- **Conjugation on cubic symbols.** `(x̄/c̄)₃ = \overline{(x/c)₃}`. -/
theorem symbol_conjO (x c : O) : symbol (conjO x) (conjO c) = conjO (symbol x c) := by
  rw [symbol, symbol, span_conjO, idealSymbol_conj]

theorem ringComplex_symbol_conjO (x c : O) :
    ringComplex (symbol (conjO x) (conjO c)) = star (ringComplex (symbol x c)) := by
  rw [symbol_conjO, ringComplex_conjO]

/-! ### Primary generators -/

theorem conjO_primary {c : O} (hc : lambda ^ 2 ∣ c - 1) : lambda ^ 2 ∣ conjO c - 1 := by
  obtain ⟨d, hd⟩ := hc
  refine ⟨(omega + 1) ^ 2 * conjO d, ?_⟩
  rw [show conjO c - 1 = conjO (c - 1) by rw [map_sub, map_one], hd, map_mul, map_pow, conjO_lambda]
  ring

theorem conjO_ne_zero {c : O} (hc : c ≠ 0) : conjO c ≠ 0 :=
  (map_ne_zero_iff _ conjO.injective).mpr hc

private theorem primaryIdealGenerator_conj_of_ne {I : Ideal O} (h : primaryIdealGenerator I ≠ 0) :
    primaryIdealGenerator (conjIdeal I) = conjO (primaryIdealGenerator I) := by
  obtain ⟨hspan, hp⟩ := primaryIdealGenerator_spec I h
  conv_lhs => rw [← hspan, ← span_conjO]
  exact primaryIdealGenerator_span _ (conjO_ne_zero h) (conjO_primary hp)

/-- The primary generator of `Ī` is the conjugate of the primary generator of `I`. -/
theorem primaryIdealGenerator_conj (I : Ideal O) :
    primaryIdealGenerator (conjIdeal I) = conjO (primaryIdealGenerator I) := by
  by_cases h : primaryIdealGenerator I = 0
  · rw [h, map_zero]
    by_contra h'
    have hc := primaryIdealGenerator_conj_of_ne h'
    rw [conjIdeal_conjIdeal, h] at hc
    exact conjO_ne_zero h' hc.symm
  · exact primaryIdealGenerator_conj_of_ne h

/-! ### Squarefreeness and norms -/

/-- Conjugation of ideals as a multiplicative involution. -/
def conjIdealEquiv : Ideal O ≃* Ideal O where
  toFun := conjIdeal
  invFun := conjIdeal
  left_inv := conjIdeal_conjIdeal
  right_inv := conjIdeal_conjIdeal
  map_mul' := conjIdeal_mul

theorem squarefree_conjIdeal {I : Ideal O} (h : Squarefree I) : Squarefree (conjIdeal I) := by
  intro J hJ
  have h' : conjIdeal J * conjIdeal J ∣ I := by
    rw [← conjIdeal_mul, ← conjIdeal_conjIdeal I]
    exact map_dvd conjIdealEquiv hJ
  have hu := (h _ h').map conjIdealEquiv
  rwa [show conjIdealEquiv (conjIdeal J) = J from conjIdeal_conjIdeal J] at hu

theorem squarefree_conjIdeal_iff {I : Ideal O} : Squarefree (conjIdeal I) ↔ Squarefree I :=
  ⟨fun h => by simpa only [conjIdeal_conjIdeal] using squarefree_conjIdeal h, squarefree_conjIdeal⟩

theorem absNorm_conjIdeal (I : Ideal O) : Ideal.absNorm (conjIdeal I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (conjQuotient I).toEquiv).symm

/-! ### Cubic Gauss sums -/

/-- `(1 + 2ω)‾ = −(1 + 2ω)`: the different is purely imaginary. -/
theorem conjO_traceLambda : conjO traceLambda = -traceLambda := by
  unfold traceLambda
  rw [map_add, map_one, map_mul, conjO_omega, map_ofNat]
  linear_combination 2 * omega_sq_add

theorem ringComplex_ne_zero {c : O} (hc : c ≠ 0) : ringComplex c ≠ 0 := by
  rw [← map_zero ringComplex]
  exact fun h => hc (ringComplex_injective h)

/-- The trace phase of `-z̄` is the conjugate phase. -/
theorem tracePhase_neg_star (z : ℂ) : tracePhase (-star z) = star (tracePhase z) := by
  change Complex.exp _ = star (Complex.exp _)
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_add, map_neg, Complex.conj_conj, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

theorem star_ringComplex_traceLambda : star (ringComplex traceLambda) = -ringComplex traceLambda := by
  rw [← ringComplex_conjO, conjO_traceLambda, map_neg]

theorem residueAdditive_conj (h b d : O) :
    residueAdditive (3 * conjO h) (conjO b) (conjO d) = star (residueAdditive (3 * h) b d) := by
  unfold residueAdditive
  rw [← tracePhase_neg_star]
  congr 1
  unfold cuspFrequency
  simp only [map_mul, ringComplex_conjO, map_ofNat, star_div₀, star_mul', star_ofNat,
    star_ringComplex_traceLambda]
  ring

/-- The residues modulo `c` and modulo `c̄`. -/
def conjSpanQuotient (c : O) : O ⧸ Ideal.span {c} ≃+* O ⧸ Ideal.span {conjO c} :=
  Ideal.quotientEquiv _ _ conjO (by rw [Ideal.map_span, Set.image_singleton]; rfl)

theorem conjSpanQuotient_mk (c x : O) :
    conjSpanQuotient c (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (conjO x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

/-- Conjugation of invertible residues. -/
def conjUnitResidue (c : O) : CubicUnitResidue c ≃ CubicUnitResidue (conjO c) :=
  (conjSpanQuotient c).toEquiv.subtypeEquiv fun r => (isUnit_map_iff (conjSpanQuotient c) r).symm

/-- **Conjugation on cubic Gauss sums.** `g(h̄, c̄) = \overline{g(h, c)}`. -/
theorem cubicUnitGaussSum_conj (h c : O) (hc : c ≠ 0) :
    cubicUnitGaussSum (conjO h) (conjO c) = star (cubicUnitGaussSum h c) := by
  unfold cubicUnitGaussSum
  rw [tsum_star, ← (conjUnitResidue c).tsum_eq]
  congr 1
  funext r
  have hrep : conjO c ∣ principalResidueRep (conjO c) (conjUnitResidue c r).1 -
      conjO (principalResidueRep c r.1) := by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [principalResidueRep_spec]
    change conjSpanQuotient c r.1 = _
    rw [← conjSpanQuotient_mk, principalResidueRep_spec]
  rw [symbol_congr hrep, residueAdditive_three_congr _ _ _ _ (conjO_ne_zero hc) hrep,
    ringComplex_symbol_conjO, residueAdditive_conj, star_mul']

/-- `G̃(c̄) = \overline{G̃(c)}` for the normalized cubic Gauss sum. -/
theorem normalizedCubicUnitGauss_conj (c : O) :
    normalizedCubicUnitGauss (conjO c) = star (normalizedCubicUnitGauss c) := by
  by_cases hc : c = 0
  · simp [hc, normalizedCubicUnitGauss]
  · have h1 := cubicUnitGaussSum_conj 1 c hc
    rw [map_one] at h1
    rw [normalizedCubicUnitGauss, normalizedCubicUnitGauss, h1, ringComplex_conjO, norm_star, star_div₀,
      Complex.star_def, Complex.conj_ofReal]

/-! ### Theta-square weights -/

/-- **The theta-square weight of `Ā` is the conjugate weight.** -/
theorem thetaSquareWeight_conj (A : Ideal O) :
    SpectralTheoryOfTheCubicCover.thetaSquareWeight (conjIdeal A) =
      star (SpectralTheoryOfTheCubicCover.thetaSquareWeight A) := by
  unfold SpectralTheoryOfTheCubicCover.thetaSquareWeight
  rw [primaryIdealGenerator_conj, normalizedCubicUnitGauss_conj,
    show symbol 9 (conjO (primaryIdealGenerator A)) = symbol (conjO 9) (conjO (primaryIdealGenerator A)) by
      rw [map_ofNat],
    ringComplex_symbol_conjO, star_pow, star_mul', star_star]

end GaloisForLFunctions.OrderSixMetaplecticTheory
