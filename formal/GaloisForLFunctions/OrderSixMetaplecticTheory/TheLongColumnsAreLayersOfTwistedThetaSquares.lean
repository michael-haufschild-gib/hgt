import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedThetaSquareFactorsThroughATwistedCubeFactor
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFamilyTwistsThePlainSquares
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFirstMomentIsReal
import GaloisForLFunctions.FamilyContinuationTheory.TheQuadraticPhaseIsABicharacterModuloFour
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.RayExpansionsAndCompletedSums

/-!
# The long columns are layers of twisted theta squares

The `n`-th long column of the order-six Kubota series has the coefficient
`g_c(n)/|c| = overline{r(n, c)} (c/n)₃ (c/n)₂ ω₆(c)` (column law, `rowRoot_column`), with
`ω₆(c) = Γ(c)χ₂(c)G̃(c)²` (`columnRootNumber_eq_columnWeight`). Three facts make it Rankin–Selberg data of the
cubic theta function at the series level:

* `G̃(c)² = overline{(ω²λ²/c)₃²σ(c)}`: the coefficient of the 3-adic layer `S_{ω²λ²}`;
* the column twist `ψ_n(c) = (c/n)₃(c/n)₂` is completely multiplicative in `c` (`columnTwist`);
* the 2-adic weight `W_n(c) = overline{r(n, c)}Γ(c)χ₂(c)` depends only on `c` modulo `4` (`twoAdicWeight_congr`),
  so it is a finite combination `Σ_η a_η(n) η(c)` of the characters of `(O/4)^×`.

Hence (`columnSeries_eq_layers`), for `Re w > 1`,

`Σ_A g_{gen A}(n)/|gen A| N(A)^{−w} = Σ_η a_η(n) overline{S^{Ξ_{η,n}}_{ω²λ²}(w̄)}`,   `Ξ_{η,n} = overline{ηψ_n}`,

a combination of twelve `ω²λ²`-layers of the twisted theta squares `L_{Ξ_{η,n}}`
(`twistDirichletG_eq_zeta_mul`). The column enters only through the character `ψ_n` of conductor `n` and through
the coefficients `a_η(n)` of the bicharacter `r(n, ·)` modulo `4`.
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.Eisenstein.Coordinates MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RayFourExpansion
  MetaplecticMobiusDescent.CubicEisenstein.FiniteRayExpansion

/-! ### The 2-adic weight -/

theorem fixedDualAverage_congr {c d : O} (h : (4 : O) ∣ c - d) : fixedDualAverage c = fixedDualAverage d := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  obtain ⟨e, he⟩ := h
  obtain ⟨a', b', rfl⟩ := exists_eval e
  have hd : d = eval (a - 4 * a') (b - 4 * b') := by
    simp only [eval] at he ⊢
    push_cast
    linear_combination -he
  have h4 : ((4 : ℤ) : ZMod 4) = 0 := rfl
  rw [hd, fixedDualAverage_eval, fixedDualAverage_eval]
  simp only [Int.cast_sub, Int.cast_mul, h4, zero_mul, sub_zero]

/-- The 2-adic weight `W_n(c) = overline{r(n, c)} Γ(c) χ₂(c)` of column `n`. -/
def twoAdicWeight (n c : O) : ℂ := star (quadraticPhase n c) * fixedDualAverage c * cubicTwoChar c

theorem twoAdicWeight_congr (n : O) {c d : O} (h : (4 : O) ∣ c - d) : twoAdicWeight n c = twoAdicWeight n d := by
  have hn : (4 : O) ∣ n * c - n * d := by
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right h n
  unfold twoAdicWeight quadraticPhase
  rw [fixedDualAverage_congr hn, fixedDualAverage_congr h, cubicTwoChar_congr (dvd_trans ⟨2, by norm_num⟩ h)]

/-- A lift of a residue modulo `4`. -/
def liftFour (r : RayRing) : O := (Ideal.Quotient.mk_surjective r).choose

theorem mk_liftFour (r : RayRing) : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (liftFour r) = r :=
  (Ideal.Quotient.mk_surjective r).choose_spec

/-- `W_n` as a function on `O/4`. -/
def twoAdicWeightMod (n : O) (r : RayRing) : ℂ := twoAdicWeight n (liftFour r)

theorem twoAdicWeightMod_mk (n c : O) :
    twoAdicWeightMod n (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = twoAdicWeight n c := by
  apply twoAdicWeight_congr
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_liftFour]

/-- The coefficients `a_η(n)` of `W_n` on the characters of `(O/4)^×`. -/
def twoAdicCoeff (n : O) (η : RayCharacter) : ℂ := phaseCoeff (twoAdicWeightMod n) η

theorem two_prime : Prime (2 : O) := by
  have h : (Ideal.span {(-2 : O)}).IsMaximal := by
    simpa only [cubicTwoIdeal] using cubicTwoIdeal_isMaximal
  have hp : Prime (-2 : O) :=
    (Ideal.span_singleton_prime (by norm_num)).mp h.isPrime
  simpa using hp.neg

theorem isUnit_mk_four_iff (c : O) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) ↔ ¬ (2 : O) ∣ c := by
  constructor
  · rintro hu ⟨k, rfl⟩
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {(4 : O)})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at hv
    obtain ⟨e, he⟩ := hv
    exact two_prime.not_unit (isUnit_of_dvd_one ⟨k * d - 2 * e, by linear_combination -he⟩)
  · intro hc
    have hcp : IsCoprime c (2 : O) := (two_prime.irreducible.coprime_iff_not_dvd.mpr hc).symm
    obtain ⟨a, b, hab⟩ := hcp.pow_right (n := 2)
    refine IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {(4 : O)})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨-b, by linear_combination hab⟩

/-- **The 2-adic weight is a combination of characters of `(O/4)^×`.** -/
theorem twoAdicWeight_expansion (n c : O) (hc : ¬ (2 : O) ∣ c) :
    twoAdicWeight n c = ∑ η : RayCharacter, twoAdicCoeff n η * rayMonoid η c := by
  have h := phase_expansion (twoAdicWeightMod n) c
  rw [if_pos ((isUnit_mk_four_iff c).mpr hc), one_mul, twoAdicWeightMod_mk] at h
  exact h

/-! ### The column twist -/

theorem norm_multiset_prod_le_one (s : Multiset ℂ) (h : ∀ x ∈ s, ‖x‖ ≤ 1) : ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (h a (Multiset.mem_cons_self a s)) (norm_nonneg _)
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem norm_quadSymbol_le (x n : O) : ‖quadSymbol x n‖ ≤ 1 := by
  unfold quadSymbol quadIdealSymbol
  split_ifs
  · simp
  · apply norm_multiset_prod_le_one
    intro y hy
    obtain ⟨P, hPm, rfl⟩ := Multiset.mem_map.mp hy
    have hP0 : P ≠ ⊥ := (UniqueFactorizationMonoid.prime_of_normalized_factor P hPm).ne_zero
    unfold quadPrimeValue
    split_ifs with hP
    · letI := hP.1
      letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
      letI : Fintype (O ⧸ P) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    · simp

theorem norm_symbol_le (x n : O) (hn : lambda ^ 2 ∣ n - 1) : ‖ringComplex (symbol x n)‖ ≤ 1 := by
  by_cases hc : IsCoprime x n
  · exact (symbol_norm_one x n hn hc).le
  · rw [ringComplex_symbol_eq_zero hn hc, norm_zero]
    exact zero_le_one

/-- The column twist `ψ_n(c) = (c/n)₃ (c/n)₂`, completely multiplicative in `c`. -/
def columnTwist (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2) : O →* ℂ where
  toFun c := ringComplex (symbol c n) * quadSymbol c n
  map_one' := by rw [symbol_one_numerator n hn, quadSymbol_one_numerator hn0 hn2, map_one, one_mul]
  map_mul' a b := by
    rw [symbol_mul_numerator, quadSymbol_mul_numerator, map_mul]
    ring

/-- The twist `\overline{μψ_n}` of the layer read by column `n` against a 2-adic factor `μ`. -/
def layerTwist (μ : O →* ℂ) (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2) : O →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp (μ * columnTwist n hn hn0 hn2)

theorem layerTwist_apply (μ : O →* ℂ) (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0)
    (hn2 : IsCoprime n 2) (c : O) :
    layerTwist μ n hn hn0 hn2 c = star (μ c * (ringComplex (symbol c n) * quadSymbol c n)) :=
  rfl

theorem norm_layerTwist_le (μ : O →* ℂ) (hμ : ∀ c, ‖μ c‖ ≤ 1) (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0)
    (hn2 : IsCoprime n 2) (c : O) : ‖layerTwist μ n hn hn0 hn2 c‖ ≤ 1 := by
  rw [layerTwist_apply, norm_star, norm_mul, norm_mul]
  exact mul_le_one₀ (hμ c) (by positivity)
    (mul_le_one₀ (norm_symbol_le c n hn) (norm_nonneg _) (norm_quadSymbol_le c n))

/-- The twist `Ξ_{η,n} = \overline{ηψ_n}` of the layer read by column `n` and the 2-adic character `η`. -/
abbrev columnLayerTwist (η : RayCharacter) (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0)
    (hn2 : IsCoprime n 2) : O →* ℂ :=
  layerTwist (rayMonoid η) n hn hn0 hn2

/-! ### The column series -/

/-- The column-`n` weight `overline{r(n, c)}(c/n)₃(c/n)₂ω₆(c)`. -/
def columnWeight (n c : O) : ℂ :=
  star (quadraticPhase n c) * (ringComplex (symbol c n) * quadSymbol c n) * orderSixWeight c

/-- The coefficient of column `n` on ideals: `g_c(n)/|c|` at the primary generator of a squarefree odd row. -/
def columnCoefficient (n : O) (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ ¬ (2 : O) ∣ primaryIdealGenerator A then
    columnWeight n (primaryIdealGenerator A) else 0

/-- The `n`-th long column `Σ_A g_{gen A}(n)/|gen A| N(A)^{−w}`. -/
def columnSeries (n : O) (w : ℂ) : ℂ := ∑' A : Ideal O, columnCoefficient n A * unramifiedNormWeight w A

theorem star_unramifiedNormWeight (w : ℂ) (A : Ideal O) :
    star (unramifiedNormWeight (star w) A) = unramifiedNormWeight w A := by
  by_cases hA : primaryIdealGenerator A = 0
  · rw [unramifiedNormWeight_of_bad _ A hA, unramifiedNormWeight_of_bad _ A hA, star_zero]
  · rw [unramifiedNormWeight_of_good _ A hA, unramifiedNormWeight_of_good _ A hA]
    have harg : ((Ideal.absNorm A : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    have h := Complex.cpow_conj ((Ideal.absNorm A : ℕ) : ℂ) (-w) harg
    rw [Complex.conj_natCast] at h
    change (starRingEnd ℂ) (((Ideal.absNorm A : ℕ) : ℂ) ^ (-star w)) = _
    rw [show -star w = (starRingEnd ℂ) (-w) by rw [map_neg]; rfl, h, Complex.conj_conj]

/-- The summand of the layer `S^ψ_{ω²λ²}`. -/
abbrev layerTerm (ψ : O →* ℂ) (w : ℂ) (A : Ideal O) : ℂ :=
  if Squarefree A then unramifiedNormWeight w A * (ψ (primaryIdealGenerator A) *
    (ringComplex (symbol (omega ^ 2 * lambda ^ 2) (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)) else 0

theorem summable_layerTerm (ψ : O →* ℂ) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (w : ℂ) (hw : 1 < w.re) :
    Summable (layerTerm ψ w) := by
  refine Summable.of_norm_bounded (unramifiedNormWeight_summable_norm w hw) (fun A => ?_)
  simp only [layerTerm]
  split_ifs with hsq
  · by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, norm_zero]
    · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_thetaSquareWeight A hA hsq, mul_one]
      refine mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (hψ _) (by positivity) ?_)
      exact pow_le_one₀ (norm_nonneg _) (norm_symbol_le _ _ (primaryIdealGenerator_spec A hA).2)
  · rw [norm_zero]
    exact norm_nonneg _

/-- **A 2-adic expansion of the weight turns a long column into layers, coefficient by coefficient.** If
`W_n(c) = Σ_i γ_i μ_i(c)` on odd `c` with multiplicative `μ_i` vanishing on even `c`, then
`g(n)N(A)^{−w} = Σ_i γ_i \overline{(\text{layer term of } \overline{μ_iψ_n})(w̄)}`. -/
theorem columnCoefficient_eq_of_expansion {ι : Type*} (S : Finset ι) (γ : ι → ℂ) (μ : ι → O →* ℂ)
    (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2)
    (hμ0 : ∀ i c, (2 : O) ∣ c → μ i c = 0)
    (hW : ∀ c, ¬ (2 : O) ∣ c → twoAdicWeight n c = ∑ i ∈ S, γ i * μ i c) (w : ℂ) (A : Ideal O) :
    columnCoefficient n A * unramifiedNormWeight w A =
      ∑ i ∈ S, γ i * star (layerTerm (layerTwist (μ i) n hn hn0 hn2) (star w) A) := by
  by_cases hsq : Squarefree A
  swap
  · simp only [columnCoefficient, layerTerm, hsq, false_and, if_false, zero_mul, star_zero, mul_zero,
      Finset.sum_const_zero]
  by_cases hg : primaryIdealGenerator A = 0
  · simp only [columnCoefficient, layerTerm, hsq, hg, unramifiedNormWeight_of_bad _ A hg, mul_zero,
      zero_mul, star_zero, if_true, Finset.sum_const_zero]
  set c := primaryIdealGenerator A with hc
  by_cases h2 : (2 : O) ∣ c
  · have hz : ∀ i, μ i c = 0 := fun i => hμ0 i c h2
    simp only [columnCoefficient, layerTerm, hsq, layerTwist_apply, hz, zero_mul, star_zero, mul_zero,
      if_true, Finset.sum_const_zero, ← hc, h2, not_true_eq_false, and_false, if_false]
  · have hspan : Ideal.span {c} = A := (primaryIdealGenerator_spec A hg).1
    have hG := congrArg star (twisted_coefficient_eq_plain_square c (primaryIdealGenerator_spec A hg).2)
    simp only [star_mul', star_pow, star_star, hspan] at hG
    rw [columnCoefficient, if_pos ⟨hsq, hg, h2⟩]
    simp only [layerTerm, if_pos hsq, layerTwist_apply]
    simp only [star_mul', star_star, star_pow]
    rw [star_unramifiedNormWeight]
    unfold columnWeight orderSixWeight
    have hrhs : ∀ i, γ i * (unramifiedNormWeight w A *
        (μ i c * (ringComplex (symbol c n) * quadSymbol c n) *
          (star (ringComplex (symbol (omega ^ 2 * lambda ^ 2) c)) ^ 2 * star (thetaSquareWeight A)))) =
        (γ i * μ i c) * (unramifiedNormWeight w A *
          ((ringComplex (symbol c n) * quadSymbol c n) *
            (star (ringComplex (symbol (omega ^ 2 * lambda ^ 2) c)) ^ 2 * star (thetaSquareWeight A)))) := by
      intro i
      ring
    rw [Finset.sum_congr rfl (fun i _ => hrhs i), ← Finset.sum_mul, ← hW c h2, ← hG]
    unfold twoAdicWeight
    ring

/-- **A 2-adic expansion of the weight turns a long column into layers.** -/
theorem columnSeries_eq_of_expansion {ι : Type*} (S : Finset ι) (γ : ι → ℂ) (μ : ι → O →* ℂ)
    (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2)
    (hμ : ∀ i c, ‖μ i c‖ ≤ 1) (hμ0 : ∀ i c, (2 : O) ∣ c → μ i c = 0)
    (hW : ∀ c, ¬ (2 : O) ∣ c → twoAdicWeight n c = ∑ i ∈ S, γ i * μ i c) (w : ℂ) (hw : 1 < w.re) :
    columnSeries n w = ∑ i ∈ S, γ i *
      star (twistedSquarefreeSeriesG (layerTwist (μ i) n hn hn0 hn2) (omega ^ 2 * lambda ^ 2) (star w)) := by
  have hw' : 1 < (star w).re := by rwa [Complex.star_def, Complex.conj_re]
  have hs : ∀ i ∈ S, Summable (fun A => γ i *
      star (layerTerm (layerTwist (μ i) n hn hn0 hn2) (star w) A)) := fun i _ =>
    ((summable_layerTerm _ (norm_layerTwist_le (μ i) (hμ i) n hn hn0 hn2) _ hw').star).mul_left _
  rw [columnSeries, tsum_congr (columnCoefficient_eq_of_expansion S γ μ n hn hn0 hn2 hμ0 hW w),
    Summable.tsum_finsetSum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, ← tsum_star]
  rfl

theorem rayMonoid_eq_zero_of_even (η : RayCharacter) (c : O) (h2 : (2 : O) ∣ c) : rayMonoid η c = 0 := by
  rw [rayMonoid_apply, MulChar.map_nonunit _ (fun hu => (isUnit_mk_four_iff c).mp hu h2)]

/-- **The long columns are layers of twisted theta squares.** For a primary column `n` prime to `2` and
`Re w > 1`, `Σ_A g_{gen A}(n)/|gen A| N(A)^{−w} = Σ_η a_η(n) \overline{S^{Ξ_{η,n}}_{ω²λ²}(w̄)}`. -/
theorem columnSeries_eq_layers (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2) (w : ℂ)
    (hw : 1 < w.re) :
    columnSeries n w = ∑ η : RayCharacter, twoAdicCoeff n η *
      star (twistedSquarefreeSeriesG (columnLayerTwist η n hn hn0 hn2) (omega ^ 2 * lambda ^ 2) (star w)) :=
  columnSeries_eq_of_expansion Finset.univ (twoAdicCoeff n) rayMonoid n hn hn0 hn2 rayMonoid_norm_le
    rayMonoid_eq_zero_of_even (fun c hc => twoAdicWeight_expansion n c hc) w hw

/-! ### The actual root numbers -/

section Rows

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop in
/-- **The column root number is the column weight:** `g_c(n)/|c| = overline{r(n, c)}(c/n)₃(c/n)₂ω₆(c)` at a squarefree
row `c = Π_{π ∈ s} π`. -/
theorem columnRootNumber_eq_columnWeight (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn2 : IsCoprime n 2)
    (hnc : IsCoprime n (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) n / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) = columnWeight n (∏ π ∈ s, π) := by
  obtain ⟨hP, hc2⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  rw [rowRoot_column n _ hn hP hn2 hc2 hnc, mul_div_assoc,
    rowRootNumber_eq_weil_mul_cubicTwo s hnz hmax hlam h2 hprim hcop]
  rfl

end Rows

end GaloisForLFunctions.OrderSixMetaplecticTheory
