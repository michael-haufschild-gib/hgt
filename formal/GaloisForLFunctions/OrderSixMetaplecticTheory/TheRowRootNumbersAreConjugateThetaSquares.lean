import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberIsTheSquareOfTheThetaCoefficient
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CubicSieveNorm

/-!
# The row root numbers are conjugate theta squares

The long columns of the cubic-theta probe are first moments of the row root numbers
`Φ(c) = g_c^{(1)}(1)/|c|` (normalized sextic Gauss sums; FCT/CRF normalization). The spectral theory of
the cubic cover (STCC) reads squares of the Fourier coefficients `T(ν)` of the cubic theta function
(MMD normalization). This module identifies the two languages.

* `tracePhase_div_eq_principalTraceChar`, `residueAdditive_eq_principalTraceChar`: MMD's additive
  character `residueAdditive (3h) c` is FCT's `exp(2πi Tr(h d/(√−3 c)))`.
* `sexticSymbol_sq_eq`: `χ_c(x)² = (x/c)₃` for primary `c` prime to `2`.
* `thetaGauss_eq_normalizedCubicUnitGauss`: the theta coefficient `γ₂(c) = g_c^{(2)}(1)/|c|` is MMD's
  normalized cubic Gauss sum `G̃(c)`.
* `rowRootNumber_eq_conj_thetaSquareWeight`: for squarefree `c`, `Φ(c) = G(c) (9/c)₃² \overline{σ(c)}`,
  where `σ(c) = ((9/c)₃ \overline{G̃(c)})²` is the weight of the squarefree theta-square series of STCC
  (`T(c)² = \overline{C}² σ(c)`).
* `rowRoot_column`: a primary column `n` prime to `2c` twists the row root number by
  `\overline{r(n, c)} (c/n)₃ (c/n)₂`: a cubic and a quadratic character of the row modulo `n`, times the
  quadratic bicharacter modulo `4`. At square columns the quadratic character drops out
  (`rowRoot_square_column`).
* `rowRoot_tower`: the angular character of infinity type `−6k` (the rungs `ψ₆^k`) turns `Φ` into
  `G γ₂² \overline{γ₂}^{18k}`.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory CoherenceTheoryOfReciprocityFamilies MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  MetaplecticMobiusDescent.CubicJacobi

/-! ### The additive characters -/

theorem ringComplex_omega_sq : ringComplex omega ^ 2 + ringComplex omega + 1 = 0 := by
  have hp : IsPrimitiveRoot (ringComplex omega) 3 :=
    omega_primitive.map_of_injective ringComplex_injective
  have h := hp.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one] at h
  linear_combination h

/-- **The trace character.** `tracePhase(e/(√−3 c)) = exp(2πi Tr_{K/ℚ}(e/(√−3 c)))`: in coordinates
`c = a + bω`, `e = x + yω`, both are `exp(2πi (ay − bx)/(a² − ab + b²))`. -/
theorem tracePhase_div_eq_principalTraceChar (c e : O) (hc : c ≠ 0) :
    tracePhase (ringComplex e / (ringComplex traceLambda * ringComplex c)) =
      principalTraceChar c hc (Ideal.Quotient.mk (Ideal.span {c}) e) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℤ, Coordinates.eval a b = c := ⟨_, _, Coordinates.eval_coords c⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℤ, Coordinates.eval x y = e := ⟨_, _, Coordinates.eval_coords e⟩
  rw [principalTraceChar_eval a b x y hc]
  change Complex.exp (2 * Real.pi * Complex.I * (_ + starRingEnd ℂ _)) = _
  set w := ringComplex omega with hwdef
  have hw2 : w ^ 2 + w + 1 = 0 := ringComplex_omega_sq
  have hA : ringComplex (Coordinates.eval a b) = (a : ℂ) + (b : ℂ) * w := ringComplex_eval a b
  have hX : ringComplex (Coordinates.eval x y) = (x : ℂ) + (y : ℂ) * w := ringComplex_eval x y
  have hA0 : ringComplex (Coordinates.eval a b) ≠ 0 := ringComplex_ne_zero hc
  have hL0 : ringComplex traceLambda ≠ 0 := ringComplex_ne_zero traceLambda_ne_zero
  -- `\overline{a + bω} = (a − b) − bω`
  have hAc : starRingEnd ℂ (ringComplex (Coordinates.eval a b)) =
      (((a - b : ℤ) : ℝ) : ℂ) + (((-b : ℤ) : ℝ) : ℂ) * w := by
    rw [hA, map_add, map_mul, map_intCast, map_intCast, complex_omega_conjugate]
    push_cast
    ring
  have hAc0 : starRingEnd ℂ (ringComplex (Coordinates.eval a b)) ≠ 0 := (map_ne_zero _).mpr hA0
  -- `|a + bω|² = a² − ab + b²`
  have hNd : ((a * a - a * b + b * b : ℤ) : ℂ) =
      ringComplex (Coordinates.eval a b) * starRingEnd ℂ (ringComplex (Coordinates.eval a b)) := by
    rw [hAc, hA]
    push_cast
    linear_combination (b : ℂ) ^ 2 * hw2
  have hN0 : ((a * a - a * b + b * b : ℤ) : ℂ) ≠ 0 := by
    rw [hNd]
    exact mul_ne_zero hA0 hAc0
  -- the argument as `Y/N` with `Y = (x + yω)\overline{(a + bω)}/√−3`
  set Y : ℂ := ((((x : ℤ) : ℝ) : ℂ) + (((y : ℤ) : ℝ) : ℂ) * w) *
      ((((a - b : ℤ) : ℝ) : ℂ) + (((-b : ℤ) : ℝ) : ℂ) * w) / ringComplex traceLambda with hYdef
  have hz : ringComplex (Coordinates.eval x y) /
      (ringComplex traceLambda * ringComplex (Coordinates.eval a b)) =
      Y / ((a * a - a * b + b * b : ℤ) : ℂ) := by
    rw [hNd, hYdef, ← hAc, hX]
    push_cast
    field_simp
  have hY : Y + starRingEnd ℂ Y =
      ((((x : ℤ) : ℝ) * ((-b : ℤ) : ℝ) + ((y : ℤ) : ℝ) * ((a - b : ℤ) : ℝ) -
        ((y : ℤ) : ℝ) * ((-b : ℤ) : ℝ) : ℝ) : ℂ) :=
    complexTrace_real_basis_product _ _ _ _
  have hNr : starRingEnd ℂ ((a * a - a * b + b * b : ℤ) : ℂ) = ((a * a - a * b + b * b : ℤ) : ℂ) :=
    map_intCast _ _
  rw [hz, map_div₀, hNr, ← add_div, hY]
  congr 2
  push_cast
  ring

/-- **The two additive normalizations agree.** `residueAdditive (3h) c d = ψ_c(h d)`, `ψ_c` FCT's
primitive trace character modulo `c`. -/
theorem residueAdditive_eq_principalTraceChar (h c d : O) (hc : c ≠ 0) :
    residueAdditive (3 * h) c d =
      principalTraceChar c hc (Ideal.Quotient.mk (Ideal.span {c}) (h * d)) := by
  rw [← tracePhase_div_eq_principalTraceChar c (h * d) hc]
  unfold residueAdditive cuspFrequency
  congr 1
  have hL0 := ringComplex_ne_zero traceLambda_ne_zero
  have hc0 := ringComplex_ne_zero hc
  simp only [map_mul, map_ofNat]
  field_simp

/-! ### The square of the sextic symbol is the cubic symbol -/

theorem ringComplex_symbol_eq_zero {x c : O} (hc : lambda ^ 2 ∣ c - 1) (hxc : ¬ IsCoprime x c) :
    ringComplex (symbol x c) = 0 := by
  have hc0 : c ≠ 0 := primary_ne_zero c hc
  have hm := CubicSieve.idealSymbol_cube_mask (Ideal.span {c}) x
    (by rw [primaryIdealGenerator_span c hc0 hc]; exact hc0)
  have hcop : ¬ IsCoprime (Ideal.span {c}) (Ideal.span {x}) := by
    rw [Ideal.isCoprime_span_singleton_iff]
    exact fun h => hxc h.symm
  rw [if_neg hcop] at hm
  have h3 : ringComplex (symbol x c) ^ 3 = 0 := by simpa only [symbol] using hm
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h3

/-- `χ_c(x)² = (x/c)₃` for primary `c` prime to `2`: the square of the sextic symbol is the cubic
symbol (zero off the units). -/
theorem sexticSymbol_sq_eq (x c : O) (hc : lambda ^ 2 ∣ c - 1) (hc2 : IsCoprime c 2) :
    sexticSymbol x c ^ 2 = ringComplex (symbol x c) := by
  have hc0 : c ≠ 0 := primary_ne_zero c hc
  by_cases hxc : IsCoprime x c
  · have h3 := symbol_cube_of_isCoprime x c hc hxc
    have hq := quadSymbol_sq hc0 hc2 hxc
    unfold sexticSymbol
    rw [mul_pow, hq, mul_one, ← pow_mul, ← map_pow]
    congr 1
    calc symbol x c ^ (2 * 2) = symbol x c ^ 3 * symbol x c := by ring
      _ = symbol x c := by rw [h3, one_mul]
  · unfold sexticSymbol
    rw [ringComplex_symbol_eq_zero hc hxc]
    simp

/-! ### The theta coefficient is the normalized cubic Gauss sum -/

/-- `g_c^{(2)}(1) = Σ_{d ∈ (O/c)ˣ} (d/c)₃ ψ_c(d)`: FCT's Gauss sum of `χ_c²` is MMD's cubic unit Gauss
sum. -/
theorem sexticGaussPow_two_eq_cubicUnitGaussSum (c : O) [NeZero c] (hc : lambda ^ 2 ∣ c - 1)
    (hc2 : IsCoprime c 2) : sexticGaussPow 2 c 1 = cubicUnitGaussSum 1 c := by
  have hc0 : c ≠ 0 := NeZero.ne c
  let f : O ⧸ Ideal.span {c} → ℂ := fun r =>
    ringComplex (symbol (principalResidueRep c r) c) * residueAdditive (3 * 1) c (principalResidueRep c r)
  have hunit : (∑' r : CubicUnitResidue c, f r.val) = ∑' r : O ⧸ Ideal.span {c}, f r := by
    apply tsum_subtype_eq_of_support_subset (s := {r | IsUnit r})
    intro r hr
    have hn : ringComplex (symbol (principalResidueRep c r) c) ≠ 0 := left_ne_zero_of_mul hr
    have hcop : IsCoprime (principalResidueRep c r) c := by
      by_contra h
      exact hn (ringComplex_symbol_eq_zero hc h)
    have hu := isUnit_mk_of_isCoprime hcop
    rwa [principalResidueRep_spec] at hu
  have hdef : cubicUnitGaussSum 1 c = ∑' r : CubicUnitResidue c, f r.val := rfl
  rw [hdef, hunit, tsum_fintype]
  unfold sexticGaussPow
  refine Finset.sum_congr rfl fun r _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hrep : c ∣ principalResidueRep c (Ideal.Quotient.mk _ x) - x := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, principalResidueRep_spec]
  simp only [f]
  rw [sexticResidue_mk, sexticSymbol_sq_eq x c hc hc2, symbol_congr hrep,
    residueAdditive_eq_principalTraceChar 1 c _ hc0, one_mul, principalResidueRep_spec, map_one,
    one_mul]

/-- **The theta coefficient is MMD's normalized cubic Gauss sum.** `γ₂(c) = G̃(c)`. -/
theorem thetaGauss_eq_normalizedCubicUnitGauss (c : O) [NeZero c] (hc : lambda ^ 2 ∣ c - 1)
    (hc2 : IsCoprime c 2) : thetaGauss c = normalizedCubicUnitGauss c := by
  unfold thetaGauss normalizedCubicUnitGauss
  rw [sexticGaussPow_two_eq_cubicUnitGaussSum c hc hc2]

/-! ### Unimodular phases -/

/-- A unit of `ℂ` of finite order: `z * \bar z = 1`. -/
theorem mul_conj_eq_one_of_pow {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    z * starRingEnd ℂ z = 1 := by
  have h1 : ‖z‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp
    rw [← norm_pow, hz, norm_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  norm_num

/-- `(9/c)₃` is a cube root of unity for primary `c`. -/
theorem symbol_nine_mul_conj {c : O} (hc : lambda ^ 2 ∣ c - 1) :
    ringComplex (symbol 9 c) * starRingEnd ℂ (ringComplex (symbol 9 c)) = 1 := by
  have h3 : IsCoprime (3 : O) c := by
    simpa only [Units.val_one, pow_zero, mul_one] using ramified_primary_coprime (1 : Oˣ) 0 c hc
  have h9 : IsCoprime (9 : O) c := by
    have := h3.pow_left (m := 2)
    norm_num at this
    exact this
  refine mul_conj_eq_one_of_pow (n := 3) (by norm_num) ?_
  rw [← map_pow, symbol_cube_of_isCoprime 9 c hc h9, map_one]

/-- A quadratic symbol at a coprime numerator is real. -/
theorem conj_quadSymbol {x a : O} (ha0 : a ≠ 0) (ha2 : IsCoprime a 2) (hxa : IsCoprime x a) :
    starRingEnd ℂ (quadSymbol x a) = quadSymbol x a := by
  have hq := quadSymbol_sq ha0 ha2 hxa
  have h : (quadSymbol x a - 1) * (quadSymbol x a + 1) = 0 := by linear_combination hq
  rcases mul_eq_zero.mp h with h | h
  · rw [sub_eq_zero.mp h, map_one]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_one]

/-- The conjugate square of a cube root of unity is itself. -/
theorem conj_sq_of_cube {z : ℂ} (hz : z ^ 3 = 1) : starRingEnd ℂ z ^ 2 = z := by
  have hu := mul_conj_eq_one_of_pow (n := 3) (by norm_num) hz
  have h : starRingEnd ℂ z = z ^ 2 := by
    calc starRingEnd ℂ z = starRingEnd ℂ z * z ^ 3 := by rw [hz, mul_one]
      _ = (z * starRingEnd ℂ z) * z ^ 2 := by ring
      _ = z ^ 2 := by rw [hu, one_mul]
  rw [h, ← pow_mul]
  calc z ^ (2 * 2) = z ^ 3 * z := by ring
    _ = z := by rw [hz, one_mul]

/-! ### The row root number through the theta-square weight -/

section Row

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop

theorem row_primary : lambda ^ 2 ∣ (∏ π ∈ s, π) - 1 ∧ IsCoprime (∏ π ∈ s, π) 2 := by
  obtain ⟨-, hP, hc2⟩ := normSq_sexticGaussPow_prod s hnz hmax hlam h2 hprim hcop
    (j := 1) one_ne_zero (by norm_num)
  exact ⟨hP, hc2⟩

/-- The phase `G(c) = \overline{χ_c(4)} Γ(c)` is unimodular. -/
theorem thetaPhase_mul_conj :
    thetaPhase (∏ π ∈ s, π) * starRingEnd ℂ (thetaPhase (∏ π ∈ s, π)) = 1 := by
  obtain ⟨-, hQ⟩ := rowHasseDavenport s hnz hmax hlam h2 hprim hcop
  obtain ⟨ha0, -, hχ⟩ := row_norm_facts s hnz hmax hlam h2 hprim hcop
  obtain ⟨hN3, -, -⟩ := normSq_sexticGaussPow_prod s hnz hmax hlam h2 hprim hcop
    (j := 3) three_ne_zero (by norm_num)
  set c := ∏ π ∈ s, π
  -- `|Γ(c)| = 1` from `g³ = |c|Γ` and `|g³| = |c|`
  have hΓ : fixedDualAverage c * starRingEnd ℂ (fixedDualAverage c) = 1 := by
    rw [hQ, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (ringComplex c)]
      at hN3
    have hc0 : ‖ringComplex c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ha0)
    have hn : Complex.normSq (fixedDualAverage c) = 1 := by
      apply mul_left_cancel₀ hc0
      linear_combination hN3
    rw [Complex.mul_conj, hn]
    norm_num
  unfold thetaPhase
  rw [map_mul, Complex.conj_conj]
  linear_combination (starRingEnd ℂ (sexticSymbol 4 c) * sexticSymbol 4 c) * hΓ +
    (fixedDualAverage c * starRingEnd ℂ (fixedDualAverage c) - 1 + 1) * hχ - hχ * (fixedDualAverage c * starRingEnd ℂ (fixedDualAverage c) - 1)

/-- **The row root number through the theta-square weight.** For squarefree `c`,
`Φ(c) = G(c) (9/c)₃² \overline{σ(c)}`, `σ(c) = ((9/c)₃ \overline{G̃(c)})²` the weight with
`T(c)² = \overline{C}² σ(c)` (STCC). -/
theorem rowRootNumber_eq_conj_thetaSquareWeight :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) =
      thetaPhase (∏ π ∈ s, π) * ringComplex (symbol 9 (∏ π ∈ s, π)) ^ 2 *
        star (SpectralTheoryOfTheCubicCover.thetaSquareWeight (Ideal.span {∏ π ∈ s, π})) := by
  obtain ⟨hP, hc2⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  have hu := symbol_nine_mul_conj hP
  rw [rowRootNumber_eq_thetaPhase_mul_sq s hnz hmax hlam h2 hprim hcop]
  set c := ∏ π ∈ s, π
  rw [thetaGauss_eq_normalizedCubicUnitGauss c hP hc2]
  unfold SpectralTheoryOfTheCubicCover.thetaSquareWeight
  rw [primaryIdealGenerator_span c (NeZero.ne c) hP, star_pow, star_mul', star_star,
    Complex.star_def]
  set z := ringComplex (symbol 9 c)
  set u := z * starRingEnd ℂ z
  linear_combination (-(thetaPhase c * normalizedCubicUnitGauss c ^ 2 * (u + 1))) * hu

/-- **The theta-square weight through the row root number.** `σ(c) = G(c)(9/c)₃² \overline{Φ(c)}`. -/
theorem thetaSquareWeight_eq_rowRootNumber :
    SpectralTheoryOfTheCubicCover.thetaSquareWeight (Ideal.span {∏ π ∈ s, π}) =
      thetaPhase (∏ π ∈ s, π) * ringComplex (symbol 9 (∏ π ∈ s, π)) ^ 2 *
        star (sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) := by
  obtain ⟨hP, -⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  have hu := symbol_nine_mul_conj hP
  have hG := thetaPhase_mul_conj s hnz hmax hlam h2 hprim hcop
  rw [rowRootNumber_eq_conj_thetaSquareWeight s hnz hmax hlam h2 hprim hcop]
  set c := ∏ π ∈ s, π
  rw [star_mul', star_mul', star_pow, star_star]
  set σ := SpectralTheoryOfTheCubicCover.thetaSquareWeight (Ideal.span {c})
  set z := ringComplex (symbol 9 c)
  set G := thetaPhase c
  set u := z * starRingEnd ℂ z
  set v := G * starRingEnd ℂ G
  linear_combination (-(σ)) * hG - σ * v * (u + 1) * hu

/-- **The tower.** The angular character of infinity type `−6k` multiplies the row root number by
`\overline{γ₂}^{18k}`: `\overline{(c/|c|)}^{6k} Φ(c) = G(c) γ₂(c)² \overline{γ₂(c)}^{18k}`, since
`c/|c| = μ(c) γ₂(c)³`. -/
theorem rowRoot_tower (k : ℕ) :
    starRingEnd ℂ (ringComplex (∏ π ∈ s, π) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) ^ (6 * k) *
        (sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) =
      thetaPhase (∏ π ∈ s, π) * thetaGauss (∏ π ∈ s, π) ^ 2 *
        starRingEnd ℂ (thetaGauss (∏ π ∈ s, π)) ^ (18 * k) := by
  have hcube := thetaGauss_cube s hnz hmax hlam h2 hprim hcop
  rw [rowRootNumber_eq_thetaPhase_mul_sq s hnz hmax hlam h2 hprim hcop]
  set c := ∏ π ∈ s, π
  have hang : ringComplex c / (‖ringComplex c‖ : ℂ) = (-1) ^ s.card * thetaGauss c ^ 3 := by
    rw [hcube, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [hang, map_mul, map_pow, map_neg, map_one, map_pow, mul_pow, ← pow_mul, ← pow_mul,
    show s.card * (6 * k) = 2 * (3 * s.card * k) by ring, pow_mul, neg_one_sq, one_pow, one_mul,
    show 3 * (6 * k) = 18 * k by ring]
  ring

end Row

/-! ### Columns -/

/-- **The column law.** For primary `n`, `c` prime to `2` and to each other,
`g_c(n) = \overline{r(n, c)} (c/n)₃ (c/n)₂ g_c(1)`: the column twists the row by a cubic and a
quadratic character of the row modulo `n`, times the quadratic bicharacter modulo `4`. -/
theorem rowRoot_column (n c : O) [NeZero c] (hn : lambda ^ 2 ∣ n - 1) (hc : lambda ^ 2 ∣ c - 1)
    (hn2 : IsCoprime n 2) (hc2 : IsCoprime c 2) (hnc : IsCoprime n c) :
    sexticGaussPow 1 c n =
      starRingEnd ℂ (quadraticPhase n c) * (ringComplex (symbol c n) * quadSymbol c n) *
        sexticGaussPow 1 c 1 := by
  have hc0 : c ≠ 0 := NeZero.ne c
  have hn0 : n ≠ 0 := primary_ne_zero n hn
  have ht := sexticSymbol_mul_sexticGauss c hnc 1
  rw [mul_one] at ht
  have hχ : ‖sexticSymbol n c‖ = 1 := norm_sexticSymbol_eq_one hc0 hc hc2 hnc
  have hχc : starRingEnd ℂ (sexticSymbol n c) * sexticSymbol n c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]
    norm_num
  have hrec := sexticSymbol_reciprocity hn hc hn2 hc2 hnc
  -- `\overline{χ_n(c)} = (c/n)₃ (c/n)₂`
  have hcube : ringComplex (symbol c n) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime c n hn hnc.symm, map_one]
  have hconj : starRingEnd ℂ (sexticSymbol c n) = ringComplex (symbol c n) * quadSymbol c n := by
    unfold sexticSymbol
    rw [map_mul, map_pow, conj_sq_of_cube hcube, conj_quadSymbol hn0 hn2 hnc.symm]
  have hg : sexticGauss c n = starRingEnd ℂ (sexticSymbol n c) * sexticGauss c 1 := by
    rw [← ht, ← mul_assoc, hχc, one_mul]
  change sexticGauss c n = _ * sexticGauss c 1
  rw [hg, hrec, map_mul, hconj]

/-- **Square columns.** At `n = m²` the quadratic character of the column drops out:
`g_c(m²) = \overline{r(m², c)} (c/m)₃² g_c(1)`. -/
theorem rowRoot_square_column (m c : O) [NeZero c] (hm : lambda ^ 2 ∣ m - 1)
    (hc : lambda ^ 2 ∣ c - 1) (hm2 : IsCoprime m 2) (hc2 : IsCoprime c 2) (hmc : IsCoprime m c) :
    sexticGaussPow 1 c (m ^ 2) =
      starRingEnd ℂ (quadraticPhase (m ^ 2) c) * ringComplex (symbol c m) ^ 2 *
        sexticGaussPow 1 c 1 := by
  have hm0 : m ≠ 0 := primary_ne_zero m hm
  have hsq : lambda ^ 2 ∣ m ^ 2 - 1 := by
    have : m ^ 2 - 1 = (m - 1) * (m + 1) := by ring
    rw [this]
    exact dvd_mul_of_dvd_left hm _
  rw [rowRoot_column (m ^ 2) c hsq hc hm2.pow_left hc2 hmc.pow_left, sq m,
    symbol_mul_denominator, quadSymbol_mul_denominator, ← sq (quadSymbol c m),
    quadSymbol_sq hm0 hm2 hmc.symm, map_mul, ← sq]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
