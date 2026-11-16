import GaloisForLFunctions.OrderSixMetaplecticTheory.TheRowRootNumbersAreConjugateThetaSquares

/-!
# The columns are shifted theta products

The long columns of the probe are the order-six Kubota series `Σ_c g_c(n)/|c| N(c)^{−w}` at column `n`. The
column law (`rowRoot_column`) twists the row root number `Φ(c) = G(c) G̃(c)²` by `(c/n)₃ (c/n)₂`. Twisted
multiplicativity of the normalized cubic Gauss sums `G̃` (the theta coefficients of the cubic theta
function up to the phases `(9/·)₃`, `C̄`) absorbs the cubic character into a **shift**:

* `cubicColumn_shift`: `(c/n₁)₃ (c/n₂)₃² G̃(c)² · G̃(n₁n₂) G̃(n₁) = G̃(n₁n₂c) G̃(n₁c)`;
* `squareColumn_shift`: `(c/m)₃² G̃(c)² · G̃(m) = G̃(mc) G̃(c)`.

Write a column as `n = n₁ n₂² k³` (`n₁, n₂, k` primary, prime to `2` and to each other). Then
(`rowRoot_column_shift`)

`g_c(n)/|c| · G̃(n₁n₂) G̃(n₁) = \overline{r(n, c)} · (c/n₁k)₂ · G(c) · G̃(n₁n₂c) G̃(n₁c)`.

So the `n`-th column of the order-six Kubota series is the shifted Rankin–Selberg product of the cubic
theta function between the dilations by `n₁n₂` and `n₁`, twisted by the quadratic character of `n₁k` and
by phases of conductor `4`. The cubic part of the column (exponents `≢ 0 mod 3`) becomes a shift of the
theta coefficients; the quadratic part (odd exponents) is what the six-fold cover adds:

* square columns `n = m²` carry no quadratic character: the column is `G̃(mc)G̃(c)` (`rowRoot_square_column_shift`),
  a cubic object;
* cube columns `n = k³` carry no shift: the column is the row family twisted by `(c/k)₂`
  (`rowRoot_cube_column`), a purely quadratic twist;
* sixth powers carry neither (the rank-one columns of the reflected Gram).

The conductor phase `G(c) = \overline{χ_c(4)} Γ(c)` splits the same way: `\overline{χ_c(4)} = (c/−2)₃²` is a shift by
`−2` (`conj_sexticSymbol_four`), so `Φ(c) G̃(−2) = Γ(c) G̃(−2c) G̃(c)` (`rowRootNumber_shift_neg_two`) and, at every
column (`rowRoot_column_shift_actual`),

`g_c(n)/|c| · G̃(−2n₁n₂) G̃(n₁) = \overline{r(n, c)} (c/n₁k)₂ Γ(c) · G̃(−2n₁n₂c) G̃(n₁c)`:

the order-six content of every long column is quadratic — the character `(c/n₁k)₂` and the Weil index `Γ(c)`
of the quadratic Gauss sum, a function of `c` modulo `4`. Together they are the normalized quadratic Gauss
sum of the row at numerator `n₁k` (`quadSymbol_mul_fixedDualAverage`), so (`rowRoot_column_hasseDavenport`)

`g_c(n)/|c| · G̃(−2n₁n₂) G̃(n₁) = \overline{r(n, c)} r(n₁k, c) · g_c^{(3)}(n₁k)/|c| · G̃(−2n₁n₂c) G̃(n₁c)`:

Hasse–Davenport at every column — the sextic Gauss sum of a row at a column is a quadratic Gauss sum of
the row times a shifted product of cubic theta coefficients.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory CoherenceTheoryOfReciprocityFamilies MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  MetaplecticMobiusDescent.CubicJacobi

theorem primary_mul {a b : O} (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1) :
    lambda ^ 2 ∣ a * b - 1 := by
  have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left ha _) hb

/-- The conjugate of a cube root of unity is its square. -/
theorem conj_eq_sq_of_cube {z : ℂ} (hz : z ^ 3 = 1) : starRingEnd ℂ z = z ^ 2 := by
  have h := mul_conj_eq_one_of_pow (n := 3) (by norm_num) hz
  calc starRingEnd ℂ z = starRingEnd ℂ z * z ^ 3 := by rw [hz, mul_one]
    _ = (z * starRingEnd ℂ z) * z ^ 2 := by ring
    _ = z ^ 2 := by rw [h, one_mul]

/-- `G̃(ab) = \overline{(a/b)₃} G̃(a) G̃(b)` for coprime primary `a, b`. -/
theorem normalizedCubicUnitGauss_mul {a b : O} (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1)
    (hab : IsCoprime a b) :
    normalizedCubicUnitGauss (a * b) =
      starRingEnd ℂ (ringComplex (symbol a b)) * normalizedCubicUnitGauss a * normalizedCubicUnitGauss b := by
  have h := congrArg star (normalizedCubicUnitGauss_coprime_product a b (primary_ne_zero a ha)
    (primary_ne_zero b hb) ha hb hab)
  rw [star_star, star_mul', star_mul', star_star, star_star] at h
  rw [h]
  rfl

/-- The cube root of unity `(c/n)₃` at coprime primary `n`. -/
theorem symbol_cube {c n : O} (hn : lambda ^ 2 ∣ n - 1) (hcn : IsCoprime c n) :
    ringComplex (symbol c n) ^ 3 = 1 := by
  rw [← map_pow, symbol_cube_of_isCoprime c n hn hcn, map_one]

/-- **The cubic part of a column is a shift.** For primary, pairwise coprime `c, n₁, n₂`:
`(c/n₁)₃ (c/n₂)₃² G̃(c)² · G̃(n₁n₂) G̃(n₁) = G̃(n₁n₂c) G̃(n₁c)`. -/
theorem cubicColumn_shift {c n₁ n₂ : O} (hc : lambda ^ 2 ∣ c - 1) (h1 : lambda ^ 2 ∣ n₁ - 1)
    (h2 : lambda ^ 2 ∣ n₂ - 1) (hc1 : IsCoprime n₁ c) (hc2 : IsCoprime n₂ c) :
    ringComplex (symbol c n₁) * ringComplex (symbol c n₂) ^ 2 * normalizedCubicUnitGauss c ^ 2 *
        (normalizedCubicUnitGauss (n₁ * n₂) * normalizedCubicUnitGauss n₁) =
      normalizedCubicUnitGauss (n₁ * n₂ * c) * normalizedCubicUnitGauss (n₁ * c) := by
  have h12 := primary_mul h1 h2
  rw [normalizedCubicUnitGauss_mul h12 hc (hc1.mul_left hc2), normalizedCubicUnitGauss_mul h1 hc hc1,
    symbol_mul_numerator, map_mul, map_mul, symbol_reciprocity n₁ c h1 hc, symbol_reciprocity n₂ c h2 hc]
  set z₁ := ringComplex (symbol c n₁)
  set z₂ := ringComplex (symbol c n₂)
  have e1 : starRingEnd ℂ z₁ ^ 2 = z₁ := conj_sq_of_cube (symbol_cube h1 hc1.symm)
  have e2 : starRingEnd ℂ z₂ = z₂ ^ 2 := conj_eq_sq_of_cube (symbol_cube h2 hc2.symm)
  rw [e2]
  linear_combination (-(z₂ ^ 2 * normalizedCubicUnitGauss c ^ 2 *
    (normalizedCubicUnitGauss (n₁ * n₂) * normalizedCubicUnitGauss n₁))) * e1

/-- **Square columns shift once.** `(c/m)₃² G̃(c)² · G̃(m) = G̃(mc) G̃(c)`. -/
theorem squareColumn_shift {c m : O} (hc : lambda ^ 2 ∣ c - 1) (hm : lambda ^ 2 ∣ m - 1)
    (hmc : IsCoprime m c) :
    ringComplex (symbol c m) ^ 2 * normalizedCubicUnitGauss c ^ 2 * normalizedCubicUnitGauss m =
      normalizedCubicUnitGauss (m * c) * normalizedCubicUnitGauss c := by
  rw [normalizedCubicUnitGauss_mul hm hc hmc, symbol_reciprocity m c hm hc,
    conj_eq_sq_of_cube (symbol_cube hm hmc.symm)]
  ring


/-! ### The conductor phase -/

/-- `(−1/c)₃ = 1`. -/
theorem symbol_neg_one {c : O} (hc : lambda ^ 2 ∣ c - 1) : ringComplex (symbol (-1) c) = 1 := by
  have h3 := symbol_cube_of_isCoprime (-1) c hc ((isCoprime_one_left : IsCoprime (1 : O) c).neg_left)
  have hm : symbol (-1) c = symbol (-1) c ^ 3 := by
    calc symbol (-1) c = symbol ((-1) * (-1) * (-1)) c := by norm_num
      _ = symbol (-1) c ^ 3 := by rw [symbol_mul_numerator, symbol_mul_numerator]; ring
  rw [hm, h3, map_one]

theorem primary_neg_two : lambda ^ 2 ∣ (-2 : O) - 1 := by
  have h : (-2 : O) - 1 = -3 := by ring
  rw [h]
  exact lambda_sq_dvd_three.neg_right

/-- **The cubic part of the conductor phase.** `\overline{χ_c(4)} = (c/−2)₃²` for primary `c` prime to `2`. -/
theorem conj_sexticSymbol_four {c : O} (hc : lambda ^ 2 ∣ c - 1) (hc2 : IsCoprime c 2) :
    starRingEnd ℂ (sexticSymbol 4 c) = ringComplex (symbol c (-2)) ^ 2 := by
  have h4 : sexticSymbol 4 c = ringComplex (symbol 2 c) := by
    rw [show (4 : O) = 2 * 2 by norm_num, sexticSymbol_mul_numerator, ← sq, sexticSymbol_sq_eq 2 c hc hc2]
  have h2 : ringComplex (symbol 2 c) = ringComplex (symbol c (-2)) := by
    have hsplit : symbol 2 c = symbol (-1) c * symbol (-2) c := by
      rw [← symbol_mul_numerator]
      norm_num
    rw [hsplit, map_mul, symbol_neg_one hc, one_mul, symbol_reciprocity (-2) c primary_neg_two hc]
  rw [h4, h2, conj_eq_sq_of_cube (symbol_cube primary_neg_two hc2.neg_right)]

/-! ### The column dictionary on the rows -/

section Row

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop

/-- The row root number `Φ(c) = G(c) G̃(c)²`. -/
theorem rowRootNumber_eq_thetaPhase_mul_gauss_sq :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) =
      thetaPhase (∏ π ∈ s, π) * normalizedCubicUnitGauss (∏ π ∈ s, π) ^ 2 := by
  obtain ⟨hP, hc2⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  rw [rowRootNumber_eq_thetaPhase_mul_sq s hnz hmax hlam h2 hprim hcop,
    thetaGauss_eq_normalizedCubicUnitGauss _ hP hc2]

/-- **The column dictionary.** For a column `n = n₁ n₂² k³` (`n₁, n₂, k` primary, prime to `2`, to each
other and to the row `c`):
`g_c(n)/|c| · G̃(n₁n₂) G̃(n₁) = \overline{r(n, c)} (c/n₁k)₂ G(c) G̃(n₁n₂c) G̃(n₁c)`. -/
theorem rowRoot_column_shift (n₁ n₂ k : O) (h1 : lambda ^ 2 ∣ n₁ - 1) (h2' : lambda ^ 2 ∣ n₂ - 1)
    (hk : lambda ^ 2 ∣ k - 1) (h12 : IsCoprime n₁ 2) (h22 : IsCoprime n₂ 2) (hk2 : IsCoprime k 2)
    (hc1 : IsCoprime n₁ (∏ π ∈ s, π)) (hc2 : IsCoprime n₂ (∏ π ∈ s, π))
    (hck : IsCoprime k (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) (n₁ * n₂ ^ 2 * k ^ 3) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) *
        (normalizedCubicUnitGauss (n₁ * n₂) * normalizedCubicUnitGauss n₁) =
      starRingEnd ℂ (quadraticPhase (n₁ * n₂ ^ 2 * k ^ 3) (∏ π ∈ s, π)) *
        quadSymbol (∏ π ∈ s, π) (n₁ * k) * thetaPhase (∏ π ∈ s, π) *
          (normalizedCubicUnitGauss (n₁ * n₂ * ∏ π ∈ s, π) *
            normalizedCubicUnitGauss (n₁ * ∏ π ∈ s, π)) := by
  obtain ⟨hP, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  set c := ∏ π ∈ s, π
  have hc0 : c ≠ 0 := NeZero.ne c
  have hn : lambda ^ 2 ∣ n₁ * n₂ ^ 2 * k ^ 3 - 1 :=
    primary_mul (primary_mul h1 (by rw [show n₂ ^ 2 = n₂ * n₂ from sq n₂]; exact primary_mul h2' h2'))
      (by rw [show k ^ 3 = k * k * k by ring]; exact primary_mul (primary_mul hk hk) hk)
  have hn2 : IsCoprime (n₁ * n₂ ^ 2 * k ^ 3) 2 := (h12.mul_left h22.pow_left).mul_left hk2.pow_left
  have hnc : IsCoprime (n₁ * n₂ ^ 2 * k ^ 3) c := (hc1.mul_left hc2.pow_left).mul_left hck.pow_left
  have hcol := rowRoot_column (n₁ * n₂ ^ 2 * k ^ 3) c hn hP hn2 hc2' hnc
  -- the cubic and quadratic characters of the column
  have hz : ringComplex (symbol c (n₁ * n₂ ^ 2 * k ^ 3)) =
      ringComplex (symbol c n₁) * ringComplex (symbol c n₂) ^ 2 := by
    rw [show n₂ ^ 2 = n₂ * n₂ from sq n₂, show k ^ 3 = k * k * k by ring]
    simp only [symbol_mul_denominator, map_mul]
    have hk3 : ringComplex (symbol c k) ^ 3 = 1 := symbol_cube hk hck.symm
    linear_combination (ringComplex (symbol c n₁) * ringComplex (symbol c n₂) ^ 2) * hk3
  have hq : quadSymbol c (n₁ * n₂ ^ 2 * k ^ 3) = quadSymbol c (n₁ * k) := by
    have hq2 : quadSymbol c n₂ ^ 2 = 1 :=
      quadSymbol_sq (primary_ne_zero n₂ h2') h22 hc2.symm
    have hqk : quadSymbol c k ^ 2 = 1 := quadSymbol_sq (primary_ne_zero k hk) hk2 hck.symm
    rw [show n₂ ^ 2 = n₂ * n₂ from sq n₂, show k ^ 3 = k * k * k by ring]
    simp only [quadSymbol_mul_denominator]
    linear_combination (quadSymbol c n₁ * quadSymbol c k * (quadSymbol c k ^ 2)) * hq2 +
      (quadSymbol c n₁ * quadSymbol c k) * hqk
  have hΦ := rowRootNumber_eq_thetaPhase_mul_gauss_sq s hnz hmax hlam h2 hprim hcop
  have hshift := cubicColumn_shift hP h1 h2' hc1 hc2
  have ha0 : (‖ringComplex c‖ : ℂ) ≠ 0 := by
    have : ringComplex c ≠ 0 := fun h => hc0 (ringComplex_injective (by rw [h, map_zero]))
    exact_mod_cast norm_ne_zero_iff.mpr this
  rw [hcol, hz, hq, mul_div_assoc, hΦ, ← hshift]
  ring


/-- **The conductor phase is a shift by `−2`.** The row root number is the quadratic Weil index
`Γ(c)` times a shifted theta product: `Φ(c) · G̃(−2) = Γ(c) · G̃(−2c) G̃(c)`. -/
theorem rowRootNumber_shift_neg_two :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) * normalizedCubicUnitGauss (-2) =
      fixedDualAverage (∏ π ∈ s, π) *
        (normalizedCubicUnitGauss (-2 * ∏ π ∈ s, π) * normalizedCubicUnitGauss (∏ π ∈ s, π)) := by
  obtain ⟨hP, hc2⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  rw [rowRootNumber_eq_thetaPhase_mul_gauss_sq s hnz hmax hlam h2 hprim hcop, thetaPhase,
    conj_sexticSymbol_four hP hc2,
    ← squareColumn_shift hP primary_neg_two hc2.symm.neg_left]
  ring

/-- **The column dictionary of the actual row family.** For a column `n = n₁ n₂² k³` (`n₁, n₂, k` primary,
prime to `2`, to each other and to the row `c`):
`g_c(n)/|c| · G̃(−2n₁n₂) G̃(n₁) = \overline{r(n, c)} (c/n₁k)₂ Γ(c) · G̃(−2n₁n₂c) G̃(n₁c)`.
All cubic data of the row, the column and the conductor phase are a shift of the theta coefficients;
what remains is quadratic: the character `(c/n₁k)₂` and the Weil index `Γ(c)` of conductor `4`. -/
theorem rowRoot_column_shift_actual (n₁ n₂ k : O) (h1 : lambda ^ 2 ∣ n₁ - 1) (h2' : lambda ^ 2 ∣ n₂ - 1)
    (hk : lambda ^ 2 ∣ k - 1) (h12 : IsCoprime n₁ 2) (h22 : IsCoprime n₂ 2) (hk2 : IsCoprime k 2)
    (hc1 : IsCoprime n₁ (∏ π ∈ s, π)) (hc2 : IsCoprime n₂ (∏ π ∈ s, π))
    (hck : IsCoprime k (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) (n₁ * n₂ ^ 2 * k ^ 3) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) *
        (normalizedCubicUnitGauss (n₁ * (-2 * n₂)) * normalizedCubicUnitGauss n₁) =
      starRingEnd ℂ (quadraticPhase (n₁ * n₂ ^ 2 * k ^ 3) (∏ π ∈ s, π)) *
        quadSymbol (∏ π ∈ s, π) (n₁ * k) * fixedDualAverage (∏ π ∈ s, π) *
          (normalizedCubicUnitGauss (n₁ * (-2 * n₂) * ∏ π ∈ s, π) *
            normalizedCubicUnitGauss (n₁ * ∏ π ∈ s, π)) := by
  obtain ⟨hP, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  set c := ∏ π ∈ s, π
  have hn : lambda ^ 2 ∣ n₁ * n₂ ^ 2 * k ^ 3 - 1 :=
    primary_mul (primary_mul h1 (by rw [show n₂ ^ 2 = n₂ * n₂ from sq n₂]; exact primary_mul h2' h2'))
      (by rw [show k ^ 3 = k * k * k by ring]; exact primary_mul (primary_mul hk hk) hk)
  have hn2 : IsCoprime (n₁ * n₂ ^ 2 * k ^ 3) 2 := (h12.mul_left h22.pow_left).mul_left hk2.pow_left
  have hnc : IsCoprime (n₁ * n₂ ^ 2 * k ^ 3) c := (hc1.mul_left hc2.pow_left).mul_left hck.pow_left
  have hcol := rowRoot_column (n₁ * n₂ ^ 2 * k ^ 3) c hn hP hn2 hc2' hnc
  have hz : ringComplex (symbol c (n₁ * n₂ ^ 2 * k ^ 3)) =
      ringComplex (symbol c n₁) * ringComplex (symbol c n₂) ^ 2 := by
    rw [show n₂ ^ 2 = n₂ * n₂ from sq n₂, show k ^ 3 = k * k * k by ring]
    simp only [symbol_mul_denominator, map_mul]
    have hk3 : ringComplex (symbol c k) ^ 3 = 1 := symbol_cube hk hck.symm
    linear_combination (ringComplex (symbol c n₁) * ringComplex (symbol c n₂) ^ 2) * hk3
  have hq : quadSymbol c (n₁ * n₂ ^ 2 * k ^ 3) = quadSymbol c (n₁ * k) := by
    have hq2 : quadSymbol c n₂ ^ 2 = 1 :=
      quadSymbol_sq (primary_ne_zero n₂ h2') h22 hc2.symm
    have hqk : quadSymbol c k ^ 2 = 1 := quadSymbol_sq (primary_ne_zero k hk) hk2 hck.symm
    rw [show n₂ ^ 2 = n₂ * n₂ from sq n₂, show k ^ 3 = k * k * k by ring]
    simp only [quadSymbol_mul_denominator]
    linear_combination (quadSymbol c n₁ * quadSymbol c k * (quadSymbol c k ^ 2)) * hq2 +
      (quadSymbol c n₁ * quadSymbol c k) * hqk
  -- the shift by `−2n₂` absorbs the cubic part of the conductor phase
  have hm2 : lambda ^ 2 ∣ -2 * n₂ - 1 := primary_mul primary_neg_two h2'
  have hm2c : IsCoprime (-2 * n₂) c := hc2'.symm.neg_left.mul_left hc2
  have hsym : ringComplex (symbol c (-2 * n₂)) = ringComplex (symbol c (-2)) * ringComplex (symbol c n₂) := by
    rw [symbol_mul_denominator, map_mul]
  have hshift := cubicColumn_shift hP h1 hm2 hc1 hm2c
  have hΦ := rowRootNumber_eq_thetaPhase_mul_gauss_sq s hnz hmax hlam h2 hprim hcop
  rw [hcol, hz, hq, mul_div_assoc, hΦ, thetaPhase, conj_sexticSymbol_four hP hc2', ← hshift, hsym]
  ring


/-- **The quadratic content of a column.** For a row `c` and a primary `q` prime to `2c`:
`(c/q)₂ Γ(c) = r(q, c) · g_c^{(3)}(q)/|c|` — the quadratic character of the column times the Weil index of
the row is the normalized quadratic Gauss sum of the row at numerator `q`. -/
theorem quadSymbol_mul_fixedDualAverage (q : O) (hq : lambda ^ 2 ∣ q - 1) (hq2 : IsCoprime q 2)
    (hqc : IsCoprime q (∏ π ∈ s, π)) :
    quadSymbol (∏ π ∈ s, π) q * fixedDualAverage (∏ π ∈ s, π) =
      quadraticPhase q (∏ π ∈ s, π) *
        (sexticGaussPow 3 (∏ π ∈ s, π) q / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) := by
  obtain ⟨hP, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  obtain ⟨-, hQ⟩ := rowHasseDavenport s hnz hmax hlam h2 hprim hcop
  have hc0 : (∏ π ∈ s, π) ≠ 0 := NeZero.ne _
  have ha0 : (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) ≠ 0 := by
    have : ringComplex (∏ π ∈ s, π) ≠ 0 := fun h => hc0 (ringComplex_injective (by rw [h, map_zero]))
    exact_mod_cast norm_ne_zero_iff.mpr this
  have hrec := quadSymbol_reciprocity hq hP hq2 hc2' hqc
  have hcol3 := sexticSymbol_pow_mul_sexticGaussPow 3 (∏ π ∈ s, π) hqc 1
  rw [mul_one] at hcol3
  -- `χ_c(q)³ = (q/c)₂`
  have hχ3 : sexticSymbol q (∏ π ∈ s, π) ^ 3 = quadSymbol q (∏ π ∈ s, π) := by
    have h3 : ringComplex (symbol q (∏ π ∈ s, π)) ^ 3 = 1 := symbol_cube hP hqc
    have h2q : quadSymbol q (∏ π ∈ s, π) ^ 2 = 1 := quadSymbol_sq hc0 hc2' hqc
    rw [sexticSymbol]
    linear_combination (ringComplex (symbol q (∏ π ∈ s, π)) ^ 3 + 1) *
      quadSymbol q (∏ π ∈ s, π) ^ 3 * h3 + quadSymbol q (∏ π ∈ s, π) * h2q
  rw [hχ3, hQ] at hcol3
  rw [mul_div_assoc', eq_div_iff ha0]
  linear_combination (-quadSymbol (∏ π ∈ s, π) q) * hcol3 +
    sexticGaussPow 3 (∏ π ∈ s, π) q * hrec

/-- **Hasse–Davenport at the columns.** At a column `n = n₁ n₂² k³` the sextic Gauss sum of the row is
the quadratic Gauss sum of the row at numerator `n₁k` times the shifted cubic theta product:
`g_c(n)/|c| · G̃(−2n₁n₂) G̃(n₁) = \overline{r(n, c)} r(n₁k, c) · g_c^{(3)}(n₁k)/|c| · G̃(−2n₁n₂c) G̃(n₁c)`. -/
theorem rowRoot_column_hasseDavenport (n₁ n₂ k : O) (h1 : lambda ^ 2 ∣ n₁ - 1)
    (h2' : lambda ^ 2 ∣ n₂ - 1) (hk : lambda ^ 2 ∣ k - 1) (h12 : IsCoprime n₁ 2)
    (h22 : IsCoprime n₂ 2) (hk2 : IsCoprime k 2) (hc1 : IsCoprime n₁ (∏ π ∈ s, π))
    (hc2 : IsCoprime n₂ (∏ π ∈ s, π)) (hck : IsCoprime k (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) (n₁ * n₂ ^ 2 * k ^ 3) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) *
        (normalizedCubicUnitGauss (n₁ * (-2 * n₂)) * normalizedCubicUnitGauss n₁) =
      starRingEnd ℂ (quadraticPhase (n₁ * n₂ ^ 2 * k ^ 3) (∏ π ∈ s, π)) *
        quadraticPhase (n₁ * k) (∏ π ∈ s, π) *
          (sexticGaussPow 3 (∏ π ∈ s, π) (n₁ * k) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) *
            (normalizedCubicUnitGauss (n₁ * (-2 * n₂) * ∏ π ∈ s, π) *
              normalizedCubicUnitGauss (n₁ * ∏ π ∈ s, π)) := by
  rw [rowRoot_column_shift_actual s hnz hmax hlam h2 hprim hcop n₁ n₂ k h1 h2' hk h12 h22 hk2 hc1 hc2 hck,
    mul_assoc (starRingEnd ℂ _) (quadSymbol _ _),
    quadSymbol_mul_fixedDualAverage s hnz hmax hlam h2 hprim hcop (n₁ * k) (primary_mul h1 hk)
      (h12.mul_left hk2) (hc1.mul_left hck)]
  ring

/-- **Square columns are cubic.** At `n = m²`: `g_c(m²)/|c| · G̃(m) = \overline{r(m², c)} G(c) G̃(mc) G̃(c)`. -/
theorem rowRoot_square_column_shift (m : O) (hm : lambda ^ 2 ∣ m - 1) (hm2 : IsCoprime m 2)
    (hmc : IsCoprime m (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) (m ^ 2) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) *
        normalizedCubicUnitGauss m =
      starRingEnd ℂ (quadraticPhase (m ^ 2) (∏ π ∈ s, π)) * thetaPhase (∏ π ∈ s, π) *
        (normalizedCubicUnitGauss (m * ∏ π ∈ s, π) * normalizedCubicUnitGauss (∏ π ∈ s, π)) := by
  obtain ⟨hP, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  have hcol := rowRoot_square_column m (∏ π ∈ s, π) hm hP hm2 hc2' hmc
  have hΦ := rowRootNumber_eq_thetaPhase_mul_gauss_sq s hnz hmax hlam h2 hprim hcop
  rw [hcol, mul_div_assoc, hΦ, ← squareColumn_shift hP hm hmc]
  ring

/-- **Cube columns are quadratic twists.** At `n = k³`: `g_c(k³)/|c| = \overline{r(k³, c)} (c/k)₂ Φ(c)`. -/
theorem rowRoot_cube_column (k : O) (hk : lambda ^ 2 ∣ k - 1) (hk2 : IsCoprime k 2)
    (hkc : IsCoprime k (∏ π ∈ s, π)) :
    sexticGaussPow 1 (∏ π ∈ s, π) (k ^ 3) / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) =
      starRingEnd ℂ (quadraticPhase (k ^ 3) (∏ π ∈ s, π)) * quadSymbol (∏ π ∈ s, π) k *
        (sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ)) := by
  obtain ⟨hP, hc2'⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  set c := ∏ π ∈ s, π
  have hk3 : lambda ^ 2 ∣ k ^ 3 - 1 := by
    rw [show k ^ 3 = k * k * k by ring]
    exact primary_mul (primary_mul hk hk) hk
  have hcol := rowRoot_column (k ^ 3) c hk3 hP hk2.pow_left hc2' hkc.pow_left
  have hz : ringComplex (symbol c (k ^ 3)) = 1 := by
    rw [show k ^ 3 = k * k * k by ring]
    simp only [symbol_mul_denominator, map_mul]
    have hk3' : ringComplex (symbol c k) ^ 3 = 1 := symbol_cube hk hkc.symm
    linear_combination hk3'
  have hq : quadSymbol c (k ^ 3) = quadSymbol c k := by
    have hqk : quadSymbol c k ^ 2 = 1 := quadSymbol_sq (primary_ne_zero k hk) hk2 hkc.symm
    rw [show k ^ 3 = k * k * k by ring]
    simp only [quadSymbol_mul_denominator]
    linear_combination quadSymbol c k * hqk
  rw [hcol, hz, hq, mul_div_assoc]
  ring

end Row

end GaloisForLFunctions.OrderSixMetaplecticTheory
