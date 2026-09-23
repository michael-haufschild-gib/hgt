import GaloisForLFunctions.RHTower.XiResolventTraceHankelCriterion

/-!
# The resolvent ladder: RH from the Hankel array of the Euler-ray response

`xiResolventTrace X p = sum_q u q * (p (u q))^(2 : ℕ)` with `u q = (w q + X)^(-1)`.  Expanding `p` in the
monomial basis turns the criterion of `XiResolventTraceHankelCriterion` into positive
semidefiniteness of the Hankel array of the **resolvent moments**

`R n X = sum_q (u q)^(n+1)`,

whose order zero is the Euler-ray response `logDeriv xi (1/2 + x) / x` at `X = x^(2 : ℕ)`.  So the open
core becomes a single explicit matrix condition on the derivative array of one prime--Gamma
function.

Two structural facts are recorded with it.  The resolvent coordinates are bounded by `1`, because
the divisor's height gap `2 < g^(2 : ℕ)` keeps every squared spectral point at distance at least `2` in
the `normSq` scale; this makes every moment absolutely summable.  And the second Hankel minor has
the variance form

`R0 R2 - R1^(2 : ℕ) = (1/2) sum_(q,q') u q * u q' * (u q - u q')^(2 : ℕ)`,

whose conjugate-pair terms are the exact negative reals `-4 ‖u q‖^(2 : ℕ) (Im (u q))^(2 : ℕ)`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## §1 Boundedness and summability of the resolvent powers -/

/-- The height gap bounds every resolvent coordinate by one. -/
theorem norm_xiResolventPoint_le_one {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    ‖xiResolventPoint X q‖ ≤ 1 := by
  have hbound := norm_xiResolventPoint_le hX q
  have hgap : (2 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, xiSpectralPoint_re_eq]
    have h := xiZeroCopy_two_lt_im_sq q
    nlinarith [sq_nonneg (xiSpectralPoint q).im, sq_nonneg ((q.1 : ℂ).im)]
  have hpos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by linarith
  have : 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) ≤ 1 := by
    rw [mul_one_div, div_le_one hpos]
    linarith
  linarith

theorem summable_norm_xiResolventPoint_pow {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    Summable (fun q : XiZeroCopy => ‖xiResolventPoint X q ^ (n + 1)‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) ?_
    (summable_norm_xiResolventPoint hX)
  intro q
  rw [norm_pow, pow_succ]
  have h1 : ‖xiResolventPoint X q‖ ^ n ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX q)
  nlinarith [norm_nonneg (xiResolventPoint X q), pow_nonneg
    (norm_nonneg (xiResolventPoint X q)) n]

theorem summable_xiResolventPoint_pow {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    Summable (fun q : XiZeroCopy => xiResolventPoint X q ^ (n + 1)) :=
  summable_norm_iff.mp (summable_norm_xiResolventPoint_pow hX n)

/-! ## §2 The Hankel form of the resolvent moments -/

/-- The Hankel quadratic form of the resolvent moments. -/
def xiResolventHankelForm (N : ℕ) (a : ℕ → ℝ) (X : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
    ((a j : ℂ) * (a k : ℂ)) * xiResolventMoment (j + k) X

/-- **The resolvent trace of a monomial-basis polynomial is the Hankel form of its
coefficients.** -/
theorem xiResolventTrace_rangeSum {X : ℝ} (hX : 0 ≤ X) (N : ℕ) (a : ℕ → ℝ) :
    xiResolventTrace X (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) =
      xiResolventHankelForm N a X := by
  have hterm : ∀ q : XiZeroCopy,
      xiResolventPoint X q *
          evalRealPolynomial
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j)
            (xiResolventPoint X q) ^ 2 =
        ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          ((a j : ℂ) * (a k : ℂ)) * xiResolventPoint X q ^ (j + k + 1) := by
    intro q
    rw [evalRealPolynomial_rangeSum, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, pow_add, pow_one]
    ring
  rw [xiResolventTrace, tsum_congr hterm, xiResolventHankelForm]
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum fun k _ =>
    ((summable_xiResolventPoint_pow hX (j + k)).mul_left _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum (fun k _ =>
    ((summable_xiResolventPoint_pow hX (j + k)).mul_left _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [xiResolventMoment, tsum_mul_left]

/-- **RH from positive semidefiniteness of the Euler-ray moment array.**  The entries
`xiResolventMoment n X` are the moments whose order zero is `logDeriv xi (1/2 + x) / x`. -/
theorem riemannHypothesis_of_forall_xiResolventHankelForm_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ (N : ℕ) (a : ℕ → ℝ), 0 ≤ (xiResolventHankelForm N a X).re) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_xiResolventTrace_re_nonneg hX fun p => ?_
  have hp : p = ∑ j ∈ Finset.range (p.natDegree + 1),
      Polynomial.C (p.coeff j) * Polynomial.X ^ j := by
    conv_lhs => rw [Polynomial.as_sum_range' p (p.natDegree + 1) (Nat.lt_succ_self _)]
    exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial.symm
  rw [hp, xiResolventTrace_rangeSum hX]
  exact h _ _

/-! ## §3 The second minor and its exact negative core -/

/-- One ordered pair of the variance expansion of the resolvent Turán minor. -/
def xiResolventPairTerm (X : ℝ) (z : XiZeroCopy × XiZeroCopy) : ℂ :=
  xiResolventPoint X z.1 * xiResolventPoint X z.2 *
    (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ 2

/-- **The variance expansion of the resolvent Turán minor.** -/
theorem two_mul_xiResolventTuranMinor_eq_tsum_pair {X : ℝ} (hX : 0 ≤ X) :
    2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
        xiResolventMoment 1 X ^ 2) =
      ∑' z : XiZeroCopy × XiZeroCopy, xiResolventPairTerm X z := by
  have h0 := summable_norm_xiResolventPoint_pow hX 0
  have h1 := summable_norm_xiResolventPoint_pow hX 1
  have h2 := summable_norm_xiResolventPoint_pow hX 2
  have hA := tsum_mul_tsum_of_summable_norm h0 h2
  have hB := tsum_mul_tsum_of_summable_norm h1 h1
  have hC := tsum_mul_tsum_of_summable_norm h2 h0
  have hsumA := summable_mul_of_summable_norm h0 h2
  have hsumB := summable_mul_of_summable_norm h1 h1
  have hsumC := summable_mul_of_summable_norm h2 h0
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy, xiResolventPairTerm X z =
      ((xiResolventPoint X z.1 ^ (0 + 1) * xiResolventPoint X z.2 ^ (2 + 1) -
          2 * (xiResolventPoint X z.1 ^ (1 + 1) * xiResolventPoint X z.2 ^ (1 + 1))) +
        xiResolventPoint X z.1 ^ (2 + 1) * xiResolventPoint X z.2 ^ (0 + 1)) := by
    intro z
    rw [xiResolventPairTerm]
    ring
  rw [xiResolventMoment, xiResolventMoment, xiResolventMoment,
    tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
    hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
  ring

/-- The line conjugate of a copy conjugates its resolvent coordinate. -/
theorem xiResolventPoint_lineConj (X : ℝ) (q : XiZeroCopy) :
    xiResolventPoint X (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiResolventPoint X q) := by
  rw [xiResolventPoint, xiResolventPoint, xiSpectralSq_lineConj, map_inv₀, map_add,
    Complex.conj_ofReal]

/-- **The exact negative core of the resolvent Turán minor.**  Pairing a copy with its
critical-line conjugate contributes the closed-form real number `-4 ‖u‖^(2 : ℕ) (Im u)^(2 : ℕ)`. -/
theorem xiResolventPairTerm_lineConj (X : ℝ) (q : XiZeroCopy) :
    xiResolventPairTerm X (q, xiZeroCopyLineConjEquiv q) =
      (((-4 * ‖xiResolventPoint X q‖ ^ 2 *
        (xiResolventPoint X q).im ^ 2) : ℝ) : ℂ) := by
  have hprod : xiResolventPoint X q *
      xiResolventPoint X (xiZeroCopyLineConjEquiv q) =
      ((‖xiResolventPoint X q‖ ^ 2 : ℝ) : ℂ) := by
    rw [xiResolventPoint_lineConj, Complex.mul_conj, Complex.sq_norm]
  have hdiff : (xiResolventPoint X q -
      xiResolventPoint X (xiZeroCopyLineConjEquiv q)) ^ 2 =
      (((-4 * (xiResolventPoint X q).im ^ 2) : ℝ) : ℂ) := by
    rw [xiResolventPoint_lineConj, Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [xiResolventPairTerm, hprod, hdiff, ← Complex.ofReal_mul]
  push_cast
  ring

/-- The negative core is strictly negative exactly at an off-critical copy. -/
theorem xiResolventPairTerm_lineConj_re_neg_of_im_ne_zero {X : ℝ} {q : XiZeroCopy}
    (hX : 0 ≤ X) (h : (xiResolventPoint X q).im ≠ 0) :
    (xiResolventPairTerm X (q, xiZeroCopyLineConjEquiv q)).re < 0 := by
  rw [xiResolventPairTerm_lineConj, Complex.ofReal_re]
  have hsq : 0 < (xiResolventPoint X q).im ^ 2 := by positivity
  have hn : 0 < ‖xiResolventPoint X q‖ ^ 2 := by
    have := xiResolventPoint_ne_zero hX q
    positivity
  nlinarith

end

end RHTower
