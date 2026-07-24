import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect

/-!
# RH as positive semidefiniteness of one explicit Hankel matrix

The polynomial-square Gaussian criterion and the Turán minor are the same object read at
different orders.  Expanding a real polynomial in the monomial basis turns

`T(P,t) = sum_q (P (w q))^2 exp (-t * w q)`,   `w q = xiSpectralPoint q ^ 2`,

into the quadratic form of the Hankel matrix built from the Gaussian-damped moments
`M n t = sum_q (w q)^n exp (-t * w q)`:

`T(P,t) = sum_(j,k) P_j P_k * M (j+k) t`.

Hence RH is exactly positive semidefiniteness of `(M (j+k) t)_(j,k)` — an explicit real symmetric
matrix whose entries are, through the Weil explicit formula with the Hermite test functions
`u^(2n) exp (-t u^2)`, absolutely convergent Gaussian-damped von Mangoldt sums plus archimedean
terms.  The leading minors give a ladder of source inequalities, each strictly weaker than RH:
order one is the plain heat trace, order two is the Turán minor of
`XiGaussianHeatTuranDefect`, and the conjunction over all orders is RH.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Hankel quadratic form of the Gaussian-damped moments. -/
def xiHeatHankelForm (N : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
    a j * a k * xiGaussianHeatMomentReal (j + k) t

/-- Evaluation of a monomial-basis real polynomial at a complex point. -/
theorem evalRealPolynomial_rangeSum (N : ℕ) (a : ℕ → ℝ) (w : ℂ) :
    evalRealPolynomial
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) w =
      ∑ j ∈ Finset.range N, (a j : ℂ) * w ^ j := by
  simp [evalRealPolynomial, Polynomial.map_sum, Polynomial.eval_finsetSum]

/-- **The trace of a monomial-basis polynomial is the Hankel form of its coefficients.** -/
theorem xiPolynomialGaussianHeatTrace_rangeSum {t : ℝ} (ht : 0 < t) (N : ℕ) (a : ℕ → ℝ) :
    xiPolynomialGaussianHeatTrace
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((a j : ℂ) * (a k : ℂ)) * xiGaussianHeatMoment (j + k) t := by
  have hterm : ∀ q : XiZeroCopy,
      xiPolynomialGaussianHeatTerm
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q =
        ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          ((a j : ℂ) * (a k : ℂ)) *
            ((xiSpectralPoint q ^ 2) ^ (j + k) * xiGaussianHeatTerm t q) := by
    intro q
    rw [xiPolynomialGaussianHeatTerm, evalRealPolynomial_rangeSum, pow_two,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
    ring
  rw [xiPolynomialGaussianHeatTrace, tsum_congr hterm]
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum fun k _ =>
    ((summable_xiGaussianHeatMonomialTerm ht (j + k)).mul_left _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum (fun k _ =>
    ((summable_xiGaussianHeatMonomialTerm ht (j + k)).mul_left _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [xiGaussianHeatMoment, tsum_mul_left]

/-- Real form of the previous identity. -/
theorem xiPolynomialGaussianHeatTraceReal_rangeSum {t : ℝ} (ht : 0 < t) (N : ℕ) (a : ℕ → ℝ) :
    xiPolynomialGaussianHeatTraceReal
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t =
      xiHeatHankelForm N a t := by
  rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace_rangeSum ht,
    Complex.re_sum, xiHeatHankelForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [xiGaussianHeatMomentReal, ← Complex.ofReal_mul]
  simp [Complex.mul_re]

/-- **RH is positive semidefiniteness of the Gaussian-damped Hankel matrix.**  Every entry
`xiGaussianHeatMomentReal n t` is an unconditional real number, and the whole family is a single
explicit matrix of prime-plus-archimedean data. -/
theorem riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (a : ℕ → ℝ) (t : ℝ), 0 < t → 0 ≤ xiHeatHankelForm N a t := by
  rw [riemannHypothesis_iff_forall_xiPolynomialGaussianHeatTraceReal_nonneg]
  constructor
  · intro h N a t ht
    rw [← xiPolynomialGaussianHeatTraceReal_rangeSum ht N a]
    exact h _ t ht
  · intro h P t ht
    have hP : P = ∑ j ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff j) * Polynomial.X ^ j := by
      conv_lhs => rw [Polynomial.as_sum_range' P (P.natDegree + 1) (Nat.lt_succ_self _)]
      exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial.symm
    rw [hP, xiPolynomialGaussianHeatTraceReal_rangeSum ht]
    exact h _ _ t ht

/-! ## The first two rungs -/

/-- Order one of the ladder is the plain Gaussian heat trace. -/
theorem xiHeatHankelForm_one (a : ℕ → ℝ) (t : ℝ) :
    xiHeatHankelForm 1 a t = a 0 * a 0 * xiGaussianHeatMomentReal 0 t := by
  simp [xiHeatHankelForm]

/-- Order two of the ladder, expanded. -/
theorem xiHeatHankelForm_two (a : ℕ → ℝ) (t : ℝ) :
    xiHeatHankelForm 2 a t =
      a 0 * a 0 * xiGaussianHeatMomentReal 0 t +
        2 * (a 0 * a 1) * xiGaussianHeatMomentReal 1 t +
        a 1 * a 1 * xiGaussianHeatMomentReal 2 t := by
  simp [xiHeatHankelForm, Finset.sum_range_succ]
  ring

/-- **The Turán minor is exactly the order-two rung.**  Nonnegativity of the Hankel form up to
order two forces the second Hankel determinant to be nonnegative, with no positivity assumption on
the trace itself. -/
theorem xiHeatTuranDefect_nonneg_of_forall_xiHeatHankelForm
    (h : ∀ (N : ℕ) (a : ℕ → ℝ) (t : ℝ), 0 < t → 0 ≤ xiHeatHankelForm N a t)
    {t : ℝ} (ht : 0 < t) : 0 ≤ xiHeatTuranDefect t := by
  classical
  set M0 : ℝ := xiGaussianHeatMomentReal 0 t with hM0
  set M1 : ℝ := xiGaussianHeatMomentReal 1 t with hM1
  set M2 : ℝ := xiGaussianHeatMomentReal 2 t with hM2
  have hquad : ∀ u v : ℝ,
      0 ≤ u * u * M0 + 2 * (u * v) * M1 + v * v * M2 := by
    intro u v
    have := h 2 (fun n => if n = 0 then u else v) t ht
    rwa [xiHeatHankelForm_two] at this
  have hM0nonneg : 0 ≤ M0 := by simpa using hquad 1 0
  rcases eq_or_lt_of_le hM0nonneg with hzero | hpos
  · -- a vanishing trace forces the first moment to vanish too
    have hM1zero : M1 = 0 := by
      by_contra hne
      have hbad := hquad (-(M2 + 1) / (2 * M1)) 1
      rw [← hzero] at hbad
      have hcancel : 2 * (-(M2 + 1) / (2 * M1) * 1) * M1 = -(M2 + 1) := by
        field_simp
      rw [hcancel] at hbad
      simp at hbad
      linarith
    rw [xiHeatTuranDefect, ← hM0, ← hM1, ← hM2, ← hzero, hM1zero]
    norm_num
  · have hkey := hquad (-M1) M0
    have hexpand : (-M1) * (-M1) * M0 + 2 * ((-M1) * M0) * M1 + M0 * M0 * M2 =
        M0 * (M0 * M2 - M1 ^ 2) := by ring
    rw [hexpand] at hkey
    have := nonneg_of_mul_nonneg_right hkey hpos
    rw [xiHeatTuranDefect, ← hM0, ← hM1, ← hM2]
    linarith [this]

end

end RHTower
