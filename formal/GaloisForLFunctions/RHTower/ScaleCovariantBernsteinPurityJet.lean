import GaloisForLFunctions.RHTower.PrimeArchBernsteinLoschmidtPurity

/-!
# Scale-covariant Bernstein purity jets

For a real moment sequence `m`, dilation by a scalar `x` replaces `m r` by
`x ^ r * m r`.  At fixed Bernstein degree `N`, the squared coefficient norm is therefore a
polynomial in `x`.  This file identifies its coefficients and proves the triangular recovery law:
the coefficient of degree `r ≤ N` contains `m r` only through

`2 * (-1)^r * choose N r * m 0 * m r`.

This is a finite algebraic theorem.  It uses neither a positivity hypothesis nor any statement
about the Riemann zeta function.
-/

open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

open HTGeometry

/-- Insert the moments as diagonal weights on the monomial coefficients of a polynomial. -/
def momentScalePolynomial (m : ℕ → ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  p.sum fun r a => Polynomial.monomial r (a * m r)

@[simp] theorem coeff_momentScalePolynomial (m : ℕ → ℝ) (p : Polynomial ℝ) (r : ℕ) :
    (momentScalePolynomial m p).coeff r = p.coeff r * m r := by
  classical
  rw [momentScalePolynomial, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  by_cases hr : r ∈ p.support
  · rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro b hb hbr
      simp [Polynomial.coeff_monomial, hbr]
    · simp [hr]
  · rw [Finset.sum_eq_zero]
    · have hcoeff : p.coeff r = 0 := by
        simpa only [Polynomial.mem_support_iff, not_ne_iff] using hr
      simp [hcoeff]
    · intro b hb
      have hbr : b ≠ r := by
        intro h
        subst h
        exact hr hb
      simp [Polynomial.coeff_monomial, hbr]

/-- Evaluation of the scale polynomial is the moment functional of the dilated sequence. -/
theorem eval_momentScalePolynomial (m : ℕ → ℝ) (p : Polynomial ℝ) (x : ℝ) :
    (momentScalePolynomial m p).eval x =
      momentFunctional (fun r => x ^ r * m r) p := by
  classical
  rw [momentScalePolynomial, Polynomial.eval_sum, momentFunctional_eq_support_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- The scale polynomial of one Bernstein coefficient. -/
def bernsteinScaleRowPolynomial (m : ℕ → ℝ) (N k : ℕ) : Polynomial ℝ :=
  momentScalePolynomial m (bernsteinPolynomial ℝ N k)

/-- The scale-covariant Bernstein purity polynomial. -/
def bernsteinScalePurityPolynomial (m : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (N + 1), (bernsteinScaleRowPolynomial m N k) ^ 2

theorem eval_bernsteinScaleRowPolynomial (m : ℕ → ℝ) (N k : ℕ) (x : ℝ) :
    (bernsteinScaleRowPolynomial m N k).eval x =
      bernsteinCoefficient (fun r => x ^ r * m r) N k := by
  rw [bernsteinScaleRowPolynomial, eval_momentScalePolynomial]
  rfl

/-- The observed scale curve is exactly the evaluation of the purity polynomial. -/
theorem eval_bernsteinScalePurityPolynomial (m : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (bernsteinScalePurityPolynomial m N).eval x =
      bernsteinCoefficientPurity (fun r => x ^ r * m r) N := by
  rw [bernsteinScalePurityPolynomial, bernsteinCoefficientPurity,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_pow, eval_bernsteinScaleRowPolynomial]

/-- Coefficient kernel of two Bernstein basis vectors at a fixed degree. -/
def bernsteinPurityCoefficientKernel (N k a b : ℕ) : ℝ :=
  (bernsteinPolynomial ℝ N k).coeff a * (bernsteinPolynomial ℝ N k).coeff b

/-- Exact antidiagonal coefficient formula for the scale-purity polynomial. -/
theorem coeff_bernsteinScalePurityPolynomial (m : ℕ → ℝ) (N r : ℕ) :
    (bernsteinScalePurityPolynomial m N).coeff r =
      ∑ k ∈ Finset.range (N + 1),
        ∑ ab ∈ Finset.antidiagonal r,
          bernsteinPurityCoefficientKernel N k ab.1 ab.2 * m ab.1 * m ab.2 := by
  classical
  rw [bernsteinScalePurityPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_two, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  simp only [coeff_momentScalePolynomial, bernsteinScaleRowPolynomial,
    bernsteinPurityCoefficientKernel]
  ring

@[simp] theorem coeff_zero_bernsteinPolynomial (N k : ℕ) :
    (bernsteinPolynomial ℝ N k).coeff 0 = if k = 0 then 1 else 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact bernsteinPolynomial.eval_at_0 ℝ N k

/-- The degree-`r` coefficient of `(1-X)^N`. -/
theorem coeff_bernsteinPolynomial_zero (N r : ℕ) :
    (bernsteinPolynomial ℝ N 0).coeff r = (-1 : ℝ) ^ r * N.choose r := by
  classical
  rw [bernsteinPolynomial]
  simp only [Nat.choose_zero_right, Nat.cast_one, C_1, one_mul, pow_zero, one_mul,
    Nat.sub_zero]
  rw [show (1 - X : Polynomial ℝ) = -(X + C (-1 : ℝ)) by ext n <;> simp [sub_eq_add_neg]]
  rw [neg_pow]
  have hC : (-1 : Polynomial ℝ) ^ N = C ((-1 : ℝ) ^ N) := by simp
  rw [hC, Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_X_add_C_pow]
  by_cases hr : r ≤ N
  · have hparity : (-1 : ℝ) ^ N * ((-1 : ℝ) ^ (N - r) * (N.choose r : ℝ)) =
        (-1 : ℝ) ^ r * (N.choose r : ℝ) := by
      rw [← mul_assoc, ← pow_add]
      have htwo : N + (N - r) = r + 2 * (N - r) := by omega
      rw [htwo, pow_add, pow_mul]
      norm_num
    simpa using hparity
  · have hlt : N < r := Nat.lt_of_not_ge hr
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

/-- Only the zeroth Bernstein row has a nonzero constant coefficient. -/
theorem sum_bernstein_constant_mul_coeff (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
        (bernsteinPolynomial ℝ N k).coeff 0 *
          (bernsteinPolynomial ℝ N k).coeff r =
      (-1 : ℝ) ^ r * N.choose r := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp [coeff_bernsteinPolynomial_zero]
  · intro k hk hk0
    simp [hk0]
  · simp

/-- Erase the `r`th moment while retaining every other coordinate. -/
def eraseMoment (m : ℕ → ℝ) (r : ℕ) : ℕ → ℝ :=
  fun j => if j = r then 0 else m j

/-- The explicit lower-order part of the degree-`r` purity coefficient. -/
def bernsteinScalePurityLower (m : ℕ → ℝ) (N r : ℕ) : ℝ :=
  (bernsteinScalePurityPolynomial (eraseMoment m r) N).coeff r

private theorem antidiagonal_index_le {a b r : ℕ}
    (h : (a, b) ∈ Finset.antidiagonal r) : a ≤ r ∧ b ≤ r := by
  have hab : a + b = r := Finset.mem_antidiagonal.mp h
  omega

/-- The constant purity coefficient is exactly the square of the pointed mass. -/
@[simp] theorem coeff_zero_bernsteinScalePurityPolynomial (m : ℕ → ℝ) (N : ℕ) :
    (bernsteinScalePurityPolynomial m N).coeff 0 = m 0 ^ 2 := by
  rw [coeff_bernsteinScalePurityPolynomial]
  simp [bernsteinPurityCoefficientKernel]
  ring

/-- The degree-`r` purity coefficient depends only on the moment prefix through degree `r`. -/
theorem coeff_bernsteinScalePurityPolynomial_congr_prefix
    {m m' : ℕ → ℝ} (N r : ℕ) (h : ∀ j ≤ r, m j = m' j) :
    (bernsteinScalePurityPolynomial m N).coeff r =
      (bernsteinScalePurityPolynomial m' N).coeff r := by
  classical
  rw [coeff_bernsteinScalePurityPolynomial,
    coeff_bernsteinScalePurityPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro ab hab
  have hle := antidiagonal_index_le hab
  rw [h ab.1 hle.1, h ab.2 hle.2]

/-- Exact triangular coefficient law.  No moment above `r` occurs, and the only dependence on
`m r` is the displayed cross term with the pointed mass `m 0`. -/
theorem coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower
    (m : ℕ → ℝ) (N : ℕ) {r : ℕ} (hr0 : 0 < r) (hr : r ≤ N) :
    (bernsteinScalePurityPolynomial m N).coeff r =
      2 * (-1 : ℝ) ^ r * N.choose r * m 0 * m r +
        bernsteinScalePurityLower m N r := by
  classical
  rw [coeff_bernsteinScalePurityPolynomial,
    bernsteinScalePurityLower, coeff_bernsteinScalePurityPolynomial]
  have hrne : r ≠ 0 := hr0.ne'
  have hsplit :
      (∑ k ∈ Finset.range (N + 1),
          ∑ ab ∈ Finset.antidiagonal r,
            bernsteinPurityCoefficientKernel N k ab.1 ab.2 * m ab.1 * m ab.2) -
        (∑ k ∈ Finset.range (N + 1),
          ∑ ab ∈ Finset.antidiagonal r,
            bernsteinPurityCoefficientKernel N k ab.1 ab.2 *
              eraseMoment m r ab.1 * eraseMoment m r ab.2) =
        2 * m 0 * m r *
          (∑ k ∈ Finset.range (N + 1),
            (bernsteinPolynomial ℝ N k).coeff 0 *
              (bernsteinPolynomial ℝ N k).coeff r) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_sub_distrib]
      calc
        ∑ ab ∈ Finset.antidiagonal r,
            (bernsteinPurityCoefficientKernel N k ab.1 ab.2 * m ab.1 * m ab.2 -
              bernsteinPurityCoefficientKernel N k ab.1 ab.2 *
                eraseMoment m r ab.1 * eraseMoment m r ab.2) =
            (bernsteinPurityCoefficientKernel N k 0 r * m 0 * m r - 0) +
              (bernsteinPurityCoefficientKernel N k r 0 * m r * m 0 - 0) := by
          rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.antidiagonal r)
            (i := (0, r))]
          · rw [Finset.sum_eq_add_sum_diff_singleton
                (s := Finset.antidiagonal r \ {(0, r)}) (i := (r, 0))]
            · rw [Finset.sum_eq_zero]
              · simp [eraseMoment, bernsteinPurityCoefficientKernel]
              · intro ab hab
                have habAnti : ab ∈ Finset.antidiagonal r :=
                  (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hab).1).1
                have hab0 : ab ≠ (0, r) := by
                  simpa using (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hab).1).2
                have habr : ab ≠ (r, 0) := by
                  simpa using (Finset.mem_sdiff.mp hab).2
                have hle := antidiagonal_index_le habAnti
                have ha : ab.1 ≠ r := by
                  intro h
                  have hb : ab.2 = 0 := by
                    have := Finset.mem_antidiagonal.mp habAnti
                    omega
                  exact habr (Prod.ext h hb)
                have hb : ab.2 ≠ r := by
                  intro h
                  have ha0 : ab.1 = 0 := by
                    have := Finset.mem_antidiagonal.mp habAnti
                    omega
                  exact hab0 (Prod.ext ha0 h)
                simp [eraseMoment, ha, hb]
            · simp [hrne]
          · simp
        _ = 2 * m 0 * m r *
            ((bernsteinPolynomial ℝ N k).coeff 0 *
              (bernsteinPolynomial ℝ N k).coeff r) := by
          by_cases hk0 : k = 0 <;>
            simp [bernsteinPurityCoefficientKernel, hk0] <;> ring
  have hkernel := sum_bernstein_constant_mul_coeff N r
  rw [hkernel] at hsplit
  linarith

/-- The lower term only uses moments of index strictly below `r`. -/
theorem bernsteinScalePurityLower_congr
    {m m' : ℕ → ℝ} (N : ℕ) {r : ℕ}
    (h : ∀ j < r, m j = m' j) :
    bernsteinScalePurityLower m N r = bernsteinScalePurityLower m' N r := by
  classical
  rw [bernsteinScalePurityLower, bernsteinScalePurityLower,
    coeff_bernsteinScalePurityPolynomial, coeff_bernsteinScalePurityPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro ab hab
  have hle := antidiagonal_index_le hab
  have ha : eraseMoment m r ab.1 = eraseMoment m' r ab.1 := by
    by_cases har : ab.1 = r
    · simp [eraseMoment, har]
    · simp [eraseMoment, har, h ab.1 (lt_of_le_of_ne hle.1 har)]
  have hb : eraseMoment m r ab.2 = eraseMoment m' r ab.2 := by
    by_cases hbr : ab.2 = r
    · simp [eraseMoment, hbr]
    · simp [eraseMoment, hbr, h ab.2 (lt_of_le_of_ne hle.2 hbr)]
  rw [ha, hb]

/-- Equality of the first `N+1` purity coefficients recovers the pointed moment prefix. -/
theorem bernsteinScalePurityJet_injectiveOn_pointed
    {m m' : ℕ → ℝ} {N : ℕ}
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    (hjet : ∀ r ≤ N,
      (bernsteinScalePurityPolynomial m N).coeff r =
        (bernsteinScalePurityPolynomial m' N).coeff r) :
    ∀ r ≤ N, m r = m' r := by
  intro r hr
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hr0 : r = 0
      · subst r
        have h0 := hjet 0 (Nat.zero_le N)
        rw [coeff_bernsteinScalePurityPolynomial,
          coeff_bernsteinScalePurityPolynomial] at h0
        simp [bernsteinPurityCoefficientKernel] at h0
        nlinarith
      · have hlower := bernsteinScalePurityLower_congr (m := m) (m' := m') N
          (r := r) (fun j hj => ih j hj (hj.le.trans hr))
        have hm0eq : m 0 = m' 0 := ih 0 (Nat.pos_of_ne_zero hr0) (Nat.zero_le N)
        have hleft := coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower m N
          (Nat.pos_of_ne_zero hr0) hr
        have hright := coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower m' N
          (Nat.pos_of_ne_zero hr0) hr
        have hchoose : (N.choose r : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hr).ne'
        rw [hjet r hr, hright, hm0eq, hlower] at hleft
        have hcoef : 2 * (-1 : ℝ) ^ r * (N.choose r : ℝ) * m' 0 ≠ 0 := by
          positivity
        apply mul_left_cancel₀ hcoef
        nlinarith [hleft]

/-- Equality of the complete scale polynomials recovers the pointed prefix. -/
theorem bernsteinScalePurityPolynomial_injectiveOn_pointed
    {m m' : ℕ → ℝ} {N : ℕ}
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    (hpoly : bernsteinScalePurityPolynomial m N =
      bernsteinScalePurityPolynomial m' N) :
    ∀ r ≤ N, m r = m' r := by
  apply bernsteinScalePurityJet_injectiveOn_pointed hm0 hm0'
  intro r hr
  rw [hpoly]

/-- Agreement of scale observations on a nonempty open interval already forces pointed prefix
agreement, because the observations are polynomial evaluations. -/
theorem bernsteinScalePurity_interval_tomography
    {m m' : ℕ → ℝ} {N : ℕ}
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    {a b : ℝ} (hab : a < b)
    (hobs : ∀ x ∈ Set.Ioo a b,
      bernsteinCoefficientPurity (fun r => x ^ r * m r) N =
        bernsteinCoefficientPurity (fun r => x ^ r * m' r) N) :
    ∀ r ≤ N, m r = m' r := by
  apply bernsteinScalePurityPolynomial_injectiveOn_pointed hm0 hm0'
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Ioo_infinite hab)
  intro x hx
  show (bernsteinScalePurityPolynomial m N).eval x =
    (bernsteinScalePurityPolynomial m' N).eval x
  simpa only [eval_bernsteinScalePurityPolynomial] using hobs x hx

end

end RHTower
