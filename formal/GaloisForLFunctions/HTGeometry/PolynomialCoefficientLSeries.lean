import GaloisForLFunctions.HTGeometry.GammaShiftDirichletResidual

/-! Far-right extraction for polynomial-valued Dirichlet coefficients. -/

open scoped BigOperators Topology

namespace GaloisForLFunctions

open Filter Polynomial LSeries

noncomputable section

def polynomialCoeffStream (P : ℕ → ℂ[X]) (k n : ℕ) : ℂ :=
  (P n).coeff k

theorem LSeries_polynomial_eval_eq_sum (P : ℕ → ℂ[X]) (d : ℕ)
    (hdeg : ∀ n, (P n).natDegree ≤ d) (x : ℂ)
    (hsumm : ∀ k ≤ d, LSeriesSummable (polynomialCoeffStream P k) x) :
    LSeries (fun n => (P n).eval x) x =
      ∑ k ∈ Finset.range (d + 1), x ^ k * LSeries (polynomialCoeffStream P k) x := by
  have hterm (n : ℕ) :
      LSeries.term (fun m => (P m).eval x) x n =
        ∑ k ∈ Finset.range (d + 1),
          x ^ k * LSeries.term (polynomialCoeffStream P k) x n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, (P n).eval_eq_sum_range'
        (Nat.lt_succ_of_le (hdeg n))]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [LSeries.term_of_ne_zero hn]
      simp only [polynomialCoeffStream]
      ring
  rw [LSeries]
  simp_rw [hterm]
  have hsum : ∀ k ∈ Finset.range (d + 1),
      Summable (fun n => x ^ k * LSeries.term (polynomialCoeffStream P k) x n) := by
    intro k hk
    exact (hsumm k (by have := Finset.mem_range.mp hk; omega)).mul_left _
  rw [Summable.tsum_finsetSum hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [LSeries, tsum_mul_left]

theorem polynomialMonomial_ratio_tendsto (k d : ℕ) (hkd : k ≤ d) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ k / (x : ℂ) ^ d)
      atTop (𝓝 (if k = d then 1 else 0)) := by
  have h := tendsto_polynomial_eval_div_pow (Polynomial.X ^ k) d (by simpa using hkd)
  simpa [Polynomial.eval_pow, Polynomial.coeff_X_pow, eq_comm] using h

/-- A polynomial-valued coefficient stream with a common convergence point is read at its first
nonzero index, with the top polynomial coefficient surviving the prescribed power normalization. -/
theorem polynomialCoeffLSeries_firstCoeff_tendsto
    (P : ℕ → ℂ[X]) (d a : ℕ) (B : ℝ)
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hzero : ∀ n ≤ a, P n = 0)
    (hsumm : ∀ k ≤ d,
      LSeriesSummable (polynomialCoeffStream P k) (B : ℂ)) :
    Tendsto (fun x : ℝ =>
      ((a : ℂ) + 1) ^ (x : ℂ) * LSeries (fun n => (P n).eval (x : ℂ)) (x : ℂ) /
        (x : ℂ) ^ d)
      atTop (𝓝 ((P (a + 1)).coeff d)) := by
  have hzeroCoeff (k : ℕ) : ∀ n ≤ a, polynomialCoeffStream P k n = 0 := by
    intro n hn
    rw [polynomialCoeffStream, hzero n hn]
    simp
  have habscissa (k : ℕ) (hk : k ≤ d) :
      LSeries.abscissaOfAbsConv (polynomialCoeffStream P k) < ⊤ :=
    (hsumm k hk).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top B)
  have hterm : ∀ k ∈ Finset.range (d + 1),
      Tendsto (fun x : ℝ =>
        ((x : ℂ) ^ k / (x : ℂ) ^ d) *
          (((a : ℂ) + 1) ^ (x : ℂ) *
            LSeries (polynomialCoeffStream P k) (x : ℂ)))
        atTop (𝓝 (if k = d then (P (a + 1)).coeff d else 0)) := by
    intro k hk
    have hkd : k ≤ d := by
      have := Finset.mem_range.mp hk
      omega
    have hratio := polynomialMonomial_ratio_tendsto k d hkd
    have hfirst := LSeries.tendsto_cpow_mul_atTop
      (f := polynomialCoeffStream P k) (n := a) (hzeroCoeff k) (habscissa k hkd)
    by_cases hkeq : k = d
    · subst k
      simpa [polynomialCoeffStream] using hratio.mul hfirst
    · simpa [hkeq] using hratio.mul hfirst
  have hsum := tendsto_finsetSum (s := Finset.range (d + 1)) hterm
  have hlimit : (∑ k ∈ Finset.range (d + 1),
      if k = d then (P (a + 1)).coeff d else 0) = (P (a + 1)).coeff d := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro k hk hkd
      simp [hkd]
    · simp
  rw [hlimit] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop B, eventually_gt_atTop (0 : ℝ)] with x hxB hx0
  have hsummx : ∀ k ≤ d,
      LSeriesSummable (polynomialCoeffStream P k) (x : ℂ) := by
    intro k hk
    exact (hsumm k hk).of_re_le_re (by simpa using hxB)
  rw [LSeries_polynomial_eval_eq_sum P d hdeg (x : ℂ) hsummx]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hxne : (x : ℂ) ^ d ≠ 0 := pow_ne_zero d (Complex.ofReal_ne_zero.mpr hx0.ne')
  field_simp

end
end GaloisForLFunctions
