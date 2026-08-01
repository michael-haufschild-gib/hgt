import GaloisForLFunctions.HTGeometry.PolygammaFactorialComparison

/-!
# Decay order of a rational function with a rising-factorial denominator

Every remainder produced by one expansion step of a polygamma jet is a rational function whose
denominator is a power of the argument times a rising factorial.  Its decay order is the degree
defect: a numerator of degree `d` over `x^a·x(x+1)⋯(x+b−1)` decays like `‖x‖^{d−a−b}`, because a
polynomial is bounded by its degree power and a rising factorial dominates the corresponding power
of the modulus.

This is the workhorse of the induction on expansion depth: it converts an algebraic degree count into
an analytic decay order, with no further estimates.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- A polynomial is bounded by its degree power outside the unit disc. -/
theorem exists_norm_polynomial_le (P : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 1 ≤ ‖x‖ → ‖P.eval x‖ ≤ C * ‖x‖ ^ P.natDegree := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖, by positivity, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i‖
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i * x ^ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖x‖ ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖x‖ ^ P.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx ?_) (norm_nonneg _)
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * ‖x‖ ^ P.natDegree := by
        rw [← Finset.sum_mul]

/-- **The order bound.**  A numerator of degree `d` over `x^a` times a rising factorial of length `b`
decays at order `a + b − d`. -/
theorem exists_norm_div_risingProd_le (P : Polynomial ℂ) (a b p : ℕ)
    (hdeg : P.natDegree + p ≤ a + b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 < x.re → 1 ≤ ‖x‖ →
      ‖P.eval x / (x ^ a * risingProd x b)‖ ≤ C * ‖x‖⁻¹ ^ p := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_polynomial_le P
  refine ⟨C, hC, fun x hx hx1 => ?_⟩
  have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
  have hden : ‖x‖ ^ (a + b) ≤ ‖x ^ a * risingProd x b‖ := by
    rw [norm_mul, norm_pow, pow_add]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_norm_risingProd hx b) (by positivity)
  have hdenpos : (0 : ℝ) < ‖x ^ a * risingProd x b‖ :=
    lt_of_lt_of_le (by positivity) hden
  rw [norm_div, div_le_iff₀ hdenpos]
  have hnum : ‖P.eval x‖ ≤ C * ‖x‖ ^ P.natDegree := hbound x hx1
  have hstep : C * ‖x‖ ^ P.natDegree ≤ C * ‖x‖⁻¹ ^ p * ‖x‖ ^ (a + b) := by
    rw [inv_pow]
    rw [mul_assoc, mul_comm ((‖x‖ ^ p)⁻¹) (‖x‖ ^ (a + b)), ← mul_assoc]
    have hpow : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (a + b) * (‖x‖ ^ p)⁻¹ := by
      rw [← pow_sub₀ _ (ne_of_gt hxpos) (by omega : p ≤ a + b)]
      exact pow_le_pow_right₀ hx1 (by omega)
    calc C * ‖x‖ ^ P.natDegree ≤ C * (‖x‖ ^ (a + b) * (‖x‖ ^ p)⁻¹) :=
          mul_le_mul_of_nonneg_left hpow hC
      _ = C * ‖x‖ ^ (a + b) * (‖x‖ ^ p)⁻¹ := by ring
  refine le_trans hnum (le_trans hstep ?_)
  exact mul_le_mul_of_nonneg_left hden (by positivity)

end GaloisForLFunctions
