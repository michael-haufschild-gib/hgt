/-
# The normalized polynomial factor of a convergent determinant family converges

A determinant factor `exp P` does not determine `P` pointwise -- the exponential is not injective --
but its *logarithmic derivative* does: `P' = (exp P)'/(exp P)`.  Normalizing by `P(0) = 0` then
pins `P` itself, because a polynomial is recovered from its derivative and its constant term.  So
convergence of the logarithmic derivatives at finitely many nodes forces coefficientwise
convergence of the polynomial factors, and the limit is again a polynomial of the same degree
bound vanishing at the origin.

Main results:
* `normalizedAntiderivative` — the antiderivative with vanishing constant term.
* `coeff_normalizedAntiderivative_zero`, `coeff_normalizedAntiderivative_succ`,
  `natDegree_normalizedAntiderivative_le` — its coefficients and degree.
* `exists_limit_of_tendsto_derivative_samples` — **the normalized polynomial factor converges**.
-/
import GaloisForLFunctions.HTGeometry.BoundedDegreePolynomialLimit

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The antiderivative of a polynomial, normalized to vanish at the origin. -/
def normalizedAntiderivative (J : ℕ) (R : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (J + 1), Polynomial.C (R.coeff k / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1)

theorem coeff_normalizedAntiderivative (J : ℕ) (R : Polynomial ℂ) (m : ℕ) :
    (normalizedAntiderivative J R).coeff m
      = ∑ k ∈ Finset.range (J + 1),
          (if m = k + 1 then R.coeff k / ((k : ℂ) + 1) else 0) := by
  rw [normalizedAntiderivative, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : m = k + 1 <;> simp [h]

theorem coeff_normalizedAntiderivative_zero (J : ℕ) (R : Polynomial ℂ) :
    (normalizedAntiderivative J R).coeff 0 = 0 := by
  rw [coeff_normalizedAntiderivative]
  exact Finset.sum_eq_zero fun k _ => by simp

theorem coeff_normalizedAntiderivative_succ (J : ℕ) (R : Polynomial ℂ) {k : ℕ} (hk : k ≤ J) :
    (normalizedAntiderivative J R).coeff (k + 1) = R.coeff k / ((k : ℂ) + 1) := by
  classical
  rw [coeff_normalizedAntiderivative]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (by omega)]
  · intro hc
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hc

theorem natDegree_normalizedAntiderivative_le (J : ℕ) (R : Polynomial ℂ) :
    (normalizedAntiderivative J R).natDegree ≤ J + 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  rw [coeff_normalizedAntiderivative]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkJ : k < J + 1 := Finset.mem_range.mp hk
  rw [if_neg (by omega)]

/-- **The normalized polynomial factor converges.**  A sequence of polynomials of degree at most
`J+1` with vanishing constant term, whose derivatives converge at the `J+1` fixed nodes, converges
coefficientwise and pointwise to a polynomial of the same degree bound with vanishing constant
term. -/
theorem exists_limit_of_tendsto_derivative_samples {J : ℕ} {P : ℕ → Polynomial ℂ}
    (hP : ∀ n, (P n).natDegree ≤ J + 1) (hP0 : ∀ n, (P n).coeff 0 = 0)
    {w : Fin (J + 1) → ℂ}
    (hconv : ∀ i, Tendsto
      (fun n => (Polynomial.derivative (P n)).eval (gaussianLagrangeNodes J i)) atTop
      (nhds (w i))) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      ∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h)) := by
  classical
  have hderdeg : ∀ n, (Polynomial.derivative (P n)).natDegree ≤ J := by
    intro n
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [Polynomial.coeff_derivative]
    have : (P n).coeff (m + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP n) (by omega))
    rw [this, zero_mul]
  have hcoeff := tendsto_coeff_of_tendsto_samples hderdeg hconv
  refine ⟨normalizedAntiderivative J (lagrangeLimitPoly J w),
    natDegree_normalizedAntiderivative_le J _, coeff_normalizedAntiderivative_zero J _, ?_⟩
  intro h
  match h with
  | 0 =>
      rw [coeff_normalizedAntiderivative_zero]
      exact Filter.Tendsto.congr (fun n => (hP0 n).symm) tendsto_const_nhds
  | (k + 1) =>
      by_cases hk : k ≤ J
      · rw [coeff_normalizedAntiderivative_succ J _ hk]
        have hne : ((k : ℂ) + 1) ≠ 0 := by
          have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [this]
          exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        have hrep : ∀ n, (P n).coeff (k + 1)
            = (Polynomial.derivative (P n)).coeff k / ((k : ℂ) + 1) := by
          intro n
          rw [Polynomial.coeff_derivative]
          field_simp
        refine Filter.Tendsto.congr (fun n => (hrep n).symm) ?_
        exact (hcoeff k).div_const _
      · have hz : ∀ n, (P n).coeff (k + 1) = 0 :=
          fun n => Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (hP n) (by omega))
        have hz0 : (normalizedAntiderivative J (lagrangeLimitPoly J w)).coeff (k + 1) = 0 := by
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          exact lt_of_le_of_lt (natDegree_normalizedAntiderivative_le J _) (by omega)
        rw [hz0]
        exact Filter.Tendsto.congr (fun n => (hz n).symm) tendsto_const_nhds

end

end GaloisForLFunctions.HTGeometry
