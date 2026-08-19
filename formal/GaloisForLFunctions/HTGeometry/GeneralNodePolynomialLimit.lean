/-
# Bounded-degree polynomial limits at arbitrary nodes

The interpolation recovery of a bounded-degree polynomial from its samples works at any injective
family of nodes, not only at the fixed integer nodes.  This is what lets the recovery be run inside
a prescribed region -- for instance a disc on which a limit function does not vanish.

Main results:
* `nodeLimitPoly`, `natDegree_nodeLimitPoly_le`, `eq_nodeLimitPoly_of_natDegree_le` — the
  interpolant at arbitrary nodes.
* `coeff_eq_sum_lagrangeBasis` — the linear coefficient recovery at arbitrary nodes.
* `tendsto_coeff_of_tendsto_samples_at` — coefficientwise convergence from sample convergence.
* `tendsto_eval_of_tendsto_coeff` — values converge when coefficients do.
* `exists_limit_of_tendsto_derivative_samples_at` — **the normalized polynomial factor converges**,
  at arbitrary nodes.
-/
import GaloisForLFunctions.HTGeometry.NormalizedPolynomialFactorLimit

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J : ℕ}

/-- The interpolant of a sample vector at an arbitrary node family. -/
def nodeLimitPoly (v w : Fin (J + 1) → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ v w

theorem natDegree_nodeLimitPoly_le {v : Fin (J + 1) → ℂ} (hv : Function.Injective v)
    (w : Fin (J + 1) → ℂ) : (nodeLimitPoly v w).natDegree ≤ J := by
  have hdeg := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (J + 1))))
    (v := v) w hv.injOn
  rw [Finset.card_univ, Fintype.card_fin] at hdeg
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg ?_)
  exact_mod_cast Nat.succ_le_of_lt hm

theorem eq_nodeLimitPoly_of_natDegree_le {v : Fin (J + 1) → ℂ} (hv : Function.Injective v)
    {P : Polynomial ℂ} (hP : P.natDegree ≤ J) :
    P = nodeLimitPoly v (fun i => P.eval (v i)) := by
  have hdegree : P.degree < ((Finset.univ : Finset (Fin (J + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h1 : P.degree ≤ (J : WithBot ℕ) := Polynomial.natDegree_le_iff_degree_le.mp hP
    have h2 : (J : WithBot ℕ) < ((J + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self J
    exact lt_of_le_of_lt h1 h2
  exact Lagrange.eq_interpolate hv.injOn hdegree

theorem coeff_nodeLimitPoly (v w : Fin (J + 1) → ℂ) (h : ℕ) :
    (nodeLimitPoly v w).coeff h
      = ∑ i, w i * (Lagrange.basis Finset.univ v i).coeff h := by
  rw [nodeLimitPoly, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_C_mul]

/-- **The linear coefficient recovery at arbitrary nodes.** -/
theorem coeff_eq_sum_lagrangeBasis {v : Fin (J + 1) → ℂ} (hv : Function.Injective v)
    {P : Polynomial ℂ} (hP : P.natDegree ≤ J) (h : ℕ) :
    P.coeff h = ∑ i, P.eval (v i) * (Lagrange.basis Finset.univ v i).coeff h := by
  conv_lhs => rw [eq_nodeLimitPoly_of_natDegree_le hv hP]
  rw [coeff_nodeLimitPoly]

/-- **Coefficientwise convergence from convergence of the samples.** -/
theorem tendsto_coeff_of_tendsto_samples_at {v : Fin (J + 1) → ℂ} (hv : Function.Injective v)
    {P : ℕ → Polynomial ℂ} (hP : ∀ n, (P n).natDegree ≤ J) {w : Fin (J + 1) → ℂ}
    (hconv : ∀ i, Tendsto (fun n => (P n).eval (v i)) atTop (nhds (w i))) (h : ℕ) :
    Tendsto (fun n => (P n).coeff h) atTop (nhds ((nodeLimitPoly v w).coeff h)) := by
  rw [coeff_nodeLimitPoly]
  refine Filter.Tendsto.congr
    (fun n => (coeff_eq_sum_lagrangeBasis hv (hP n) h).symm) ?_
  exact tendsto_finsetSum _ fun i _ => (hconv i).mul_const _

/-- Values converge when coefficients do, under a common degree bound. -/
theorem tendsto_eval_of_tendsto_coeff {N : ℕ} {P : ℕ → Polynomial ℂ} {Q : Polynomial ℂ}
    (hP : ∀ n, (P n).natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (hc : ∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h))) (z : ℂ) :
    Tendsto (fun n => (P n).eval z) atTop (nhds (Q.eval z)) := by
  have hrep : ∀ n, (P n).eval z = ∑ i ∈ Finset.range (N + 1), (P n).coeff i * z ^ i :=
    fun n => Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (hP n) (Nat.lt_succ_self N)) z
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hQ (Nat.lt_succ_self N)) z]
  refine Filter.Tendsto.congr (fun n => (hrep n).symm) ?_
  exact tendsto_finsetSum _ fun i _ => (hc i).mul_const _

/-- **The normalized polynomial factor converges, at arbitrary nodes.** -/
theorem exists_limit_of_tendsto_derivative_samples_at {v : Fin (J + 1) → ℂ}
    (hv : Function.Injective v) {P : ℕ → Polynomial ℂ}
    (hP : ∀ n, (P n).natDegree ≤ J + 1) (hP0 : ∀ n, (P n).coeff 0 = 0)
    {w : Fin (J + 1) → ℂ}
    (hconv : ∀ i, Tendsto (fun n => (Polynomial.derivative (P n)).eval (v i)) atTop
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
  have hcoeff := tendsto_coeff_of_tendsto_samples_at hv hderdeg hconv
  refine ⟨normalizedAntiderivative J (nodeLimitPoly v w),
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
          have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [hcast]
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
        have hz0 : (normalizedAntiderivative J (nodeLimitPoly v w)).coeff (k + 1) = 0 := by
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          exact lt_of_le_of_lt (natDegree_normalizedAntiderivative_le J _) (by omega)
        rw [hz0]
        exact Filter.Tendsto.congr (fun n => (hz n).symm) tendsto_const_nhds

end

end GaloisForLFunctions.HTGeometry
