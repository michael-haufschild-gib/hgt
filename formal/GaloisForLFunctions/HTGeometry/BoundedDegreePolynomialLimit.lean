/-
# Bounded-degree polynomials are closed under pointwise limits

A polynomial of degree at most `J` is a *linear* function of its values at `J+1` fixed nodes, so
convergence of those values forces convergence of every coefficient and of every value.  The limit
is again a polynomial of degree at most `J`: the finite-dimensional space of bounded-degree
polynomials is closed.

This is the step that pins the fibre of a determinant completion: the polynomial factors of a
convergent family of finite-rank determinants converge to a polynomial factor of the same degree
bound.

Main results:
* `lagrangeLimitPoly` — the interpolant of a limiting sample vector.
* `eq_lagrangeLimitPoly_of_natDegree_le` — a bounded-degree polynomial is its own interpolant.
* `tendsto_eval_of_tendsto_samples` — **values converge to the values of the limit polynomial**.
* `tendsto_coeff_of_tendsto_samples` — **and so does every coefficient**.
-/
import GaloisForLFunctions.HTGeometry.GaussianTorsionLanguageTailLock

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J : ℕ}

/-- The interpolant of a sample vector at the fixed nodes. -/
def lagrangeLimitPoly (J : ℕ) (w : Fin (J + 1) → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (gaussianLagrangeNodes J) w

theorem natDegree_lagrangeLimitPoly_le (J : ℕ) (w : Fin (J + 1) → ℂ) :
    (lagrangeLimitPoly J w).natDegree ≤ J := by
  have hdeg := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (J + 1))))
    (v := gaussianLagrangeNodes J) w (gaussianLagrangeNodes_injective J).injOn
  rw [Finset.card_univ, Fintype.card_fin] at hdeg
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg ?_)
  exact_mod_cast Nat.succ_le_of_lt hm

theorem eval_lagrangeLimitPoly (J : ℕ) (w : Fin (J + 1) → ℂ) (x : ℂ) :
    (lagrangeLimitPoly J w).eval x
      = ∑ i : Fin (J + 1),
          w i * (Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).eval x := by
  rw [lagrangeLimitPoly, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- A polynomial of degree at most `J` is its own interpolant at the fixed nodes. -/
theorem eq_lagrangeLimitPoly_of_natDegree_le {P : Polynomial ℂ} (hP : P.natDegree ≤ J) :
    P = lagrangeLimitPoly J (fun i => P.eval (gaussianLagrangeNodes J i)) := by
  have hdegree : P.degree < ((Finset.univ : Finset (Fin (J + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h1 : P.degree ≤ (J : WithBot ℕ) := Polynomial.natDegree_le_iff_degree_le.mp hP
    have h2 : (J : WithBot ℕ) < ((J + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast Nat.lt_succ_self J
    exact lt_of_le_of_lt h1 h2
  exact Lagrange.eq_interpolate (gaussianLagrangeNodes_injective J).injOn hdegree

/-- **Values converge to the values of the limit polynomial.** -/
theorem tendsto_eval_of_tendsto_samples {P : ℕ → Polynomial ℂ} (hP : ∀ n, (P n).natDegree ≤ J)
    {w : Fin (J + 1) → ℂ}
    (hconv : ∀ i, Tendsto (fun n => (P n).eval (gaussianLagrangeNodes J i)) atTop (nhds (w i)))
    (x : ℂ) :
    Tendsto (fun n => (P n).eval x) atTop (nhds ((lagrangeLimitPoly J w).eval x)) := by
  have hrep : ∀ n, (P n).eval x
      = ∑ i : Fin (J + 1), (P n).eval (gaussianLagrangeNodes J i)
          * (Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).eval x := by
    intro n
    conv_lhs => rw [eq_lagrangeLimitPoly_of_natDegree_le (hP n)]
    rw [eval_lagrangeLimitPoly]
  rw [eval_lagrangeLimitPoly]
  refine Filter.Tendsto.congr (fun n => (hrep n).symm) ?_
  exact tendsto_finsetSum _ fun i _ => (hconv i).mul_const _

/-- **Every coefficient converges to the corresponding coefficient of the limit polynomial.** -/
theorem tendsto_coeff_of_tendsto_samples {P : ℕ → Polynomial ℂ} (hP : ∀ n, (P n).natDegree ≤ J)
    {w : Fin (J + 1) → ℂ}
    (hconv : ∀ i, Tendsto (fun n => (P n).eval (gaussianLagrangeNodes J i)) atTop (nhds (w i)))
    (h : ℕ) :
    Tendsto (fun n => (P n).coeff h) atTop (nhds ((lagrangeLimitPoly J w).coeff h)) := by
  by_cases hh : h ≤ J
  · have hrep : ∀ n, (P n).coeff h
        = ∑ i : Fin (J + 1), (P n).eval (gaussianLagrangeNodes J i)
            * (Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).coeff h :=
      fun n => coeff_eq_sum_gaussianLagrange J (P n) (hP n) h
    have hlim : (lagrangeLimitPoly J w).coeff h
        = ∑ i : Fin (J + 1), w i
            * (Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).coeff h := by
      have := coeff_eq_sum_gaussianLagrange J (lagrangeLimitPoly J w)
        (natDegree_lagrangeLimitPoly_le J w) h
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hval : (lagrangeLimitPoly J w).eval (gaussianLagrangeNodes J i) = w i := by
        rw [lagrangeLimitPoly]
        exact Lagrange.eval_interpolate_at_node w (gaussianLagrangeNodes_injective J).injOn
          (Finset.mem_univ i)
      exact hval
    rw [hlim]
    refine Filter.Tendsto.congr (fun n => (hrep n).symm) ?_
    exact tendsto_finsetSum _ fun i _ => (hconv i).mul_const _
  · have hz : ∀ n, (P n).coeff h = 0 :=
      fun n => Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP n) (by omega))
    have hz0 : (lagrangeLimitPoly J w).coeff h = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_lagrangeLimitPoly_le J w) (by omega))
    rw [hz0]
    exact Filter.Tendsto.congr (fun n => (hz n).symm) tendsto_const_nhds

end

end GaloisForLFunctions.HTGeometry
