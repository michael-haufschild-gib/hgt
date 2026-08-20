/-
# Restricting a multivariable polynomial to a line through the origin

Sending each variable to its coordinate times a single new variable turns a polynomial of total
degree at most `d` into a one-variable polynomial of degree at most `d` whose value at `t` is the
original value at `t·v`.  This is the reduction that carries the one-variable determinant-completion
law along every line of a parameter space, and it is what makes the multivariable jet convergent
coefficientwise.

Main results:
* `polynomialLineRestrictionLineRestrict`, `eval_lineRestrict` — the restriction and its evaluation law.
* `lineRestrict_eq_sum` — its monomial expansion.
* `natDegree_lineRestrict_le` — **the degree does not grow**.
* `tendsto_eval_of_line_coeff` — pointwise jet convergence from coefficient convergence on lines.
-/
import GaloisForLFunctions.HTGeometry.GeneralNodePolynomialLimit

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- The restriction of a multivariable polynomial to the line through `v`. -/
def polynomialLineRestrictionLineRestrict (v : Fin m → ℂ) : MvPolynomial (Fin m) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.C : ℂ →+* Polynomial ℂ)
    (fun i => Polynomial.C (v i) * Polynomial.X)

theorem eval_lineRestrict (v : Fin m → ℂ) (P : MvPolynomial (Fin m) ℂ) (t : ℂ) :
    Polynomial.eval t (polynomialLineRestrictionLineRestrict v P) = MvPolynomial.eval (fun i => t * v i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [polynomialLineRestrictionLineRestrict]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [polynomialLineRestrictionLineRestrict, map_mul, MvPolynomial.eval₂Hom_X', Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, MvPolynomial.eval_X]
      rw [show (MvPolynomial.eval₂Hom (Polynomial.C : ℂ →+* Polynomial ℂ)
        (fun j => Polynomial.C (v j) * Polynomial.X)) p = polynomialLineRestrictionLineRestrict v p from rfl, hp]
      ring

theorem lineRestrict_eq_sum (v : Fin m → ℂ) (P : MvPolynomial (Fin m) ℂ) :
    polynomialLineRestrictionLineRestrict v P = ∑ s ∈ P.support,
      Polynomial.C (MvPolynomial.coeff s P)
        * ∏ i, (Polynomial.C (v i) * Polynomial.X) ^ (s i) := by
  classical
  show MvPolynomial.eval₂ (Polynomial.C : ℂ →+* Polynomial ℂ)
      (fun i => Polynomial.C (v i) * Polynomial.X) P = _
  rw [MvPolynomial.eval₂_eq']

/-- **The line restriction does not raise the degree.** -/
theorem natDegree_lineRestrict_le (v : Fin m → ℂ) {P : MvPolynomial (Fin m) ℂ} {d : ℕ}
    (hP : P.totalDegree ≤ d) : (polynomialLineRestrictionLineRestrict v P).natDegree ≤ d := by
  classical
  rw [lineRestrict_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hterm : ∀ i : Fin m, (((Polynomial.C (v i) * Polynomial.X) ^ (s i)).natDegree) ≤ s i := by
    intro i
    refine le_trans Polynomial.natDegree_pow_le ?_
    have hone : (Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      simp
    calc s i * (Polynomial.C (v i) * Polynomial.X).natDegree ≤ s i * 1 :=
          Nat.mul_le_mul_left _ hone
      _ = s i := by ring
  refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
  have hsum : ∑ i, s i = s.sum fun _ e => e := by
    rw [Finsupp.sum_fintype]
    intro i
    rfl
  rw [hsum]
  exact le_trans (MvPolynomial.le_totalDegree hs) hP

/-- **Pointwise jet convergence from coefficient convergence on lines.** -/
theorem tendsto_eval_of_line_coeff {d : ℕ} {P : ℕ → MvPolynomial (Fin m) ℂ}
    (hdeg : ∀ n, (P n).totalDegree ≤ d) (v : Fin m → ℂ) {Q : Polynomial ℂ}
    (hQ : Q.natDegree ≤ d)
    (hc : ∀ h : ℕ, Tendsto (fun n => (polynomialLineRestrictionLineRestrict v (P n)).coeff h) atTop
      (nhds (Q.coeff h))) :
    Tendsto (fun n => MvPolynomial.eval v (P n)) atTop (nhds (Polynomial.eval 1 Q)) := by
  have hbase := tendsto_eval_of_tendsto_coeff
    (fun n => natDegree_lineRestrict_le v (hdeg n)) hQ hc 1
  refine hbase.congr fun n => ?_
  rw [eval_lineRestrict]
  simp

end

end GaloisForLFunctions.HTGeometry
