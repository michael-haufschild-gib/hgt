import GaloisForLFunctions.HTGeometry.JetPolynomialDescent
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Multivariate polynomials as differential relations

An algebraic differential relation is the evaluation of a multivariate polynomial on the jet
coordinates.  Its Fréchet derivative is the sum of the polynomial's partial derivatives against the
coordinate projections, proved by the monomial induction, so the analytic data of the relation is
computed by `pderiv`.

This is the form the descent needs: `pderiv` degrades the polynomial, whereas a monomial family
carries redundant data.
-/

open Filter Topology MvPolynomial

namespace GaloisForLFunctions

variable {M : ℕ}

/-- The Fréchet derivative of the evaluation of a multivariate polynomial: the sum of its partial
derivatives against the coordinate projections. -/
noncomputable def mvJetDeriv (p : MvPolynomial (Fin M) ℂ) (y : Fin M → ℂ) :
    (Fin M → ℂ) →L[ℂ] ℂ :=
  ∑ k : Fin M, (MvPolynomial.eval y (MvPolynomial.pderiv k p)) •
    (ContinuousLinearMap.proj k : (Fin M → ℂ) →L[ℂ] ℂ)

theorem mvJetDeriv_add (p q : MvPolynomial (Fin M) ℂ) (y : Fin M → ℂ) :
    mvJetDeriv (p + q) y = mvJetDeriv p y + mvJetDeriv q y := by
  ext v
  simp only [mvJetDeriv, map_add, FunLike.coe_sum, Finset.sum_apply, smul_apply, add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The partial derivative of a variable is the corresponding Kronecker delta. -/
theorem eval_pderiv_X (i x : Fin M) (y : Fin M → ℂ) :
    (MvPolynomial.eval y) ((pderiv x) (X i : MvPolynomial (Fin M) ℂ))
      = if i = x then 1 else 0 := by
  classical
  rw [pderiv_X]
  by_cases h : i = x
  · subst h
    simp
  · have hne : x ≠ i := fun hc => h hc.symm
    simp [h]

theorem mvJetDeriv_mul_X (p : MvPolynomial (Fin M) ℂ) (i : Fin M) (y : Fin M → ℂ) :
    mvJetDeriv (p * X i) y
      = (y i) • mvJetDeriv p y + (MvPolynomial.eval y p) •
        (ContinuousLinearMap.proj i : (Fin M → ℂ) →L[ℂ] ℂ) := by
  classical
  ext v
  simp only [mvJetDeriv, pderiv_mul, map_add, map_mul, eval_X,
    add_apply, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hstep : ∀ x : Fin M,
      ((MvPolynomial.eval y) ((pderiv x) p) * y i
          + (MvPolynomial.eval y) p * (MvPolynomial.eval y) ((pderiv x) (X i))) * v x
        = y i * ((MvPolynomial.eval y) ((pderiv x) p) * v x)
          + (MvPolynomial.eval y) p * ((if i = x then (1 : ℂ) else 0) * v x) := by
    intro x
    rw [eval_pderiv_X]
    ring
  rw [Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **A polynomial evaluation is Fréchet differentiable, with the partial derivatives as its
derivative.** -/
theorem hasFDerivAt_mvEval (p : MvPolynomial (Fin M) ℂ) (y : Fin M → ℂ) :
    HasFDerivAt (fun z : Fin M → ℂ => MvPolynomial.eval z p) (mvJetDeriv p y) y := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h0 : mvJetDeriv (C a : MvPolynomial (Fin M) ℂ) y = 0 := by
        ext v
        simp [mvJetDeriv]
      rw [h0]
      simpa using (hasFDerivAt_const a y)
  | add p q hp hq =>
      have hfun : (fun z : Fin M → ℂ => MvPolynomial.eval z (p + q))
          = fun z : Fin M → ℂ => MvPolynomial.eval z p + MvPolynomial.eval z q := by
        funext z
        simp
      rw [hfun, mvJetDeriv_add]
      exact hp.add hq
  | mul_X p i hp =>
      have hproj : HasFDerivAt (fun z : Fin M → ℂ => z i)
          (ContinuousLinearMap.proj i : (Fin M → ℂ) →L[ℂ] ℂ) y :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin M => ℂ) i).hasFDerivAt
      have hmul : HasFDerivAt (fun z : Fin M → ℂ => MvPolynomial.eval z p * z i)
          ((MvPolynomial.eval y p) •
              (ContinuousLinearMap.proj i : (Fin M → ℂ) →L[ℂ] ℂ) + (y i) • mvJetDeriv p y) y :=
        hp.mul hproj
      have hfun : (fun z : Fin M → ℂ => MvPolynomial.eval z (p * X i))
          = fun z : Fin M → ℂ => MvPolynomial.eval z p * z i := by
        funext z
        simp
      rw [hfun, mvJetDeriv_mul_X]
      exact hmul.congr_fderiv (by rw [add_comm])

theorem continuous_mvEval (p : MvPolynomial (Fin M) ℂ) :
    Continuous fun y : Fin M → ℂ => MvPolynomial.eval y p :=
  continuous_iff_continuousAt.mpr fun y => (hasFDerivAt_mvEval p y).continuousAt

theorem continuous_mvJetDeriv (p : MvPolynomial (Fin M) ℂ) : Continuous (mvJetDeriv p) := by
  refine continuous_finsetSum _ fun k _ => ?_
  exact (continuous_mvEval ((pderiv k) p)).smul continuous_const

/-- The `k`-th partial coefficient of the derivative is the `k`-th partial derivative. -/
theorem partialCoeff_mvJetDeriv (p : MvPolynomial (Fin M) ℂ) (y : Fin M → ℂ) (k : Fin M) :
    partialCoeff (mvJetDeriv p y) k = MvPolynomial.eval y ((pderiv k) p) := by
  classical
  rw [partialCoeff, mvJetDeriv]
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- A monomial family and its coefficients define a multivariate polynomial with the same
evaluation. -/
theorem jetPoly_eq_mvEval {N : ℕ} (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (y : Fin M → ℂ) :
    jetPoly d e y
      = MvPolynomial.eval y (∑ α : Fin N, C (d α) * ∏ j : Fin M, (X j) ^ (e α j)) := by
  simp [jetPoly, map_sum]

end GaloisForLFunctions
