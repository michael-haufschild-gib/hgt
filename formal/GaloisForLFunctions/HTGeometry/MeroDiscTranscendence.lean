import GaloisForLFunctions.HTGeometry.MeroDiscComplexFrame
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# Nonconstant analytic germs are transcendental over the constants

Over an algebraically closed base an algebraic element of a field extension is a constant, because
its minimal polynomial is irreducible and hence linear.  So a germ that is algebraic over `ℂ` in a
meromorphic germ field is the germ of a constant, and faithfulness of the germ realization turns
that into constancy of the function on the domain.

The same argument gives polynomial evaluation on germs: evaluating a univariate polynomial at the
realization of an analytic function is the realization of the pointwise composite.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Set

noncomputable section

/-- Over an algebraically closed field an algebraic element is a scalar. -/
theorem exists_eq_algebraMap_of_isAlgebraic {M : Type*} [Field M] [Algebra ℂ M] {y : M}
    (h : IsAlgebraic ℂ y) : ∃ c : ℂ, y = algebraMap ℂ M c := by
  have hint : IsIntegral ℂ y := h.isIntegral
  have hirr := minpoly.irreducible hint
  have hdeg : (minpoly ℂ y).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible ℂ hirr
  have hmonic : (minpoly ℂ y).Monic := minpoly.monic hint
  have hnd : (minpoly ℂ y).natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have heq : minpoly ℂ y = Polynomial.X + Polynomial.C ((minpoly ℂ y).coeff 0) :=
    hmonic.eq_X_add_C hnd
  have h0 := minpoly.aeval ℂ y
  rw [heq, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h0
  refine ⟨-((minpoly ℂ y).coeff 0), ?_⟩
  rw [map_neg]
  linear_combination h0

/-- Pointwise evaluation of a polynomial at an analytic function is analytic. -/
theorem analyticOnNhd_eval_poly_comp {U : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (Q : Polynomial ℂ) : AnalyticOnNhd ℂ (fun z => Q.eval (F z)) U := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      have heq : (fun z => (p + q).eval (F z)) = fun z => p.eval (F z) + q.eval (F z) := by
        funext z; simp
      rw [heq]
      intro x hx
      exact (hp x hx).add (hq x hx)
  | monomial m a =>
      have heq : (fun z => (Polynomial.monomial m a).eval (F z)) = fun z => a * (F z) ^ m := by
        funext z; simp
      rw [heq]
      intro x hx
      exact analyticAt_const.mul ((hF x hx).pow m)

/-- **Polynomial evaluation on germs.** -/
theorem aeval_analyticMeroElement {U : Set ℂ} [IsDomain (analyticSubring U)] {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Q : Polynomial ℂ) :
    letI := meroComplexAlgebra U
    Polynomial.aeval (analyticMeroElement F hF) Q
      = analyticMeroElement (fun z => Q.eval (F z)) (analyticOnNhd_eval_poly_comp hF Q) := by
  letI := meroComplexAlgebra U
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq, ← analyticMeroElement_add]
      exact analyticMeroElement_congr _ _ (by funext z; simp)
  | monomial m a =>
      rw [Polynomial.aeval_monomial]
      have hconst : (algebraMap ℂ (meroField U)) a
          = analyticMeroElement (fun _ : ℂ => a) analyticOnNhd_const := by
        rw [analyticMeroElement_const]
        rfl
      rw [hconst, ← analyticMeroElement_pow, ← analyticMeroElement_mul]
      exact analyticMeroElement_congr _ _ (by funext z; simp)

/-- **A nonconstant analytic germ is transcendental over the constants.** -/
theorem transcendental_analyticMeroElement_of_nonconstant_on {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (hnc : ¬ ∃ c : ℂ, ∀ z ∈ U, F z = c) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroComplexAlgebra U
    Transcendental ℂ (analyticMeroElement F hF) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroComplexAlgebra U
  intro halg
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isAlgebraic halg
  refine hnc ⟨c, ?_⟩
  have hconst : (algebraMap ℂ (meroField U)) c
      = analyticMeroElement (fun _ : ℂ => c) analyticOnNhd_const := by
    rw [analyticMeroElement_const]
    rfl
  have hsub : analyticMeroElement (fun z => F z - c) (hF.sub analyticOnNhd_const) = 0 := by
    rw [analyticMeroElement_sub hF analyticOnNhd_const, hc, hconst, sub_self]
  intro z hz
  have hval := (analyticMeroElement_eq_zero_iff (hF.sub analyticOnNhd_const)).mp hsub z hz
  exact sub_eq_zero.mp hval

end

end GaloisForLFunctions.HTGeometry
