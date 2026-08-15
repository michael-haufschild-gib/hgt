import GaloisForLFunctions.RHTower.BakerGeneralProof.ComponentTransport

/-!
# Iterated analytic transport for Baker auxiliary functions

Every ordinary derivative of an auxiliary function is represented exactly by the corresponding
iterate of the analytic polynomial derivation.  This is the analytic half of the higher-jet
transport; the component and integral half is supplied by `ComponentTransport` and the upcoming
multi-index expansion.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Iterated differentiation of a complex auxiliary polynomial evaluates its iterated derivation. -/
theorem SolvedRelation.iteratedDeriv_eval_auxiliaryPoint
    (R : SolvedRelation) (k : ℕ) (Q : MvPolynomial R.Variable ℂ) :
    iteratedDeriv k (fun w => MvPolynomial.eval (R.auxiliaryPoint w) Q) =
      fun z => MvPolynomial.eval (R.auxiliaryPoint z) (R.analyticDerivation^[k] Q) := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      rw [R.deriv_eval_auxiliaryPoint]
      simp only [Function.iterate_succ_apply']

/-- Iterated ordinary derivatives of a number-field auxiliary function are analytic-derivation
iterates after coefficient extension. -/
theorem SolvedRelation.iteratedDeriv_auxiliaryFunction
    (R : SolvedRelation) (k : ℕ)
    (P : MvPolynomial R.Variable R.CoefficientField) (z : ℂ) :
    iteratedDeriv k (R.auxiliaryFunction P) z =
      MvPolynomial.eval (R.auxiliaryPoint z)
        (R.analyticDerivation^[k] (R.complexify P)) := by
  exact congrFun (R.iteratedDeriv_eval_auxiliaryPoint k (R.complexify P)) z

end GaloisForLFunctions.RHTower.BakerGeneralProof
