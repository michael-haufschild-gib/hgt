import GaloisForLFunctions.HTGeometry.MeroDiscTranscendence
import GaloisForLFunctions.HTGeometry.RittPoincareCocycle

/-!
# Evaluating a rational function at an analytic germ

Splitting a rational function into its numerator and denominator turns its evaluation at the
realization of an analytic function into a quotient of the realizations of the pointwise composites.
A pointwise identity `F(z)·D(G(z)) = N(G(z))` on the domain therefore says exactly that the germ of
`F` is the value of `N/D` at the germ of `G` — the form in which the Poincaré equation enters the
Ritt bridge.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Set

noncomputable section

/-- **Rational evaluation at an analytic germ is a quotient of composites.** -/
theorem ratFuncEval_analyticMeroElement {U : Set ℂ} [IsDomain (analyticSubring U)] {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G U)
    (htr : letI := meroComplexAlgebra U; Transcendental ℂ (analyticMeroElement G hG))
    (Q : RatFunc ℂ) :
    letI := meroComplexAlgebra U
    ratFuncEval (analyticMeroElement G hG) htr Q
      = analyticMeroElement (fun z => Q.num.eval (G z)) (analyticOnNhd_eval_poly_comp hG Q.num)
        / analyticMeroElement (fun z => Q.denom.eval (G z))
          (analyticOnNhd_eval_poly_comp hG Q.denom) := by
  letI := meroComplexAlgebra U
  conv_lhs => rw [← RatFunc.num_div_denom Q]
  rw [map_div₀, ratFuncEval_polyImage, ratFuncEval_polyImage, aeval_analyticMeroElement,
    aeval_analyticMeroElement]

/-- **A pointwise rational identity is a germ-level evaluation.** -/
theorem analyticMeroElement_eq_ratFuncEval {U : Set ℂ} [IsDomain (analyticSubring U)]
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (htr : letI := meroComplexAlgebra U; Transcendental ℂ (analyticMeroElement G hG))
    {Q : RatFunc ℂ} (hden : ¬ ∀ z ∈ U, Q.denom.eval (G z) = 0)
    (hpt : ∀ z ∈ U, F z * Q.denom.eval (G z) = Q.num.eval (G z)) :
    letI := meroComplexAlgebra U
    analyticMeroElement F hF = ratFuncEval (analyticMeroElement G hG) htr Q := by
  letI := meroComplexAlgebra U
  have hD0 : analyticMeroElement (fun z => Q.denom.eval (G z))
      (analyticOnNhd_eval_poly_comp hG Q.denom) ≠ 0 := by
    intro h
    exact hden ((analyticMeroElement_eq_zero_iff _).mp h)
  rw [ratFuncEval_analyticMeroElement hG htr Q, eq_div_iff hD0,
    ← analyticMeroElement_mul hF (analyticOnNhd_eval_poly_comp hG Q.denom)]
  have hzero : analyticMeroElement (fun z => F z * Q.denom.eval (G z))
        (hF.mul (analyticOnNhd_eval_poly_comp hG Q.denom))
      - analyticMeroElement (fun z => Q.num.eval (G z))
        (analyticOnNhd_eval_poly_comp hG Q.num) = 0 := by
    rw [← analyticMeroElement_sub (hF.mul (analyticOnNhd_eval_poly_comp hG Q.denom))
      (analyticOnNhd_eval_poly_comp hG Q.num), analyticMeroElement_eq_zero_iff]
    intro z hz
    rw [hpt z hz, sub_self]
  linear_combination hzero

end

end GaloisForLFunctions.HTGeometry
