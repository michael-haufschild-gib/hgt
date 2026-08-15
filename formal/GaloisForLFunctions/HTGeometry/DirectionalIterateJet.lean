import GaloisForLFunctions.HTGeometry.SeveralVariableDirectionalDifferential

/-!
# Iterates of the directional derivative are the jets along the line

For an entire function the `r`-fold directional derivative at `z` is the `r`-th derivative at `0` of
the restriction to the line through `z` in that direction: one step is the chain rule, and the
induction runs because the directional derivative of an analytic function is analytic.

This identifies the differential jets of the several-variable differential field with the jets used
by a line-restriction argument.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions.HTGeometry

open Bottcher

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative of the restriction of a differentiable function to a line. -/
theorem hasDerivAt_line {f : E → ℂ} {z : E} (w : E) (s : ℂ)
    (hf : DifferentiableAt ℂ f (z + s • w)) :
    HasDerivAt (fun t : ℂ => f (z + t • w)) (fderiv ℂ f (z + s • w) w) s := by
  have hline : HasDerivAt (fun t : ℂ => z + t • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add z
  exact (hf.hasFDerivAt.comp_hasDerivAt s hline)

/-- **One step: the derivative along the line is the directional derivative.** -/
theorem deriv_line_eq (w : E) {f : E → ℂ} (hf : Differentiable ℂ f) (z : E) :
    deriv (fun t : ℂ => f (z + t • w)) = fun s => dirDerivFun w f (z + s • w) := by
  funext s
  exact (hasDerivAt_line w s (hf _)).deriv

/-- **The iterates of the directional derivative are the jets along the line.** -/
theorem dirDerivFun_iterate_eq_iteratedDeriv (w : E) :
    ∀ (r : ℕ) {f : E → ℂ}, AnalyticOnNhd ℂ f Set.univ → ∀ z : E,
      (dirDerivFun w)^[r] f z = iteratedDeriv r (fun s : ℂ => f (z + s • w)) 0
  | 0, f, _, z => by simp
  | r + 1, f, hf, z => by
      have hdiff : Differentiable ℂ f := fun x => (hf x (Set.mem_univ x)).differentiableAt
      have hfd : AnalyticOnNhd ℂ (dirDerivFun w f) Set.univ := analyticOnNhd_dirDerivFun w hf
      rw [Function.iterate_succ_apply,
        dirDerivFun_iterate_eq_iteratedDeriv w r hfd z, iteratedDeriv_succ',
        deriv_line_eq w hdiff z]

end

end GaloisForLFunctions.HTGeometry
