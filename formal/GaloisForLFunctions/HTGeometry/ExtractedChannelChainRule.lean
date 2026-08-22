import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-!
# Extracted-channel chain rule

This module formalizes Okten--Turan, arXiv:2608.19244v1, equation `(67)`.  A moving angular label
contributes the spatial differential applied to the label velocity in addition to the fixed-label
time derivative.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Equation `(67)` in Fréchet-derivative form.  `k` is the fixed-label time partial derivative,
`D` is the angular differential, and `v` is the extraction-label velocity. -/
theorem extractedChannel_chainRule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ × E → ℝ) (Phi : ℝ → E) (u : ℝ)
    (L : ℝ × E →L[ℝ] ℝ) (k : ℝ) (D : E →L[ℝ] ℝ) (v : E)
    (hp : HasFDerivAt p L (u, Phi u)) (hPhi : HasDerivAt Phi v u)
    (hL : ∀ z, L z = k * z.1 + D z.2) :
    deriv (fun t => p (t, Phi t)) u = k + D v := by
  have hcurve : HasDerivAt (fun t => (t, Phi t)) (1, v) u :=
    (hasDerivAt_id u).prodMk hPhi
  have hcomp := hp.comp_hasDerivAt u hcurve
  have hd : deriv (fun t => p (t, Phi t)) u = L (1, v) := by
    simpa only [Function.comp_def] using hcomp.deriv
  rw [hd, hL]
  simp

end GaloisForLFunctions.HTGeometry
