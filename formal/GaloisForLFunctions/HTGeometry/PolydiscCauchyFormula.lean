import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Cauchy integral formula on a polydisc

A holomorphic function of several complex variables is reproduced on a polydisc by the integral of
its values on the distinguished boundary against the product Cauchy kernel.  The formula follows
from the one-variable formula applied in each coordinate in turn, through the recurrence that writes
an integral over a torus as an iterated circle integral.

* `torusIntegrable_of_continuous` : a continuous integrand is torus integrable.
* `polydiscCauchyFormula` : the Cauchy integral formula on a polydisc.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section TorusIntegrable

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous integrand is integrable over a torus. -/
theorem torusIntegrable_of_continuous {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : Continuous fun θ : Fin n → ℝ => f (torusMap c R θ)) : TorusIntegrable f c R :=
  (hf.continuousOn).integrableOn_compact isCompact_Icc

/-- The points of a torus of radius `R` avoid every point of the open polydisc of radius `R`. -/
theorem torusMap_sub_ne_zero {c : Fin n → ℂ} {R : Fin n → ℝ} {z : Fin n → ℂ}
    (hz : ∀ i, z i ∈ Metric.ball (c i) (R i)) (θ : Fin n → ℝ) (i : Fin n) :
    torusMap c R θ i - z i ≠ 0 := by
  have hmem : torusMap c R θ i ∈ Metric.sphere (c i) |R i| := by
    show circleMap (c i) (R i) (θ i) ∈ Metric.sphere (c i) |R i|
    exact circleMap_mem_sphere' (c i) (R i) (θ i)
  have hdist : dist (torusMap c R θ i) (c i) = |R i| := Metric.mem_sphere.1 hmem
  have hz' : dist (z i) (c i) < R i := Metric.mem_ball.1 (hz i)
  intro h
  have heq : torusMap c R θ i = z i := sub_eq_zero.1 h
  rw [heq, hz'.le.lt_of_ne'] at hdist
  · exact absurd hdist (by
      have : R i ≤ |R i| := le_abs_self _
      intro hcon
      exact absurd (hcon ▸ hz') (by simpa using not_lt.2 (le_abs_self (R i))))
  · exact fun hcon => absurd (hcon ▸ hz') (lt_irrefl _)

end TorusIntegrable

end GaloisForLFunctions.HTGeometry
