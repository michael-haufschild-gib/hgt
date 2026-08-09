import GaloisForLFunctions.RHTower.BaezDuarteDistance
import GaloisForLFunctions.RHTower.LeastSquaresProjection

/-!
# The Báez-Duarte distance from the Gram matrix and the pairing vector

Everything the quantitative Nyman--Beurling theory needs about a finite section is now expressible in
closed form.  The two data are

* the Gram matrix `bdGram θᵢ θⱼ = ∫₁^∞ ({θᵢu} − θᵢ{u})({θⱼu} − θⱼ{u}) u^{-2} du`
  (`BaezDuarteGram.inner_bdGen_eq_bdGram`), and
* the pairing vector `⟪bdGen θᵢ, bdTarget⟫ = −θᵢ log θᵢ` (`BaezDuarteTargetPairing`),

and `LeastSquaresProjection` turns a solution of the normal equations into the distance.  The result is the
classical least-squares formula for the Báez-Duarte distances, unconditionally and with every constant
explicit:

`d² = 1 + ∑ᵢ cᵢ · θᵢ log θᵢ`,  where  `∑ⱼ bdGram θᵢ θⱼ · cⱼ = −θᵢ log θᵢ`.

The `1` is `‖bdTarget‖²` (`norm_bdTarget`).  Nothing here evaluates `bdGram`; the point is that the
distance is now a function of the Gram matrix alone, so the analytic problem is isolated in one place.
-/

open MeasureTheory Set Complex Metric
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {I : Type*} [Fintype I]

/-- The distance from the target to a finite generator span, from a solution of the normal equations. -/
theorem bdDist_eq_of_normalEquations (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (c : I → ℂ)
    (hc : ∀ i, ∑ j, ((bdGram (θ i) (θ j) : ℝ) : ℂ) * c j
      = ((-(θ i * Real.log (θ i)) : ℝ) : ℂ)) :
    bdDist θ = ‖bdTarget - ∑ j, c j • bdGen (θ j)‖ := by
  refine infDist_span_eq (fun i => bdGen (θ i)) bdTarget c ?_
  intro i
  rw [inner_bdGen_bdTarget (hθ i).1 (hθ i).2, ← hc i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_bdGen_eq_bdGram]

/-- **The least-squares value of a Báez-Duarte distance**, with complex coefficients. -/
theorem bdDist_sq_eq_of_normalEquations (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (c : I → ℂ)
    (hc : ∀ i, ∑ j, ((bdGram (θ i) (θ j) : ℝ) : ℂ) * c j
      = ((-(θ i * Real.log (θ i)) : ℝ) : ℂ)) :
    bdDist θ ^ 2
      = 1 - RCLike.re (∑ i, (starRingEnd ℂ) (c i) * ((-(θ i * Real.log (θ i)) : ℝ) : ℂ)) := by
  have hnorm : ∀ i, inner ℂ (bdGen (θ i)) bdTarget = ((-(θ i * Real.log (θ i)) : ℝ) : ℂ) :=
    fun i => inner_bdGen_bdTarget (hθ i).1 (hθ i).2
  have hne : ∀ i, ∑ j, inner ℂ (bdGen (θ i)) (bdGen (θ j)) * c j = inner ℂ (bdGen (θ i)) bdTarget := by
    intro i
    rw [hnorm i, ← hc i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_bdGen_eq_bdGram]
  have hsum : ∑ i, (starRingEnd ℂ) (c i) * inner ℂ (bdGen (θ i)) bdTarget
      = ∑ i, (starRingEnd ℂ) (c i) * ((-(θ i * Real.log (θ i)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnorm i]
  rw [bdDist_eq_of_normalEquations θ hθ c hc,
    norm_sq_residual (fun i => bdGen (θ i)) bdTarget c hne, norm_bdTarget, hsum]
  norm_num

/-- **The classical form.**  With real coefficients solving the real Gram system, the squared
Báez-Duarte distance is `1 + ∑ᵢ cᵢ θᵢ log θᵢ`. -/
theorem bdDist_sq_eq_of_realNormalEquations (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (c : I → ℝ)
    (hc : ∀ i, ∑ j, bdGram (θ i) (θ j) * c j = -(θ i * Real.log (θ i))) :
    bdDist θ ^ 2 = 1 + ∑ i, c i * (θ i * Real.log (θ i)) := by
  have hcC : ∀ i, ∑ j, ((bdGram (θ i) (θ j) : ℝ) : ℂ) * ((c j : ℝ) : ℂ)
      = ((-(θ i * Real.log (θ i)) : ℝ) : ℂ) := by
    intro i
    rw [← hc i]
    push_cast
    rfl
  rw [bdDist_sq_eq_of_normalEquations θ hθ (fun i => ((c i : ℝ) : ℂ)) hcC]
  have hre : RCLike.re (∑ i, (starRingEnd ℂ) (((c i : ℝ) : ℂ))
      * ((-(θ i * Real.log (θ i)) : ℝ) : ℂ))
      = ∑ i, c i * (-(θ i * Real.log (θ i))) := by
    have : ∑ i, (starRingEnd ℂ) (((c i : ℝ) : ℂ)) * ((-(θ i * Real.log (θ i)) : ℝ) : ℂ)
        = ((∑ i, c i * (-(θ i * Real.log (θ i))) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [this]
    show ((∑ i, c i * (-(θ i * Real.log (θ i))) : ℝ) : ℂ).re = _
    exact Complex.ofReal_re _
  rw [hre]
  have : ∑ i, c i * (-(θ i * Real.log (θ i))) = -∑ i, c i * (θ i * Real.log (θ i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  ring

end RHTower

end
