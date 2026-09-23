import GaloisForLFunctions.HTGeometry.MeasureGramVanishing

/-!
# The chamber lower bound

Assembling the last connection.  The scaled Cauchy kernel is continuous at every nonzero height, so
the Cauchy-Schwarz bound on the measure off-diagonal holds eventually, and with the diagonal limits
the off-diagonal vanishes too.

With both parts of the measure Gram vanishing, the total scaled Gram is negative definite at all
small heights whenever every inserted coefficient is negative.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix

noncomputable section

/-- At a nonzero height the Cauchy factor never vanishes on the real line. -/
theorem sub_upperNode_ne_zero {a y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    (t : ℂ) - upperNode a y ≠ 0 := by
  intro h
  have hns := normSq_sub_upperNode a y t
  rw [h, map_zero] at hns
  have hy2 : 0 < y ^ (2 : ℕ) := by positivity
  nlinarith [sq_nonneg (t - a)]

/-- The modulus of the scaled Cauchy kernel is continuous at a nonzero height. -/
theorem continuous_scaledCauchyNorm {a y : ℝ} (hy : y ≠ 0) :
    Continuous fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ := by
  refine (continuous_const.mul ?_).norm
  refine Continuous.inv₀ ?_ (sub_upperNode_ne_zero hy)
  exact Complex.continuous_ofReal.sub continuous_const

/-- **The measure off-diagonal vanishes.**  The Cauchy-Schwarz bound holds at every small height and
the two diagonals vanish, so the off-diagonal does too. -/
theorem tendsto_measureGram_offdiag_of_dominant {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ)
    (l m : Fin d) (R : ℝ) (hR : 0 < R)
    (hdoml : Integrable (atomDominant (a l) R) ν)
    (hdomm : Integrable (atomDominant (a m) R) ν)
    (hatoml : ν {a l} = 0) (hatomm : ν {a m} = 0) :
    Tendsto (fun y : ℝ => measureGram ν a y l m) (𝓝[≠] 0) (𝓝 0) := by
  have hliml := tendsto_integral_atomKernel_of_notAtom_herglotz ν R hR hdoml hatoml
  have hlimm := tendsto_integral_atomKernel_of_notAtom_herglotz ν R hR hdomm hatomm
  refine tendsto_measureGram_offdiag ν a l m ?_ hliml hlimm
  filter_upwards [self_mem_nhdsWithin,
    eventually_integrable_atomKernel ν (a l) R hR hdoml,
    eventually_integrable_atomKernel ν (a m) R hR hdomm] with y hy hil him
  exact norm_measureGram_sq_le ν a y l m hil him

/-- **The chamber lower bound.**  At pairwise distinct non-atomic insertion points with a Herglotz
dominant, and with every inserted coefficient negative, the total scaled Pick Gram is negative
definite at all small heights. -/
theorem eventually_negDef_totalGram_chamber {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j ≤ -δ)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν)
    (hatom : ∀ j : Fin d, ν {a j} = 0) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x : Fin d → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0 :=
  eventually_negDef_totalGram_of_measure_vanishing ν a c ha hδ hc
    (fun l => tendsto_measureGram_diagonal_of_dominant ν a l R hR (hdom l) (hatom l))
    (fun l m _ => tendsto_measureGram_offdiag_of_dominant ν a l m R hR
      (hdom l) (hdom m) (hatom l) (hatom m))

end

end GaloisForLFunctions.HTGeometry
