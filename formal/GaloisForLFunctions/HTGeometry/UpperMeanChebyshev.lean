import GaloisForLFunctions.HTGeometry.CubicPhaseEvaluationUniformity

/-!
# Chebyshev against an upper mean bound

A variable whose mean is only known to lie below a threshold still has a Chebyshev tail above that
threshold: exceeding the threshold by `kappa` forces a deviation of at least `kappa` from the true
mean.  This is the form a moment calculation delivers, where the mean is estimated from above and
the variance from above, and both bounds are used without computing either exactly.

At collision scale the two bounds `2/D` and `96/D^3` at deviation `kappa/D` give the tail
`96/(kappa^2 D)`.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

section Chebyshev

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Chebyshev with an upper mean bound.**  If the mean is at most `m` and the variance at most
`V`, then the probability of exceeding `m + kappa` is at most `V/kappa²`. -/
theorem measureReal_gt_le_of_mean_le {X : Ω → ℝ} (hX : MemLp X 2 μ) {m V κ : ℝ}
    (hmean : ∫ ω, X ω ∂μ ≤ m) (hvar : Var[X; μ] ≤ V) (hκ : 0 < κ) :
    μ.real {ω | m + κ < X ω} ≤ V / κ ^ 2 := by
  have hsub : {ω | m + κ < X ω} ⊆ {ω | κ ≤ |X ω - ∫ x, X x ∂μ|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hgap : κ ≤ X ω - ∫ x, X x ∂μ := by linarith
    calc κ ≤ X ω - ∫ x, X x ∂μ := hgap
      _ ≤ |X ω - ∫ x, X x ∂μ| := le_abs_self _
  have hcheb := meas_ge_le_variance_div_sq (μ := μ) hX hκ
  have hle : μ {ω | m + κ < X ω} ≤ ENNReal.ofReal (Var[X; μ] / κ ^ 2) :=
    le_trans (measure_mono hsub) hcheb
  have hvarnn : 0 ≤ Var[X; μ] := variance_nonneg X μ
  calc μ.real {ω | m + κ < X ω}
      ≤ (ENNReal.ofReal (Var[X; μ] / κ ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = Var[X; μ] / κ ^ 2 := ENNReal.toReal_ofReal (by positivity)
    _ ≤ V / κ ^ 2 := by
        refine div_le_div_of_nonneg_right hvar ?_
        positivity

end Chebyshev

section Scale

/-- **`(9)`: the collision tail at the two-design scale.**  A mean below `2/D` and a variance below
`96/D³` give the tail `96/(kappa² D)` at threshold `(2+kappa)/D`. -/
theorem collision_tail_scale {D κ : ℝ} (hD : 0 < D) (hκ : 0 < κ) :
    (96 / D ^ 3) / (κ / D) ^ 2 = 96 / (κ ^ 2 * D) := by
  field_simp

/-- The threshold `(2+kappa)/D` is the mean bound `2/D` displaced by `kappa/D`. -/
theorem collision_threshold_split {D κ : ℝ} (hD : D ≠ 0) :
    (2 + κ) / D = 2 / D + κ / D := by
  field_simp

end Scale

end GaloisForLFunctions.HTGeometry
