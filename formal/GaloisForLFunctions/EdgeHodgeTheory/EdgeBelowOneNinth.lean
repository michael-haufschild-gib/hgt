import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeIsAThresholdCurve
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineReceivesAtTheEighthRoot
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity

/-!
# The universal detection edge below `1 / 9` and the `[1 / 9, 1 / 8]` eighth-root window

Unconditional all-vector positivity of `completeWeilMatrix tiltedUnitSpline c N` across
`1 ≤ c ≤ (log N)^α` for every `0 < α < 1 / 9` lifts the universal regime of the detection edge
`edge tiltedUnitSpline N`, pairs with the fourth-order Euler–Maclaurin synthesis receiver above
`1 / 8` to trap the non-RH detection edge inside `[(log N)^α, 2 (log N)^β]` (`0 < α < 1 / 9`,
`1 / 8 < β`), and places every horizon `N` strictly below the detection threshold
`horizonThreshold (atomDilate tiltedUnitSpline (c / N))` across `1 ≤ c ≤ (log N)^α`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace ENNReal

namespace GaloisForLFunctions.EdgeHodgeTheory

open HTGeometry SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  RenormalizedArithmeticPotentialTheory

/-- **Universal edge lower bound below `1 / 9`.**
Unconditionally, for every `0 < α < 1 / 9`, eventually in `N`,
`ENNReal.ofReal (Real.log N ^ α) ≤ edge tiltedUnitSpline N`. -/
theorem eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline_below_one_ninth
    {α : ℝ} (hα : 0 < α)
    (hα_lt : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (Real.log (N : ℝ) ^ α) ≤ edge tiltedUnitSpline N := by
  filter_upwards [CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
    hα hα_lt] with N hN
  refine ofReal_le_firstFailure_iff.mpr fun c hc hca x => ?_
  exact RenormalizedIntersectionTheory.energy_nonneg_of_posDef
    (completeWeilMatrix_isHermitian _ _ _) (hN c hc hca.le) x

/-- **Explicit one-tenth universal edge lower bound (`α = 1 / 10`).** -/
theorem eventually_ofReal_rpow_log_one_tenth_le_edge_tiltedUnitSpline :
    ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (Real.log (N : ℝ) ^ (1 / 10 : ℝ)) ≤ edge tiltedUnitSpline N :=
  eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline_below_one_ninth
    (by norm_num)
    (by norm_num [CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent])

/-- **Eighth-root edge ceiling under `¬ RH`.**
Because fourth-order synthesis makes `tiltedUnitSpline` an RH receiver at every exponent above
`1 / 8`, failure of the Riemann Hypothesis forces `edge tiltedUnitSpline N ≤ 2 (log N)^β`
infinitely often for every `β > 1 / 8`. -/
theorem frequently_edge_tiltedUnitSpline_le_eighthRoot_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) {β : ℝ} (hβ : 1 / 8 < β) :
    ∃ᶠ N : ℕ in atTop, edge tiltedUnitSpline N ≤ ENNReal.ofReal (2 * Real.log (N : ℝ) ^ β) :=
  frequently_firstFailure_le (P := fun N c => PositiveAt tiltedUnitSpline c N)
    (eventually_one_le_two_mul_rpow_log (by linarith))
    fun H => hRH ((riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_log_eighth hβ).mpr H)

/-- **Narrowed non-RH edge detection window `[(log N)^α, 2 (log N)^β]` (`0 < α < 1 / 9`, `β > 1 / 8`).**
If the Riemann Hypothesis fails, then for every `0 < α < 1 / 9` and every `β > 1 / 8`,
`edge tiltedUnitSpline N` lies in `[(log N)^α, 2 (log N)^β]` infinitely often. -/
theorem frequently_edge_mem_eighthRoot_window_of_not_riemannHypothesis_below_one_ninth
    (hRH : ¬ RiemannHypothesis) {α β : ℝ} (hα : 0 < α)
    (hα_lt : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent)
    (hβ : 1 / 8 < β) :
    ∃ᶠ N : ℕ in atTop,
      ENNReal.ofReal (Real.log (N : ℝ) ^ α) ≤ edge tiltedUnitSpline N ∧
        edge tiltedUnitSpline N ≤ ENNReal.ofReal (2 * Real.log (N : ℝ) ^ β) :=
  ((frequently_edge_tiltedUnitSpline_le_eighthRoot_of_not_riemannHypothesis hRH hβ).and_eventually
    (eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline_below_one_ninth hα hα_lt)).mono
    fun _ h => ⟨h.2, h.1⟩

/-- **Quarter-root non-RH edge window `[(log N)^α, 2 (log N)^β]` (`0 < α < 1 / 9`, `β > 1 / 4`).** -/
theorem frequently_edge_mem_window_of_not_riemannHypothesis_below_one_ninth
    (hRH : ¬ RiemannHypothesis) {α β : ℝ} (hα : 0 < α)
    (hα_lt : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent)
    (hβ : 1 / 4 < β) :
    ∃ᶠ N : ℕ in atTop,
      ENNReal.ofReal (Real.log (N : ℝ) ^ α) ≤ edge tiltedUnitSpline N ∧
        edge tiltedUnitSpline N ≤ ENNReal.ofReal (2 * Real.log (N : ℝ) ^ β) :=
  frequently_edge_mem_eighthRoot_window_of_not_riemannHypothesis_below_one_ninth
    hRH hα hα_lt (by linarith)

/-- **Threshold-curve lower bound below `1 / 9`.**
For every `0 < α < 1 / 9`, eventually in `N`, every overlap `1 ≤ c ≤ (log N)^α` places `N`
strictly below the detection horizon `horizonThreshold (atomDilate tiltedUnitSpline (c / N))`. -/
theorem eventually_lt_horizonThreshold_tiltedUnitSpline_below_one_ninth
    {α : ℝ} (hα : 0 < α)
    (hα_lt : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (N : ℕ∞) < horizonThreshold (atomDilate tiltedUnitSpline (c / N)) := by
  filter_upwards [CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
    hα hα_lt, eventually_ge_atTop 1] with N hN hN1 c hc1 hcup
  refine (positiveAt_iff_lt_horizonThreshold admissible_tiltedUnitSpline
    (zero_lt_one.trans_le hc1) hN1).mp fun x => ?_
  exact RenormalizedIntersectionTheory.energy_nonneg_of_posDef
    (completeWeilMatrix_isHermitian _ _ _) (hN c hc1 hcup) x

end GaloisForLFunctions.EdgeHodgeTheory

#print axioms GaloisForLFunctions.EdgeHodgeTheory.eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline_below_one_ninth
#print axioms GaloisForLFunctions.EdgeHodgeTheory.eventually_ofReal_rpow_log_one_tenth_le_edge_tiltedUnitSpline
#print axioms GaloisForLFunctions.EdgeHodgeTheory.frequently_edge_tiltedUnitSpline_le_eighthRoot_of_not_riemannHypothesis
#print axioms GaloisForLFunctions.EdgeHodgeTheory.frequently_edge_mem_eighthRoot_window_of_not_riemannHypothesis_below_one_ninth
#print axioms GaloisForLFunctions.EdgeHodgeTheory.frequently_edge_mem_window_of_not_riemannHypothesis_below_one_ninth
#print axioms GaloisForLFunctions.EdgeHodgeTheory.eventually_lt_horizonThreshold_tiltedUnitSpline_below_one_ninth
