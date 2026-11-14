import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetTurningPoints
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/-!
# Existence and uniqueness of charged thermal saddles

The saddle polynomial has opposite signs at zero and an explicit positive
trial radius. A positive algebraic decomposition supplies the upper sign,
so the intermediate value theorem proves existence without asymptotic or
numerical input. Above the neutral coupling threshold, strict temperature
monotonicity gives uniqueness.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def thermalPolynomial (a v w x : ℝ) : ℝ :=
  6 * x ^ 6 + 3 * x ^ 4 - Real.exp v ^ 2 -
    6 * Real.pi * Real.exp w * x ^ 3 * (x ^ 2 + 2 * a ^ 2)

def thermalTrialRadius (a v w : ℝ) : ℝ :=
  1 + Real.exp v + 2 * Real.pi * Real.exp w * (1 + 2 * a ^ 2)

theorem thermalTrialRadius_pos (a v w : ℝ) : 0 < thermalTrialRadius a v w := by
  unfold thermalTrialRadius
  positivity

theorem thermalPolynomial_zero_neg (a v w : ℝ) : thermalPolynomial a v w 0 < 0 := by
  norm_num [thermalPolynomial]
  positivity

/-- Every term in the explicit upper-endpoint certificate is nonnegative. -/
theorem thermalPolynomial_trial_decomposition (a v w : ℝ) :
    thermalPolynomial a v w (thermalTrialRadius a v w) =
      thermalTrialRadius a v w ^ 2 * (thermalTrialRadius a v w - 1) *
        (thermalTrialRadius a v w + 1) * (thermalTrialRadius a v w ^ 2 + 1) +
      (thermalTrialRadius a v w - Real.exp v) * (thermalTrialRadius a v w + Real.exp v) +
      2 * thermalTrialRadius a v w ^ 6 + 3 * thermalTrialRadius a v w ^ 4 +
      3 * thermalTrialRadius a v w ^ 3 *
        (thermalTrialRadius a v w ^ 2 * (1 + Real.exp v) +
          4 * Real.pi * Real.exp w * a ^ 2 * (thermalTrialRadius a v w - 1) *
            (thermalTrialRadius a v w + 1)) := by
  have hr : thermalTrialRadius a v w - 2 * Real.pi * Real.exp w -
      4 * Real.pi * Real.exp w * a ^ 2 = 1 + Real.exp v := by
    unfold thermalTrialRadius
    ring
  have hc := congrArg (fun x : ℝ => 3 * thermalTrialRadius a v w ^ 5 * x) hr
  unfold thermalPolynomial
  nlinarith only [hc]

theorem thermalPolynomial_trial_pos (a v w : ℝ) :
    0 < thermalPolynomial a v w (thermalTrialRadius a v w) := by
  have hB : 0 < 2 * Real.pi * Real.exp w * (1 + 2 * a ^ 2) := by positivity
  have h₁ : 0 < thermalTrialRadius a v w - 1 := by
    unfold thermalTrialRadius
    linarith only [hB, Real.exp_pos v]
  have hq : 0 < thermalTrialRadius a v w - Real.exp v := by
    unfold thermalTrialRadius
    linarith only [hB]
  have hX := thermalTrialRadius_pos a v w
  rw [thermalPolynomial_trial_decomposition]
  positivity

/-- Every nonnegative coupling and positive charge has a saddle at each positive bath temperature. -/
theorem temperature_charged_saddle_exists (a v w : ℝ) :
    ∃ x : ℝ, 0 < x ∧ temperature (a ^ 2) (Real.exp v) x = Real.exp w := by
  have hc : Continuous (thermalPolynomial a v w) := by
    unfold thermalPolynomial
    fun_prop
  obtain ⟨x, hx, hroot⟩ := intermediate_value_Icc (thermalTrialRadius_pos a v w).le
    hc.continuousOn ⟨(thermalPolynomial_zero_neg a v w).le, (thermalPolynomial_trial_pos a v w).le⟩
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    exact (thermalPolynomial_zero_neg a v w).ne hroot
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
  refine ⟨x, hxpos, ?_⟩
  unfold temperature
  have hden : 6 * Real.pi * x ^ 3 * (x ^ 2 + 2 * a ^ 2) ≠ 0 := by positivity
  apply (div_eq_iff hden).mpr
  unfold thermalPolynomial at hroot
  nlinarith only [hroot]

/-- At and above `λ=1/36`, the positive-temperature charged saddle exists and is unique. -/
theorem temperature_charged_unique_saddle (a v w : ℝ) :
    ∃! x : ℝ, 0 < x ∧ temperature (1 / 36 + a ^ 2) (Real.exp v) x = Real.exp w := by
  have hs : Real.sqrt (1 / 36 + a ^ 2) ^ 2 = 1 / 36 + a ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨x, hx, hT⟩ := temperature_charged_saddle_exists (Real.sqrt (1 / 36 + a ^ 2)) v w
  rw [hs] at hT
  refine ⟨x, ⟨hx, hT⟩, ?_⟩
  intro y hy
  exact temperature_charged_fiber_subsingleton a v (Real.exp w) hy ⟨hx, hT⟩

#print axioms thermalPolynomial_trial_decomposition
#print axioms temperature_charged_saddle_exists
#print axioms temperature_charged_unique_saddle

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
