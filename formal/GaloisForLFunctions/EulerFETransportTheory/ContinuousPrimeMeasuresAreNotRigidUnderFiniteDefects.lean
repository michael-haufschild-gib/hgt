import GaloisForLFunctions.EulerFETransportTheory.ContinuousPrimePerturbationsSatisfyTheHamburgerStrip

/-!
# Finite functional-equation defects do not rigidify continuous prime measures

A positive atomless addition to the Riemann prime-power measure produces a
nonclassical positive Euler measure with the unit atom unchanged. Its zeta
function has the same zeros as Riemann zeta. Nevertheless it satisfies all
Hamburger strip conditions with an uncompleted defect in both `L¹` and `L²`.
Thus the finite-defect rigidity of countable prime systems does not extend
to positive prime-power measures.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.EulerFETransportTheory

/-- An explicit positive continuous prime perturbation satisfies every analytic
Hamburger hypothesis with finite defect, while its prime measure is nonclassical. -/
theorem continuous_prime_measure_finite_defect_counterexample :
    let P := perturbedRiemannPrimeMeasure 1
    let E := continuousEulerRemainder 1
    let β := continuousEulerResidue 1
    let g := continuousEulerDefect 1
    P ≠ riemannPrimeMeasure ∧ P (Iic 1) = 0 ∧
      Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) P ∧
      beurlingIntegerMeasure P {1} = 1 ∧
      ContinuousOn E (verticalStrip (1 / 2) (3 / 2)) ∧
      DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2} ∧
      (∃ C : ℝ, ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2)) ∧
      (∀ s : ℂ, s.re = 3 / 2 →
        Complex.Gammaℝ s * measureDirichlet (beurlingIntegerMeasure P) s =
          E s + β * Complex.Gammaℝ (s - 1)) ∧
      (∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
        -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) +
          Complex.Gammaℝ s * g (s.im / 2)) ∧
      Measurable g ∧ (∃ Cg : ℝ, ∀ t : ℝ, ‖g t‖ ≤ Cg) ∧
      Integrable g ∧ MemLp g 2 (volume : Measure ℝ) := by
  dsimp only
  refine ⟨?_, perturbedRiemannPrimeMeasure_Iic_one 1,
    integrable_rpow_perturbedRiemannPrimeMeasure 1 (by norm_num),
    beurlingIntegerMeasure_singleton_one (perturbedRiemannPrimeMeasure_Iic_one 1),
    continuousOn_continuousEulerRemainder_strip 1, ?_,
    exists_decay_continuousEulerRemainder 1,
    fun s hs => continuousEulerRemainder_right_boundary 1 hs,
    fun s hs => continuousEulerRemainder_center 1 hs,
    (continuous_continuousEulerDefect 1).measurable, ?_,
    integrable_continuousEulerDefect 1, memLp_continuousEulerDefect 1⟩
  · exact fun h => one_ne_zero ((perturbedRiemannPrimeMeasure_eq_iff 1).mp h)
  · apply (differentiableOn_continuousEulerRemainder 1).mono
    intro s hs
    linarith only [hs.1]
  · obtain ⟨C, hC, hbound⟩ := exists_uniform_continuousEulerDefect_bound
    refine ⟨C * Real.exp 1, fun t => ?_⟩
    have h := hbound 1 t
    norm_num only [NNReal.coe_one, mul_one] at h
    exact h.trans (div_le_self (by positivity) (by nlinarith only [sq_nonneg t]))

#print axioms continuous_prime_measure_finite_defect_counterexample

end GaloisForLFunctions.EulerFETransportTheory
