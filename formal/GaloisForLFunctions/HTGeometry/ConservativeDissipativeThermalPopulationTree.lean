import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalGibbs

/-!
# Measured thermal channels and homogeneous tree messages

This application of the conservative–dissipative mechanism from arXiv:2609.04530
uses the constructed thermal Kraus semigroup. Its measured north/south transition
probabilities produce a real homogeneous tree recursion. The actual derivative
at zero is the branch count times the survival mass, independent of bath bias.
Strictly physical tanh messages remain strictly physical under every finite
branch count. The rational GADC comparison is developed separately.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Measured upper population after applying the constructed channel to the north pole. -/
def spinThermalPositiveProbability (a u : ℝ) (t : NNReal) : ℝ :=
  ((spinThermalChannel a u t).map spinZCutoff) 0 0 |>.re

/-- The same measurement after the normalized south-pole input. -/
def spinThermalNegativeProbability (a u : ℝ) (t : NNReal) : ℝ :=
  ((spinThermalChannel a u t).map (spinChartDensity 0)) 0 0 |>.re

/-- Exact positive-input transition probability of the physical channel. -/
theorem spinThermalPositiveProbability_eq (a u : ℝ) (t : NNReal) :
    spinThermalPositiveProbability a u t = 1 - (1 - spinDecayMass a t) * spinBathLower u := by
  unfold spinThermalPositiveProbability
  rw [spinThermalChannel_entries, spinZCutoff_entries]
  simp [Matrix.trace, Fin.sum_univ_two, spinBathLower]
  ring

/-- Exact negative-input transition probability of the same channel. -/
theorem spinThermalNegativeProbability_eq (a u : ℝ) (t : NNReal) :
    spinThermalNegativeProbability a u t = (1 - spinDecayMass a t) * spinBathUpper u := by
  unfold spinThermalNegativeProbability
  rw [spinThermalChannel_entries, spinChartDensity_trace, spinChartDensity_entries]
  simp [Matrix.smul_apply]

/-- The experimentally accessible population gap equals the dissipative survival mass. -/
theorem spinThermalProbability_gap (a u : ℝ) (t : NNReal) :
    spinThermalPositiveProbability a u t - spinThermalNegativeProbability a u t = spinDecayMass a t := by
  rw [spinThermalPositiveProbability_eq, spinThermalNegativeProbability_eq, spinBathLower]
  ring

/-- Both transition probabilities lie in the unit interval; no positivity premise is supplied. -/
theorem spinThermalProbability_bounds (a u : ℝ) (t : NNReal) :
    0 ≤ spinThermalPositiveProbability a u t ∧ spinThermalPositiveProbability a u t ≤ 1 ∧
    0 ≤ spinThermalNegativeProbability a u t ∧ spinThermalNegativeProbability a u t ≤ 1 := by
  have hm := spinDecayMass_pos a t
  have hm1 := spinDecayMass_le_one a t
  have hu := spinBathUpper_pos u
  have hu1 : spinBathUpper u ≤ 1 := spinMixRadius_le_one u
  have hml := mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hu1)
  have hmu := mul_nonneg (sub_nonneg.mpr hm1) hu.le
  rw [spinThermalPositiveProbability_eq, spinThermalNegativeProbability_eq, spinBathLower]
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · exact hmu
  · nlinarith

/-- Real message recursion formed from actual measured conditional probabilities. -/
def spinThermalTreeBP (p : ℕ) (a u : ℝ) (t : NNReal) (y : ℝ) : ℝ :=
  ((1 + (2 * spinThermalPositiveProbability a u t - 1) * y) ^ p -
    (1 + (2 * spinThermalNegativeProbability a u t - 1) * y) ^ p) /
  ((1 + (2 * spinThermalPositiveProbability a u t - 1) * y) ^ p +
    (1 + (2 * spinThermalNegativeProbability a u t - 1) * y) ^ p)

/-- The recursion is the normalized difference of literal conditional likelihood products. -/
theorem spinThermalTreeBP_likelihood (p : ℕ) (a u : ℝ) (t : NNReal) (y : ℝ) :
    spinThermalTreeBP p a u t y =
      ((spinThermalPositiveProbability a u t * (1 + y) +
          (1 - spinThermalPositiveProbability a u t) * (1 - y)) ^ p -
        (spinThermalNegativeProbability a u t * (1 + y) +
          (1 - spinThermalNegativeProbability a u t) * (1 - y)) ^ p) /
      ((spinThermalPositiveProbability a u t * (1 + y) +
          (1 - spinThermalPositiveProbability a u t) * (1 - y)) ^ p +
        (spinThermalNegativeProbability a u t * (1 + y) +
          (1 - spinThermalNegativeProbability a u t) * (1 - y)) ^ p) := by
  have h (v : ℝ) : v * (1 + y) + (1 - v) * (1 - y) = 1 + (2 * v - 1) * y := by ring
  simp only [h, spinThermalTreeBP]

/-- The unbiased message is always a fixed point, including the branch-free case. -/
theorem spinThermalTreeBP_zero (p : ℕ) (a u : ℝ) (t : NNReal) : spinThermalTreeBP p a u t 0 = 0 := by
  simp [spinThermalTreeBP]

/-- The actual analytic derivative is branch number times survival, independent of bath bias. -/
theorem hasDerivAt_spinThermalTreeBP (p : ℕ) (a u : ℝ) (t : NNReal) :
    HasDerivAt (spinThermalTreeBP p a u t) ((p : ℝ) * spinDecayMass a t) 0 := by
  let α := spinThermalPositiveProbability a u t
  let γ := spinThermalNegativeProbability a u t
  have hα : HasDerivAt (fun y : ℝ => 1 + (2 * α - 1) * y) (2 * α - 1) 0 := by
    convert ((hasDerivAt_id 0).const_mul (2 * α - 1)).const_add 1 using 1 <;> first | rfl | simp
  have hγ : HasDerivAt (fun y : ℝ => 1 + (2 * γ - 1) * y) (2 * γ - 1) 0 := by
    convert ((hasDerivAt_id 0).const_mul (2 * γ - 1)).const_add 1 using 1 <;> first | rfl | simp
  have hd : (1 + (2 * α - 1) * (0 : ℝ)) ^ p + (1 + (2 * γ - 1) * 0) ^ p ≠ 0 := by
    simp
  have h := ((hα.pow p).sub (hγ.pow p)).div ((hα.pow p).add (hγ.pow p)) hd
  have hg : α - γ = spinDecayMass a t := spinThermalProbability_gap a u t
  change HasDerivAt (spinThermalTreeBP p a u t) _ 0 at h
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, mul_zero, add_zero, one_pow, mul_one, sub_self, zero_mul, sub_zero] at h
  convert h using 1
  rw [← hg]
  ring

/-- The usual derivative operator agrees with the exact physical multiplier. -/
theorem deriv_spinThermalTreeBP (p : ℕ) (a u : ℝ) (t : NNReal) :
    deriv (spinThermalTreeBP p a u t) 0 = (p : ℝ) * spinDecayMass a t :=
  (hasDerivAt_spinThermalTreeBP p a u t).deriv

/-- Physical tanh messages give strictly positive branch likelihoods. -/
theorem spinThermalTree_likelihood_pos (a u x : ℝ) (t : NNReal) :
    0 < 1 + (2 * spinThermalPositiveProbability a u t - 1) * Real.tanh x ∧
    0 < 1 + (2 * spinThermalNegativeProbability a u t - 1) * Real.tanh x := by
  obtain ⟨hα0, hα1, hγ0, hγ1⟩ := spinThermalProbability_bounds a u t
  have hx0 := Real.neg_one_lt_tanh x
  have hx1 := Real.tanh_lt_one x
  have h (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < 1 + (2 * v - 1) * Real.tanh x := by
    by_cases hx : 0 ≤ Real.tanh x
    · have hh := mul_nonneg hv0 hx
      nlinarith
    · have hh := mul_nonneg (sub_nonneg.mpr hv1) (neg_nonneg.mpr (le_of_not_ge hx))
      nlinarith
  exact ⟨h _ hα0 hα1, h _ hγ0 hγ1⟩

/-- Every finite branching preserves the open physical message interval. -/
theorem spinThermalTreeBP_physical (p : ℕ) (a u x : ℝ) (t : NNReal) :
    |spinThermalTreeBP p a u t (Real.tanh x)| < 1 := by
  obtain ⟨hα, hγ⟩ := spinThermalTree_likelihood_pos a u x t
  have hp := pow_pos hα p
  have hn := pow_pos hγ p
  unfold spinThermalTreeBP
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ (add_pos hp hn)).mpr
    linarith
  · apply (div_lt_iff₀ (add_pos hp hn)).mpr
    linarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
