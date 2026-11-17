import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatProbeDissipation
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatRootContraction

/-!
# Square-root potential tests in the actual Gamma domain

Applying `sqrt (2χ)` to finite signed probe profiles preserves every
half-line energy-domain condition. Its squared physical mass is exactly
twice the integrated potential, while its positive Lévy energy contracts.
Consequently the Gamma form contracts after retaining its precise mass
correction; no positivity of the uncentered Gamma form is presumed.
-/

open MeasureTheory Set Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower
noncomputable section

/-- The square-root flat potential of an actual finite signed probe profile. -/
def rootProbeSum (p c : ℕ → ℝ) (n : ℕ) : ℝ → ℝ := rootPotential ∘ probeSum p c n

/-- The complete Gamma, support, physical and exponential-weight domain is preserved. -/
theorem rootProbeSum_domain (p c : ℕ → ℝ) (n : ℕ) :
    CriticalHalfLineEnergyDomain (rootProbeSum p c n) :=
  (probeSum_domain p c n).comp_contraction rootPotential_contraction rootPotential_zero

/-- The physical mass of the new test is the integrated flat convex energy exactly. -/
theorem rootProbeSum_mass (p c : ℕ → ℝ) (n : ℕ) :
    (∫ u, rootProbeSum p c n u ^ 2) = 2 * ∫ u, potential (probeSum p c n u) := by
  simp only [rootProbeSum, Function.comp_apply, rootPotential_sq, integral_const_mul]

/-- Every translated jump of the transformed profile has no larger integrated square. -/
theorem rootProbeSum_jump_bound (p c : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (∫ u, (rootProbeSum p c n u - rootProbeSum p c n (u + x)) ^ 2) ≤
      ∫ u, (probeSum p c n u - probeSum p c n (u + x)) ^ 2 := by
  have hf := (probeSum_domain p c n).memLp_real
  have hr := (rootProbeSum_domain p c n).memLp_real
  apply integral_mono
    (integrable_sq_of_memLp (hr.sub (memLp_two_shift hr x)))
    (integrable_sq_of_memLp (hf.sub (memLp_two_shift hf x)))
  intro u
  have h := rootPotential_contraction.norm_sub_le (probeSum p c n u) (probeSum p c n (u + x))
  simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs] at h
  have hs := mul_nonneg (sub_nonneg.mpr h)
    (add_nonneg (abs_nonneg (probeSum p c n u - probeSum p c n (u + x)))
      (abs_nonneg (rootPotential (probeSum p c n u) - rootPotential (probeSum p c n (u + x)))))
  change (rootPotential (probeSum p c n u) - rootPotential (probeSum p c n (u + x))) ^ 2 ≤ _
  nlinarith only [hs, sq_abs (probeSum p c n u - probeSum p c n (u + x)),
    sq_abs (rootPotential (probeSum p c n u) - rootPotential (probeSum p c n (u + x)))]

/-- The full positive Gamma jump energy contracts for every finite real probe combination. -/
theorem rootProbeSum_levy_bound (p c : ℕ → ℝ) (n : ℕ) :
    levyEnergy (rootProbeSum p c n) ≤ levyEnergy (probeSum p c n) := by
  apply integral_mono_ae (rootProbeSum_domain p c n).integrableOn_levyIntegrand
    (probeSum_domain p c n).integrableOn_levyIntegrand
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_le_mul_of_nonneg_left (rootProbeSum_jump_bound p c n x) (archLevyDensity_pos hx).le

/-- The exact mass-centered Gamma inequality, with the flat potential retained explicitly. -/
theorem rootProbeSum_centered_gamma_bound (p c : ℕ → ℝ) (n : ℕ) :
    archForm (rootProbeSum p c n) -
        4 * gammaHardyPhaseRate 0 * (∫ u, potential (probeSum p c n u)) ≤
      archForm (probeSum p c n) -
        2 * gammaHardyPhaseRate 0 * (∫ u, probeSum p c n u ^ 2) := by
  rw [(rootProbeSum_domain p c n).archForm_eq_levyEnergy,
    (probeSum_domain p c n).archForm_eq_levyEnergy, rootProbeSum_mass]
  linarith only [rootProbeSum_levy_bound p c n]

#print axioms rootProbeSum_domain
#print axioms rootProbeSum_mass
#print axioms rootProbeSum_levy_bound
#print axioms rootProbeSum_centered_gamma_bound
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
