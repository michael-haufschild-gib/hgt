import Mathlib

/-!
# Gaussian Cramer--Rao energy laws

This file audits the energy formulas in arXiv:2608.25870, Eqs. (9)--(11).
The lower bound obtained from `C_opt >= 1` is not by itself sufficient to
prepare the claimed optimal probe: its squeezing already has a larger energy
cost.  A closed symbolic counterexample is given at `r = log 5 / 4`.
-/

namespace HTGeometry

noncomputable section

/-- Optimal momentum-squeezing magnitude stated before Eq. (9). -/
def gaussianOptimalProbeSqueezing (r : ℝ) : ℝ :=
  Real.log (2 * Real.exp (4 * r) - 1) / 4

/-- Energy consumed by the squeezing part of the claimed optimal probe. -/
def gaussianOptimalProbeSqueezingEnergy (r : ℝ) : ℝ :=
  Real.sinh (gaussianOptimalProbeSqueezing r) ^ 2

/-- Eq. (10), obtained in the paper by imposing `C_opt >= 1`. -/
def gaussianPublishedMinimumEnergy (r : ℝ) : ℝ :=
  (Real.exp (2 * r) * (2 - Real.sqrt (2 - Real.exp (-4 * r))) - 1) / 2

/-- Eq. (11), the published inverse range associated with Eq. (10). -/
def gaussianPublishedMaximumEncoding (energy : ℝ) : ℝ :=
  Real.log (1 + 2 * energy + Real.sqrt (2 * energy * (1 + energy))) / 2

/-- Corrected simultaneous requirement: precision threshold and probe preparation cost. -/
def gaussianFeasibleMinimumEnergy (r : ℝ) : ℝ :=
  max (gaussianPublishedMinimumEnergy r) (gaussianOptimalProbeSqueezingEnergy r)

/-- Exact positive encoding strength used for the symbolic energy audit. -/
def gaussianEnergyAuditEncoding : ℝ := Real.log 5 / 4

private theorem exp_half_log_five :
    Real.exp (Real.log 5 / 2) = Real.sqrt 5 := by
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (Real.exp_pos _).le]
  calc
    (5 : ℝ) = Real.exp (Real.log 5) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 5)).symm
    _ = Real.exp (Real.log 5 / 2 + Real.log 5 / 2) := by congr 1; ring
    _ = Real.exp (Real.log 5 / 2) * Real.exp (Real.log 5 / 2) :=
      Real.exp_add _ _

private theorem exp_half_log_three :
    Real.exp (Real.log 3 / 2) = Real.sqrt 3 := by
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (Real.exp_pos _).le]
  calc
    (3 : ℝ) = Real.exp (Real.log 3) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 3)).symm
    _ = Real.exp (Real.log 3 / 2 + Real.log 3 / 2) := by congr 1; ring
    _ = Real.exp (Real.log 3 / 2) * Real.exp (Real.log 3 / 2) :=
      Real.exp_add _ _

/-- At the audit point the paper's optimal squeezing is `log 3 / 2`. -/
theorem gaussianOptimalProbeSqueezing_at_auditEncoding :
    gaussianOptimalProbeSqueezing gaussianEnergyAuditEncoding = Real.log 3 / 2 := by
  rw [gaussianOptimalProbeSqueezing, gaussianEnergyAuditEncoding]
  rw [show 4 * (Real.log 5 / 4) = Real.log 5 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  rw [show (2 : ℝ) * 5 - 1 = 3 ^ 2 by norm_num, Real.log_pow]
  ring

/-- Preparing the stated optimal squeezing at the audit point costs exactly `1/3`. -/
theorem gaussianOptimalProbeSqueezingEnergy_at_auditEncoding :
    gaussianOptimalProbeSqueezingEnergy gaussianEnergyAuditEncoding = 1 / 3 := by
  rw [gaussianOptimalProbeSqueezingEnergy,
    gaussianOptimalProbeSqueezing_at_auditEncoding, Real.sinh_eq]
  rw [exp_half_log_three]
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [Real.exp_neg, exp_half_log_three]
  field_simp [ne_of_gt hsqrt3_pos]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- Eq. (10) gives only `sqrt 5 - 2` energy at the same encoding point. -/
theorem gaussianPublishedMinimumEnergy_at_auditEncoding :
    gaussianPublishedMinimumEnergy gaussianEnergyAuditEncoding = Real.sqrt 5 - 2 := by
  rw [gaussianPublishedMinimumEnergy, gaussianEnergyAuditEncoding]
  rw [show 2 * (Real.log 5 / 4) = Real.log 5 / 2 by ring,
    show -4 * (Real.log 5 / 4) = -Real.log 5 by ring,
    exp_half_log_five, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_term : Real.sqrt (2 - (5 : ℝ)⁻¹) = 3 / Real.sqrt 5 := by
    rw [show (2 : ℝ) - 5⁻¹ = 9 / 5 by norm_num,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9),
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsqrt_term]
  field_simp [ne_of_gt hsqrt5_pos]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

/-- Eq. (10)'s energy is strictly below the squeezing cost of its alleged optimal probe. -/
theorem gaussianPublishedMinimumEnergy_lt_optimalProbeSqueezingEnergy_at_auditEncoding :
    gaussianPublishedMinimumEnergy gaussianEnergyAuditEncoding <
      gaussianOptimalProbeSqueezingEnergy gaussianEnergyAuditEncoding := by
  rw [gaussianPublishedMinimumEnergy_at_auditEncoding,
    gaussianOptimalProbeSqueezingEnergy_at_auditEncoding]
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

/-- Closed refutation of the prose after Eq. (10): satisfying that displayed
energy condition does not imply enough energy to realize the optimal squeezing. -/
theorem gaussianPublishedEnergyCondition_does_not_imply_probeFeasibility :
    let r := gaussianEnergyAuditEncoding
    let energy := gaussianPublishedMinimumEnergy r
    gaussianPublishedMinimumEnergy r ≤ energy ∧
      energy < gaussianOptimalProbeSqueezingEnergy r := by
  dsimp
  exact ⟨le_rfl,
    gaussianPublishedMinimumEnergy_lt_optimalProbeSqueezingEnergy_at_auditEncoding⟩

/-- Corrected energy requirement always contains the paper's precision threshold. -/
theorem gaussianPublishedMinimumEnergy_le_feasibleMinimumEnergy (r : ℝ) :
    gaussianPublishedMinimumEnergy r ≤ gaussianFeasibleMinimumEnergy r :=
  le_max_left _ _

/-- Corrected energy requirement always contains the squeezing preparation cost. -/
theorem gaussianOptimalProbeSqueezingEnergy_le_feasibleMinimumEnergy (r : ℝ) :
    gaussianOptimalProbeSqueezingEnergy r ≤ gaussianFeasibleMinimumEnergy r :=
  le_max_right _ _

/-- At the audit point physical feasibility corrects Eq. (10) upward to `1/3`. -/
theorem gaussianFeasibleMinimumEnergy_at_auditEncoding :
    gaussianFeasibleMinimumEnergy gaussianEnergyAuditEncoding = 1 / 3 := by
  rw [gaussianFeasibleMinimumEnergy, max_eq_right,
    gaussianOptimalProbeSqueezingEnergy_at_auditEncoding]
  exact le_of_lt
    gaussianPublishedMinimumEnergy_lt_optimalProbeSqueezingEnergy_at_auditEncoding

/-- The corrected requirement is strictly stronger than Eq. (10) at the audit point. -/
theorem gaussianPublishedMinimumEnergy_lt_feasibleMinimumEnergy_at_auditEncoding :
    gaussianPublishedMinimumEnergy gaussianEnergyAuditEncoding <
      gaussianFeasibleMinimumEnergy gaussianEnergyAuditEncoding := by
  rw [gaussianFeasibleMinimumEnergy_at_auditEncoding]
  simpa [gaussianOptimalProbeSqueezingEnergy_at_auditEncoding] using
    gaussianPublishedMinimumEnergy_lt_optimalProbeSqueezingEnergy_at_auditEncoding

end

end HTGeometry
