import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Density and pressure identities in higher-dimensional cyclic cosmology

arXiv:2303.04638 uses pressure coefficients four and five in equations
(4) and (12). A phantom substitution `P = -3 rho/2` gives a uniform
coefficient law and identifies the missing density factor in its printed
(13). The loop-density factor of (10) has an exact global square completion,
and its difference from the factor printed in (3) is recorded explicitly.
These are algebraic identities of the displayed model, not derivations of
Einstein's equations or proofs of a cosmological bounce.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Acceleration value in the displayed higher-dimensional Raychaudhuri model. -/
def cyclicRaychaudhuri (d G rho pressure Lambda : ℝ) : ℝ :=
  -(4 * Real.pi * G / 3) * (d * pressure + rho) + Lambda / 3

/-- Uniform phantom-pressure law, retaining the density factor. -/
theorem cyclicRaychaudhuri_phantom (d G rho Lambda : ℝ) :
    cyclicRaychaudhuri d G rho (-(3 / 2) * rho) Lambda =
      (2 * Real.pi * G * rho * (3 * d - 2) + Lambda) / 3 := by
  unfold cyclicRaychaudhuri
  ring

/-- Incrementing the pressure coefficient changes acceleration by exactly one pressure term. -/
theorem cyclicRaychaudhuri_dimension_increment (d G rho pressure Lambda : ℝ) :
    cyclicRaychaudhuri (d + 1) G rho pressure Lambda -
      cyclicRaychaudhuri d G rho pressure Lambda = -(4 * Real.pi * G / 3) * pressure := by
  unfold cyclicRaychaudhuri
  ring

/-- Phantom pressure with nonnegative coupling and density increases acceleration with dimension. -/
theorem cyclicRaychaudhuri_phantom_dimension_mono (d G rho Lambda : ℝ) :
    cyclicRaychaudhuri d (G ^ 2) (rho ^ 2) (-(3 / 2) * rho ^ 2) Lambda ≤
      cyclicRaychaudhuri (d + 1) (G ^ 2) (rho ^ 2) (-(3 / 2) * rho ^ 2) Lambda := by
  have h := cyclicRaychaudhuri_dimension_increment d (G ^ 2) (rho ^ 2)
    (-(3 / 2) * rho ^ 2) Lambda
  have hn : 0 ≤ -(4 * Real.pi * G ^ 2 / 3) * (-(3 / 2) * rho ^ 2) := by
    have hp := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg hp.le (sq_nonneg G)) (sq_nonneg rho)]
  linarith

/-- Exact residual of the missing `rho` in the paper's equation (13). -/
theorem cyclicRaychaudhuri_six_dimensional_residual (G rho Lambda : ℝ) :
    cyclicRaychaudhuri 5 G rho (-(3 / 2) * rho) Lambda -
      (26 * Real.pi * G + Lambda) / 3 = 26 * Real.pi * G * (rho - 1) / 3 := by
  rw [cyclicRaychaudhuri_phantom]
  ring

/-- The printed density-free specialization holds precisely at unit density or zero coupling. -/
theorem cyclicRaychaudhuri_printed_six_dimensional_iff (G rho Lambda : ℝ) :
    cyclicRaychaudhuri 5 G rho (-(3 / 2) * rho) Lambda =
      (26 * Real.pi * G + Lambda) / 3 ↔ G = 0 ∨ rho = 1 := by
  rw [← sub_eq_zero, cyclicRaychaudhuri_six_dimensional_residual]
  simp [div_eq_zero_iff, mul_eq_zero, Real.pi_ne_zero, sub_eq_zero]

/-- The density factor used in the paper's corrected equation (10). -/
def cyclicLoopDensity (critical rho : ℝ) : ℝ := rho * (1 - rho / critical)

/-- Both zero density and critical density are roots, without a division hypothesis. -/
theorem cyclicLoopDensity_roots (critical : ℝ) :
    cyclicLoopDensity critical 0 = 0 ∧ cyclicLoopDensity critical critical = 0 := by
  by_cases h : critical = 0
  · simp [cyclicLoopDensity, h]
  · simp [cyclicLoopDensity, h]

/-- The global upper bound is sharp, with an exact nonnegative deficit. -/
theorem cyclicLoopDensity_square_completion (c rho : ℝ) :
    Real.exp c / 4 - cyclicLoopDensity (Real.exp c) rho =
      (rho - Real.exp c / 2) ^ 2 / Real.exp c := by
  unfold cyclicLoopDensity
  field_simp
  ring

/-- The corrected density can never exceed a quarter of positive critical density. -/
theorem cyclicLoopDensity_le_quarter (c rho : ℝ) :
    cyclicLoopDensity (Real.exp c) rho ≤ Real.exp c / 4 := by
  have h := cyclicLoopDensity_square_completion c rho
  have hn : 0 ≤ (rho - Real.exp c / 2) ^ 2 / Real.exp c := by positivity
  linarith

/-- The upper endpoint is attained exactly at half critical density. -/
theorem cyclicLoopDensity_eq_quarter_iff (c rho : ℝ) :
    cyclicLoopDensity (Real.exp c) rho = Real.exp c / 4 ↔ rho = Real.exp c / 2 := by
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero, cyclicLoopDensity_square_completion]
  simp [div_eq_zero_iff, Real.exp_ne_zero, sub_eq_zero]

/-- Exact discrepancy between the loop factor printed in (3) and the one used in (10). -/
theorem cyclicLoopDensity_printed_discrepancy (critical rho : ℝ) :
    cyclicLoopDensity critical rho - rho * (1 - rho) / critical =
      rho * (1 - 1 / critical) := by
  unfold cyclicLoopDensity
  ring

end GaloisForLFunctions.HTGeometry
