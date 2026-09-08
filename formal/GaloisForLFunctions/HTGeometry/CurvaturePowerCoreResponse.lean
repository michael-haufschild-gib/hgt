import GaloisForLFunctions.HTGeometry.RadialPolynomialGravity
import Mathlib.Algebra.Ring.GeomSum

/-!
# Constant-core response for every curvature power

Mechanically specialize arXiv:2608.23600 equations (6), (7), (15) to the actual
quadratic core metric. Derive the source from the action R+βR^(n+2), then feed
that source to the corpus's regular radial polynomial inverse. The quadratic
model cancels, the cubic and quartic sources have opposite signs on positive
cores, and the corrected trace has an exact β² factor, not an assumed O(β²).
Here n is the excess over the quadratic power; all n≥0 are handled together.
-/
noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.HTGeometry

/-- Every power at least two, parameterized without a lower-bound hypothesis. -/
def curvaturePowerAction (n : ℕ) (β R : ℝ) : ℝ := R + β * R ^ (n + 2)

theorem curvaturePowerAction_hasDerivAt (n : ℕ) (β R : ℝ) :
    HasDerivAt (curvaturePowerAction n β) (1 + (n + 2 : ℝ) * β * R ^ (n + 1)) R := by
  have h := (hasDerivAt_id R).add (((hasDerivAt_id R).pow (n + 2)).const_mul β)
  simp only [Pi.add_def, id_eq] at h
  apply h.congr_deriv
  simp only [mul_one, show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Constant Einstein-core tt field component from f'G+(f'R-f)/2. -/
def curvaturePowerFieldTT (n : ℕ) (β R : ℝ) : ℝ :=
  deriv (curvaturePowerAction n β) R * (-R / 4) +
    (deriv (curvaturePowerAction n β) R * R - curvaturePowerAction n β R) / 2

/-- Constant-curvature specialization of the trace identity f'R-2f. -/
def curvaturePowerTrace (n : ℕ) (β R : ℝ) : ℝ :=
  deriv (curvaturePowerAction n β) R * R - 2 * curvaturePowerAction n β R

/-- Equation (6) collapses to a single exact power-law correction. -/
theorem curvaturePowerFieldTT_eq (n : ℕ) (β R : ℝ) :
    curvaturePowerFieldTT n β R = -R / 4 + n * β * R ^ (n + 2) / 4 := by
  unfold curvaturePowerFieldTT
  rw [(curvaturePowerAction_hasDerivAt n β R).deriv]
  unfold curvaturePowerAction
  simp only [pow_succ]
  ring

/-- Equation (7) on a constant scalar, derived from the action. -/
theorem curvaturePowerTrace_eq (n : ℕ) (β R : ℝ) :
    curvaturePowerTrace n β R = -R + n * β * R ^ (n + 2) := by
  unfold curvaturePowerTrace
  rw [(curvaturePowerAction_hasDerivAt n β R).deriv]
  unfold curvaturePowerAction
  simp only [pow_succ]
  ring

theorem curvaturePowerTrace_field_consistency (n : ℕ) (β R : ℝ) :
    curvaturePowerTrace n β R = 4 * curvaturePowerFieldTT n β R := by
  rw [curvaturePowerTrace_eq, curvaturePowerFieldTT_eq]
  ring

/-- The source is extracted by differentiating the actual field formula in β. -/
def curvaturePowerCoreSource (n : ℕ) (c : ℝ) : ℝ :=
  deriv (fun β => curvaturePowerFieldTT n β (-12 * c) / (8 * Real.pi)) 0

theorem curvaturePowerCoreSource_eq (n : ℕ) (c : ℝ) :
    curvaturePowerCoreSource n c = n * (-12 * c) ^ (n + 2) / (32 * Real.pi) := by
  unfold curvaturePowerCoreSource
  have he : (fun β => curvaturePowerFieldTT n β (-12 * c) / (8 * Real.pi)) =
      (fun β => (-(-12 * c) / 4 + n * β * (-12 * c) ^ (n + 2) / 4) / (8 * Real.pi)) := by
    funext β
    rw [curvaturePowerFieldTT_eq]
  rw [he]
  have h := (((((hasDerivAt_id (0 : ℝ)).const_mul (n : ℝ)).mul_const
    ((-12 * c) ^ (n + 2))).div_const 4).const_add (-(-12 * c) / 4)).div_const (8 * Real.pi)
  simp only [id_eq] at h
  rw [h.deriv]
  field_simp
  ring

/-- Feed the extracted source to the regular integral inverse, rather than posit its coefficient. -/
theorem curvaturePowerCoreSource_radial_inverse (n : ℕ) (c : ℝ) :
    radialPolynomialCorrection (C (curvaturePowerCoreSource n c)) =
      C (n * (-12 * c) ^ (n + 2) / 12) * X ^ 2 := by
  rw [radialPolynomialCorrection_constant, curvaturePowerCoreSource_eq]
  congr 2
  field_simp
  ring

/-- The polynomial inverse gives the exact first-order core metric family. -/
theorem curvaturePowerCore_corrected_metric (n : ℕ) (c β : ℝ) :
    radialCorrectedMetric (quadraticCoreMetric c) (C (curvaturePowerCoreSource n c)) β =
      quadraticCoreMetric (c - β * n * (-12 * c) ^ (n + 2) / 12) := by
  rw [quadraticCoreMetric_correction, curvaturePowerCoreSource_eq]
  congr 1
  field_simp
  ring

/-- Actual curvature of the corrected metric realizes the predicted linearized trace shift. -/
theorem curvaturePowerCore_corrected_ricci (n : ℕ) (c β t : ℝ) :
    radialRicciScalar
        (radialCorrectedMetric (quadraticCoreMetric c) (C (curvaturePowerCoreSource n c)) β) (Real.exp t) =
      -12 * c + β * n * (-12 * c) ^ (n + 2) := by
  rw [curvaturePowerCore_corrected_metric, quadraticCoreMetric_ricci]
  ring

/-- Curvature update induced by the constructed regular inverse. -/
def curvaturePowerUpdatedScalar (n : ℕ) (β R : ℝ) : ℝ := R + β * n * R ^ (n + 2)

/-- Exact residual: the omitted contribution is a difference of powers times β. -/
theorem curvaturePowerTrace_residual (n : ℕ) (β R : ℝ) :
    curvaturePowerTrace n β (curvaturePowerUpdatedScalar n β R) + R =
      β * n * ((curvaturePowerUpdatedScalar n β R) ^ (n + 2) - R ^ (n + 2)) := by
  rw [curvaturePowerTrace_eq]
  unfold curvaturePowerUpdatedScalar
  ring

/-- Dependency-closed second-order remainder, valid even where the two curvatures coincide. -/
theorem curvaturePowerTrace_residual_quadratic (n : ℕ) (β R : ℝ) :
    curvaturePowerTrace n β (curvaturePowerUpdatedScalar n β R) + R =
      β ^ 2 * (n : ℝ) ^ 2 * R ^ (n + 2) *
        ∑ i ∈ range (n + 2), (curvaturePowerUpdatedScalar n β R) ^ i * R ^ (n + 2 - 1 - i) := by
  rw [curvaturePowerTrace_residual, ← geom_sum₂_mul]
  unfold curvaturePowerUpdatedScalar
  ring

/-- The quadratic model is exactly unchanged on every constant-curvature core. -/
theorem curvaturePowerCore_quadratic_source (c : ℝ) : curvaturePowerCoreSource 0 c = 0 := by
  rw [curvaturePowerCoreSource_eq]
  simp

theorem curvaturePowerCore_quadratic_metric (c β : ℝ) :
    radialCorrectedMetric (quadraticCoreMetric c) (C (curvaturePowerCoreSource 0 c)) β =
      quadraticCoreMetric c := by
  rw [curvaturePowerCore_corrected_metric]
  simp

theorem curvaturePowerTrace_quadratic_exact (β R : ℝ) : curvaturePowerTrace 0 β R = -R := by
  rw [curvaturePowerTrace_eq]
  simp

/-- Cubic and quartic models expose opposite near-core correction directions. -/
theorem curvaturePowerCore_cubic_source (c : ℝ) :
    curvaturePowerCoreSource 1 c = -54 * c ^ 3 / Real.pi := by
  rw [curvaturePowerCoreSource_eq]
  norm_num
  ring

theorem curvaturePowerCore_quartic_source (c : ℝ) :
    curvaturePowerCoreSource 2 c = 1296 * c ^ 4 / Real.pi := by
  rw [curvaturePowerCoreSource_eq]
  norm_num
  ring

theorem curvaturePowerCore_cubic_negative (k : ℝ) : curvaturePowerCoreSource 1 (Real.exp k) < 0 := by
  rw [curvaturePowerCore_cubic_source]
  apply div_neg_of_neg_of_pos _ Real.pi_pos
  have h : 0 < 54 * Real.exp k ^ 3 := by positivity
  linarith

theorem curvaturePowerCore_quartic_positive (k : ℝ) : 0 < curvaturePowerCoreSource 2 (Real.exp k) := by
  rw [curvaturePowerCore_quartic_source]
  positivity

/-- Full algebraic classification of constant-curvature vacuum trace roots. -/
theorem curvaturePowerTrace_vacuum_iff (n : ℕ) (β R : ℝ) :
    curvaturePowerTrace n β R = 0 ↔ R = 0 ∨ (n : ℝ) * β * R ^ (n + 1) = 1 := by
  rw [curvaturePowerTrace_eq]
  have he : -R + n * β * R ^ (n + 2) = R * ((n : ℝ) * β * R ^ (n + 1) - 1) := by
    rw [pow_succ]
    ring
  rw [he, mul_eq_zero, sub_eq_zero]

/-- Quadratic vacuum trace has no nonzero constant-curvature root. -/
theorem curvaturePowerTrace_quadratic_vacuum (β R : ℝ) :
    curvaturePowerTrace 0 β R = 0 ↔ R = 0 := by
  rw [curvaturePowerTrace_quadratic_exact, neg_eq_zero]

end GaloisForLFunctions.HTGeometry
