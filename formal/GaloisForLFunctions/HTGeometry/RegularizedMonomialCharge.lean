import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Regularized monomial divisor charge

The smooth logarithmic factor `log (|z|^(2m) + ε²) / 2` has explicit radial flux.
For every positive radius that flux tends to the monomial multiplicity as `ε → 0`.
Geometric curvature integrals and winding are connected in downstream modules.
-/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace HTGeometry.RegularizedMonomialCharge

def logFactor (m : ℕ) (ε : ℝ) (z : ℂ) : ℝ :=
  Real.log ((‖z‖ ^ 2) ^ m + ε ^ 2) / 2

theorem denominator_pos (m : ℕ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    0 < (‖z‖ ^ 2) ^ m + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (pow_nonneg (sq_nonneg _) _) (sq_pos_of_ne_zero hε)

theorem contDiff_logFactor (m : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (logFactor m ε) :=
  (((contDiff_norm_sq ℝ).pow m).add contDiff_const).log
    (fun z => (denominator_pos m hε z).ne') |>.div_const 2

theorem fderiv_logFactor_radial (m : ℕ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    fderiv ℝ (logFactor m ε) z z =
      (m : ℝ) * (‖z‖ ^ 2) ^ m / ((‖z‖ ^ 2) ^ m + ε ^ 2) := by
  have hd := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.pow m).add_const (ε ^ 2)).log
    (denominator_pos m hε z).ne').mul_const (1/2 : ℝ)
  change fderiv ℝ (fun z : ℂ => Real.log ((‖z‖ ^ 2) ^ m + ε ^ 2) / 2) z z = _
  have he : (fun z : ℂ => Real.log ((‖z‖ ^ 2) ^ m + ε ^ 2) / 2) =
      (fun z : ℂ => Real.log ((‖z‖ ^ 2) ^ m + ε ^ 2) * (1/2 : ℝ)) := by
    funext z; ring
  rw [he, hd.fderiv]
  have hinner : (innerSL ℝ z) z = ‖z‖^2 := real_inner_self_eq_norm_sq z
  simp only [smul_apply, smul_eq_mul, hinner]
  cases m with
  | zero => simp
  | succ m =>
      simp only [Nat.succ_sub_one, pow_succ, Nat.cast_add, Nat.cast_one]
      ring

theorem fderiv_logFactor_unit (m : ℕ) {ε : ℝ} (hε : ε ≠ 0)
    {z : ℂ} (hz : ‖z‖ = 1) :
    fderiv ℝ (logFactor m ε) z z = (m : ℝ) / (1 + ε ^ 2) := by
  rw [fderiv_logFactor_radial m hε z, hz]
  simp

def charge (m : ℕ) (ε R : ℝ) : ℝ :=
  (m : ℝ) * (R ^ 2) ^ m / ((R ^ 2) ^ m + ε ^ 2)

theorem tendsto_charge (m : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => charge m ε R) (𝓝 0) (𝓝 (m : ℝ)) := by
  have hd : (R ^ 2) ^ m ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hR.ne')
  have h := (tendsto_const_nhds (x := (m : ℝ) * (R^2)^m)).div (tendsto_const_nhds.add (tendsto_id.pow 2))
    (show (R ^ 2) ^ m + (0 : ℝ) ^ 2 ≠ 0 by simpa using hd)
  convert h using 1
  · funext ε; rfl
  · simp [hd]

end HTGeometry.RegularizedMonomialCharge
