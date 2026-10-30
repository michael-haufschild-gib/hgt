import GaloisForLFunctions.CompletedArithmeticForms.ConductorHeatThreshold
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# The completed conductor Green operator

The reciprocal completed energies define a compact injective operator on
the arithmetic coordinate space. Its exact norm is the pole inverse cost,
although no positive integer power of its coordinate eigenvalues is summable.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.CompletedArithmeticForms

open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  HTGeometry.LpDiagonal

/-- The actual reciprocal completed-conductor multipliers. -/
def tiltedConductorGreenWeight (c : ℝ) (n : ℕ) : ℂ :=
  ((completedConductorEnergy tiltedUnitSpline c (n + 1))⁻¹ : ℝ)

theorem norm_tiltedConductorGreenWeight {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ‖tiltedConductorGreenWeight c n‖ =
      (completedConductorEnergy tiltedUnitSpline c (n + 1))⁻¹ := by
  rw [tiltedConductorGreenWeight, Complex.norm_real, Real.norm_of_nonneg]
  exact (inv_pos.mpr (tiltedWeilConductorEnergy_pos hc (Nat.succ_pos n))).le

/-- The pole pays every coordinate in the infinite arithmetic Green completion. -/
theorem norm_tiltedConductorGreenWeight_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ‖tiltedConductorGreenWeight c n‖ ≤ tiltedWeilInverseCost c := by
  rw [norm_tiltedConductorGreenWeight hc, tiltedWeilInverseCost]
  exact (inv_le_inv₀ (tiltedWeilConductorEnergy_pos hc (Nat.succ_pos n))
    (tiltedWeilGroundEnergy_pos hc)).mpr
      (completedConductorEnergy_one_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos hc (Nat.succ_pos n))

/-- The Green completion of the exact arithmetic coordinate energies on complex `ℓ²`. -/
def tiltedConductorGreen (c : ℝ) (hc : 0 < c) : LpTwo ℕ →L[ℂ] LpTwo ℕ :=
  lpDiag (tiltedConductorGreenWeight c) (tiltedWeilInverseCost c)
    (tiltedWeilInverseCost_pos hc).le (norm_tiltedConductorGreenWeight_le hc)

@[simp] theorem tiltedConductorGreen_apply (c : ℝ) (hc : 0 < c) (v : LpTwo ℕ) (n : ℕ) :
    (tiltedConductorGreen c hc v) n = tiltedConductorGreenWeight c n * v n := rfl

/-- Every arithmetic coordinate is an exact Green eigenvector. -/
theorem tiltedConductorGreen_single (c : ℝ) (hc : 0 < c) (n : ℕ) :
    tiltedConductorGreen c hc (lp.single 2 n (1 : ℂ)) =
      tiltedConductorGreenWeight c n • lp.single 2 n (1 : ℂ) :=
  lpDiag_single _ _ _ _ n

/-- The exact infinite inverse norm equals the sharp finite-horizon limiting cost. -/
theorem norm_tiltedConductorGreen (c : ℝ) (hc : 0 < c) :
    ‖tiltedConductorGreen c hc‖ = tiltedWeilInverseCost c := by
  apply le_antisymm (norm_lpDiag_le _ _ _ _)
  have h := (tiltedConductorGreen c hc).le_opNorm (lp.single 2 0 (1 : ℂ))
  rw [tiltedConductorGreen_single, norm_smul, lp.norm_single (by norm_num), norm_one,
    mul_one, mul_one, norm_tiltedConductorGreenWeight hc] at h
  simpa only [Nat.zero_add, tiltedWeilInverseCost] using h

/-- Properness of the actual conductor energies gives a compact arithmetic Green operator. -/
theorem isCompactOperator_tiltedConductorGreen (c : ℝ) (hc : 0 < c) :
    IsCompactOperator (tiltedConductorGreen c hc) := by
  apply isCompactOperator_lpDiag
  rw [Nat.cofinite_eq_atTop]
  simpa only [norm_tiltedConductorGreenWeight hc] using
    tendsto_completedConductorEnergy_inv_zero tiltedUnitSpline hc

/-- Completion introduces no radical: every coordinate weight is strictly positive. -/
theorem tiltedConductorGreen_injective (c : ℝ) (hc : 0 < c) :
    Function.Injective (tiltedConductorGreen c hc) := by
  intro v w h
  apply lp.ext
  funext n
  have he := congrArg (fun z : LpTwo ℕ => z n) h
  rw [tiltedConductorGreen_apply, tiltedConductorGreen_apply] at he
  have hn : tiltedConductorGreenWeight c n ≠ 0 := by
    change (((completedConductorEnergy tiltedUnitSpline c (n + 1))⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast (inv_ne_zero (tiltedWeilConductorEnergy_pos hc (Nat.succ_pos n)).ne')
  exact mul_left_cancel₀ hn he

/-- Compactness does not pay even one integer power sum of the actual Green coordinate spectrum. -/
theorem not_summable_tiltedConductorGreen_coordinate_power (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ¬ Summable (fun n : ℕ => ‖tiltedConductorGreen c hc (lp.single 2 n (1 : ℂ))‖ ^ k) := by
  simpa only [tiltedConductorGreen_single, norm_smul, lp.norm_single (by norm_num),
    norm_one, mul_one, norm_tiltedConductorGreenWeight hc] using
      not_summable_tiltedWeil_inverse_energy_pow hc k

#print axioms norm_tiltedConductorGreen
#print axioms isCompactOperator_tiltedConductorGreen
#print axioms tiltedConductorGreen_injective
#print axioms not_summable_tiltedConductorGreen_coordinate_power

end GaloisForLFunctions.CompletedArithmeticForms
