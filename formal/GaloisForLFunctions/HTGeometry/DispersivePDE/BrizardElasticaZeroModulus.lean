import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiEndpoints
import Mathlib.Tactic

/-!
# Zero-modulus speed-wall degeneration

At `m=0`, choosing `q₀=1/3` lands exactly on the zero-speed wall.  The reconstructed invariants
are `γ²=0`, `ν²=2`; the Jacobi curvature is constant, and its Hasimoto image is an NLS plane wave.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def oneThirdUnit : ℝˣ :=
  Units.mk0 (1 / 3 : ℝ) (by norm_num)

noncomputable def zeroSpeedHelixParameters : Parameters :=
  zeroModulusParameters oneThirdUnit

theorem zeroSpeedHelix_modulus : zeroSpeedHelixParameters.modulus = 0 := by
  rfl

theorem zeroSpeedHelix_q₀ : (zeroSpeedHelixParameters.q₀ : ℝ) = 1 / 3 := by
  rfl

theorem zeroSpeedHelix_gammaSq : gammaSq zeroSpeedHelixParameters = 0 := by
  rw [gammaSq, zeroSpeedHelixParameters, zeroModulusParameters, oneThirdUnit]
  norm_num

theorem zeroSpeedHelix_nuSq : nuSq zeroSpeedHelixParameters = 2 := by
  rw [nuSq, zeroSpeedHelixParameters, zeroModulusParameters, oneThirdUnit]
  norm_num

theorem zeroSpeedHelix_on_speedWall :
    1 + zeroSpeedHelixParameters.modulus =
      3 * (zeroSpeedHelixParameters.q₀ : ℝ) := by
  rw [zeroSpeedHelix_modulus, zeroSpeedHelix_q₀]
  norm_num

theorem zeroSpeedHelix_real_invariants :
    0 ≤ gammaSq zeroSpeedHelixParameters ∧ 0 < nuSq zeroSpeedHelixParameters := by
  rw [zeroSpeedHelix_gammaSq, zeroSpeedHelix_nuSq]
  norm_num

theorem zeroSpeedHelix_dimensionlessCurvature (v : ℝ) :
    jacobiSquaredCurvature zeroSpeedHelixParameters jacobiZeroSystem v = 1 / 3 := by
  simp [jacobiSquaredCurvature, zeroSpeedHelixParameters,
    zeroModulusParameters, oneThirdUnit]

/-- Physical squared curvature reconstructed from `κ²=k₀²q/q₀`. -/
noncomputable def zeroSpeedHelixCurvatureSq (k₀ v : ℝ) : ℝ :=
  k₀ ^ 2 / (1 / 3 : ℝ) *
    jacobiSquaredCurvature zeroSpeedHelixParameters jacobiZeroSystem v

theorem zeroSpeedHelixCurvatureSq_eq (k₀ v : ℝ) :
    zeroSpeedHelixCurvatureSq k₀ v = k₀ ^ 2 := by
  rw [zeroSpeedHelixCurvatureSq, zeroSpeedHelix_dimensionlessCurvature]
  ring

/-- The zero-modulus constant-curvature branch has exactly plane-wave NLS density. -/
theorem planeWave_normSq_eq_zeroSpeedHelixCurvatureSq (D k₀ τ t x v : ℝ) :
    ‖planeWave D k₀ τ t x‖ ^ 2 = zeroSpeedHelixCurvatureSq k₀ v := by
  rw [norm_planeWave_sq, zeroSpeedHelixCurvatureSq_eq]

theorem zeroSpeedHelix_no_motion :
    ¬ ∃ γ : ℝ, γ ≠ 0 ∧ γ ^ 2 = gammaSq zeroSpeedHelixParameters := by
  rw [zeroSpeedHelix_gammaSq]
  rintro ⟨γ, hγ, hsquare⟩
  exact hγ (sq_eq_zero_iff.mp hsquare)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
