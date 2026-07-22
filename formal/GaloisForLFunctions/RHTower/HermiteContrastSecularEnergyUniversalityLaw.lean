import GaloisForLFunctions.RHTower.HermiteContrastLp
import GaloisForLFunctions.RHTower.LadderLimitSecular
import GaloisForLFunctions.RHTower.LadderAdjacentScaleSeparation

/-!
# Hermite contrast secular-energy universality

The squared Hilbert norm of the canonical depth contrast, normalized by its next Hermite weight
and accumulated mass, recovers the ladder coordinate `Qₖ/Qₖ₊₁`.  Thus one scalar defined from
the orthogonal `ℓ²` geometry is simultaneously the unique zero of the limiting secular law and the
coordinate whose consecutive ratio governs every aperture-rescaled adjacent-rung limit.
-/

open Filter

namespace RHTower

noncomputable section

/-- Secular coordinate recovered from the Hilbert norm of the canonical contrast, its next
Hermite weight, and the accumulated next-depth mass. -/
def hermiteContrastSecularEnergyCoordinate (k : ℕ) : ℝ :=
  (‖hermiteContrastLp k‖ ^ 2 * constrainedProlateHermiteWeight (k + 1)) /
    (Real.sqrt 2 * constrainedProlateHermiteWeightSum (k + 1) ^ 2)

/-- Hilbert normalization recovers the original ladder mass ratio exactly. -/
theorem hermiteContrastSecularEnergyCoordinate_eq_theta (k : ℕ) :
    hermiteContrastSecularEnergyCoordinate k = constrainedProlateHermiteTheta k := by
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hweight : constrainedProlateHermiteWeight (k + 1) ≠ 0 :=
    (constrainedProlateHermiteWeight_pos (k + 1)).ne'
  have hsum : constrainedProlateHermiteWeightSum (k + 1) ≠ 0 :=
    (constrainedProlateHermiteWeightSum_pos (k + 1)).ne'
  rw [hermiteContrastSecularEnergyCoordinate, norm_sq_hermiteContrastLp_eq,
    constrainedProlateHermiteTheta]
  field_simp

/-- **Hermite secular-energy universality law.**  Hilbert contrast energy is the unique interior
zero of the limiting secular law, and consecutive energy coordinates give every
aperture-rescaled adjacent-rung limit. -/
theorem hermiteContrastSecularEnergyUniversality (k : ℕ) :
    hermiteContrastSecularEnergyCoordinate k ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
        (ladderLimitSecular (constrainedProlateHermiteWeightSum k)
          (constrainedProlateHermiteWeight (k + 1)) x = 0 ↔
            x = hermiteContrastSecularEnergyCoordinate k)) ∧
      ∀ (A : ℕ → ℝ), (∀ j, 0 < A j) →
        Tendsto (fun lam : ℝ =>
            (ladderTwoModeRoot A (k + 1) lam / ladderTwoModeRoot A k lam) / lam ^ 8)
          atTop (nhds
            ((hermiteContrastSecularEnergyCoordinate (k + 1) /
                hermiteContrastSecularEnergyCoordinate k) *
              (A (k + 2) / A (k + 1)))) := by
  have hcoord := hermiteContrastSecularEnergyCoordinate_eq_theta
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoord]
    exact constrainedProlateHermiteTheta_mem_Ioo k
  · intro x hx
    constructor
    · intro hzero
      rw [hcoord]
      exact ladderLimitSecular_theta_unique hx hzero
    · intro hxeq
      rw [hxeq, hcoord]
      exact ladderLimitSecular_theta_root k
  · intro A hA
    simpa only [hcoord] using ladder_adjacent_ratio_scaled_tendsto hA k

end

end RHTower
