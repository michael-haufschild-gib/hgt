/-
# Chen--Gupta--Li smooth character-packet kernel

Chen--Gupta--Li's fourth-moment argument replaces a sharp logarithmic cutoff
by a compact smooth function which is one on the unit core.  Its Fourier
multiplier, evaluated at an additive pair-frequency, decays faster than every
power.  This module provides that canonical cutoff and the exact scaled
multiplier used by the finite packet model.

No RH, GRH, smoothness, energy, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFourthMomentNear
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily
import GaloisForLFunctions.HTGeometry.CompactTestTransformOrder

open Complex MeasureTheory Set Filter

open scoped ContDiff

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Canonical smooth cutoff: it is one on `[-1, 1]` and vanishes outside
`[-2, 2]`. -/
noncomputable def cglCanonicalSmoothCutoff : ℝ → ℂ :=
  fun τ => ((widthBump (by norm_num : (0 : ℝ) < 2) τ : ℝ) : ℂ)

/-- The canonical CGL cutoff is smooth to every order. -/
theorem contDiff_cglCanonicalSmoothCutoff : ContDiff ℝ ∞ cglCanonicalSmoothCutoff := by
  unfold cglCanonicalSmoothCutoff
  exact Complex.ofRealCLM.contDiff.comp (widthBump (by norm_num : (0 : ℝ) < 2)).contDiff

/-- The canonical CGL cutoff is compactly supported. -/
theorem hasCompactSupport_cglCanonicalSmoothCutoff : HasCompactSupport cglCanonicalSmoothCutoff := by
  unfold cglCanonicalSmoothCutoff
  exact (widthBump (by norm_num : (0 : ℝ) < 2)).hasCompactSupport.comp_left
    (g := Complex.ofRealCLM) Complex.ofReal_zero

/-- The cutoff has the unit core required in the CGL smoothing argument. -/
theorem cglCanonicalSmoothCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) :
    cglCanonicalSmoothCutoff x = 1 := by
  unfold cglCanonicalSmoothCutoff
  rw [(widthBump (by norm_num : (0 : ℝ) < 2)).one_of_mem_closedBall]
  · norm_num
  · simpa [widthBump, Real.dist_eq] using hx

/-- The scaled smooth Fourier multiplier at a real additive frequency. -/
noncomputable def cglCharacterPacketSmoothMultiplier (X : NNReal) (δ : ℝ) : ℂ :=
  (X : ℂ) * testTransform cglCanonicalSmoothCutoff (((X : ℝ) * δ : ℝ) : ℂ)

/-- The CGL smooth multiplier has arbitrarily high polynomial decay in the
scaled additive frequency. -/
theorem exists_norm_cglCharacterPacketSmoothMultiplier_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : NNReal, ∀ δ : ℝ,
      ‖cglCharacterPacketSmoothMultiplier X δ‖ ≤
        (X : ℝ) * C / (1 + |(X : ℝ) * δ|) ^ k := by
  obtain ⟨C, hC0, hC⟩ := exists_testTransform_decay_order
    contDiff_cglCanonicalSmoothCutoff hasCompactSupport_cglCanonicalSmoothCutoff 0 0 k
  refine ⟨C, hC0, fun X δ => ?_⟩
  have hzero : ((((X : ℝ) * δ : ℝ) : ℂ)).im ∈ Set.uIcc (0 : ℝ) 0 := by simp
  have h := hC (((X : ℝ) * δ : ℝ) : ℂ) hzero
  have hnorm : ‖(((X : ℝ) * δ : ℝ) : ℂ)‖ = |(X : ℝ) * δ| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [cglCharacterPacketSmoothMultiplier, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from X.2)]
  rw [hnorm] at h
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h (NNReal.zero_le_coe)

end RHTower
