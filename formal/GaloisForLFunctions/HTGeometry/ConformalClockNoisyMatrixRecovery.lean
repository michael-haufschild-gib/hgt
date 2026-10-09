import GaloisForLFunctions.HTGeometry.ConformalClockMatrixRecovery
import GaloisForLFunctions.HTGeometry.ClockGapEnvelopeRecovery

/-!
# Exact noisy recovery for projective matrix clocks

The norm of a projective-panel discrepancy between two real scales of the same
known mass matrix is exactly the absolute scale difference times the mass-panel
norm. Independently varying common scalar defects cancel before taking the norm.
The mass-panel norm vanishes exactly at scalar matrices, including the one-channel
case. This norm is the existing reporter panel's norm, not a spectral-gap surrogate.

Combining that identity with the least Lipschitz envelope gives a complete noisy
feasible-anchor classification on any pseudometric space. Only the scale difference
belongs to the classified Lipschitz class; no regularity of the mass field, reference
scale, or scalar defects is needed. The scales in this theorem are real; strict
positivity of competing physical scales is a separate constraint.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The actual projective reporter panel is complex homogeneous. -/
theorem projectiveDelayPanel_smul {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    projectiveDelayPanel (s • M) = s • projectiveDelayPanel M := by
  funext p
  rcases p with ⟨⟨i, j⟩, hp⟩
  simp only [projectiveDelayPanel, projectiveDelayNormalize_smul, Pi.smul_apply,
    matrixDelayPanel, matrixDelayDiagonal, matrixDelayPlus, matrixDelayImaginary,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The projective panel of the zero matrix is zero in every dimension. -/
theorem projectiveDelayPanel_zero (n : ℕ) :
    projectiveDelayPanel (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  simpa only [zero_smul] using
    projectiveDelayPanel_smul (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0

/-- Exact zero-sensitivity boundary for the observed reporter norm. -/
theorem projectiveDelayPanel_norm_zero_iff_scalar {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ‖projectiveDelayPanel M‖ = 0 ↔ ∃ c : ℂ, M = c • 1 := by
  rw [norm_eq_zero]
  simpa [projectiveDelayPanel_zero] using
    projectiveDelayPanel_mixedClock_eq_iff M 1 0 0 0

/-- Observed noise factors exactly into scale error and mass-panel sensitivity. -/
theorem projectiveMixedClock_noise_exact {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s₁ s₂ : ℝ) (d₁ d₂ : ℂ) :
    ‖projectiveDelayPanel ((s₁ : ℂ) • M + d₁ • 1) -
        projectiveDelayPanel ((s₂ : ℂ) • M + d₂ • 1)‖ =
      |s₁ - s₂| * ‖projectiveDelayPanel M‖ := by
  rw [projectiveDelayPanel_add_scalar, projectiveDelayPanel_add_scalar,
    projectiveDelayPanel_smul, projectiveDelayPanel_smul, ← sub_smul, norm_smul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Eliminate the unknown scale field from noisy projective-clock feasibility. -/
theorem noisyProjectiveClock_feasible_iff {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (baseline : X → ℝ) (d₁ d₂ : X → ℂ) (L epsilon : NNReal) (p : X) (a : ℝ) :
    (∃ other : X → ℝ, LipschitzWith L (fun x => other x - baseline x) ∧
      other p - baseline p = a ∧
      ∀ x, ‖projectiveDelayPanel ((other x : ℂ) • M x + d₁ x • 1) -
        projectiveDelayPanel ((baseline x : ℂ) • M x + d₂ x • 1)‖ ≤ epsilon) ↔
      ∀ x, ‖projectiveDelayPanel (M x)‖ * |a| ≤
        (epsilon : ℝ) + ‖projectiveDelayPanel (M x)‖ * L * dist x p := by
  let g : X → NNReal := fun x => ⟨‖projectiveDelayPanel (M x)‖, norm_nonneg _⟩
  have hg (x : X) : (g x : ℝ) = ‖projectiveDelayPanel (M x)‖ := rfl
  change _ ↔ ∀ x, (g x : ℝ) * |a| ≤ (epsilon : ℝ) + (g x : ℝ) * L * dist x p
  rw [← weightedClockGap_feasible_iff_affine L epsilon g p a]
  constructor
  · rintro ⟨other, hu, ha, hbound⟩
    refine ⟨fun x => other x - baseline x, hu, ha, ?_⟩
    intro x
    have hb := hbound x
    rw [projectiveMixedClock_noise_exact] at hb
    rw [hg x]
    simpa only [mul_comm] using hb
  · rintro ⟨u, hu, ha, hbound⟩
    refine ⟨fun x => baseline x + u x, ?_, ?_, ?_⟩
    · simpa only [add_sub_cancel_left] using hu
    · simpa only [add_sub_cancel_left] using ha
    · intro x
      rw [projectiveMixedClock_noise_exact]
      have hb := hbound x
      rw [hg x] at hb
      simpa only [add_sub_cancel_left, mul_comm] using hb

end GaloisForLFunctions.HTGeometry
