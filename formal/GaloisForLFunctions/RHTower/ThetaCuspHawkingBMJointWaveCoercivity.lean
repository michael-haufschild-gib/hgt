import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! All right-half-plane frequencies have a coercive joint wave form after the exact Laplace rotation. -/
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
namespace RHTower.D4BMJointWave
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The full joint wave form on its constructed domain: derivative energy plus w² scalar mass. -/
def waveFormOperator (J : V →L[ℂ] H) (w : ℂ) : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V +
    (w^2-1) • J.adjoint.comp J

def rotatedWaveOperator (J : V →L[ℂ] H) (w : ℂ) : V →L[ℂ] V :=
  conj w • waveFormOperator J w

/-- Exact form identity before any estimate; all spatial derivative components are retained. -/
theorem waveFormOperator_inner (J : V →L[ℂ] H) (w : ℂ) (u v : V) :
    inner ℂ u (waveFormOperator J w v) = inner ℂ u v +
      (w^2-1)*inner ℂ (J u) (J v) := by
  change inner ℂ u (v+(w^2-1) • J.adjoint (J v)) = _
  rw [inner_add_right,inner_smul_right,J.adjoint_inner_right]

/-- Rotation by conjugate Laplace frequency makes the complete spatial form positive. -/
theorem rotatedWaveOperator_energy (J : V →L[ℂ] H) (w : ℂ) (u : V) :
    (inner ℂ (rotatedWaveOperator J w u) u).re =
      w.re * (‖u‖^2-‖J u‖^2 + Complex.normSq w * ‖J u‖^2) := by
  change (inner ℂ (conj w • waveFormOperator J w u) u).re = _
  rw [inner_smul_left_eq_star_smul]
  simp only [starRingEnd_self_apply, smul_eq_mul]
  have he : inner ℂ (waveFormOperator J w u) u =
      conj (inner ℂ u (waveFormOperator J w u)) := (inner_conj_symm _ _).symm
  rw [he,waveFormOperator_inner,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp [pow_two,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

def waveCoercivity (w : ℂ) : ℝ := w.re * min 1 (Complex.normSq w)

theorem waveCoercivity_pos (w : ℂ) (hw : 0 < w.re) : 0 < waveCoercivity w := by
  apply mul_pos hw
  apply lt_min (by norm_num)
  exact Complex.normSq_pos.mpr (fun h => by simp [h] at hw)

/-- Quantitative coercivity throughout Re(w)>0, including the positive real axis. -/
theorem rotatedWaveOperator_coercive (J : V →L[ℂ] H)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) (w : ℂ) (hw : 0 < w.re) (u : V) :
    waveCoercivity w * ‖u‖^2 ≤ (inner ℂ (rotatedWaveOperator J w u) u).re := by
  rw [rotatedWaveOperator_energy]
  have hmass : ‖J u‖^2 ≤ ‖u‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hJ u) 2
  have ha : min 1 (Complex.normSq w) ≤ 1 := min_le_left _ _
  have hb : min 1 (Complex.normSq w) ≤ Complex.normSq w := min_le_right _ _
  have h1 := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hmass)
  have h2 := mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg ‖J u‖)
  have hi : min 1 (Complex.normSq w) * ‖u‖^2 ≤
      ‖u‖^2-‖J u‖^2 + Complex.normSq w * ‖J u‖^2 := by
    nlinarith
  unfold waveCoercivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hw.le

/-- A bounded inverse of the full rotated joint wave operator, with explicit norm control. -/
theorem rotatedWaveOperator_inverse (J : V →L[ℂ] H)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) (w : ℂ) (hw : 0 < w.re) :
    ∃ S : V →L[ℂ] V,
      (∀ v, rotatedWaveOperator J w (S v) = v) ∧
      (∀ u, S (rotatedWaveOperator J w u) = u) ∧
      ∀ v, ‖S v‖ ≤ (waveCoercivity w)⁻¹ * ‖v‖ :=
  exists_inverse_of_coercive (waveCoercivity_pos w hw) (rotatedWaveOperator_coercive J hJ w hw)

end
end RHTower.D4BMJointWave
