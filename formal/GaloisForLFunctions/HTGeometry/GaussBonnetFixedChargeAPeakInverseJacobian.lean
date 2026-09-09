import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedGibbsProfile

/-!
# Jacobian of the exact moving-peak coordinate

The rational inverse coordinate is smooth even at the phase endpoints.
Its Jacobian is positive and its first variation is explicit. These
identities differentiate the physical radius directly, without taking
derivatives of the arcsine representation at its endpoints.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakInverseJacobian (τ φ ψ : ℝ) : ℝ :=
  (1 - egbFixedChargeAMiddleGapCoordinate τ φ ^ 2) /
    (1 + egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ) ^ 2

theorem egbFixedChargeAPeakInverseJacobian_pos (τ φ ψ : ℝ) :
    0 < egbFixedChargeAPeakInverseJacobian τ φ ψ := by
  have hc := egbFixedChargeAMiddleGapCoordinate_bounds τ φ
  have hn : 0 < 1 - egbFixedChargeAMiddleGapCoordinate τ φ ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - egbFixedChargeAMiddleGapCoordinate τ φ)
      (by linarith : 0 < 1 + egbFixedChargeAMiddleGapCoordinate τ φ)]
  have hd := egbFixedChargeAPeakInverseCoordinate_denominator_pos τ φ ψ
  unfold egbFixedChargeAPeakInverseJacobian
  positivity

theorem egbFixedChargeAPeakInverseCoordinate_hasDerivAt (τ φ ψ : ℝ) :
    HasDerivAt (egbFixedChargeAPeakInverseCoordinate τ φ)
      (egbFixedChargeAPeakInverseJacobian τ φ ψ * cos ψ) ψ := by
  have hf : egbFixedChargeAPeakInverseCoordinate τ φ =
      fun x => (sin x + egbFixedChargeAMiddleGapCoordinate τ φ) / (1 + egbFixedChargeAMiddleGapCoordinate τ φ * sin x) := by
    funext x
    exact egbFixedChargeAPeakInverseCoordinate_formula τ φ x
  rw [hf]
  have hd := egbFixedChargeAPeakInverseCoordinate_denominator_pos τ φ ψ
  have h := ((hasDerivAt_sin ψ).add_const (egbFixedChargeAMiddleGapCoordinate τ φ)).div
    (((hasDerivAt_sin ψ).const_mul (egbFixedChargeAMiddleGapCoordinate τ φ)).const_add 1) hd.ne'
  apply h.congr_deriv
  unfold egbFixedChargeAPeakInverseJacobian
  ring

theorem egbFixedChargeAPeakInverseCoordinate_linear_formula (τ φ ψ : ℝ) :
    (egbFixedChargeAPeakInverseCoordinate τ φ ψ - sin ψ) / egbCoexistenceASymmetricRatio τ =
      (egbFixedChargeAMiddleGapCoordinate τ φ / egbCoexistenceASymmetricRatio τ) * cos ψ ^ 2 /
        (1 + egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ) := by
  have hd := egbFixedChargeAPeakInverseCoordinate_denominator_pos τ φ ψ
  have hd' : 1 + sin ψ * egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by simpa only [mul_comm] using hd.ne'
  have hz := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hs : cos ψ ^ 2 = 1 - sin ψ ^ 2 := by linarith [sin_sq_add_cos_sq ψ]
  rw [egbFixedChargeAPeakInverseCoordinate_formula, hs]
  field_simp [hd.ne', hd', hz.ne'] <;> ring

theorem egbFixedChargeAPeakInverseJacobian_linear_formula (τ φ ψ : ℝ) :
    (egbFixedChargeAPeakInverseJacobian τ φ ψ - 1) / egbCoexistenceASymmetricRatio τ =
      -(egbFixedChargeAMiddleGapCoordinate τ φ / egbCoexistenceASymmetricRatio τ) *
        (2 * sin ψ + egbFixedChargeAMiddleGapCoordinate τ φ * (1 + sin ψ ^ 2)) /
          (1 + egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ) ^ 2 := by
  have hd := egbFixedChargeAPeakInverseCoordinate_denominator_pos τ φ ψ
  have hd' : 1 + sin ψ * egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by simpa only [mul_comm] using hd.ne'
  have hz := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAPeakInverseJacobian
  field_simp [hd.ne', hd', hz.ne'] <;> ring

theorem egbFixedChargeAPeakInverseCoordinate_linear_limit (φ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakInverseCoordinate τ φ ψ - sin ψ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (egbFixedChargeAMiddleMeanCorrection φ * cos ψ ^ 2)) := by
  have hc := egbFixedChargeAMiddleGapCoordinate_critical_limit φ
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add (hc.mul (tendsto_const_nhds (x := sin ψ)))
  simp only [zero_mul, add_zero] at hden
  have h := ((egbFixedChargeAMiddleGapCoordinate_linear_limit φ).mul (tendsto_const_nhds (x := cos ψ ^ 2))).div hden one_ne_zero
  simpa only [egbFixedChargeAPeakInverseCoordinate_linear_formula, Pi.div_def, div_one] using h

theorem egbFixedChargeAPeakInverseJacobian_critical_limit (φ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPeakInverseJacobian τ φ ψ) atBot (𝓝 (1 : ℝ)) := by
  have hc := egbFixedChargeAMiddleGapCoordinate_critical_limit φ
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add (hc.mul (tendsto_const_nhds (x := sin ψ)))
  simp only [zero_mul, add_zero] at hden
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hc.pow 2)).div (hden.pow 2) (by norm_num)
  simpa only [egbFixedChargeAPeakInverseJacobian, Pi.div_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, one_pow, div_one] using h

theorem egbFixedChargeAPeakInverseJacobian_linear_limit (φ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakInverseJacobian τ φ ψ - 1) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (-2 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ)) := by
  have hc := egbFixedChargeAMiddleGapCoordinate_critical_limit φ
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add (hc.mul (tendsto_const_nhds (x := sin ψ)))
  simp only [zero_mul, add_zero] at hden
  have hnum := (tendsto_const_nhds (x := 2 * sin ψ)).add (hc.mul (tendsto_const_nhds (x := 1 + sin ψ ^ 2)))
  simp only [zero_mul, add_zero] at hnum
  have h := (((egbFixedChargeAMiddleGapCoordinate_linear_limit φ).neg).mul hnum).div (hden.pow 2) (by norm_num)
  have he : (-egbFixedChargeAMiddleMeanCorrection φ) * (2 * sin ψ) / (1 : ℝ) ^ 2 =
      -2 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ := by ring
  rw [he] at h
  simpa only [egbFixedChargeAPeakInverseJacobian_linear_formula, Pi.div_def] using h

end GaloisForLFunctions.HTGeometry
