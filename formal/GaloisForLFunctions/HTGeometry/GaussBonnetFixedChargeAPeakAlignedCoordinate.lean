import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsNormalizedOddProfile

/-!
# Endpoint-preserving alignment of the moving Gibbs peak

The fractional linear coordinate (t - c)/(1 - c*t), where c is the actual
middle stationary coordinate, fixes both phase endpoints and sends the
true peak to zero. Its denominator stays positive throughout the entire
physical interval. All statements hold for arbitrary real input data.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakAlignedCoordinate (τ φ ψ : ℝ) : ℝ :=
  (sin ψ - egbFixedChargeAMiddleGapCoordinate τ φ) /
    (1 - egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ)

theorem egbFixedChargeAPeakAlignedCoordinate_denominator_pos (τ φ ψ : ℝ) :
    0 < 1 - egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ := by
  have hc : |egbFixedChargeAMiddleGapCoordinate τ φ| < 1 := abs_lt.mpr (egbFixedChargeAMiddleGapCoordinate_bounds τ φ)
  have hs : |sin ψ| ≤ 1 := abs_le.mpr ⟨neg_one_le_sin ψ, sin_le_one ψ⟩
  have hm : |egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hc)
  linarith [le_abs_self (egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ)]

theorem egbFixedChargeAPeakAlignedCoordinate_bounds (τ φ ψ : ℝ) :
    -1 ≤ egbFixedChargeAPeakAlignedCoordinate τ φ ψ ∧ egbFixedChargeAPeakAlignedCoordinate τ φ ψ ≤ 1 := by
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ
  have hc := egbFixedChargeAMiddleGapCoordinate_bounds τ φ
  have hs := neg_one_le_sin ψ
  have ht := sin_le_one ψ
  unfold egbFixedChargeAPeakAlignedCoordinate
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - egbFixedChargeAMiddleGapCoordinate τ φ) (by linarith : 0 ≤ 1 + sin ψ)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + egbFixedChargeAMiddleGapCoordinate τ φ) (by linarith : 0 ≤ 1 - sin ψ)]

theorem egbFixedChargeAPeakAlignedCoordinate_zero_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedCoordinate τ φ ψ = 0 ↔ sin ψ = egbFixedChargeAMiddleGapCoordinate τ φ := by
  unfold egbFixedChargeAPeakAlignedCoordinate
  rw [div_eq_zero_iff]
  have hd := (egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ).ne'
  simp only [hd, or_false, sub_eq_zero]

theorem egbFixedChargeAPeakAlignedCoordinate_large_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedCoordinate τ φ ψ = 1 ↔ sin ψ = 1 := by
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ
  have hc := (egbFixedChargeAMiddleGapCoordinate_bounds τ φ).1
  unfold egbFixedChargeAPeakAlignedCoordinate
  rw [div_eq_iff hd.ne']
  constructor
  · intro he
    have hp : (sin ψ - 1) * (1 + egbFixedChargeAMiddleGapCoordinate τ φ) = 0 := by nlinarith [he]
    have hn : 1 + egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hn)
  · intro he
    rw [he]
    ring

theorem egbFixedChargeAPeakAlignedCoordinate_small_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedCoordinate τ φ ψ = -1 ↔ sin ψ = -1 := by
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ
  have hc := (egbFixedChargeAMiddleGapCoordinate_bounds τ φ).2
  unfold egbFixedChargeAPeakAlignedCoordinate
  rw [div_eq_iff hd.ne']
  constructor
  · intro he
    have hp : (sin ψ + 1) * (1 - egbFixedChargeAMiddleGapCoordinate τ φ) = 0 := by nlinarith [he]
    have hn : 1 - egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by linarith
    have hz := (mul_eq_zero.mp hp).resolve_right hn
    linarith
  · intro he
    rw [he]
    ring

theorem egbFixedChargeAPeakAlignedCoordinate_critical_limit (φ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPeakAlignedCoordinate τ φ ψ) atBot (𝓝 (sin ψ)) := by
  have hc := egbFixedChargeAMiddleGapCoordinate_critical_limit φ
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).sub (hc.mul (tendsto_const_nhds (x := sin ψ)))
  simp only [zero_mul, sub_zero] at hden
  have h := ((tendsto_const_nhds (x := sin ψ)).sub hc).div hden one_ne_zero
  simpa only [sub_zero, div_one, Pi.div_def, egbFixedChargeAPeakAlignedCoordinate] using h

theorem egbFixedChargeAPeakAlignedCoordinate_linear_formula (τ φ ψ : ℝ) :
    (egbFixedChargeAPeakAlignedCoordinate τ φ ψ - sin ψ) / egbCoexistenceASymmetricRatio τ =
      -(egbFixedChargeAMiddleGapCoordinate τ φ / egbCoexistenceASymmetricRatio τ) * cos ψ ^ 2 /
        (1 - egbFixedChargeAMiddleGapCoordinate τ φ * sin ψ) := by
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ
  have hz := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hs : cos ψ ^ 2 = 1 - sin ψ ^ 2 := by linarith [sin_sq_add_cos_sq ψ]
  unfold egbFixedChargeAPeakAlignedCoordinate
  rw [hs]
  have hd' : 1 - sin ψ * egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by simpa only [mul_comm] using hd.ne'
  field_simp [hd.ne', hd', hz.ne'] <;> ring

theorem egbFixedChargeAPeakAlignedCoordinate_linear_limit (φ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakAlignedCoordinate τ φ ψ - sin ψ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (-egbFixedChargeAMiddleMeanCorrection φ * cos ψ ^ 2)) := by
  have hc := egbFixedChargeAMiddleGapCoordinate_critical_limit φ
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).sub (hc.mul (tendsto_const_nhds (x := sin ψ)))
  simp only [zero_mul, sub_zero] at hden
  have h := (((egbFixedChargeAMiddleGapCoordinate_linear_limit φ).neg).mul
    (tendsto_const_nhds (x := cos ψ ^ 2))).div hden one_ne_zero
  simpa only [egbFixedChargeAPeakAlignedCoordinate_linear_formula, Pi.div_def, div_one] using h

end GaloisForLFunctions.HTGeometry
