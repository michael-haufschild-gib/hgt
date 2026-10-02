import GaloisForLFunctions.RHTower.ThetaTwoNodeSignedSturmEnergy

/-! Actual inverse-Gram feedback exceeds the source secant for every
positive pair anchored at the center. Its signed representer energy is negative. -/

noncomputable section
open MeasureTheory Set
namespace RHTower.ThetaCenterFeedback
open ThetaSturm ThetaSourceWard

private theorem slope_zero : thetaCuspLogDecaySlope 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

theorem feedback_comm (x z : ℝ) : feedback x z = feedback z x := by
  simp only [feedback, representerLeft, representerRight, determinant,
    thetaTailFirstMomentKernel_comm z x]
  ring

/-- Exact square decomposition for the literal inverse-Gram source feedback. -/
theorem feedback_eq_single_add_square {x z : ℝ} (hxz : x ≠ z) :
    feedback x z = thetaCuspFullSource x^2/thetaTailFirstMomentKernel x x +
      (thetaTailFirstMomentKernel x x*thetaCuspFullSource z-
        thetaTailFirstMomentKernel x z*thetaCuspFullSource x)^2/
        (thetaTailFirstMomentKernel x x*determinant x z) := by
  have hxx : thetaTailFirstMomentKernel x x ≠ 0 := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact (thetaPrimeGammaCutEnergy_pos x).ne'
  have hD : determinant x z ≠ 0 := (ThetaTailTwoPoint.kernel_two_point_det_pos hxz).ne'
  dsimp only [feedback, representerLeft, representerRight]
  field_simp [hxx, hD]
  dsimp only [determinant]
  ring

theorem single_le_feedback {x z : ℝ} (hxz : x ≠ z) :
    thetaCuspFullSource x^2/thetaTailFirstMomentKernel x x ≤ feedback x z := by
  rw [feedback_eq_single_add_square hxz]
  have hxx : 0 < thetaTailFirstMomentKernel x x := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact thetaPrimeGammaCutEnergy_pos x
  have hn := div_nonneg
    (sq_nonneg (thetaTailFirstMomentKernel x x*thetaCuspFullSource z-
      thetaTailFirstMomentKernel x z*thetaCuspFullSource x))
    (mul_pos hxx (ThetaTailTwoPoint.kernel_two_point_det_pos hxz)).le
  dsimp only [determinant]
  linarith only [hn]

/-- The literal two-node feedback exceeds the secant for every center-anchored
pair. This uses the full-tail diagonal comparison at the positive node. -/
theorem center_secant_lt_feedback {z : ℝ} (hz : 0 < z) :
    secant 0 z 0 < feedback 0 z := by
  have h := ThetaTailTwoPoint.diagonal_tail_lt_source_square hz
  have hc : thetaCuspLogDecaySlope z/z <
      thetaCuspFullSource z^2/thetaTailFirstMomentKernel z z := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact (lt_div_iff₀ (thetaPrimeGammaCutEnergy_pos z)).mpr h
  have hle := single_le_feedback hz.ne'
  rw [feedback_comm z 0] at hle
  simpa only [secant, add_zero, sub_zero, slope_zero] using hc.trans_le hle

/-- Every actual center-anchored inverse-Gram source representer has strictly
negative signed Sturm energy. In particular this density cannot be discarded. -/
theorem center_representer_signed_energy_neg {z : ℝ} (hz : 0 < z) :
    (∫ t in Ioi 0, density 0 z t*(representer 0 z t)^2) < 0 := by
  have he := feedback_sub_secant_eq_signed_energy (le_refl (0:ℝ)) hz
  have hp := div_pos (secant_pos hz 0) (feedback_pos hz)
  have hn : -(secant 0 z 0/feedback 0 z)*
      (∫ t in Ioi 0, density 0 z t*(representer 0 z t)^2) > 0 := by
    rw [← he]
    exact sub_pos.mpr (center_secant_lt_feedback hz)
  by_contra h
  have := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) (le_of_not_gt h)
  exact (not_lt_of_ge this) hn

/-- The old-span packet vanishing at the source endpoint has an exact,
strictly positive signed energy. This is the positive direction surviving
the actual negative representer direction. -/
theorem source_zero_packet_signed_energy_eq {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    (∫ t in Ioi 0, density x z t*
      (packet x z (thetaCuspFullSource z) (-thetaCuspFullSource x) t)^2) =
      determinant x z*feedback x z := by
  have h := energy_eq_boundary_add_signed_integral hx hxz
    (thetaCuspFullSource z) (-thetaCuspFullSource x)
  have hz : packet x z (thetaCuspFullSource z) (-thetaCuspFullSource x) 0 = 0 := by
    simp only [packet, add_zero]
    ring
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add] at h
  rw [← h]
  have hD : determinant x z ≠ 0 := (ThetaTailTwoPoint.kernel_two_point_det_pos hxz.ne).ne'
  dsimp only [energy, feedback, representerLeft, representerRight]
  field_simp [hD]
  ring

theorem source_zero_packet_signed_energy_pos {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    0 < ∫ t in Ioi 0, density x z t*
      (packet x z (thetaCuspFullSource z) (-thetaCuspFullSource x) t)^2 := by
  rw [source_zero_packet_signed_energy_eq hx hxz]
  exact mul_pos (ThetaTailTwoPoint.kernel_two_point_det_pos hxz.ne) (feedback_pos hxz)

end RHTower.ThetaCenterFeedback
