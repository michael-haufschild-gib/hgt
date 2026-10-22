import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiLeakageRankIndex
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner

open GaloisForLFunctions.HTGeometry
open Complex

namespace RHTower

noncomputable section

/-- Suzuki's exact Boolean endpoint for the literal anti-causal shifted-Xi quotient: RH holds
exactly when every positive-shift leakage operator vanishes.  The reverse implication remains
valid at exceptional shifts because a nearby shift can be selected where the chosen denominator
zero is not cancelled by the numerator. -/
theorem riemannHypothesis_iff_forall_suzukiShiftedXiHardyLeakage_eq_zero :
    RiemannHypothesis ↔
      ∀ omega : ℝ, 0 < omega → suzukiShiftedXiHardyLeakage omega = 0 := by
  constructor
  · intro hRH omega homega
    letI : IsEmpty (XiShiftRightZeroCopy omega) :=
      ⟨fun q ↦ by
        have hright : (q.1.1 : ℂ) ∈ rightHalf := by
          rw [mem_rightHalf]
          have hdisp : (I * xiSpectralPoint q.1).re =
              (q.1.1 : ℂ).re - 1 / 2 := by
            simp [xiSpectralPoint, mul_re]
          linarith [q.2]
        exact (rh_iff_xi_ne_zero_right.mp hRH (q.1.1 : ℂ) hright)
          (xi_eq_zero_of_mem_divisor_support q.1.1)⟩
    exact suzukiShiftedXiHardyLeakage_eq_zero_of_isEmpty homega.le
  · intro hleak
    rw [rh_iff_xi_ne_zero_right]
    intro rho hrho hxi
    rw [mem_rightHalf] at hrho
    let delta : ℝ := rho.re - 1 / 2
    have hgap : 0 < delta := by
      dsimp only [delta]
      linarith
    obtain ⟨omega, homega, homegaDelta, hnumXi⟩ :=
      exists_suzuki_shift_avoiding_xi_zero hgap rho
    let zroot : ℂ := (1 / 2 + (omega : ℂ) - rho) * (-I)
    have hzrootIm : 0 < zroot.im := by
      dsimp only [zroot]
      norm_num [mul_im, sub_im, add_im]
      dsimp only [delta] at homegaDelta
      linarith
    have hdenZero : suzukiCanonicalE omega zroot = 0 := by
      rw [suzukiCanonicalE]
      convert hxi using 1
      dsimp only [zroot]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [mul_assoc, hI, mul_one]
      ring
    obtain ⟨q, hq⟩ :=
      exists_xiShiftRightZeroCopy_of_suzukiCanonicalE_eq_zero
        omega hdenZero hzrootIm
    have hsource :
        suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0 := by
      rw [hq]
      rw [suzukiCanonicalE_neg_eq_thetaNumerator]
      convert hnumXi using 1
      dsimp only [zroot]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [mul_assoc, hI, mul_one]
      ring
    have hnum :=
      xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero_of_source
        homega.le q hsource
    have hpositive : 0 < ‖(xiShiftInfiniteSchurNumerator homega.le).fn
        (xiShiftPoleDiskCoordinate omega q)‖ := norm_pos_iff.mpr hnum
    have hlower := norm_xiShiftInfiniteSchurNumerator_pole_le_leakage
      homega.le q
    rw [← norm_suzukiShiftedXiHardyLeakage_eq_infiniteLeakageCore homega.le]
      at hlower
    have hzeroNorm : ‖suzukiShiftedXiHardyLeakage omega‖ = 0 := by
      rw [hleak omega homega]
      exact @norm_zero (UpperHardyL2 →L[ℂ] LowerHardyL2) inferInstance
    rw [hzeroNorm] at hlower
    exact (not_lt_of_ge hlower) hpositive

end

end RHTower
