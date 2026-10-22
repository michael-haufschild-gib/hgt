import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCompletedDividedEnergy
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactFluxEnergy
import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux

/-!
# Route R: same-fibre completed-Xi/theta orientation

Source reflection makes the theta root energy even at every zero of the completed source
transform.  This removes the reflected argument from the completed divided-energy identity and
places the compact theta boundary form on the same Xi divisor fibre:

`pi * M * B_theta(rho) = Im(alpha_rho) * ‖Q_rho‖^(2 : ℕ)`.

Here `Q_rho` is the genuine completed first-divided Xi vector, `M` is the fixed positive theta
mass, and `B_theta` is the rank-two boundary form on the actual compact-source eigenvector.  At a
hypothetical right-half Xi divisor this current is strictly negative, whereas Burnol's fixed
co-Poisson divided-shift head current is strictly positive.  Thus any Route-R comparison capable
of producing Burnol dissipativity must change this now-explicit orientation; an ordinary positive
same-fibre identification cannot do so.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmPrimeTranslation
open HedenmalmThetaSource

/-- **Root-energy reflection.**  At a zero of the even theta-source transform, reflection of the
spectral parameter preserves the full quantile root energy. -/
theorem thetaRootEnergy_neg_of_zero {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    thetaRootEnergy (-z) = thetaRootEnergy z := by
  have hzneg : |(-z).im| < 1 := by simpa
  rw [thetaRootEnergy_eq_integral_norm_sq_sourceModeU_div_mass_sq hzneg,
    thetaRootEnergy_eq_integral_norm_sq_sourceModeU_div_mass_sq hz]
  congr 1
  rw [← MeasureTheory.integral_neg_eq_self
    (fun x : ℝ => ‖sourceModeU thetaSource (-z) x‖ ^ (2 : ℕ)) volume]
  apply integral_congr_ae
  filter_upwards with x
  rw [sourceModeU_neg thetaSource thetaSource_even
    (hasShiftedTail_thetaSource hz) hzero x, norm_neg]

/-- The completed first-divided Xi norm lands on root energy at the same centered divisor point,
not merely at its reflected point. -/
theorem norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy
    (rho : XiDivisorSupport) :
    ‖completedXiFirstDividedL2 rho‖ ^ (2 : ℕ) =
      2 * Real.pi * thetaSource.mass ^ (2 : ℕ) *
        thetaRootEnergy (xiSpectralPointSupport rho) := by
  rw [norm_sq_completedXiFirstDividedL2_eq_thetaRootEnergy]
  congr 1
  have him : (xiSpectralPointSupport rho).im = 1 / 2 - (rho : ℂ).re := by
    simp [xiSpectralPointSupport, Complex.mul_im]
  apply thetaRootEnergy_neg_of_zero
  · rw [him, abs_lt]
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    constructor <;> linarith
  · have hstrip : |(xiSpectralPointSupport rho).im| < 1 := by
      rw [him, abs_lt]
      have hrange := xi_divisor_support_re_mem_open_unit rho
      constructor <;> linarith
    rw [xiC_thetaSource hstrip]
    exact XiC_xiSpectralPointSupport_eq_zero rho

/-- **Coefficient-faithful same-fibre boundary law.**  The genuine compact-theta boundary flux is
horizontal displacement times the norm square of the genuine completed first-divided Xi vector,
with only the fixed positive source normalization `pi * M`. -/
theorem thetaXiRankTwoBoundaryFlux_completedXi_sameFiber
    (q : XiZeroCopy) :
    Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q =
      (xiSpectralPoint q).im * ‖completedXiFirstDividedL2 q.1‖ ^ (2 : ℕ) := by
  rw [xiSpectralPoint_eq_support]
  rw [thetaXiRankTwoBoundaryFlux_eq,
    norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy]
  simp only [thetaXiRootEnergy, xiSpectralPoint_eq_support]
  ring

/-- The same-fibre compact-source boundary current is strictly negative at every hypothetical
right-half Xi divisor. -/
theorem thetaXiRankTwoBoundaryFlux_neg_of_rightHalf
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    thetaXiRankTwoBoundaryFlux q < 0 := by
  have hnorm : 0 < ‖completedXiFirstDividedL2 q.1‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr (completedXiFirstDividedL2_ne_zero q.1))
  have him : (xiSpectralPoint q).im < 0 := by
    rw [xiSpectralPoint_im_eq]
    linarith
  have hmass : 0 < Real.pi * thetaSource.mass :=
    mul_pos Real.pi_pos thetaSource.mass_pos
  have hid := thetaXiRankTwoBoundaryFlux_completedXi_sameFiber q
  nlinarith

/-- **Orientation obstruction.**  On a hypothetical right-half Xi fibre, completed-Xi/theta
boundary flux and Burnol's fixed divided-shift head current have strictly opposite signs. -/
theorem burnolThetaSameFiber_orientedCurrents_opposed
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    thetaXiRankTwoBoundaryFlux q *
      burnolCartierDividedShiftHeadFlux (q.1 : ℂ) < 0 := by
  exact mul_neg_of_neg_of_pos
    (thetaXiRankTwoBoundaryFlux_neg_of_rightHalf q h)
    (burnolCartierDividedShiftHeadFlux_pos h
      (xiDivisor_re_lt_one_of_half_lt q.1 h))

end

end RHTower
