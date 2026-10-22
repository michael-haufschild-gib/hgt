import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPacketApproximation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyTiltedAngularLeakage
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

/-!
# Sharp native scattering residual in the actual modular operator domain

The original modular Friedrichs operator is `A = 1 - Delta_H`. Its explicitly
normalized cusp packets have residual square `eta² + C1/L² + C2/L⁴` at
`5/4 + tau² + i eta`. The universal imaginary lower bound is therefore sharp.

For every actual Xi zero `rho = beta + i gamma`, the native modular scattering
exponent is `s = rho/2`. Its shifted energy `1+s(1-s)` has real part above the
cusp threshold and optimal unit residual `|gamma|(1-beta)/2 > 0`. Explicit
original-domain packets approach that floor. Literal scattering occurrence
cannot be an approximate eigenvalue of this operator, even at critical zeros.
The result supplies an exact residual floor and source sequence, not RH or a
replacement spectral occurrence map.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open RHTower.D4BMModularCore

namespace RHTower.SelbergScatteringNativeResidual
noncomputable section

/-- Complex spectral parameter above the original shifted cusp threshold. -/
def cuspParameter (tau eta : ℝ) : ℂ := 5 / 4 + (tau : ℂ) ^ (2 : ℕ) + (eta : ℂ) * I

/-- Real part of the shifted cusp parameter. -/
theorem cuspParameter_re (tau eta : ℝ) :
    (cuspParameter tau eta).re = 5 / 4 + tau ^ (2 : ℕ) := by
  simp [cuspParameter, pow_two]

/-- Imaginary part of the shifted cusp parameter. -/
theorem cuspParameter_im (tau eta : ℝ) : (cuspParameter tau eta).im = eta := by
  simp [cuspParameter, pow_two]

/-- Exact Pythagorean residual identity in the actual modular operator domain. -/
theorem native_residual_sq (z : ℂ) (x : energyOperator.domain) :
    ‖energyOperator x - z • (x : Space)‖ ^ (2 : ℕ) =
      ‖energyOperator x - (z.re : ℂ) • (x : Space)‖ ^ (2 : ℕ) +
        z.im ^ (2 : ℕ) * ‖(x : Space)‖ ^ (2 : ℕ) := by
  apply complexSymmetric_residual_norm_sq
  exact (isFormalAdjoint_of_isSelfAdjoint energyOperator_selfAdjoint x x).symm

/-- Constructed cusp packets retain exactly the imaginary floor and both cutoff derivative costs. -/
theorem cuspUnitPacket_complex_residual_sq (tau eta : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖energyOperator (cuspUnitPacket tau L hL) -
      cuspParameter tau eta • (cuspUnitPacket tau L hL : Space)‖ ^ (2 : ℕ) =
      eta ^ (2 : ℕ) + (4 * tau ^ (2 : ℕ) * cuspWindowMoment 1 / cuspWindowMoment 0) * L⁻¹ ^ (2 : ℕ) +
        (cuspWindowMoment 2 / cuspWindowMoment 0) * L⁻¹ ^ (4 : ℕ) := by
  rw [native_residual_sq, cuspParameter_re, cuspParameter_im, cuspUnitPacket_norm]
  have hreal : ((5 / 4 + tau ^ (2 : ℕ) : ℝ) : ℂ) = 5 / 4 + (tau : ℂ) ^ (2 : ℕ) := by
    push_cast
    rfl
  rw [hreal, cuspUnitPacket_residual_norm_sq]
  ring

/-- Every unit vector in the original domain pays the imaginary residual floor. -/
theorem native_unit_residual_lower (tau eta : ℝ) (x : energyOperator.domain)
    (hx : ‖(x : Space)‖ = 1) :
    |eta| ≤ ‖energyOperator x - cuspParameter tau eta • (x : Space)‖ := by
  simpa only [cuspParameter_im, hx, mul_one] using
    norm_sub_smul_lower_bound energyOperator_selfAdjoint (cuspParameter tau eta) x

/-- The actual normalized cusp sequence approaches the universal imaginary floor. -/
theorem cuspApproximateVector_complex_residual_tendsto (tau eta : ℝ) :
    Tendsto (fun n : ℕ => ‖energyOperator (cuspApproximateVector tau n) -
      cuspParameter tau eta • (cuspApproximateVector tau n : Space)‖)
      atTop (𝓝 |eta|) := by
  have hsq : Tendsto (fun n : ℕ => ‖energyOperator (cuspApproximateVector tau n) -
      cuspParameter tau eta • (cuspApproximateVector tau n : Space)‖ ^ (2 : ℕ))
      atTop (𝓝 (eta ^ (2 : ℕ))) := by
    have h := ((cuspApproximateVector_residual_tendsto tau).pow 2).add_const (eta ^ (2 : ℕ))
    simp_rw [native_residual_sq (cuspParameter tau eta), cuspParameter_re, cuspParameter_im,
      cuspApproximateVector_norm, one_pow, mul_one]
    have hreal : ((5 / 4 + tau ^ (2 : ℕ) : ℝ) : ℂ) = 5 / 4 + (tau : ℂ) ^ (2 : ℕ) := by
      push_cast
      rfl
    simpa only [hreal, zero_pow (by norm_num : 2 ≠ 0), zero_add] using h
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] using hsq.sqrt

/-- Native modular scattering energy at exponent `rho/2`, shifted for `1-Delta_H`. -/
def scatteringEnergy (rho : ℂ) : ℂ := 1 + (rho / 2) * (1 - rho / 2)

/-- Exact real native energy in the original uncentered argument. -/
theorem scatteringEnergy_re (rho : ℂ) :
    (scatteringEnergy rho).re = 5 / 4 + (rho.im ^ (2 : ℕ) - (1 - rho.re) ^ (2 : ℕ)) / 4 := by
  simp [scatteringEnergy, Complex.mul_re]
  ring

/-- Exact imaginary native energy in the original uncentered argument. -/
theorem scatteringEnergy_im (rho : ℂ) :
    (scatteringEnergy rho).im = rho.im * (1 - rho.re) / 2 := by
  simp [scatteringEnergy, Complex.mul_im]
  ring

/-- The irreducible unit residual attached to an actual Xi zero. -/
def xiResidualFloor (q : XiZeroCopy) : ℝ := |(q.1 : ℂ).im| * (1 - (q.1 : ℂ).re) / 2

/-- The actual open Xi strip and nonzero ordinate make every native residual floor positive. -/
theorem xiResidualFloor_pos (q : XiZeroCopy) : 0 < xiResidualFloor q := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hi := xi_divisor_support_im_ne_zero q.1
  exact div_pos (mul_pos (abs_pos.mpr hi) (sub_pos.mpr hs.2)) (by norm_num)

/-- The proposed native floor is exactly the imaginary spectral distance. -/
theorem xi_scatteringEnergy_abs_im (q : XiZeroCopy) :
    |(scatteringEnergy (q.1 : ℂ)).im| = xiResidualFloor q := by
  rw [scatteringEnergy_im, abs_div, abs_mul,
    abs_of_pos (sub_pos.mpr (xi_divisor_support_re_mem_open_unit q.1).2)]
  norm_num [xiResidualFloor]

/-- The source-pure Xi height bound puts every native real part above the constructed cusp ray. -/
theorem xi_scatteringEnergy_re_gt_cusp (q : XiZeroCopy) :
    5 / 4 < (scatteringEnergy (q.1 : ℂ)).re := by
  rw [scatteringEnergy_re]
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hh := xiZeroCopy_one_lt_im_sq q
  nlinarith [sq_nonneg (q.1 : ℂ).re]

/-- Explicit real cusp frequency paired with the real part of an actual scattering energy. -/
def xiPacketFrequency (q : XiZeroCopy) : ℝ :=
  Real.sqrt ((scatteringEnergy (q.1 : ℂ)).re - 5 / 4)

/-- The explicit cusp frequency and original imaginary part recover the complete native energy. -/
theorem xiPacketFrequency_parameter (q : XiZeroCopy) :
    cuspParameter (xiPacketFrequency q) (scatteringEnergy (q.1 : ℂ)).im =
      scatteringEnergy (q.1 : ℂ) := by
  apply Complex.ext
  · rw [cuspParameter_re, xiPacketFrequency,
      Real.sq_sqrt (sub_nonneg.mpr (xi_scatteringEnergy_re_gt_cusp q).le)]
    ring
  · exact cuspParameter_im _ _

/-- Actual normalized modular-domain packet sequence for each Xi scattering energy. -/
def xiNativePacket (q : XiZeroCopy) (n : ℕ) : energyOperator.domain :=
  cuspApproximateVector (xiPacketFrequency q) n

/-- All constructed Xi packets have exact unit Hilbert norm. -/
theorem xiNativePacket_norm (q : XiZeroCopy) (n : ℕ) :
    ‖(xiNativePacket q n : Space)‖ = 1 := cuspApproximateVector_norm _ _

/-- The native scattering floor bounds the residual of every original-domain unit vector. -/
theorem xi_unit_residual_lower (q : XiZeroCopy) (x : energyOperator.domain)
    (hx : ‖(x : Space)‖ = 1) :
    xiResidualFloor q ≤ ‖energyOperator x - scatteringEnergy (q.1 : ℂ) • (x : Space)‖ := by
  simpa only [xi_scatteringEnergy_abs_im, hx, mul_one] using
    norm_sub_smul_lower_bound energyOperator_selfAdjoint (scatteringEnergy (q.1 : ℂ)) x

/-- Explicit original-domain packets attain the native scattering floor in the limit. -/
theorem xiNativePacket_residual_tendsto (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => ‖energyOperator (xiNativePacket q n) -
      scatteringEnergy (q.1 : ℂ) • (xiNativePacket q n : Space)‖)
      atTop (𝓝 (xiResidualFloor q)) := by
  simpa only [xiNativePacket, xiPacketFrequency_parameter, xi_scatteringEnergy_abs_im] using
    cuspApproximateVector_complex_residual_tendsto (xiPacketFrequency q)
      (scatteringEnergy (q.1 : ℂ)).im

/-- No actual Xi scattering energy admits a unit approximate eigenvector sequence in this domain. -/
theorem xi_scattering_no_approximate_eigenvectors (q : XiZeroCopy) :
    ¬ ∃ v : ℕ → energyOperator.domain, (∀ n, ‖(v n : Space)‖ = 1) ∧
      Tendsto (fun n => ‖energyOperator (v n) -
        scatteringEnergy (q.1 : ℂ) • (v n : Space)‖) atTop (𝓝 0) := by
  rintro ⟨v, hv, hlim⟩
  have h := ge_of_tendsto' hlim (fun n => xi_unit_residual_lower q (v n) (hv n))
  exact (not_le_of_gt (xiResidualFloor_pos q)) h

/-- The exact greatest lower bound of all original-domain unit residuals at each actual Xi scattering energy. -/
theorem xi_residual_isGLB (q : XiZeroCopy) :
    IsGLB {r : ℝ | ∃ x : energyOperator.domain, ‖(x : Space)‖ = 1 ∧
      r = ‖energyOperator x - scatteringEnergy (q.1 : ℂ) • (x : Space)‖}
      (xiResidualFloor q) := by
  constructor
  · rintro r ⟨x, hx, rfl⟩
    exact xi_unit_residual_lower q x hx
  · intro c hc
    exact ge_of_tendsto' (xiNativePacket_residual_tendsto q) (fun n =>
      hc ⟨xiNativePacket q n, xiNativePacket_norm q n, rfl⟩)

/-- At a critical zero the native residual floor is a quarter of its absolute ordinate. -/
theorem xiResidualFloor_critical (q : XiZeroCopy) (hq : (q.1 : ℂ).re = 1 / 2) :
    xiResidualFloor q = |(q.1 : ℂ).im| / 4 := by
  rw [xiResidualFloor, hq]
  ring

end
end RHTower.SelbergScatteringNativeResidual
