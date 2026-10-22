import GaloisForLFunctions.RHTower.Suzuki.SuzukiFourierLivsicSecondJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualDefectJet

/-!
# Actual Suzuki v2 second defect coordinate

The first literal defect jet sees the even/odd covariance-energy imbalance.  The next coefficient
is not another energy ratio: it is the signed endpoint torque coupling both derivatives of the
actual completed prime--polar--Gamma Fourier source.  This module identifies that coefficient
exactly at every positive aperture, before any compactness, scalarization, or Xi comparison.
-/

open Complex

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Literal endpoint torque of Suzuki's completed finite-aperture source. -/
def suzukiTaV2EndpointSecondTorque (a : SuzukiPositiveAperture) : ℂ :=
  let F := suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)
  4 * I * (deriv F I * F (-I) + F I * deriv F (-I)) / F (-I) ^ (2 : ℕ)

/-- Exact second disk jet of the actual Suzuki v2 Livšic characteristic. -/
theorem iteratedDeriv_two_suzukiTaV2Livsic_disk_zero_eq_endpointSecondTorque
    (a : SuzukiPositiveAperture) :
    iteratedDeriv 2
        (fun w => suzukiTaV2Livsic a (suzukiUpperCayleyInv w)) 0 =
      suzukiTaV2EndpointSecondTorque a := by
  let F : ℂ → ℂ := suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)
  have hFi : ContDiffAt ℂ 2 F I :=
    ((differentiable_suzukiTaPhysicalFourier a
      (suzukiTaPlusDeficiency a)).analyticAt I).contDiffAt
  have hFni : ContDiffAt ℂ 2 F (-I) :=
    ((differentiable_suzukiTaPhysicalFourier a
      (suzukiTaPlusDeficiency a)).analyticAt (-I)).contDiffAt
  have hnorm : ‖suzukiTaRawDeficiency a 1‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a 1)
  have hscaled :
      ‖suzukiTaRawDeficiency a 1‖ *
          (suzukiTaCoalescingEvenEnergy a 1 +
            suzukiTaCoalescingOddEnergy a 1) ≠ 0 := by
    rw [suzukiTaCoalescingEnergy_add_eq_norm_sq]
    exact mul_ne_zero hnorm (pow_ne_zero 2 hnorm)
  have hFni0 : F (-I) ≠ 0 := by
    rw [show F (-I) =
        ((‖suzukiTaRawDeficiency a 1‖ *
          (suzukiTaCoalescingEvenEnergy a 1 +
            suzukiTaCoalescingOddEnergy a 1) : ℝ) : ℂ) by
      simpa [F] using physicalFourier_plus_negI_eq_scaled_energy_add a]
    exact Complex.ofReal_ne_zero.mpr hscaled
  have hquot : suzukiTaV2Livsic a =
      suzukiLivsicQuotient (suzukiFourierNumerator F)
        (suzukiFourierDenominator F) := by
    funext z
    change
      ((z - I) * F z) /
          ((z + I) * suzukiTaPhysicalFourier a
            (suzukiTaMinusDeficiency a) z) =
        ((z - I) * F z) / ((z + I) * F (-z))
    rw [suzukiTaPhysicalFourier_minusDeficiency_reflection]
  rw [hquot]
  exact iteratedDeriv_two_suzukiFourierLivsic_disk_zero hFi hFni hFni0

end RHTower
end
