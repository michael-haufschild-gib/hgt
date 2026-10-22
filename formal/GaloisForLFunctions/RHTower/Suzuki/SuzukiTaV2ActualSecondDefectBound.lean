import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualSecondDefectJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAllAngleCarrierSchurSecondJet

/-!
# Uniform bound for Suzuki's actual completed-source torque

All-angle self-adjoint realization makes every literal finite-aperture carrier Schur.  Closing the
extremal equality case of the anchored second-jet theorem therefore gives a sharp, unconditional
bound on the actual prime--polar--Gamma endpoint torque, with no continuity or real-representative
assumption on its `L²` source.
-/

open Complex Metric Set

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Sharp aperture-by-aperture Schur slack bound for the literal completed-source torque. -/
theorem norm_suzukiTaV2EndpointSecondTorque_le_schurSlack
    (a : SuzukiPositiveAperture) :
    ‖suzukiTaV2EndpointSecondTorque a‖ ≤
      2 * (1 - ‖(suzukiDefectAngle
        (suzukiTaCoalescingEvenEnergy a 1)
        (suzukiTaCoalescingOddEnergy a 1) : ℂ)‖ ^ (2 : ℕ)) := by
  have hbound := norm_suzukiAllAngleCarrier_secondJet_le_schurSlack
    (differentiable_suzukiTaV2CharacteristicA a)
    (differentiable_suzukiTaV2CharacteristicE a)
    (suzukiTaV2CharacteristicA_I a)
    (suzukiTaV2_allAngleRealZeros a)
  change
    ‖iteratedDeriv 2
      (fun w => suzukiTaV2Livsic a (suzukiUpperCayleyInv w)) 0‖ ≤
      2 * (1 - ‖deriv
        (fun w => suzukiTaV2Livsic a (suzukiUpperCayleyInv w)) 0‖ ^ (2 : ℕ))
    at hbound
  rw [iteratedDeriv_two_suzukiTaV2Livsic_disk_zero_eq_endpointSecondTorque,
    deriv_suzukiTaV2Livsic_disk_zero_eq_coalescingDefectAngle] at hbound
  exact hbound

/-- Universal aperture-independent bound for actual Suzuki endpoint torque. -/
theorem norm_suzukiTaV2EndpointSecondTorque_le_two
    (a : SuzukiPositiveAperture) :
    ‖suzukiTaV2EndpointSecondTorque a‖ ≤ 2 := by
  calc
    ‖suzukiTaV2EndpointSecondTorque a‖ ≤
        2 * (1 - ‖(suzukiDefectAngle
          (suzukiTaCoalescingEvenEnergy a 1)
          (suzukiTaCoalescingOddEnergy a 1) : ℂ)‖ ^ (2 : ℕ)) :=
      norm_suzukiTaV2EndpointSecondTorque_le_schurSlack a
    _ ≤ 2 := by nlinarith [sq_nonneg ‖(suzukiDefectAngle
      (suzukiTaCoalescingEvenEnergy a 1)
      (suzukiTaCoalescingOddEnergy a 1) : ℂ)‖]

end RHTower
end
