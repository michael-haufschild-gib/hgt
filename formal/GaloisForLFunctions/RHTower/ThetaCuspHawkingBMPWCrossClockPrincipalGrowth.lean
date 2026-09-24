import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWCrossClockResidueCore
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWThreePowerDominance

open Complex Filter Topology
open RHTower RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMMixedParticularCuspFlux
open RHTower.D4BMCrossClockResidueCore
open RHTower.D4BMPWThreePowerDominance

namespace RHTower.D4BMPWCrossClockPrincipalGrowth
noncomputable section
set_option autoImplicit false

private theorem left_power_difference_one (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    (sourcePower q 1 - sourcePower q 2).re < 0 := by
  change ((1 : ℂ) - (2 - 2 * (q.1 : ℂ))).re < 0
  norm_num [Complex.sub_re,Complex.mul_re]
  linarith

private theorem left_power_difference_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    (sourcePower q 0 - sourcePower q 2).re < 0 := by
  change (2 * (q.1 : ℂ) - (2 - 2 * (q.1 : ℂ))).re < 0
  norm_num [Complex.sub_re,Complex.mul_re]
  linarith

theorem cuspResponse_left_normalized_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (b : Bool) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ (-(sourcePower q 2)) *
      cuspResponse q b ![0,y]) atTop
      (𝓝 (responseCoefficient q b 2)) := by
  have h := three_power_dominance
    (responseCoefficient q b 0) (responseCoefficient q b 1)
    (responseCoefficient q b 2)
    (sourcePower q 0) (sourcePower q 1) (sourcePower q 2)
    (left_power_difference_zero q hleft) (left_power_difference_one q hleft)
  apply h.congr'
  filter_upwards with y
  rw [cuspResponse_eq_sum]
  simp only [Fin.sum_univ_three]

/-- The two actual particular responses have a noncanceling common leading
Weyl channel on a hypothetical left-half divisor fibre. -/
theorem cuspResponse_cross_left_normalized_nonzero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    responseCoefficient q true 2 * responseCoefficient q false 2 ≠ 0 ∧
      Tendsto (fun y : ℝ =>
        ((y : ℂ) ^ (-(sourcePower q 2)) * cuspResponse q true ![0,y]) *
          ((y : ℂ) ^ (-(sourcePower q 2)) * cuspResponse q false ![0,y]))
        atTop (𝓝 (responseCoefficient q true 2 * responseCoefficient q false 2)) := by
  have hleft' : (q.1 : ℂ).re < (2 : ℝ)⁻¹ := by
    simpa only [one_div] using hleft
  have hidx : extremeIndex q = 2 := by simp [extremeIndex, hleft']
  have htrue := extreme_responseCoefficient_ne_zero q true
  have hfalse := extreme_responseCoefficient_ne_zero q false
  rw [hidx] at htrue hfalse
  exact ⟨mul_ne_zero htrue hfalse,
    (cuspResponse_left_normalized_tendsto q hleft true).mul
      (cuspResponse_left_normalized_tendsto q hleft false)⟩

end
end RHTower.D4BMPWCrossClockPrincipalGrowth
