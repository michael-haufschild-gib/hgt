import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalGreenFactor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalAngularSourceXi

/-! Exact source-moment and observation-point criteria for every original Xi fundamental pole. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem physical_fundamental_roots (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

/-- Every actual Xi fundamental numerator has the derived elementary mode and one fixed complete source scalar. -/
theorem physicalFundamentalGreen_factor (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (t : ℝ) (ht : t < 0) :
    clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
      (physicalRate q branch) a t=
      (power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*
        power (1/2) (1-horizonCoordinate t))*
      (fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a*
        clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)) := by
  have hw := physicalFundamentalFrequency_strip q side
  exact clearedReducedGreen_fundamental_factor _ _ _ _ hw.1 (abs_lt.mp hw.2).1
    (physical_fundamental_roots q side) t ht

/-- No Xi, strip, mode-normalization, or endpoint-admission premise is supplied at the actual source. -/
theorem physicalFundamentalGreen_zero_iff (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (t : ℝ) (ht : t < 0) :
    clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
      (physicalRate q branch) a t=0 ↔
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a=0 ∨
        clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)=0 := by
  have hw := physicalFundamentalFrequency_strip q side
  exact clearedReducedGreen_fundamental_zero_iff _ _ _ _ hw.1 (abs_lt.mp hw.2).1
    (physical_fundamental_roots q side) t ht

/-- The full physical Laurent coefficient retains the angular source, radial moment, onset, and actual denominator slope. -/
theorem physicalSelfResidueCoefficient_fundamental_value (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : ℝ) (ht : t < 0) :
    physicalSelfResidueCoefficient q branch side a t=
      (power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*
        power (1/2) (1-horizonCoordinate t))*
      (physicalSelfSourceCoefficient q*
        fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a*
        clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)/
        physicalFundamentalDenominatorSlope q branch side) := by
  rw [physicalSelfResidueCoefficient,physicalFundamentalGreen_factor q branch side a t ht]
  ring

/-- Full physical pole survival depends on exactly three source scalars, independently of the interior observation point. -/
theorem continuedPhysicalSelfResponse_nonremovable_iff_moment (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : ℝ) (ht : t < 0) :
    (¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) ↔
      physicalSelfSourceCoefficient q ≠ 0 ∧
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a ≠ 0 ∧
      clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side) ≠ 0 := by
  rw [continuedPhysicalSelfResponse_nonremovable_iff q branch side a t ht]
  simp only [ne_eq,physicalFundamentalGreen_zero_iff q branch side a t ht,not_or]

/-- A genuine fundamental pole is present at every interior detector as soon as it is present at one. -/
theorem continuedPhysicalSelfResponse_nonremovable_iff_at (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t u : ℝ) (ht : t < 0) (hu : u < 0) :
    (¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) ↔
    (¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a u)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) := by
  rw [continuedPhysicalSelfResponse_nonremovable_iff_moment q branch side a t ht,
    continuedPhysicalSelfResponse_nonremovable_iff_moment q branch side a u hu]

/-- The evaluated strict-right angular source leaves three affine Xi values and two explicit radial-time source factors. -/
theorem continuedPhysicalSelfResponse_nonremovable_iff_elementary (q : XiZeroCopy)
    (hq : 1/2 < (q.1:ℂ).re) (branch side : Bool) (a : ℂ) (t : ℝ) (ht : t < 0) :
    (¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) ↔
      xi (5*(q.1:ℂ)/2-1) ≠ 0 ∧ xi ((q.1:ℂ)/2) ≠ 0 ∧ xi (3*(q.1:ℂ)/2) ≠ 0 ∧
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a ≠ 0 ∧
      clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side) ≠ 0 := by
  rw [continuedPhysicalSelfResponse_nonremovable_iff_moment q branch side a t ht]
  simp only [ne_eq,physicalSelfSourceCoefficient_zero_iff_xi q hq,not_or,and_assoc]

end
end RHTower.D4BMJointSource
