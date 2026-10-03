import GaloisForLFunctions.RHTower.SuzukiTaV2PrescribedEnergySource
import GaloisForLFunctions.RHTower.SuzukiMovableDefectAnchor

open Filter
open GaloisForLFunctions.HTGeometry
open scoped Topology
noncomputable section
namespace RHTower

/-- Common scale of the actual prescribed-shift V2 parity energies. -/
def suzukiTaV2PrescribedScale (a : SuzukiPositiveAperture) : ℝ :=
  boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) * Real.exp (-2 * a.1)

theorem suzukiTaV2PrescribedScale_pos (a : SuzukiPositiveAperture) :
    0 < suzukiTaV2PrescribedScale a :=
  mul_pos (boundedPerturbedFormShift_pos _) (Real.exp_pos _)

theorem tendsto_suzukiTaV2_rawSource_profile_norm :
    Tendsto (fun a : SuzukiPositiveAperture =>
      ‖ccmArchimedeanFormToAperture a
        (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le (norm_nonneg _)
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaV2_rawSource_profile (ε ^ 2)
      (sq_pos_of_pos hε))] with a ha
    have h := ha a.2
    nlinarith [norm_nonneg (ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a 1))]

private theorem exp_neg_two_mul_sinh (a : ℝ) :
    Real.exp (-2 * a) * Real.sinh (2 * a) = (1 - Real.exp (-4 * a)) / 2 := by
  have hp : Real.exp (-2 * a) * Real.exp (2 * a) = 1 := by
    rw [← Real.exp_add, show -2 * a + 2 * a = 0 by ring, Real.exp_zero]
  have hm : Real.exp (-2 * a) * Real.exp (-(2 * a)) = Real.exp (-4 * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq]
  calc
    _ = (Real.exp (-2 * a) * Real.exp (2 * a) -
        Real.exp (-2 * a) * Real.exp (-(2 * a))) / 2 := by ring
    _ = _ := by rw [hp, hm]

/-- The actual prescribed shift has a nonzero scaled diagonal limit and a
vanishing signed cross-source limit. -/
theorem tendsto_suzukiTaV2_prescribed_energy_sum_sub :
    Tendsto (fun a : SuzukiPositiveAperture => suzukiTaV2PrescribedScale a *
      (suzukiTaCoalescingEvenEnergy a 1 + suzukiTaCoalescingOddEnergy a 1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 (1 / 2)) ∧
    Tendsto (fun a : SuzukiPositiveAperture => suzukiTaV2PrescribedScale a *
      (suzukiTaCoalescingEvenEnergy a 1 - suzukiTaCoalescingOddEnergy a 1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  let l := comap (fun a : SuzukiPositiveAperture => a.1) atTop
  let S := fun a : SuzukiPositiveAperture => suzukiTaV2PrescribedScale a *
    (suzukiTaCoalescingEvenEnergy a 1 + suzukiTaCoalescingOddEnergy a 1)
  let D := fun a : SuzukiPositiveAperture => suzukiTaV2PrescribedScale a *
    (suzukiTaCoalescingEvenEnergy a 1 - suzukiTaCoalescingOddEnergy a 1)
  let M := fun a : SuzukiPositiveAperture => Real.exp (-2 * a.1) * Real.sinh (2 * a.1)
  let N := fun a : SuzukiPositiveAperture => 2 * a.1 * Real.exp (-2 * a.1)
  let δ := fun a : SuzukiPositiveAperture => ‖ccmArchimedeanFormToAperture a
    (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
      ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1) l atTop := tendsto_comap
  have h4 : Tendsto (fun a : SuzukiPositiveAperture => 4 * a.1) l atTop :=
    hv.const_mul_atTop (by norm_num)
  have h2 : Tendsto (fun a : SuzukiPositiveAperture => 2 * a.1) l atTop :=
    hv.const_mul_atTop (by norm_num)
  have hneg : Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-4 * a.1)) l (𝓝 0) := by
    simpa only [pow_zero, one_mul, Function.comp_def, neg_mul] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp h4
  have hN : Tendsto N l (𝓝 0) := by
    simpa only [pow_one, Function.comp_def, neg_mul, N] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h2
  have hM : Tendsto M l (𝓝 (1 / 2)) := by
    have h := ((tendsto_const_nhds : Tendsto
      (fun _ : SuzukiPositiveAperture => (1 : ℝ)) l (𝓝 1)).sub hneg).div_const (2 : ℝ)
    simpa only [sub_zero, exp_neg_two_mul_sinh, M] using h
  have hbound : Tendsto (fun a => C * δ a) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_suzukiTaV2_rawSource_profile_norm.const_mul C
  have hSabs : Tendsto (fun a => |S a - M a|) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun a => (suzukiTaV2_scaled_energy_source_errors a).1) hbound
  have hDabs : Tendsto (fun a => |D a - N a|) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun a => (suzukiTaV2_scaled_energy_source_errors a).2) hbound
  have hSerr : Tendsto (fun a => S a - M a) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero, Real.norm_eq_abs] using hSabs
  have hDerr : Tendsto (fun a => D a - N a) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero, Real.norm_eq_abs] using hDabs
  constructor
  · simpa only [sub_add_cancel, zero_add] using hSerr.add hM
  · simpa only [sub_add_cancel, zero_add] using hDerr.add hN

/-- Both actual V2 parity energies have the same nonzero limit under the
common prescribed-shift scale. -/
theorem tendsto_suzukiTaV2_prescribed_parity_energies :
    Tendsto (fun a : SuzukiPositiveAperture => suzukiTaV2PrescribedScale a *
      suzukiTaCoalescingEvenEnergy a 1)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 (1 / 4)) ∧
    Tendsto (fun a : SuzukiPositiveAperture => suzukiTaV2PrescribedScale a *
      suzukiTaCoalescingOddEnergy a 1)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 (1 / 4)) := by
  obtain ⟨hs, hd⟩ := tendsto_suzukiTaV2_prescribed_energy_sum_sub
  constructor
  · have h := (hs.add hd).div_const (2 : ℝ)
    norm_num only [add_zero, div_div] at h
    convert h using 1
    ext a
    ring
  · have h := (hs.sub hd).div_const (2 : ℝ)
    norm_num only [sub_zero, div_div] at h
    convert h using 1
    ext a
    ring

/-- The actual prescribed-shift first defect collapses to zero. All source,
metric, scale and nonzero denominator obligations are discharged. -/
theorem tendsto_suzukiTaV2_prescribed_firstDefect_zero :
    Tendsto (fun a : SuzukiPositiveAperture =>
      GaloisForLFunctions.RHTower.suzukiDefectAngle
        (suzukiTaCoalescingEvenEnergy a 1) (suzukiTaCoalescingOddEnergy a 1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  obtain ⟨he, ho⟩ := tendsto_suzukiTaV2_prescribed_parity_energies
  have h := GaloisForLFunctions.RHTower.tendsto_suzukiDefectAngle_of_scaled_energies
    (Eventually.of_forall fun a => (suzukiTaV2PrescribedScale_pos a).ne') he ho
    (by norm_num : (1 / 4 : ℝ) + 1 / 4 ≠ 0)
  simpa only [sub_self, zero_div] using h

end RHTower
end
