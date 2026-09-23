import GaloisForLFunctions.RHTower.BandKaiserGroundTrueLeakage
import GaloisForLFunctions.RHTower.BandKaiserLogTail

/-!
# Logarithmically refined true ground prolate leakage

Combining the exact physical carrier, the central-window Kaiser energy lower bound, and the sharp
exterior `log(c) / c` tail proves an unconditional theorem for the actual ground prolate spectrum:

```text
1 - mu_0(a)^(2 : ℕ) <= 16 c (2 + log c) / sqrt(c) * exp(-2(c-1)),
c = 2*pi*a^(2 : ℕ).
```

This is within one logarithm of the fixed-index Fuchs ground-state prefactor.
-/

open Filter MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Exact physical Kaiser defect with the logarithmically sharp exterior-tail bound. -/
theorem groundPhysicalKaiser_defect_le_log
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ (2 : ℕ)) :
    ‖kaiserGroundPhysicalEven a ha‖ ^ (2 : ℕ) -
        ‖evenTimeBandFourier a (kaiserGroundPhysicalEven a ha)‖ ^ (2 : ℕ) ≤
      (8 + 4 * Real.log (2 * Real.pi * a ^ (2 : ℕ))) /
        (Real.pi * (2 * Real.pi * a ^ (2 : ℕ))) := by
  let c : ℝ := 2 * Real.pi * a ^ (2 : ℕ)
  have htail := integral_tail_kaiser_log_le (c := c) hc
  have hband : c / (2 * Real.pi) = a ^ (2 : ℕ) := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  rw [kaiserGroundPhysicalEven,
    norm_sq_sub_norm_sq_timeBand_continuousEvenPhysicalTrial]
  simpa only [c, hband] using htail

/-- Every vector on the Kaiser ground line retains the refined explicit Fourier-energy fraction. -/
theorem groundPhysicalKaiser_span_form_log
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ (2 : ℕ)) :
    ∀ f ∈ Submodule.span ℂ ({kaiserGroundPhysicalEven a ha} : Set evenSubspace),
      (1 - ((8 + 4 * Real.log (2 * Real.pi * a ^ (2 : ℕ))) /
          (Real.pi * (2 * Real.pi * a ^ (2 : ℕ)))) /
            kaiserCentralEnergyFactor (2 * Real.pi * a ^ (2 : ℕ))) * ‖f‖ ^ (2 : ℕ) ≤
        ‖evenTimeBandFourier a f‖ ^ (2 : ℕ) := by
  let c : ℝ := 2 * Real.pi * a ^ (2 : ℕ)
  let E : ℝ := kaiserCentralEnergyFactor c
  let T : ℝ := (8 + 4 * Real.log c) / (Real.pi * c)
  let v : evenSubspace := kaiserGroundPhysicalEven a ha
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hEpos : 0 < E := kaiserCentralEnergyFactor_pos hcpos
  have hEle : E ≤ ‖v‖ ^ (2 : ℕ) := kaiserCentralEnergyFactor_le_norm_sq_groundPhysical ha hc
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    have hlog : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
    positivity
  have hdefect : ‖v‖ ^ (2 : ℕ) - ‖evenTimeBandFourier a v‖ ^ (2 : ℕ) ≤ T := by
    exact groundPhysicalKaiser_defect_le_log ha hc
  have htail : T ≤ T / E * ‖v‖ ^ (2 : ℕ) := by
    calc
      T = T / E * E := by field_simp [hEpos.ne']
      _ ≤ T / E * ‖v‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hEle (div_nonneg hTnonneg hEpos.le)
  have hbase : (1 - T / E) * ‖v‖ ^ (2 : ℕ) ≤ ‖evenTimeBandFourier a v‖ ^ (2 : ℕ) := by
    nlinarith
  intro f hf
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg ‖z‖)
  simpa only [c, E, T, v, map_smul, norm_smul, mul_pow,
    mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- **True ground leakage with the logarithmic Kaiser refinement.** -/
theorem evenProlateLeakageValue_zero_le_kaiserLog
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ (2 : ℕ)) :
    evenProlateLeakageValue a 0 ≤
      ((8 + 4 * Real.log (2 * Real.pi * a ^ (2 : ℕ))) /
        (Real.pi * (2 * Real.pi * a ^ (2 : ℕ)))) /
          kaiserCentralEnergyFactor (2 * Real.pi * a ^ (2 : ℕ)) := by
  let v : evenSubspace := kaiserGroundPhysicalEven a ha
  let V : Submodule ℂ evenSubspace := Submodule.span ℂ ({v} : Set evenSubspace)
  have hv : v ≠ 0 := kaiserGroundPhysicalEven_ne_zero ha hc
  have hdim : 0 < Module.finrank ℂ V := by
    change 0 < Module.finrank ℂ (Submodule.span ℂ ({v} : Set evenSubspace))
    rw [finrank_span_singleton hv]
    norm_num
  exact evenProlateLeakageValue_le_of_form_trial a 0 V hdim
    (groundPhysicalKaiser_span_form_log ha hc)

/-- Signed-spectrum form of the logarithmically refined true ground leakage bound. -/
theorem one_sub_evenProlateSignedValue_zero_sq_le_kaiserLog
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ (2 : ℕ)) :
    1 - evenProlateSignedValue a 0 ^ (2 : ℕ) ≤
      ((8 + 4 * Real.log (2 * Real.pi * a ^ (2 : ℕ))) /
        (Real.pi * (2 * Real.pi * a ^ (2 : ℕ)))) /
          kaiserCentralEnergyFactor (2 * Real.pi * a ^ (2 : ℕ)) := by
  rw [← evenProlateLeakageValue_eq_signedValue_leakage a ha 0]
  exact evenProlateLeakageValue_zero_le_kaiserLog ha hc

/-- Closed algebraic form of the refined quotient. -/
theorem kaiserLogTail_div_centralEnergy_eq {c : ℝ} (hc : 0 < c) :
    ((8 + 4 * Real.log c) / (Real.pi * c)) / kaiserCentralEnergyFactor c =
      16 * (c * (2 + Real.log c) / Real.sqrt c) *
        Real.exp (-(2 * (c - 1))) := by
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hexp : Real.exp (c - 1) ≠ 0 := Real.exp_ne_zero _
  have hpow : Real.exp ((c - 1) * 2) = Real.exp (c - 1) ^ (2 : ℕ) := by
    rw [show (c - 1) * 2 = (c - 1) + (c - 1) by ring, Real.exp_add, pow_two]
  rw [kaiserCentralEnergyFactor, Real.exp_neg]
  field_simp [hsqrt, hexp, Real.pi_ne_zero]
  rw [hpow]
  ring

/-- Eventually, actual signed ground leakage obeys the `sqrt(c) log(c) exp(-2c)` envelope. -/
theorem eventually_one_sub_evenProlateSignedValue_zero_sq_le_kaiserLog :
    ∀ᶠ a : ℝ in atTop,
      1 - evenProlateSignedValue a 0 ^ (2 : ℕ) ≤
        16 * ((2 * Real.pi * a ^ (2 : ℕ)) *
          (2 + Real.log (2 * Real.pi * a ^ (2 : ℕ))) /
            Real.sqrt (2 * Real.pi * a ^ (2 : ℕ))) *
              Real.exp (-(2 * (2 * Real.pi * a ^ (2 : ℕ) - 1))) := by
  have hscale : Tendsto (fun a : ℝ => 2 * Real.pi * a ^ (2 : ℕ)) atTop atTop := by
    exact (Filter.tendsto_pow_atTop (n := 2) (by norm_num)).const_mul_atTop (by positivity)
  filter_upwards [hscale.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ)] with a hc ha
  rw [← kaiserLogTail_div_centralEnergy_eq
    (show 0 < 2 * Real.pi * a ^ (2 : ℕ) by positivity)]
  exact one_sub_evenProlateSignedValue_zero_sq_le_kaiserLog ha hc

end RHTower

end
