import GaloisForLFunctions.RHTower.BandEvenTrialCarrier
import GaloisForLFunctions.RHTower.BandKaiserCentralEnergy
import GaloisForLFunctions.RHTower.ConstrainedProlateSpectralIdentification

/-!
# Refined Kaiser upper bound for the true ground prolate leakage

The central-frequency energy estimate is transported through the actual even `L²(ℝ)` carrier.
The resulting one-dimensional Courant--Fischer trial improves the polynomial prefactor in the
true ground leakage from `c²` to `c^(3/2)` while preserving the exact Fuchs clock `exp (-2c)`.

This remains an upper bound.  Fuchs's two-sided `c^(1/2)` law requires one further power of `c`
from the exterior tail and a matching lower bound.
-/

open Filter MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Physical ground Kaiser trial at aperture `a`, with normalized bandwidth `2*pi*a²`. -/
def kaiserGroundPhysicalEven (a : ℝ) (ha : 0 < a) : evenSubspace :=
  continuousEvenPhysicalTrial a ha
    (kaiserTrial (2 * Real.pi * a ^ 2))
    (continuous_kaiserTrial (2 * Real.pi * a ^ 2))
    (kaiserTrial_even (2 * Real.pi * a ^ 2))

/-- Central-frequency energy factor for the normalized Kaiser trial. -/
def kaiserCentralEnergyFactor (c : ℝ) : ℝ :=
  Real.sqrt c / Real.pi * (Real.exp (c - 1) / (2 * c)) ^ 2

theorem kaiserCentralEnergyFactor_pos {c : ℝ} (hc : 0 < c) :
    0 < kaiserCentralEnergyFactor c := by
  rw [kaiserCentralEnergyFactor]
  positivity

theorem kaiserCentralEnergyFactor_le_norm_sq_groundPhysical
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ 2) :
    kaiserCentralEnergyFactor (2 * Real.pi * a ^ 2) ≤
      ‖kaiserGroundPhysicalEven a ha‖ ^ 2 := by
  rw [kaiserGroundPhysicalEven, norm_sq_continuousEvenPhysicalTrial]
  exact sqrt_mul_exp_sub_one_sq_div_le_energy_kaiserTrial hc

theorem kaiserGroundPhysicalEven_ne_zero
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ 2) :
    kaiserGroundPhysicalEven a ha ≠ 0 := by
  intro hzero
  have hfactor := kaiserCentralEnergyFactor_pos
    (show 0 < 2 * Real.pi * a ^ 2 by positivity)
  have hle := kaiserCentralEnergyFactor_le_norm_sq_groundPhysical ha hc
  rw [hzero, norm_zero] at hle
  norm_num at hle
  linarith

/-- The exact physical defect of the ground Kaiser trial is at most the aperture-free tail
constant `8`. -/
theorem groundPhysicalKaiser_defect_le_eight
    {a : ℝ} (ha : 0 < a) :
    ‖kaiserGroundPhysicalEven a ha‖ ^ 2 -
        ‖evenTimeBandFourier a (kaiserGroundPhysicalEven a ha)‖ ^ 2 ≤ 8 := by
  let c : ℝ := 2 * Real.pi * a ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have htail := integral_tail_kaiser_le (c := c) hc
  have hband : c / (2 * Real.pi) = a ^ 2 := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  rw [kaiserGroundPhysicalEven,
    norm_sq_sub_norm_sq_timeBand_continuousEvenPhysicalTrial]
  simpa only [hband] using htail

/-- Every vector on the ground Kaiser line retains the same explicit fraction of Fourier energy. -/
theorem groundPhysicalKaiser_span_form
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ 2) :
    ∀ f ∈ Submodule.span ℂ ({kaiserGroundPhysicalEven a ha} : Set evenSubspace),
      (1 - 8 / kaiserCentralEnergyFactor (2 * Real.pi * a ^ 2)) * ‖f‖ ^ 2 ≤
        ‖evenTimeBandFourier a f‖ ^ 2 := by
  let E : ℝ := kaiserCentralEnergyFactor (2 * Real.pi * a ^ 2)
  let v : evenSubspace := kaiserGroundPhysicalEven a ha
  have hEpos : 0 < E := kaiserCentralEnergyFactor_pos
    (show 0 < 2 * Real.pi * a ^ 2 by positivity)
  have hEle : E ≤ ‖v‖ ^ 2 := kaiserCentralEnergyFactor_le_norm_sq_groundPhysical ha hc
  have hdefect : ‖v‖ ^ 2 - ‖evenTimeBandFourier a v‖ ^ 2 ≤ 8 :=
    groundPhysicalKaiser_defect_le_eight ha
  have height : 8 ≤ 8 / E * ‖v‖ ^ 2 := by
    calc
      (8 : ℝ) = 8 / E * E := by field_simp
      _ ≤ 8 / E * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hEle (by positivity)
  have hbase : (1 - 8 / E) * ‖v‖ ^ 2 ≤ ‖evenTimeBandFourier a v‖ ^ 2 := by
    nlinarith
  intro f hf
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg ‖z‖)
  simpa only [E, v, map_smul, norm_smul, mul_pow, mul_assoc, mul_left_comm, mul_comm]
    using hscaled

/-- **True ground leakage, refined Kaiser form.**  This is an unconditional theorem about the
actual greedy prolate spectrum. -/
theorem evenProlateLeakageValue_zero_le_kaiserCentral
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ 2) :
    evenProlateLeakageValue a 0 ≤
      8 / kaiserCentralEnergyFactor (2 * Real.pi * a ^ 2) := by
  let v : evenSubspace := kaiserGroundPhysicalEven a ha
  let V : Submodule ℂ evenSubspace := Submodule.span ℂ ({v} : Set evenSubspace)
  have hv : v ≠ 0 := kaiserGroundPhysicalEven_ne_zero ha hc
  have hdim : 0 < Module.finrank ℂ V := by
    change 0 < Module.finrank ℂ (Submodule.span ℂ ({v} : Set evenSubspace))
    rw [finrank_span_singleton hv]
    norm_num
  exact evenProlateLeakageValue_le_of_form_trial a 0 V hdim
    (groundPhysicalKaiser_span_form ha hc)

/-- Signed-spectrum version of the refined true ground leakage bound. -/
theorem one_sub_evenProlateSignedValue_zero_sq_le_kaiserCentral
    {a : ℝ} (ha : 0 < a) (hc : 2 ≤ 2 * Real.pi * a ^ 2) :
    1 - evenProlateSignedValue a 0 ^ 2 ≤
      8 / kaiserCentralEnergyFactor (2 * Real.pi * a ^ 2) := by
  rw [← evenProlateLeakageValue_eq_signedValue_leakage a ha 0]
  exact evenProlateLeakageValue_zero_le_kaiserCentral ha hc

/-- The central Kaiser bound is exactly a `c^(3/2) exp(-2c)` envelope, written without real
powers. -/
theorem eight_div_kaiserCentralEnergyFactor_eq {c : ℝ} (hc : 0 < c) :
    8 / kaiserCentralEnergyFactor c =
      32 * Real.pi * (c ^ 2 / Real.sqrt c) * Real.exp (-(2 * (c - 1))) := by
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hexp : Real.exp (c - 1) ≠ 0 := Real.exp_ne_zero _
  have hpow : Real.exp ((c - 1) * 2) = Real.exp (c - 1) ^ 2 := by
    rw [show (c - 1) * 2 = (c - 1) + (c - 1) by ring, Real.exp_add, pow_two]
  rw [kaiserCentralEnergyFactor, Real.exp_neg]
  field_simp [hsqrt, hexp, Real.pi_ne_zero]
  rw [hpow]
  ring

/-- Eventually, the actual signed ground leakage obeys the refined polynomial Kaiser envelope. -/
theorem eventually_one_sub_evenProlateSignedValue_zero_sq_le_kaiserCentral :
    ∀ᶠ a : ℝ in atTop,
      1 - evenProlateSignedValue a 0 ^ 2 ≤
        32 * Real.pi * (((2 * Real.pi * a ^ 2) ^ 2) /
          Real.sqrt (2 * Real.pi * a ^ 2)) *
            Real.exp (-(2 * (2 * Real.pi * a ^ 2 - 1))) := by
  have hscale : Tendsto (fun a : ℝ => 2 * Real.pi * a ^ 2) atTop atTop := by
    exact (Filter.tendsto_pow_atTop (n := 2) (by norm_num)).const_mul_atTop (by positivity)
  filter_upwards [hscale.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ)] with a hc ha
  rw [← eight_div_kaiserCentralEnergyFactor_eq
    (show 0 < 2 * Real.pi * a ^ 2 by positivity)]
  exact one_sub_evenProlateSignedValue_zero_sq_le_kaiserCentral ha hc

end RHTower

end
