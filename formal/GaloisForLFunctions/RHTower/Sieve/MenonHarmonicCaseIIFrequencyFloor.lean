import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIFrequencyRange
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCentralDiscSchedule

namespace RHTower.Sieve

open Filter Finset

noncomputable section

def menonHarmonicCaseIIFloorEnvelopeConstant : ℝ :=
  6 * (menonHarmonicCaseIICrossConstant + 2) * (2 : ℝ) ^ (1856 : ℕ)

theorem menonHarmonicCaseIIFloorEnvelopeConstant_nonneg :
    0 ≤ menonHarmonicCaseIIFloorEnvelopeConstant := by
  rw [menonHarmonicCaseIIFloorEnvelopeConstant]
  positivity [menonHarmonicCaseIICrossConstant_nonneg]

set_option maxHeartbeats 800000 in
theorem eventually_menonHarmonicCaseIIFrequencyFloor_le_central :
    ∀ᶠ x : ℝ in atTop,
      ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        menonHarmonicCaseIIFrequencyFloor (menonFinalRangeBlockLowerNat x j) ≤
          2 * Real.pi * menonHarmonicCentralRadius x := by
  let C := menonHarmonicCaseIIFloorEnvelopeConstant
  have hlim : Tendsto (fun x : ℝ => (Real.log x) ^ (144 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (144 : ℝ))).comp Real.tendsto_log_atTop
  have hlarge := hlim.eventually_ge_atTop C
  filter_upwards [hlarge, eventually_menonFinalRangeActualBlock_caseII_endpoints,
    eventually_ge_atTop (Real.exp 3)] with x hlarge hendpoints hx
  intro j hj
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let t := Real.log x
  let la := Real.log (a : ℝ)
  let cells : ℝ := menonHarmonicCaseIICells a
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 3) hx
  have ht3 : 3 ≤ t := by
    dsimp only [t]
    simpa using Real.log_le_log (Real.exp_pos 3) hx
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rcases hendpoints j hj with ⟨ha64, haY, hYa⟩
  have hYtop : Y ≤ menonFinalRangeTopNat x := by
    dsimp only [Y, menonFinalRangeActualBlockUpperNat]
    exact min_le_left _ _
  have haTop : a ≤ menonFinalRangeTopNat x := haY.le.trans hYtop
  have htop : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have haTopR : (a : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) := by
    exact_mod_cast haTop
  have ha3x : (a : ℝ) ≤ 3 * x := haTopR.trans htop
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hlogA : 1 ≤ la := by
    dsimp only [la]
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hlog' := Real.log_le_log (Real.exp_pos 1) (hexpThree.le.trans haThree)
    simpa using hlog'
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans_eq (by norm_num)
  have hla : la ≤ 2 * t := by
    have hlogle := Real.log_le_log ha0 ha3x
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx0)] at hlogle
    dsimp only [la, t] at hlogle ⊢
    nlinarith
  have hla0 : 0 ≤ la := zero_le_one.trans hlogA
  have h2t0 : 0 ≤ 2 * t := by positivity
  have hpow1856 : la ^ (1856 : ℕ) ≤ (2 * t) ^ (1856 : ℕ) :=
    pow_le_pow_left₀ hla0 hla 1856
  have hpow200 : la ^ (200 : ℕ) ≤ la ^ (1856 : ℕ) :=
    pow_le_pow_right₀ hlogA (by omega)
  have hcells := menonHarmonicCaseIICells_cast_bounds hlogA
  have hcellsUpper : cells ≤ 2 * la ^ (200 : ℕ) := by
    simpa only [cells, la] using hcells.2
  have hfloor : menonHarmonicCaseIIFrequencyFloor a ≤
      6 * (menonHarmonicCaseIICrossConstant + 2) * (2 * t) ^ (1856 : ℕ) := by
    rw [menonHarmonicCaseIIFrequencyFloor]
    calc
      6 * (menonHarmonicCaseIICrossConstant + 1) * la ^ (1856 : ℕ) + 3 * cells ≤
          6 * (menonHarmonicCaseIICrossConstant + 1) * la ^ (1856 : ℕ) +
            3 * (2 * la ^ (200 : ℕ)) := by
              gcongr
      _ ≤ 6 * (menonHarmonicCaseIICrossConstant + 2) * la ^ (1856 : ℕ) := by
        have hK := menonHarmonicCaseIICrossConstant_nonneg
        have hp0 : 0 ≤ la ^ (200 : ℕ) := by positivity
        have hp' := mul_le_mul_of_nonneg_left hpow200 (by norm_num : (0 : ℝ) ≤ 6)
        nlinarith
      _ ≤ 6 * (menonHarmonicCaseIICrossConstant + 2) * (2 * t) ^ (1856 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hpow1856 (by
          positivity [menonHarmonicCaseIICrossConstant_nonneg])
  have hfloorC : menonHarmonicCaseIIFrequencyFloor a ≤ C * t ^ (1856 : ℕ) := by
    calc
      menonHarmonicCaseIIFrequencyFloor a ≤
          6 * (menonHarmonicCaseIICrossConstant + 2) * (2 * t) ^ (1856 : ℕ) := hfloor
      _ = C * t ^ (1856 : ℕ) := by
        rw [mul_pow]
        simp only [C, menonHarmonicCaseIIFloorEnvelopeConstant]
        ring
  have hlargeNat : C ≤ t ^ (144 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact hlarge
  have hcentral : C * t ^ (1856 : ℕ) ≤ t ^ (2000 : ℕ) := by
    calc
      C * t ^ (1856 : ℕ) ≤ t ^ (144 : ℕ) * t ^ (1856 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hlargeNat (by positivity)
      _ = t ^ (2000 : ℕ) := by ring
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    menonHarmonicCaseIIFrequencyFloor a ≤ t ^ (2000 : ℕ) := hfloorC.trans hcentral
    _ ≤ 2 * Real.pi * t ^ (2000 : ℕ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ t ^ (2000 : ℕ))
    _ = 2 * Real.pi * menonHarmonicCentralRadius x := by
      simp only [menonHarmonicCentralRadius, t]

end

end RHTower.Sieve
