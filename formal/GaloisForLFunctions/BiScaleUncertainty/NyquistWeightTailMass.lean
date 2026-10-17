import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightKernel
import GaloisForLFunctions.BiScaleUncertainty.NyquistPositiveTailComparison

/-! # Explicit and sharp all-tail mass for subcritical Nyquist producers -/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeightTailBound (β : ℝ) (m N : ℕ) : ℝ :=
  ((2 : ℝ) ^ β * β ^ (m + 1) / ((m + 2).factorial : ℝ)) *
    (1 + 1 / ((m : ℝ) + 1 - β)) * ((N + 1 : ℕ) : ℝ) ^ (β - ((m : ℝ) + 1))

theorem nyquistWeightTailMass_zero_parameter (m N : ℕ) :
    nyquistWeightTailMass 0 m N = 0 := by
  simp [nyquistWeightTailMass, nyquistWeightCellMass_zero_parameter]

theorem nyquistWeightTailMass_le {β : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    nyquistWeightTailMass β m N ≤ nyquistWeightTailBound β m N := by
  let p : ℝ := β - ((m + 2 : ℕ) : ℝ)
  let B : ℝ := (2 : ℝ) ^ β * β ^ (m + 1) / ((m + 2).factorial : ℝ)
  have hp : p < -1 := by dsimp [p]; push_cast; linarith
  have hB : 0 ≤ B := by unfold B; positivity
  have hs := (summable_nyquistWeightCellMass_tail_iff hβ m N).mpr hlt
  have hps := summable_nyquistPowerTail hp N
  have hq : -p - 1 = (m : ℝ) + 1 - β := by dsimp [p]; push_cast; ring
  have he : p + 1 = β - ((m : ℝ) + 1) := by dsimp [p]; push_cast; ring
  calc
    _ ≤ ∑' k : ℕ, B * ((N + k + 1 : ℕ) : ℝ) ^ p :=
      Summable.tsum_le_tsum (fun k => nyquistWeightCellMass_le_power hβ.le m (N + k))
        hs (hps.mul_left B)
    _ = B * nyquistPowerTail p N := by
      rw [Summable.tsum_mul_left _ hps]
      rfl
    _ ≤ B * ((1 + 1 / (-p - 1)) * ((N + 1 : ℕ) : ℝ) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left (nyquistPowerTail_le hp N) hB
    _ = nyquistWeightTailBound β m N := by
      rw [hq, he]
      exact (mul_assoc _ _ _).symm

theorem tendsto_nyquistWeightTailBound {β : ℝ} (m : ℕ) (hlt : β < (m : ℝ) + 1) :
    Tendsto (nyquistWeightTailBound β m) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (β - ((m : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < (m : ℝ) + 1 - β)).comp hn
  unfold nyquistWeightTailBound
  simpa only [mul_zero] using ht.const_mul
    (((2 : ℝ) ^ β * β ^ (m + 1) / ((m + 2).factorial : ℝ)) *
      (1 + 1 / ((m : ℝ) + 1 - β)))

theorem tendsto_nyquistWeightTailMass {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (hlt : β < (m : ℝ) + 1) : Tendsto (nyquistWeightTailMass β m) atTop (𝓝 0) :=
  squeeze_zero (nyquistWeightTailMass_nonneg hβ.le m)
    (fun N => nyquistWeightTailMass_le hβ m N hlt) (tendsto_nyquistWeightTailBound m hlt)

theorem tendsto_nyquistWeightTailMass_normalized {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    Tendsto (fun N => nyquistWeightTailMass β m N /
      ((N + 1 : ℕ) : ℝ) ^ (β - ((m : ℝ) + 1))) atTop
      (𝓝 (nyquistWeightCellConstant β m / ((m : ℝ) + 1 - β))) := by
  let p : ℝ := β - ((m + 2 : ℕ) : ℝ)
  have hp : p < -1 := by dsimp [p]; push_cast; linarith
  have ha := (summable_nyquistWeightCellMass_iff hβ m).mpr hlt
  have hb : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p) := by
    simpa only [Nat.zero_add] using summable_nyquistPowerTail hp 0
  have hpos (N : ℕ) : 0 < nyquistPowerTail p N :=
    (summable_nyquistPowerTail hp N).tsum_pos (fun k => (Real.rpow_pos_of_pos
      (by positivity : (0 : ℝ) < (N + k + 1 : ℕ)) p).le) 0
      (Real.rpow_pos_of_pos (by positivity) p)
  have hr := tendsto_nyquist_positive_tail_ratio ha hb
    (fun k => Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) p)
    (tendsto_nyquistWeightCellMass_normalized hβ m)
  change Tendsto (fun N => nyquistWeightTailMass β m N / nyquistPowerTail p N)
    atTop (𝓝 (nyquistWeightCellConstant β m)) at hr
  have ht := hr.mul (tendsto_nyquistPowerTail_normalized hp)
  have heq (N : ℕ) : (nyquistWeightTailMass β m N / nyquistPowerTail p N) *
      (nyquistPowerTail p N / ((N + 1 : ℕ) : ℝ) ^ (p + 1)) =
      nyquistWeightTailMass β m N / ((N + 1 : ℕ) : ℝ) ^ (p + 1) := by
    field_simp [(hpos N).ne']
  have hq : -p - 1 = (m : ℝ) + 1 - β := by dsimp [p]; push_cast; ring
  have he : p + 1 = β - ((m : ℝ) + 1) := by dsimp [p]; push_cast; ring
  have ht' := ht.congr' (Eventually.of_forall heq)
  simpa only [hq, he, mul_one_div] using ht'

end
end GaloisForLFunctions.BiScaleUncertainty
