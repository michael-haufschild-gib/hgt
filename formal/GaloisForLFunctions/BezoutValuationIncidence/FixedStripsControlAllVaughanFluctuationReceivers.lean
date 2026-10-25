import GaloisForLFunctions.BezoutValuationIncidence.PowerCancellationSurvivesTheDampedFloorTransform
import GaloisForLFunctions.BezoutValuationIncidence.UniformVaughanPowerBoundsAreFixedStrips
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicEnergyInTheVaughanConvolution
import GaloisForLFunctions.BezoutValuationIncidence.LogarithmicEnergySavingsForTheMobiusInterior

/-!
A fixed zero-free strip supplies uniform power bounds for every actual
Vaughan fluctuation receiver. The coefficient and floor-transform estimates
also control the bounded finite head in the pronic norm.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A global Mertens power bound is uniform over every truncation of the Möbius coefficients. -/
theorem abs_sum_truncatedMoebius_le_of_mertens_power {B β : ℝ}
    (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hM : ∀ n : ℕ, 1 ≤ n → |∑ d ∈ Icc 1 n, moebiusReal d| ≤ B * (n : ℝ) ^ β)
    (U n : ℕ) :
    |∑ d ∈ Icc 1 n, Sieve.truncatedMoebius U d| ≤ B * (n : ℝ) ^ β := by
  rw [sum_truncatedMoebius_eq_sum_min]
  rcases Nat.eq_zero_or_pos (min U n) with hzero | hpos
  · rw [hzero, Icc_eq_empty (by norm_num), sum_empty, abs_zero]
    positivity
  · exact (hM _ hpos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast min_le_right U n) hβ) hB)

/-- Common power cancellation in bounded patterns yields a common improved pronic norm power. -/
theorem exists_uniform_patternPrefix_pronicNorm_power_of_partial_sum_power
    {ι : Type*} {r : ι → ℕ → ℝ} {ε κ γ B : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hγ : 0 < γ)
    (hγκ : γ < κ * (1 - ε) / (1 + κ)) (hεγ : ε + γ < 1 / 2) (hB : 0 ≤ B)
    (hr : ∀ i : ι, ∀ d : ℕ, |r i d| ≤ 1)
    (hS : ∀ᶠ n : ℕ in atTop, ∀ i,
      |∑ d ∈ Icc 1 n, r i d| ≤ B * (n : ℝ) ^ (1 - κ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ι, ∀ T : ℕ, 1 ≤ T →
      pronicNorm (patternPrefix ε (r i)) T ≤
        C * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) := by
  have hε2 : ε < 1 / 2 := by linarith only [hεγ, hγ]
  have hdiv (i : ι) (d : ℕ) (hd : 1 ≤ d) : |r i d| ≤ 1 * (d.divisors.card : ℝ) ^ 2 := by
    have hcard : (1 : ℝ) ≤ d.divisors.card := by
      exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, by omega⟩⟩)
    exact (hr i d).trans (by nlinarith only [hcard])
  obtain ⟨K, hK, hprefix⟩ := exists_uniform_weightCenteredPrefix_dampedSign_power_of_divisor_square
    hε hε2.le (by norm_num : (0 : ℝ) ≤ 1) hB hκ hγ hγκ hdiv
    (fun i => summable_dampedSignWeight_div_of_abs_le_one hε (hr i)) hS
  have hA : 0 ≤ 1 + 1 / (1 - ε) + 1 / ε := by
    have : 0 < 1 - ε := by linarith only [hε2]
    positivity
  have hlinear (i : ι) (n : ℕ) (hn : 1 ≤ n) :
      |patternPrefix ε (r i) n| ≤ (1 + 1 / (1 - ε) + 1 / ε) * n := by
    have hc : DampedClass 1 ε (dampedSignWeight (r i) ε) := by
      intro d
      rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_mul_of_nonneg_right (hr i d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    have hb : |patternPrefix ε (r i) n| ≤
        (1 + 1 / (1 - ε) + 1 / ε) * (n : ℝ) ^ (1 - ε) := by
      simpa only [patternPrefix, one_mul] using
        abs_weightCenteredPrefix_le_of_dampedClass hε (by linarith only [hε2]) hc hn
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hA)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hn) (by linarith only [hε] : 1 - ε ≤ 1)
  exact exists_uniform_pronicNorm_power_of_eventually_prefix_power
    (by linarith only [hε, hγ]) hεγ hA hK hlinear hprefix

/-- A common undamped Vaughan power gain controls the actual damped convolution norm. -/
theorem exists_uniform_pmVaughanConvolutionFluctuation_pronicNorm_power
    {ε κ γ B : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hγ : 0 < γ)
    (hγκ : γ < κ * (1 - ε) / (1 + κ)) (hεγ : ε + γ < 1 / 2) (hB : 0 ≤ B)
    (hS : ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          B * (n : ℝ) ^ (1 - κ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V T : ℕ, 1 ≤ T →
      pronicNorm (pmVaughanConvolutionFluctuationPrefix ε U V) T ≤
        C * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) := by
  have hε2 : ε ≤ 1 / 2 := by linarith only [hεγ, hγ]
  have hS' : ∀ᶠ n : ℕ in atTop, ∀ a : ℕ × ℕ,
      |∑ d ∈ Icc 1 n, pmVaughanConvolutionFluctuation a.1 a.2 d| ≤ B * (n : ℝ) ^ (1 - κ) := by
    filter_upwards [hS] with n hn a
    simpa only [sum_pmVaughanConvolutionFluctuation] using hn a.1 a.2
  obtain ⟨K, hK, hprefix⟩ := exists_uniform_weightCenteredPrefix_dampedSign_power_of_divisor_square
    hε hε2 (by norm_num : (0 : ℝ) ≤ 2) hB hκ hγ hγκ
    (fun a d hd => abs_pmVaughanConvolutionFluctuation_le a.1 a.2 hd)
    (fun a => summable_pmVaughanConvolutionFluctuation_div hε a.1 a.2) hS'
  have hA : 0 ≤ 2 * ∑' d : ℕ, pmVaughanFloorMajorant ε d / d := by
    exact mul_nonneg (by norm_num) (tsum_nonneg fun d =>
      div_nonneg (pmVaughanFloorMajorant_nonneg ε d) (Nat.cast_nonneg d))
  obtain ⟨C, hC, hnorm⟩ := exists_uniform_pronicNorm_power_of_eventually_prefix_power
    (f := fun a : ℕ × ℕ => pmVaughanConvolutionFluctuationPrefix ε a.1 a.2)
    (by linarith only [hε, hγ]) hεγ hA hK
    (fun a n hn => abs_pmVaughanConvolutionFluctuationPrefix_le_linear hε a.1 a.2 hn) hprefix
  exact ⟨C, hC, fun U V T hT => hnorm (U, V) T hT⟩

/-- A fixed strip supplies one positive norm saving for all actual fluctuating Vaughan sources. -/
theorem exists_uniform_vaughan_source_pronicNorm_power_of_fixed_strip
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hΘ : zetaZeroAbscissa < 1) :
    ∃ γ C : ℝ, 0 < γ ∧ ε + γ < 1 / 2 ∧ 0 ≤ C ∧
      ∀ U V T : ℕ, 1 ≤ T →
        pronicNorm (pmVaughanConvolutionFluctuationPrefix ε U V) T ≤
          C * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) ∧
        pronicNorm (patternPrefix ε (Sieve.truncatedMoebius U)) T ≤
          C * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) ∧
        pronicNorm (pmBezoutInteriorPrefix ε) T ≤
          C * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) := by
  obtain ⟨κ₀, B₀, hκ₀, hB₀, hconv⟩ := zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power.mp hΘ
  obtain ⟨B, β, hB, hβ, hβ1, hM⟩ := zetaZeroAbscissa_lt_one_iff_moebius_rate.mp hΘ
  let κ : ℝ := min κ₀ (1 - β)
  let g : ℝ := κ * (1 - ε) / (1 + κ)
  let γ : ℝ := min g (1 / 2 - ε) / 2
  have hκ : 0 < κ := lt_min hκ₀ (sub_pos.mpr hβ1)
  have hg : 0 < g := by
    have : 0 < 1 - ε := by linarith only [hε2]
    dsimp only [g]
    positivity
  have hγ : 0 < γ := half_pos (lt_min hg (sub_pos.mpr hε2))
  have hγg : γ < g := (half_lt_self (lt_min hg (sub_pos.mpr hε2))).trans_le (min_le_left _ _)
  have hεγ : ε + γ < 1 / 2 := by
    have h := (half_lt_self (lt_min hg (sub_pos.mpr hε2))).trans_le (min_le_right _ _)
    linarith only [h]
  have hκ₀le : κ ≤ κ₀ := min_le_left _ _
  have hβκ : β ≤ 1 - κ := by
    have h := min_le_right κ₀ (1 - β)
    change κ ≤ 1 - β at h
    linarith only [h]
  have hconv' : ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          B₀ * (n : ℝ) ^ (1 - κ) := by
    filter_upwards [hconv, eventually_ge_atTop 1] with n hn hn1 U V
    exact (hn U V).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1)
        (by linarith only [hκ₀le])) hB₀)
  have htrunc : ∀ᶠ n : ℕ in atTop, ∀ U : ℕ,
      |∑ d ∈ Icc 1 n, Sieve.truncatedMoebius U d| ≤ B * (n : ℝ) ^ (1 - κ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn U
    exact (abs_sum_truncatedMoebius_le_of_mertens_power hB hβ hM U n).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hβκ) hB)
  have hmoebius : ∀ᶠ n : ℕ in atTop, ∀ _i : Unit,
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ B * (n : ℝ) ^ (1 - κ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn _i
    exact (hM n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hβκ) hB)
  obtain ⟨A, hA, hr⟩ := exists_uniform_pmVaughanConvolutionFluctuation_pronicNorm_power
    hε hκ hγ hγg hεγ hB₀ hconv'
  obtain ⟨D, hD, ht⟩ := exists_uniform_patternPrefix_pronicNorm_power_of_partial_sum_power
    hε hκ hγ hγg hεγ hB
    (fun U d => by simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d) htrunc
  obtain ⟨E, hE, hm⟩ := exists_uniform_patternPrefix_pronicNorm_power_of_partial_sum_power
    (r := fun _i : Unit => moebiusReal) hε hκ hγ hγg hεγ hB
    (fun _i d => abs_moebiusReal_le_one' d) hmoebius
  refine ⟨γ, A + D + E + 1 / 2, hγ, hεγ, by positivity, fun U V T hT => ?_⟩
  let P : ℝ := Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ)))
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hP1 : 1 ≤ P := by
    have hp := Real.one_le_rpow (by exact_mod_cast hT : (1 : ℝ) ≤ T)
      (by linarith only [hεγ] : 0 ≤ 1 - 2 * (ε + γ))
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
  refine ⟨(hr U V T hT).trans (mul_le_mul_of_nonneg_right
    (by linarith only [hD, hE]) hP),
    (ht U T hT).trans (mul_le_mul_of_nonneg_right
      (by linarith only [hA, hE]) hP), ?_⟩
  have hcenter : pronicNorm (pmPowerDampedCenteredDivisorPrefix ε) T ≤ E * P := by
    simpa only [patternPrefix_moebius_eq_centeredDivisorPrefix hε] using hm () T hT
  have hactive : pronicNorm (fun n => -addDiff (pmActiveSawtoothComponent ε) n) T ≤ 1 / 2 :=
    pronicNorm_le_of_abs_le (by norm_num) (fun n => by
      simpa only [abs_neg] using abs_addDiff_pmActiveSawtoothComponent_le_half hε.le n) T
  have heq : pmBezoutInteriorPrefix ε = fun n =>
      pmPowerDampedCenteredDivisorPrefix ε n + (-addDiff (pmActiveSawtoothComponent ε) n) := by
    funext n
    rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
    ring
  rw [heq]
  refine (pronicNorm_add_le _ _ T).trans ((add_le_add hcenter hactive).trans ?_)
  have hhalf : (1 / 2 : ℝ) ≤ (1 / 2) * P := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hADE : E + 1 / 2 ≤ A + D + E + 1 / 2 := by linarith only [hA, hD]
  calc
    E * P + 1 / 2 ≤ E * P + (1 / 2) * P := add_le_add le_rfl hhalf
    _ = (E + 1 / 2) * P := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hADE hP

#print axioms abs_sum_truncatedMoebius_le_of_mertens_power
#print axioms exists_uniform_patternPrefix_pronicNorm_power_of_partial_sum_power
#print axioms exists_uniform_pmVaughanConvolutionFluctuation_pronicNorm_power
#print axioms exists_uniform_vaughan_source_pronicNorm_power_of_fixed_strip
end GaloisForLFunctions.BezoutValuationIncidence
