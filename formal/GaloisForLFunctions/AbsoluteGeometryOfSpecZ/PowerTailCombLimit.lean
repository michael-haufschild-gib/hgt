import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanLimit
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceProfile
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailCombGrowth
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# Convergence of subcritical power combs

The finite polar term cancels the leading reference convolution exactly.
The remaining arithmetic terms are two improper Riemann sums. Whenever
the power parameter plus the actual zero width is below one half, the
prime deviation has an integrable power envelope. The literal comb then
has a finite Mellin-integral limit; RH gives the whole subcritical interval.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart
open SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg)

/-- The finite first degree times the bounded power-prefix discrepancy,
at the normalization of the comb. -/
def powerTailCombRemainder (a : ℝ) (N : ℕ) : ℝ :=
  2 * (N : ℝ) ^ (2 * a - 1) *
    (∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n) *
      (powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a))

/-- The limiting archimedean finite part minus the two summatory Mellin integrals. -/
def powerTailCombMellinIntegral (a : ℝ) : ℝ :=
  powerTailArchimedeanRowLimit a / (1 - 2 * a) -
    2 * (∫ t in Set.Ioc (0 : ℝ) 1, arithmeticPowerProfile (2 * a) (powerTailPrimeDeviation a) t) -
    2 * (∫ t in Set.Ioc (0 : ℝ) 1, powerTailReferenceProfile a t)

/-- Exact finite cancellation of the polar term and the leading reference sum. -/
theorem powerCombTail_eq_mellin_meshes (a : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    powerCombTail a N =
      (N : ℝ) ^ (2 * a - 1) * powerTailArchimedean a N -
        2 * ((N : ℝ) ^ (2 * a - 1) *
          ∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n) -
        2 * tailRiemannSum (powerTailReferenceProfile a) N + powerTailCombRemainder a N := by
  have hd1 : degOne (Icc 1 N) (powerTailWeight a) =
      ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n := by
    apply sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [powerTailWeight, div_eq_mul_inv]
    rw [← Real.rpow_neg_one, ← Real.rpow_add hnR]
    congr 1
    ring
  have hd2 : degTwo (Icc 1 N) (powerTailWeight a) = powerTailPrefix a N := by
    simp only [degTwo, powerTailPrefix, Nat.floor_natCast]
  have htwist : powerTailTwist a ArithmeticFunction.vonMangoldt =
      powerTailPrimeDeviation a + powerTailZeta a := by
    rw [powerTailPrimeDeviation, map_sub]
    change _ = _ - powerTailZeta a + powerTailZeta a
    exact (sub_add_cancel _ _).symm
  have hcontact : (∑ n ∈ Icc 1 N, powerTailContactCoefficient a n) =
      (∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n) +
        ∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailZeta a) n := by
    simp only [powerTailContactCoefficient_eq_convolution, htwist, mul_add,
      ArithmeticFunction.add_apply, sum_add_distrib]
  rw [powerCombTail, combForm_powerTailWeight_eq, hd1, hd2, hcontact,
    tailRiemannSum_powerTailReferenceProfile_eq a hN, powerTailCombRemainder]
  ring

/-- The finite first-degree remainder vanishes throughout the subcritical range. -/
theorem tendsto_powerTailCombRemainder {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    Tendsto (powerTailCombRemainder a) atTop (𝓝 0) := by
  have ha1 : a < 1 := by linarith only [ha2]
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hθ : 0 < 1 - 2 * a := by linarith only [ha2]
  have hz : Tendsto (fun N : ℕ =>
      (2 * powerTailPole a / (1 - a)) * (N : ℝ) ^ (2 * a - 1)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hθ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2 * powerTailPole a / (1 - a))
    simpa only [Function.comp_apply, show -(1 - 2 * a) = 2 * a - 1 by ring, mul_zero] using h
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : 0 ≤ ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n :=
    sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hT := (powerTailPole_sub_sum_bounds ha hN).1
  have hp := powerTailPrefix_sub_integral_bounds ha ha1 hNp.le
  have he : |powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)| ≤ 1 / (1 - a) :=
    abs_le.mpr ⟨hp.1, hp.2.trans (by positivity)⟩
  rw [Real.norm_eq_abs, powerTailCombRemainder, abs_mul, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (Real.rpow_nonneg hNp.le _), abs_of_nonneg hT0]
  calc
    _ ≤ (2 * (N : ℝ) ^ (2 * a - 1) * powerTailPole a) * (1 / (1 - a)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hT]) (by positivity))
        he (abs_nonneg _) (by have := powerTailPole_nonneg a; positivity)
    _ = _ := by ring

/-- The actual zero width supplies the strict growth exponent of the prime error. -/
theorem partialSumPowerBound_primeError_at_zeroWidth :
    RHTower.PartialSumPowerBound RHTower.vonMangoldtMinusOne (1 / 2 + zetaZeroWidth) := by
  apply (RHTower.partialSumPowerBound_iff_convergesRightOf _
    (by linarith only [zetaZeroWidth_nonneg])).mpr
  exact (RHTower.xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges
    zetaZeroWidth_nonneg).mp SquareRootThreshold.xiZeroHalfPlaneBound_zetaZeroWidth

/-- Below the actual width boundary, prime cancellation is strictly stronger
than the threshold required by the power-convolution integral. -/
theorem exists_powerTailPrimeDeviation_bound_of_add_width_lt_half
    {a : ℝ} (ha : 0 < a) (haw : a + zetaZeroWidth < 1 / 2) :
    ∃ β C : ℝ, 0 ≤ β ∧ 2 * a + β < 1 ∧ 0 ≤ C ∧
      ∀ N : ℕ, |∑ n ∈ Icc 1 N, powerTailPrimeDeviation a n| ≤ C * (N : ℝ) ^ β := by
  have ha2 : a < 1 / 2 := by linarith only [haw, zetaZeroWidth_nonneg]
  have hg := partialSumPowerBound_primeError_at_zeroWidth
  have he : (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ)) (n + 1)) =
      RHTower.vonMangoldtMinusOne := by
    funext n
    change ArithmeticFunction.vonMangoldt (n + 1) -
      (ζ : ArithmeticFunction ℝ) (n + 1) =
        ArithmeticFunction.vonMangoldt (n + 1) - 1
    simp
  have hw : RHTower.PartialSumPowerBound (fun n => powerTailPrimeDeviation a (n + 1))
      (1 / 2 + zetaZeroWidth - a) := by
    apply (partialSumPowerBound_powerTailTwist_iff
      (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ)) a (1 / 2 + zetaZeroWidth)
      (by linarith only [zetaZeroWidth_nonneg])
      (by linarith only [ha2, zetaZeroWidth_nonneg])).mpr
    simpa only [he] using hg
  have hs : _root_.HTGeometry.StrictNaturalPowerGrowth
      (fun N => ∑ n ∈ Icc 1 N, powerTailPrimeDeviation a n) (1 / 2 + zetaZeroWidth - a) := by
    apply (_root_.HTGeometry.strictNaturalPowerGrowth_iff_succ (by simp)
      (by linarith only [ha2, zetaZeroWidth_nonneg])).mpr
    simpa only [RHTower.PartialSumPowerBound, RHTower.sum_range_succ_eq_sourcePartialSum,
      RHTower.sourcePartialSum] using hw
  let δ : ℝ := (1 / 2 - a - zetaZeroWidth) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [haw]
  obtain ⟨C, hC, hbound⟩ := hs δ hδ
  refine ⟨1 / 2 + zetaZeroWidth - a + δ, C,
    by dsimp only [δ]; linarith only [ha2, zetaZeroWidth_nonneg],
    by dsimp only [δ]; linarith only [haw], hC, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, abs_zero]
    positivity
  · exact hbound N hN

/-- RH supplies the full subcritical range of prime-error power envelopes. -/
theorem exists_powerTailPrimeDeviation_bound_of_rh (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ β C : ℝ, 0 ≤ β ∧ 2 * a + β < 1 ∧ 0 ≤ C ∧
      ∀ N : ℕ, |∑ n ∈ Icc 1 N, powerTailPrimeDeviation a n| ≤ C * (N : ℝ) ^ β := by
  apply exists_powerTailPrimeDeviation_bound_of_add_width_lt_half ha
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH, add_zero]
  exact ha2

/-- Every positive power below the actual zero-width boundary converges,
with no assumed zero-free half-plane or analytic input. -/
theorem tendsto_powerCombTail_of_add_width_lt_half
    {a : ℝ} (ha : 0 < a) (haw : a + zetaZeroWidth < 1 / 2) :
    Tendsto (powerCombTail a) atTop (𝓝 (powerTailCombMellinIntegral a)) := by
  have ha2 : a < 1 / 2 := by linarith only [haw, zetaZeroWidth_nonneg]
  obtain ⟨β, C, hβ, hsub, hC, hbound⟩ :=
    exists_powerTailPrimeDeviation_bound_of_add_width_lt_half ha haw
  have hp := tendsto_normalized_power_convolution (show 0 ≤ 2 * a by linarith only [ha])
    hβ (show 0 < 2 * a + β by linarith only [ha, hβ]) hsub hC hbound
  have hr := (riemannOn_powerTailReferenceProfile ha ha2).2
  have h := (((tendsto_normalized_powerTailArchimedean ha ha2).sub (hp.const_mul 2)).sub
    (hr.const_mul 2)).add (tendsto_powerTailCombRemainder ha ha2)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (powerCombTail_eq_mellin_meshes a hN).symm

/-- Under RH every positive subcritical power comb has its Mellin-integral limit. -/
theorem tendsto_powerCombTail_of_rh (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    Tendsto (powerCombTail a) atTop (𝓝 (powerTailCombMellinIntegral a)) := by
  apply tendsto_powerCombTail_of_add_width_lt_half ha
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH, add_zero]
  exact ha2

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
