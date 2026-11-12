import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCriticalPowerCombDoesNotConverge
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicAbelMeans
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# Subpolynomial critical comb growth detects RH

At the critical exponent, convolution by `n⁻¹` still preserves every
strict nonnegative growth threshold. Removing the remaining `n⁻¹ᐟ²`
weight turns subpolynomial contact growth into the square-root prime-error
bound. Subtracting the forced harmonic drift and restoring the convergent
elementary remainder preserves this equivalence for the literal comb.
Ordinary divergence excludes negative thresholds, so the full threshold
set is the closed ray starting at `zetaZeroWidth`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity

/-- Harmonic numbers have every positive power bound. -/
theorem strictGrowth_harm : _root_.HTGeometry.StrictNaturalPowerGrowth harm 0 := by
  intro δ hδ
  let α : ℝ := min δ (1 / 2)
  have hα : 0 < α := lt_min hδ (by norm_num)
  have hα1 : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hαδ : α ≤ δ := min_le_left _ _
  refine ⟨1 / α, by positivity, fun N hN => ?_⟩
  have hH0 : 0 ≤ harm N := by unfold harm; positivity
  rw [abs_of_nonneg hH0, harm, zero_add]
  calc
    _ ≤ ∑ n ∈ range N, ((n : ℝ) + 1) ^ (α - 1) := by
      apply sum_le_sum
      intro n _
      have hp := Real.rpow_le_rpow_of_exponent_le
        (le_add_of_nonneg_left (Nat.cast_nonneg n) : (1 : ℝ) ≤ (n : ℝ) + 1)
        (by linarith only [hα] : (-1 : ℝ) ≤ α - 1)
      simpa only [Real.rpow_neg_one, one_div] using hp
    _ ≤ (N : ℝ) ^ α / α := _root_.HTGeometry.sum_rpow_sub_one_le hα hα1 N
    _ ≤ (N : ℝ) ^ δ / α := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hαδ) hα.le
    _ = _ := by ring

/-- Critical contacts retain the exact growth/zero-half-plane equivalence
at every nonnegative exponent, including zero. -/
theorem strictGrowth_criticalPowerContactPrefix_iff_zeroHalfPlane
    {σ : ℝ} (hσ : 0 ≤ σ) :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerContactPrefix (1 / 2)) σ ↔
      RHTower.XiZeroHalfPlaneBound σ := by
  have hp : _root_.HTGeometry.StrictNaturalPowerGrowth (powerContactPrefix (1 / 2)) σ ↔
      RHTower.PartialSumPowerBound
        (fun n => (powerTailZeta 1 * powerTailPrimeDeviation (1 / 2)) (n + 1)) σ := by
    simpa only [RHTower.PartialSumPowerBound, RHTower.sum_range_succ_eq_sourcePartialSum,
      RHTower.sourcePartialSum, powerContactPrefix,
      show 2 * (1 / 2 : ℝ) = 1 by norm_num] using
        (_root_.HTGeometry.strictNaturalPowerGrowth_iff_succ
          (by simp [powerContactPrefix] : powerContactPrefix (1 / 2) 0 = 0)
          hσ)
  have hc := partialSumPowerBound_powerTailZeta_mul_iff 1 σ
    hσ (by linarith only [hσ]) (powerTailPrimeDeviation (1 / 2))
  have hw := partialSumPowerBound_powerTailTwist_iff
    (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ))
    (1 / 2) (1 / 2 + σ) (by linarith only [hσ]) (by linarith only [hσ])
  have he : (fun n => (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ)) (n + 1)) =
      RHTower.vonMangoldtMinusOne := by
    funext n
    change ArithmeticFunction.vonMangoldt (n + 1) - (ζ : ArithmeticFunction ℝ) (n + 1) =
      ArithmeticFunction.vonMangoldt (n + 1) - 1
    simp
  have hw' : RHTower.PartialSumPowerBound
      (fun n => powerTailPrimeDeviation (1 / 2) (n + 1)) σ ↔
        RHTower.PartialSumPowerBound RHTower.vonMangoldtMinusOne (1 / 2 + σ) := by
    simpa only [show 1 / 2 + σ - (1 / 2 : ℝ) = σ by ring,
      powerTailPrimeDeviation, he] using hw
  have hz := RHTower.xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges hσ
  have hz' : RHTower.ConvergesRightOf RHTower.vonMangoldtMinusOne (1 / 2 + σ) ↔
      RHTower.XiZeroHalfPlaneBound σ := by
    simpa only [RHTower.ConvergesRightOf] using hz.symm
  exact hp.trans (hc.trans (hw'.trans
    ((RHTower.partialSumPowerBound_iff_convergesRightOf _ (by linarith only [hσ])).trans hz')))

/-- Subpolynomial critical contacts are equivalent to RH. -/
theorem strictGrowth_criticalPowerContactPrefix_iff_rh :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerContactPrefix (1 / 2)) 0 ↔
      RiemannHypothesis :=
  (strictGrowth_criticalPowerContactPrefix_iff_zeroHalfPlane (le_refl (0 : ℝ))).trans
    _root_.RHTower.xiZeroHalfPlaneBound_zero_iff_rh

/-- Removing the forced harmonic drift does not change the critical
contact growth criterion. -/
theorem strictGrowth_criticalHarmonicContacts_iff_zeroHalfPlane
    {σ : ℝ} (hσ : 0 ≤ σ) :
    _root_.HTGeometry.StrictNaturalPowerGrowth criticalHarmonicContacts σ ↔
      RHTower.XiZeroHalfPlaneBound σ := by
  have hh := (strictGrowth_harm.mono hσ).const_mul criticalPowerContactCoefficient
  constructor
  · intro hg
    apply (strictGrowth_criticalPowerContactPrefix_iff_zeroHalfPlane hσ).mp
    simpa only [criticalHarmonicContacts, sub_add_cancel] using hg.add hh
  · intro hz
    exact ((strictGrowth_criticalPowerContactPrefix_iff_zeroHalfPlane hσ).mpr hz).sub hh

/-- Harmonic subtraction preserves the subpolynomial RH criterion. -/
theorem strictGrowth_criticalHarmonicContacts_iff_rh :
    _root_.HTGeometry.StrictNaturalPowerGrowth criticalHarmonicContacts 0 ↔
      RiemannHypothesis :=
  (strictGrowth_criticalHarmonicContacts_iff_zeroHalfPlane (le_refl (0 : ℝ))).trans
    _root_.RHTower.xiZeroHalfPlaneBound_zero_iff_rh

/-- The elementary critical comb after both harmonic main terms are removed. -/
def criticalPowerCombElementaryRemainder (N : ℕ) : ℝ :=
  (powerTailArchimedean (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2) * harm N) -
    2 * tailRiemannSum criticalPowerTailReferenceProfile N + powerTailCombRemainder (1 / 2) N

/-- Its constant is expressed by an absolutely summable row correction
and an integrable reference profile. -/
def criticalPowerCombElementaryLimit : ℝ :=
  (∑' n : ℕ, criticalPowerTailArchimedeanError n) -
    2 * (∫ t in Set.Ioc (0 : ℝ) 1, criticalPowerTailReferenceProfile t) +
      2 * powerTailPole (1 / 2) * (riemannZeta ((1 / 2 : ℝ) : ℂ)).re

theorem tendsto_criticalPowerCombElementaryRemainder :
    Tendsto criticalPowerCombElementaryRemainder atTop (𝓝 criticalPowerCombElementaryLimit) := by
  have hA := summable_criticalPowerTailArchimedeanError.hasSum.tendsto_sum_nat.congr
    (fun N => sum_criticalPowerTailArchimedeanError N)
  exact (hA.sub (riemannOn_criticalPowerTailReferenceProfile.2.const_mul 2)).add
    tendsto_criticalPowerTailCombRemainder

/-- The critical comb is a convergent elementary term minus twice its
harmonically centered contacts. -/
theorem powerCombTail_half_eq_elementary_sub_contacts {N : ℕ} (hN : 1 ≤ N) :
    powerCombTail (1 / 2) N =
      criticalPowerCombElementaryRemainder N - 2 * criticalHarmonicContacts N := by
  rw [powerCombTail_eq_mellin_meshes (1 / 2) hN]
  simp only [show 2 * (1 / 2 : ℝ) - 1 = 0 by ring, Real.rpow_zero, one_mul]
  dsimp only [criticalPowerCombElementaryRemainder, criticalHarmonicContacts,
    criticalPowerContactCoefficient, powerContactPrefix]
  rw [tailRiemannSum_criticalPowerTailReferenceProfile hN]
  ring

private theorem strictGrowth_congr_pos {f g : ℕ → ℝ} {θ : ℝ}
    (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ)
    (he : ∀ N : ℕ, 1 ≤ N → f N = g N) :
    _root_.HTGeometry.StrictNaturalPowerGrowth g θ := by
  intro δ hδ
  obtain ⟨C, hC, hb⟩ := hf δ hδ
  refine ⟨C, hC, fun N hN => ?_⟩
  rw [← he N hN]
  exact hb N hN

/-- The critical literal comb reads the same zero half-plane as its
contacts, at every nonnegative growth threshold. -/
theorem strictGrowth_criticalPowerCombTail_iff_zeroHalfPlane
    {σ : ℝ} (hσ : 0 ≤ σ) :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerCombTail (1 / 2)) σ ↔
      RHTower.XiZeroHalfPlaneBound σ := by
  have hE := (strictPowerGrowth_zero_of_tendsto
    tendsto_criticalPowerCombElementaryRemainder).mono hσ
  constructor
  · intro hc
    apply (strictGrowth_criticalHarmonicContacts_iff_zeroHalfPlane hσ).mp
    apply strictGrowth_congr_pos ((hE.sub hc).const_mul (1 / 2))
    intro N hN
    rw [powerCombTail_half_eq_elementary_sub_contacts hN]
    ring
  · intro hz
    have hg := (strictGrowth_criticalHarmonicContacts_iff_zeroHalfPlane hσ).mpr hz
    exact strictGrowth_congr_pos (hE.sub (hg.const_mul 2)) fun N hN =>
      (powerCombTail_half_eq_elementary_sub_contacts hN).symm

/-- The critical literal comb has every positive power bound exactly
under RH, despite its failure of ordinary convergence. -/
theorem strictGrowth_criticalPowerCombTail_iff_rh :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerCombTail (1 / 2)) 0 ↔
      RiemannHypothesis :=
  (strictGrowth_criticalPowerCombTail_iff_zeroHalfPlane (le_refl (0 : ℝ))).trans
    _root_.RHTower.xiZeroHalfPlaneBound_zero_iff_rh

/-- A negative strict growth threshold would force ordinary convergence,
which the nonreal critical contact residues exclude. -/
private theorem criticalPowerComb_growth_threshold_nonneg {σ : ℝ}
    (hg : _root_.HTGeometry.StrictNaturalPowerGrowth (powerCombTail (1 / 2)) σ) :
    0 ≤ σ := by
  by_contra hσ
  have hneg : σ < 0 := lt_of_not_ge hσ
  obtain ⟨C, _, hb⟩ := hg (-σ / 2) (by linarith only [hneg])
  have hp := (tendsto_rpow_neg_atTop
    (by linarith only [hneg] : 0 < -σ / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(-σ / 2)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hp.const_mul C
  have hz : Tendsto (powerCombTail (1 / 2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [Real.norm_eq_abs, show σ + (-σ / 2) = -(-σ / 2) by ring] using hb N hN
  exact not_powerCombTailConverges_half ⟨0, hz⟩

/-- The literal critical comb measures exactly the zero width: its
strict growth thresholds are precisely the real numbers at least that width. -/
theorem strictGrowth_criticalPowerCombTail_iff_zeroWidth (σ : ℝ) :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerCombTail (1 / 2)) σ ↔
      SquareRootThreshold.zetaZeroWidth ≤ σ := by
  constructor
  · intro hg
    have hσ := criticalPowerComb_growth_threshold_nonneg hg
    exact (SquareRootThreshold.zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).mpr
      ((strictGrowth_criticalPowerCombTail_iff_zeroHalfPlane hσ).mp hg)
  · intro hwidth
    have hσ := SquareRootThreshold.zetaZeroWidth_nonneg.trans hwidth
    exact (strictGrowth_criticalPowerCombTail_iff_zeroHalfPlane hσ).mpr
      ((SquareRootThreshold.zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).mp hwidth)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
