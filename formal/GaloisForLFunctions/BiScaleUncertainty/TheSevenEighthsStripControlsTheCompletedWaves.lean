import GaloisForLFunctions.SquareRootThreshold.TheSevenEighthsStripBoundsTheZeroWidth
import GaloisForLFunctions.BiScaleUncertainty.WeilLagCriticalDeficitEndpointAndLimitLaw
import GaloisForLFunctions.RHTower.CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion

/-!
# Certified growth of the completed Weil and Klein–Gordon waves

The three-eighths width bounds the Weil lag and the CHMD prime wave at
the same exponent. The prime-side formulas keep the pole, Gamma and
trivial-zero terms rather than discarding their normalization.
-/

noncomputable section

open Real MeasureTheory Zeta23
open _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

/-- The literal prime expression for the Weil lag has exponential rate `3/8`. -/
theorem completedWeilLag_primeSide_bound {L : ℝ} (hL : 0 < L) :
    |Real.exp (-L / 2) *
      ((Real.exp L - Chebyshev.psi (Real.exp L)) +
        Real.exp L * (mertensSum ⌊Real.exp L⌋₊ - L + eulerMascheroniConstant) -
        Real.log (2 * π) + trivialZeroSeriesReal (Real.exp L))| ≤
      lagWeightTotal * Real.exp (3 / 8 * L) := by
  rw [← weilLagFunctionReal_eq_prime_side hL]
  simpa only [abs_of_pos hL] using
    abs_weilLagFunctionReal_le_of_zetaZeroWidth_le (by norm_num)
      zetaZeroWidth_le_three_eighths L

/-- Incoming deficit, its primitive and both critical energy forms inherit the same strip. -/
theorem three_eighths_endpoint_bounds :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitIncoming T| ≤ B * Real.exp (3 / 8 * T)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      ccmLogChebyshevDeficitPrimitive T ≤ B * Real.exp (7 / 8 * T)) ∧
    CriticalDeficitPointwiseRate (3 / 8) ∧ CoprimeCrossWorkLowerRate (3 / 8) := by
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    zetaZeroWidth_le_iff_endpoint_equivalences (σ := 3 / 8) (by norm_num) (by norm_num)
  refine ⟨h1.mp zetaZeroWidth_le_three_eighths, ?_,
    h3.mp zetaZeroWidth_le_three_eighths, h4.mp zetaZeroWidth_le_three_eighths⟩
  convert h2.mp zetaZeroWidth_le_three_eighths using 1 <;> norm_num

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower.CHMDGrowthCollapse _root_.RHTower.CHMDStage22
open _root_.RHTower.CHMDStage3 _root_.RHTower.EvenSector
open GaloisForLFunctions.HTGeometry

/-- The Klein–Gordon square root does not enlarge the certified zero width. -/
theorem abs_im_kgFreq_le_three_eighths (ρ : zetaZeroConfig.carrier) :
    |(kgFreq ρ).im| ≤ 3 / 8 := by
  have hγ : (gammaOf (ρ : ℂ)).im = 1 / 2 - (ρ : ℂ).re := by
    simp [gammaOf, Complex.div_I]
  calc
    |(kgFreq ρ).im| ≤ |(gammaOf (ρ : ℂ)).im| := abs_im_rhoC_le _
    _ = |(ρ : ℂ).re - 1 / 2| := by rw [hγ, abs_sub_comm]
    _ ≤ zetaZeroWidth := abs_re_sub_half_le_zetaZeroWidth ρ.property
    _ ≤ 3 / 8 := zetaZeroWidth_le_three_eighths

/-- The CHMD prime wave has rate `3/8`, with its actual pole and Gamma integral retained. -/
theorem chmdPrimeWave_completed_three_eighths :
    ∃ K : ℝ, ∀ u : ℝ,
      chmdPrimeWave u =
        (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (u * Real.sqrt (7 / 4)) +
          1 / (2 * Real.pi) *
            (∫ r : ℝ, Real.cos (u * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r) -
          chmdWave u ∧
      |chmdPrimeWave u| ≤ K * Real.exp (3 / 8 * |u|) := by
  obtain ⟨K, hK⟩ :=
    (chmdPrimeWave_growth_law (a := 3 / 8) (by norm_num) (by norm_num)).2.2.mpr
      abs_im_kgFreq_le_three_eighths
  refine ⟨K, fun u => ⟨?_, hK u⟩⟩
  rw [chmdPrimeWave_eq_pole_add_arch_sub_chmdWave, chmdPoleWave_eq, chmdArchWave_eq]

#print axioms ChebyshevGauge.completedWeilLag_primeSide_bound
#print axioms ChebyshevGauge.three_eighths_endpoint_bounds
#print axioms chmdPrimeWave_completed_three_eighths

end GaloisForLFunctions.BiScaleUncertainty
