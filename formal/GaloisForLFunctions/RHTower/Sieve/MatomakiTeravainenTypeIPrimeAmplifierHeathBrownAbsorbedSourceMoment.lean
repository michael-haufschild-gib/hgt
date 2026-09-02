import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownCanonicalMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSourceScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownDegreeDeficit

/-!
# Factorial-free source Type-I receiver

This is the source-scale endpoint of the powered-prime Heath--Brown replacement.  Uniformly over
the paper exponent interval, it discharges prime-scale rounding, source degree, full-support
height, factorial normalization, exact sparse support, and Brun--Titchmarsh base conditions.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Source-scale Type-I receiver with height, prime-scale, degree, factorial, support, and
Brun--Titchmarsh conditions all discharged uniformly on the paper exponent interval. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_absorbed_sourceScale :
    ∀ᶠ X : ℝ in atTop,
      ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V eta : ℝ),
      (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
      2 ≤ N → N < N' → N' ≤ 2 * N → 0 < V → 0 < eta →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound
            eta a A P ell N N' T V r := by
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards [eventually_mtTypeIPrimeDegree_linear_deficit,
    eventually_mtTypeIPrimeScale_le_height_two_fifths,
    hquarter, hlog, hXlarge] with X hdegree hPT hquarterX hlogX hX
  intro alpha T a A N N' V eta halpha halpha2 hXT hTX hN hNN' hN'le hV heta
  dsimp only
  have halpha1 : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
  have hscaleReal : Real.exp 2 ≤ (Real.log X) ^ alpha := by
    have hlogOne : (1 : ℝ) ≤ Real.log X :=
      (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
    calc
      Real.exp 2 ≤ Real.log X := hlogX
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hlogOne halpha1
  have hP : 2 ≤ mtTypeIPrimeScale X alpha := mtTypeIPrimeScale_two_le hscaleReal
  have hlogP : 1 ≤ Real.log (mtTypeIPrimeScale X alpha : ℝ) :=
    one_le_two.trans (mtTypeIPrimeScale_log_two_le hscaleReal)
  have hT : 2 ≤ T := hquarterX.trans hXT
  have hell : 0 < mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T :=
    mtTypeIPrimeDegree_pos hP (by linarith)
  have hdeg := hdegree alpha T halpha (by linarith) hTX
  have hscaleHeight := hPT alpha T halpha1 halpha2 hXT
  have hfull := mtTypeIPrimeDegree_fullSupport_le_height
    hP (one_le_two.trans hT) hscaleHeight
  exact setIntegral_mtTypeI_primeAmplifier_heathBrown_absorbed
    a A (mtTypeIPrimeScale X alpha)
      (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V eta
      hP hlogP hdeg hell hN hNN' hN'le hT hV heta hfull

end

end RHTower.Sieve
