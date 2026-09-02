import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerSourceMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierMoment

/-!
# Complete source-height dichotomy for the Type-I prime amplifier

The Heath--Brown receiver closes the sub-height branch `N ≤ T`; the elementary affine receiver
already closes `T ≤ N`.  This module selects the applicable bound internally, so no comparison
between the unit-block length and integration height remains as a premise.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Complete source-height dichotomy: Heath--Brown covers `N ≤ T`; the elementary over-height
receiver covers `T ≤ N`. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_heightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V : ℝ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 2 ≤ N → N < N' → N' ≤ 2 * N → 0 < V →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          if (N : ℝ) ≤ T then
            ∑ r : Fin ell,
              mtTypeIPrimeHeathBrownEpsilonBlockMomentBound
                epsilon a A P ell N T V r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound C epsilon a A P ell N T V r := by
  obtain ⟨C, hC, hover⟩ := exists_setIntegral_mtTypeI_primeAmplifier_coveredRange hepsilon
  refine ⟨C, hC, ?_⟩
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_epsilon_sourceScale hepsilon,
      hquarter, hlog, hXlarge] with X hsub hquarterX hlogX hX
  intro alpha T a A N N' V halpha halpha2 hXT hTX hA hN hNN' hN'le hV
  dsimp only
  by_cases hNT : (N : ℝ) ≤ T
  · rw [if_pos hNT]
    exact hsub alpha T a A N N' V halpha halpha2 hXT hTX hN hNT hNN' hN'le hV
  · rw [if_neg hNT]
    have hTN : T ≤ (N : ℝ) := le_of_not_ge hNT
    have halpha1 : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
    have hlogOne : (1 : ℝ) ≤ Real.log X :=
      (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
    have hscaleReal : Real.exp 2 ≤ (Real.log X) ^ alpha := by
      calc
        Real.exp 2 ≤ Real.log X := hlogX
        _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Real.log X) ^ alpha :=
          Real.rpow_le_rpow_of_exponent_le hlogOne halpha1
    have hP : 2 ≤ mtTypeIPrimeScale X alpha := mtTypeIPrimeScale_two_le hscaleReal
    have hT : 2 ≤ T := hquarterX.trans hXT
    have hell : 0 < mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T :=
      mtTypeIPrimeDegree_pos hP (by linarith)
    exact hover a A (mtTypeIPrimeScale X alpha)
      (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V hA
      (one_le_two.trans hP) hell (one_le_two.trans hN) hNN' hN'le hT hV
      (fun _ => Or.inl hTN)

end

end RHTower.Sieve
