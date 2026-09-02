import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierSchedule
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Degree deficit for the Heath--Brown Type-I prime amplifier

The paper exponent interval begins at `1.0999`.  Consequently the canonical raising degree is at
most `P^0.91`, while a fixed multiple of `P^0.91` is eventually below `P`.  This supplies the exact
linear reserve needed to absorb the factorial-weighted Brun--Titchmarsh numerator.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The paper exponent interval leaves a uniform `P^0.09` reserve over the raising degree. -/
theorem eventually_mtTypeIPrimeDegree_linear_deficit :
    ∀ᶠ X : ℝ in atTop, ∀ a T : ℝ,
      (10999 / 10000 : ℝ) ≤ a → 1 < T → T ≤ X →
      294 * mtTypeIPrimeDegree (mtTypeIPrimeScale X a) T ≤
        mtTypeIPrimeScale X a := by
  have hdomRaw := eventually_const_mul_rpow_polylog_le_rpow
    (C := (294 : ℝ)) (α := (91 / 100 : ℝ)) (β := (1 : ℝ)) 0 (by norm_num)
  have hdom : ∀ᶠ P : ℝ in atTop, 294 * P ^ (91 / 100 : ℝ) ≤ P := by
    filter_upwards [hdomRaw] with P hP
    simpa [Real.rpow_one] using hP
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.1 hdom
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop
    (max (Real.exp 2) P₀)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards [hlog, hXlarge] with X hlogX hX
  intro a T ha hT hTX
  let P := mtTypeIPrimeScale X a
  let ell := mtTypeIPrimeDegree P T
  have ha0 : 0 < a := (by norm_num : (0 : ℝ) < 10999 / 10000).trans_le ha
  have ha1 : (1 : ℝ) ≤ a := by norm_num at ha ⊢; linarith
  have hlogX_exp : Real.exp 2 ≤ Real.log X :=
    (le_max_left _ _).trans hlogX
  have hlogX_one : (1 : ℝ) ≤ Real.log X := by
    exact (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX_exp
  have hscaleReal : Real.exp 2 ≤ (Real.log X) ^ a := by
    calc
      Real.exp 2 ≤ Real.log X := hlogX_exp
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ a := Real.rpow_le_rpow_of_exponent_le hlogX_one ha1
  have hPtwo : 2 ≤ P := by
    dsimp only [P]
    exact mtTypeIPrimeScale_two_le hscaleReal
  have hschedule := mtTypeIPrimeDegree_source_schedule ha0 hX hscaleReal hT hTX
  have hellSource : (ell : ℝ) ≤ (P : ℝ) ^ (1 / a) := by
    simpa only [P, ell] using hschedule.2.2.2
  have hexp : 1 / a ≤ (91 / 100 : ℝ) := by
    rw [div_le_iff₀ ha0]
    nlinarith
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast (one_le_two.trans hPtwo)
  have hell : (ell : ℝ) ≤ (P : ℝ) ^ (91 / 100 : ℝ) :=
    hellSource.trans (Real.rpow_le_rpow_of_exponent_le hPone hexp)
  have hPthreshold : P₀ ≤ (P : ℝ) := by
    have hlogP₀ : P₀ ≤ Real.log X := (le_max_right _ _).trans hlogX
    have hlogScale : Real.log X ≤ (Real.log X) ^ a := by
      calc
        Real.log X = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Real.log X) ^ a := Real.rpow_le_rpow_of_exponent_le hlogX_one ha1
    have hceil := mtTypeIPrimeScale_lower X a
    exact hlogP₀.trans (hlogScale.trans (by simpa only [P] using hceil))
  have hPdom := hP₀ (P : ℝ) hPthreshold
  have hdegreeReal : (294 : ℝ) * ell ≤ P := by
    calc
      (294 : ℝ) * ell ≤ 294 * (P : ℝ) ^ (91 / 100 : ℝ) := by gcongr
      _ ≤ P := hPdom
  exact_mod_cast hdegreeReal

end

end RHTower.Sieve
