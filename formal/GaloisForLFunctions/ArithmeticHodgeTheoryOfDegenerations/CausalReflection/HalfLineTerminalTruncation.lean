import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementTail
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeightedSourceTruncation
import GaloisForLFunctions.RHTower.WeilMarkovThinNonnegativeOddPositivity

/-!
# Terminal truncation and the prime-shift gap

Small exponential excess forces a half-line profile into any fixed terminal
interval in the lower weighted norm. An interval shorter than `log 2`
contains no prime correlation, so its truncation estimates the full prime form.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Keep the part of a source between the terminal boundary and depth `h`. -/
def halfLineTerminalCut (h : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := (Icc (-h) 0).indicator F

theorem CriticalHalfLineEnergyDomain.source_integrand_le_exponential {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (u : ℝ) :
    (Real.exp |u| * F u) ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u)) := by
  by_cases hu : 0 ≤ u
  · simp only [hF.support u hu, mul_zero, zero_pow two_ne_zero, zero_mul, le_refl]
  · have hun : u ≤ 0 := (lt_of_not_ge hu).le
    rw [mul_pow, abs_of_nonpos hun, ← Real.exp_nat_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    push_cast
    linarith only [hun]

theorem CriticalHalfLineEnergyDomain.sourceMass_le_exponential {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    exponentialSourceMass F ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
  integral_mono hF.weighted.sq hF.exponential hF.source_integrand_le_exponential

theorem CriticalHalfLineEnergyDomain.terminalCut_weighted {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (h : ℝ) : WeightedTwo (halfLineTerminalCut h F) :=
  hF.weighted.indicator measurableSet_Icc

/-- The lower weighted mass discarded by a terminal cut is controlled by the excess. -/
theorem CriticalHalfLineEnergyDomain.terminalCut_error_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {h : ℝ} (hh : 0 < h) :
    exponentialSourceMass (fun u => F u - halfLineTerminalCut h F u) ≤
      criticalHalfLineExponentialDefect F / (1 - Real.exp (-(8 * h))) := by
  have hpoint (u : ℝ) :
      (Real.exp |u| * (F u - halfLineTerminalCut h F u)) ^ 2 ≤
        (Iic (-h)).indicator (fun v => F v ^ 2 * Real.exp (-(8 * v))) u := by
    by_cases hu : u ∈ Icc (-h) 0
    · simp only [halfLineTerminalCut, indicator_of_mem hu, sub_self, mul_zero,
        zero_pow two_ne_zero]
      by_cases hv : u ∈ Iic (-h)
      · rw [indicator_of_mem hv]
        exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
      · rw [indicator_of_notMem hv]
    · rw [halfLineTerminalCut, indicator_of_notMem hu, sub_zero]
      by_cases hv : u ∈ Iic (-h)
      · rw [indicator_of_mem hv]
        exact hF.source_integrand_le_exponential u
      · have hp : 0 ≤ u := by
          by_contra hn
          apply hu
          exact ⟨le_of_lt (lt_of_not_ge hv), (lt_of_not_ge hn).le⟩
        simp only [hF.support u hp, mul_zero, zero_pow two_ne_zero,
          indicator_of_notMem hv, le_refl]
  have hi := integral_mono (hF.weighted.sub (hF.terminalCut_weighted h)).sq
    (hF.exponential.indicator measurableSet_Iic) hpoint
  rw [integral_indicator measurableSet_Iic] at hi
  exact hi.trans (hF.exponential_tail_le_defect hh)

/-- A terminal interval narrower than the first prime shift has zero prime form. -/
theorem primeSum_halfLineTerminalCut_eq_zero (F : ℝ → ℝ) {h : ℝ}
    (hh : h < Real.log 2) : primeSum (halfLineTerminalCut h F) = 0 := by
  apply primeSum_eq_zero_of_width_lt (x₀ := -h) (w := h) _ hh
  intro u hu
  have hu' : u ∉ Icc (-h) 0 := by simpa only [neg_add_cancel] using hu
  exact indicator_of_notMem hu' _

/-- Prime correlations disappear uniformly as the exponential excess tends to zero. -/
theorem CriticalHalfLineEnergyDomain.prime_bound_by_excess {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hm : (∫ u, F u ^ 2) = 1)
    (hd : criticalHalfLineExponentialDefect F ≤ 1) {h : ℝ}
    (hh : 0 < h) (hgap : h < Real.log 2) :
    |primeSum F| ≤ 4 * Real.sqrt 2 * vonMangoldtThreeHalvesMass *
      Real.sqrt (criticalHalfLineExponentialDefect F / (1 - Real.exp (-(8 * h)))) := by
  have hS : exponentialSourceMass F ≤ 2 := by
    have h := hF.sourceMass_le_exponential
    dsimp only [criticalHalfLineExponentialDefect] at hd
    rw [hm] at hd
    linarith only [h, hd]
  have hT : exponentialSourceMass (halfLineTerminalCut h F) ≤ 2 :=
    (exponentialSourceMass_indicator_le hF.weighted measurableSet_Icc).trans hS
  have hp := abs_primeSum_sub_le hF.weighted (hF.terminalCut_weighted h)
  rw [primeSum_halfLineTerminalCut_eq_zero F hgap, sub_zero] at hp
  have hsum : Real.sqrt (exponentialSourceMass F) +
      Real.sqrt (exponentialSourceMass (halfLineTerminalCut h F)) ≤ 2 * Real.sqrt 2 := by
    linarith only [Real.sqrt_le_sqrt hS, Real.sqrt_le_sqrt hT]
  have hroot := Real.sqrt_le_sqrt (hF.terminalCut_error_le hh)
  have hprod := mul_le_mul hroot hsum
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) vonMangoldtThreeHalvesMass_nonneg)
  exact hp.trans (hscale.trans_eq (by ring))

/-- A single prime-free cut gives uniform disappearance of the complete prime form. -/
theorem exists_primeSum_small_of_excess {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      (∫ u, F u ^ 2) = 1 → criticalHalfLineExponentialDefect F ≤ d →
        |primeSum F| < ε := by
  let C : ℝ := 4 * Real.sqrt 2 * vonMangoldtThreeHalvesMass
  let c : ℝ := 1 - Real.exp (-(8 * (1 / 2 : ℝ)))
  let r : ℝ := ε / (2 * (C + 1))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      vonMangoldtThreeHalvesMass_nonneg
  have hc : 0 < c := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    norm_num
  have hr : 0 < r := div_pos hε (by positivity)
  refine ⟨min 1 (c * r ^ 2), lt_min zero_lt_one (mul_pos hc (sq_pos_of_pos hr)), ?_⟩
  intro F hF hm hd
  have hd1 := hd.trans (min_le_left _ _)
  have hδ : 0 ≤ criticalHalfLineExponentialDefect F :=
    (hF.exponential_defect_pos (by rw [hm]; exact zero_lt_one)).le
  have hq : 0 ≤ criticalHalfLineExponentialDefect F / c := div_nonneg hδ hc.le
  have hqle : criticalHalfLineExponentialDefect F / c ≤ r ^ 2 := by
    apply (div_le_iff₀ hc).mpr
    simpa only [mul_comm] using hd.trans (min_le_right _ _)
  have hroot : Real.sqrt (criticalHalfLineExponentialDefect F / c) ≤ r := by
    have hs := Real.sq_sqrt hq
    nlinarith only [hs, hqle, Real.sqrt_nonneg (criticalHalfLineExponentialDefect F / c), hr]
  have hCr : C * r ≤ ε / 2 := by
    dsimp only [r]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (C + 1))).mpr
    nlinarith only [hε]
  have hp := hF.prime_bound_by_excess hm hd1 (by norm_num : (0 : ℝ) < 1 / 2)
    one_div_two_lt_log_two
  change |primeSum F| ≤ C * Real.sqrt (criticalHalfLineExponentialDefect F / c) at hp
  have hb := hp.trans ((mul_le_mul_of_nonneg_left hroot hC).trans hCr)
  linarith only [hb, hε]

#print axioms CriticalHalfLineEnergyDomain.terminalCut_error_le
#print axioms CriticalHalfLineEnergyDomain.prime_bound_by_excess
#print axioms exists_primeSum_small_of_excess

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
