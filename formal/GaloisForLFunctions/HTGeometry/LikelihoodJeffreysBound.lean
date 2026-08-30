import GaloisForLFunctions.HTGeometry.LikelihoodPolarizationInformation
import GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization
import GaloisForLFunctions.HTGeometry.TanhSelfBound

/-!
# The coherence energy is bounded by Jeffreys information

Both directed relative entropies of an equivalent binary pair are rebased onto the balanced law.
Their two `klFun` integrands add to `(p − q)·log(p/q)`, which in contrast coordinates is
`4·d·artanh d`.  Since `d·artanh d ≥ d²`, the coherence energy never exceeds Jeffreys
information.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem absolutelyContinuous_balancedLaw_of_ac (P Q : Measure X) (hPQ : P ≪ Q) :
    balancedLaw P Q ≪ Q := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hz => ?_
  rw [balancedLaw, Measure.smul_apply, Measure.add_apply, hPQ hz, hz, add_zero, smul_zero]

/-- Away from a null set the reflected density is strictly positive. -/
theorem rnDeriv_right_pos (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) : ∀ᵐ x ∂(balancedLaw P Q), 0 < Q.rnDeriv (balancedLaw P Q) x :=
  (Measure.rnDeriv_pos (absolutelyContinuous_balancedLaw_right P Q)).filter_mono
    (absolutelyContinuous_balancedLaw_of_ac P Q hPQ).ae_le

/-- The likelihood ratio in balanced coordinates. -/
theorem rnDeriv_ratio (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    ∀ᵐ x ∂(balancedLaw P Q), (P.rnDeriv Q x).toReal
      = (1 + posteriorContrast P Q x) / (1 - posteriorContrast P Q x) := by
  have hchain : ∀ᵐ x ∂(balancedLaw P Q),
      P.rnDeriv Q x * Q.rnDeriv (balancedLaw P Q) x = P.rnDeriv (balancedLaw P Q) x :=
    Measure.rnDeriv_mul_rnDeriv (κ := balancedLaw P Q) hPQ
  filter_upwards [hchain, rnDeriv_right_pos P Q hPQ, rnDeriv_right_toReal P Q,
    (Measure.rnDeriv_lt_top P Q).filter_mono
      (absolutelyContinuous_balancedLaw_of_ac P Q hPQ).ae_le,
    Measure.rnDeriv_lt_top Q (balancedLaw P Q),
    Measure.rnDeriv_lt_top P (balancedLaw P Q)] with x hc hq hqr hf1 hf2 hf3
  have hR := congrArg ENNReal.toReal hc
  rw [ENNReal.toReal_mul, hqr, rnDeriv_left_toReal] at hR
  have hqpos : 0 < 1 - posteriorContrast P Q x := by
    rw [← hqr]
    exact ENNReal.toReal_pos hq.ne' hf2.ne
  field_simp
  linarith [hR]

theorem measurable_klFunComp (P Q : Measure X) :
    Measurable fun x => ENNReal.ofReal (klFun ((P.rnDeriv Q x).toReal)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  have hm : Measurable fun x => (P.rnDeriv Q x).toReal :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  exact ((hm.mul (Real.measurable_log.comp hm)).add measurable_const).sub hm

/-- Both directed relative entropies rebase onto the balanced law. -/
theorem klDiv_eq_lintegral_balanced (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    klDiv P Q = ∫⁻ x, ENNReal.ofReal ((1 - posteriorContrast P Q x)
      * klFun ((1 + posteriorContrast P Q x) / (1 - posteriorContrast P Q x)))
      ∂(balancedLaw P Q) := by
  rw [klDiv_eq_lintegral_klFun_of_ac hPQ,
    ← lintegral_rnDeriv_mul' (absolutelyContinuous_balancedLaw_right P Q)
      (measurable_klFunComp P Q)]
  refine lintegral_congr_ae ?_
  filter_upwards [rnDeriv_ratio P Q hPQ, rnDeriv_right_toReal P Q,
    Measure.rnDeriv_lt_top Q (balancedLaw P Q), rnDeriv_right_pos P Q hPQ] with x hr hq hf hpos
  have hqnn : (0:ℝ) ≤ 1 - posteriorContrast P Q x := by rw [← hq]; exact ENNReal.toReal_nonneg
  have hqe : Q.rnDeriv (balancedLaw P Q) x = ENNReal.ofReal (1 - posteriorContrast P Q x) := by
    rw [← hq, ENNReal.ofReal_toReal hf.ne]
  have hratnn : (0:ℝ) ≤ (1 + posteriorContrast P Q x) / (1 - posteriorContrast P Q x) := by
    rw [← hr]; exact ENNReal.toReal_nonneg
  rw [hr, hqe, ← ENNReal.ofReal_mul (klFun_nonneg hratnn), mul_comm]

theorem balancedLaw_symm (P Q : Measure X) : balancedLaw Q P = balancedLaw P Q := by
  rw [balancedLaw, balancedLaw, add_comm]

theorem posteriorContrast_symm (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    posteriorContrast Q P =ᵐ[balancedLaw P Q] fun x => -posteriorContrast P Q x := by
  filter_upwards [rnDeriv_right_toReal P Q] with x hq
  rw [posteriorContrast, balancedLaw_symm, hq]
  ring

theorem one_sub_posteriorContrast_pos (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    ∀ᵐ x ∂(balancedLaw P Q), 0 < 1 - posteriorContrast P Q x := by
  filter_upwards [rnDeriv_right_pos P Q hPQ, rnDeriv_right_toReal P Q,
    Measure.rnDeriv_lt_top Q (balancedLaw P Q)] with x h1 h2 h3
  rw [← h2]; exact ENNReal.toReal_pos h1.ne' h3.ne

theorem one_add_posteriorContrast_pos (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hQP : Q ≪ P) :
    ∀ᵐ x ∂(balancedLaw P Q), 0 < 1 + posteriorContrast P Q x := by
  have hac : balancedLaw P Q ≪ P := by
    rw [← balancedLaw_symm]
    exact absolutelyContinuous_balancedLaw_of_ac Q P hQP
  have h := (Measure.rnDeriv_pos
    (absolutelyContinuous_balancedLaw_left P Q)).filter_mono hac.ae_le
  filter_upwards [h, Measure.rnDeriv_lt_top P (balancedLaw P Q)] with x h1 h2
  rw [← rnDeriv_left_toReal]
  exact ENNReal.toReal_pos h1.ne' h2.ne

/-- Equivalent laws have contrast strictly inside `(-1,1)`. -/
theorem abs_posteriorContrast_lt_one (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    ∀ᵐ x ∂(balancedLaw P Q), |posteriorContrast P Q x| < 1 := by
  filter_upwards [one_sub_posteriorContrast_pos P Q hPQ,
    one_add_posteriorContrast_pos P Q hQP] with x h1 h2
  rw [abs_lt]
  constructor <;> linarith

/-- `(LPC.22)`  Jeffreys information in contrast coordinates. -/
theorem formationJeffreys_eq_lintegral (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    formationJeffreys P Q = ∫⁻ x, ENNReal.ofReal
      (4 * posteriorContrast P Q x * Real.artanh (posteriorContrast P Q x))
      ∂(balancedLaw P Q) := by
  have hQPl := klDiv_eq_lintegral_balanced Q P hQP
  rw [balancedLaw_symm] at hQPl
  have hpos := one_sub_posteriorContrast_pos P Q hPQ
  have hpos' := one_add_posteriorContrast_pos P Q hQP
  have hQPl' : klDiv Q P = ∫⁻ x, ENNReal.ofReal ((1 + posteriorContrast P Q x)
      * klFun ((1 - posteriorContrast P Q x) / (1 + posteriorContrast P Q x)))
      ∂(balancedLaw P Q) := by
    rw [hQPl]
    refine lintegral_congr_ae ?_
    filter_upwards [posteriorContrast_symm P Q] with x hsym
    rw [hsym]
    ring_nf
  rw [formationJeffreys, klDiv_eq_lintegral_balanced P Q hPQ, hQPl',
    ← lintegral_add_left (by
      refine ENNReal.measurable_ofReal.comp ?_
      have hm := measurable_posteriorContrast P Q
      have hr : Measurable fun x => (1 + posteriorContrast P Q x)
          / (1 - posteriorContrast P Q x) :=
        (measurable_const.add hm).div (measurable_const.sub hm)
      exact (measurable_const.sub hm).mul
        (((hr.mul (Real.measurable_log.comp hr)).add measurable_const).sub hr))]
  refine lintegral_congr_ae ?_
  filter_upwards [hpos, hpos'] with x h1 h2
  have hne1 : (1 - posteriorContrast P Q x) ≠ 0 := h1.ne'
  have hne2 : (1 + posteriorContrast P Q x) ≠ 0 := h2.ne'
  set d := posteriorContrast P Q x with hd
  have hL : Real.log ((1 - d) / (1 + d)) = -Real.log ((1 + d) / (1 - d)) := by
    rw [← Real.log_inv, inv_div]
  have hA : (0:ℝ) ≤ (1 - d) * klFun ((1 + d) / (1 - d)) :=
    mul_nonneg h1.le (klFun_nonneg (by positivity))
  have hB : (0:ℝ) ≤ (1 + d) * klFun ((1 - d) / (1 + d)) :=
    mul_nonneg h2.le (klFun_nonneg (by positivity))
  rw [← ENNReal.ofReal_add hA hB]
  congr 1
  have hart : Real.artanh d = 1 / 2 * Real.log ((1 + d) / (1 - d)) := by
    refine Real.artanh_eq_half_log ⟨?_, ?_⟩ <;> linarith
  rw [klFun_apply, klFun_apply, hL, hart]
  field_simp
  ring

/-- **Theorem 4.1, `(LPC.25)`.**  The coherence energy never exceeds Jeffreys information. -/
theorem coherenceWork_le_formationJeffreys (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    ENNReal.ofReal (coherenceWork P Q) ≤ formationJeffreys P Q := by
  by_cases hPQ : P ≪ Q
  · by_cases hQP : Q ≪ P
    · rw [formationJeffreys_eq_lintegral P Q hPQ hQP, coherenceWork, ← integral_const_mul]
      have hint : Integrable (fun x => 4 * (posteriorContrast P Q x) ^ 2) (balancedLaw P Q) :=
        (integrable_sq_posteriorContrast P Q).const_mul 4
      rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => by positivity)]
      refine lintegral_mono_ae ?_
      filter_upwards [abs_posteriorContrast_lt_one P Q hPQ hQP] with x hx
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_le_mul_artanh hx])
    · have : klDiv Q P = ⊤ := klDiv_eq_top_iff.mpr fun h => absurd h hQP
      rw [formationJeffreys, this]
      simp
  · have : klDiv P Q = ⊤ := klDiv_eq_top_iff.mpr fun h => absurd h hPQ
    rw [formationJeffreys, this]
    simp

end

end GaloisForLFunctions.HTGeometry
