import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineTerminalTruncation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeightedSourceLocalizedPairing

/-!
# Polar pairings vanish under terminal concentration

Split a weighted source at a terminal interval. Cauchy–Schwarz bounds the
near pairing by the interval length and the far pairing by the exponential
excess. The resulting estimate is uniform over normalized sources.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

private theorem terminalCut_pairing (F k : ℝ → ℝ) (h : ℝ) :
    (∫ u, halfLineTerminalCut h F u * k u) = ∫ u in Icc (-h) 0, F u * k u := by
  have heq : (fun u => halfLineTerminalCut h F u * k u) =
      (Icc (-h) 0).indicator (fun u => F u * k u) := by
    funext u
    by_cases hu : u ∈ Icc (-h) 0
    · simp only [halfLineTerminalCut, indicator_of_mem hu]
    · simp only [halfLineTerminalCut, indicator_of_notMem hu, zero_mul]
  rw [heq, integral_indicator measurableSet_Icc]

/-- A terminal split controls every continuous kernel of half-exponential growth. -/
theorem CriticalHalfLineEnergyDomain.kernel_pairing_sq_le_excess {F k : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hk : Continuous k)
    (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2))
    (hm : (∫ u, F u ^ 2) = 1) (hd : criticalHalfLineExponentialDefect F ≤ 1)
    {h : ℝ} (hh : 0 < h) :
    (∫ u, F u * k u) ^ 2 ≤ 4 * h +
      2 * (∫ u : ℝ, Real.exp (-|u|)) *
        (criticalHalfLineExponentialDefect F / (1 - Real.exp (-(8 * h)))) := by
  let G := halfLineTerminalCut h F
  have hG : WeightedTwo G := hF.terminalCut_weighted h
  have hS : exponentialSourceMass F ≤ 2 := by
    have h := hF.sourceMass_le_exponential
    dsimp only [criticalHalfLineExponentialDefect] at hd
    rw [hm] at hd
    linarith only [h, hd]
  have hnear : (∫ u, G u * k u) ^ 2 ≤ 2 * h := by
    rw [show (∫ u, G u * k u) = ∫ u in Icc (-h) 0, F u * k u from
      terminalCut_pairing F k h]
    exact (sq_terminalIntegral_mul_kernel_le hF.weighted hk hb hh.le).trans
      (mul_le_mul_of_nonneg_right hS hh.le)
  have hJ : 0 ≤ ∫ u : ℝ, Real.exp (-|u|) :=
    integral_nonneg fun u => (Real.exp_pos _).le
  obtain ⟨_, hD⟩ := abs_integral_mul_kernel_le (hF.weighted.sub hG) hk hb
  have hfar : (∫ u, (F u - G u) * k u) ^ 2 ≤
      (criticalHalfLineExponentialDefect F / (1 - Real.exp (-(8 * h)))) *
        (∫ u : ℝ, Real.exp (-|u|)) := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hD 2
    simp only [sq_abs, mul_pow, Real.sq_sqrt (exponentialSourceMass_nonneg _),
      Real.sq_sqrt hJ] at hsq
    exact hsq.trans (mul_le_mul_of_nonneg_right (hF.terminalCut_error_le hh) hJ)
  have iF := (abs_integral_mul_kernel_le hF.weighted hk hb).1
  have iG := (abs_integral_mul_kernel_le hG hk hb).1
  have hsum : (∫ u, (F u - G u) * k u) = (∫ u, F u * k u) - ∫ u, G u * k u := by
    simp_rw [sub_mul]
    exact integral_sub iF iG
  rw [hsum] at hfar
  nlinarith only [hnear, hfar,
    sq_nonneg ((∫ u, F u * k u) - 2 * ∫ u, G u * k u)]

/-- The pairing estimate is uniform over all normalized profiles with small excess. -/
theorem exists_kernel_pairing_sq_small_of_excess {k : ℝ → ℝ}
    (hk : Continuous k) (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      (∫ u, F u ^ 2) = 1 → criticalHalfLineExponentialDefect F ≤ d →
        (∫ u, F u * k u) ^ 2 < ε := by
  let J : ℝ := ∫ u : ℝ, Real.exp (-|u|)
  let h := ε / 16
  let c := 1 - Real.exp (-(8 * h))
  have hJ : 0 ≤ J := integral_nonneg fun u => (Real.exp_pos _).le
  have hh : 0 < h := div_pos hε (by norm_num)
  have hc : 0 < c := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith only [hh]
  have hden : 0 < 8 * (J + 1) := by positivity
  refine ⟨min 1 (ε * c / (8 * (J + 1))), lt_min zero_lt_one (by positivity), ?_⟩
  intro F hF hm hd
  have hd1 : criticalHalfLineExponentialDefect F ≤ 1 := hd.trans (min_le_left _ _)
  have hδ : 0 ≤ criticalHalfLineExponentialDefect F :=
    (hF.exponential_defect_pos (by rw [hm]; exact zero_lt_one)).le
  have hδc := (le_div_iff₀ hden).mp (hd.trans (min_le_right _ _))
  have hfar : 2 * J * (criticalHalfLineExponentialDefect F / c) ≤ ε / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hc).mpr
    nlinarith only [hδc, hδ]
  have hbound := hF.kernel_pairing_sq_le_excess hk hb hm hd1 hh
  change (∫ u, F u * k u) ^ 2 ≤ 4 * h + 2 * J *
    (criticalHalfLineExponentialDefect F / c) at hbound
  dsimp only [h] at hbound
  linarith only [hbound, hfar, hε]

/-- The prime and pole terms left after removing Gamma energy and confinement. -/
def criticalHalfLineArithmeticRemainder (F : ℝ → ℝ) : ℝ :=
  -primeSum F + 2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2

theorem criticalHalfLineFullEnergy_eq_arch_add_remainder (R : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    criticalHalfLineFullEnergy R F = archForm F +
      criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        criticalHalfLineArithmeticRemainder F := by
  unfold criticalHalfLineFullEnergy criticalHalfLineArithmeticRemainder
  rw [halfLineExpMass_eq_full hF.support]
  ring

/-- Terminal concentration removes the complete arithmetic remainder uniformly. -/
theorem exists_arithmeticRemainder_small_of_excess {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      (∫ u, F u ^ 2) = 1 → criticalHalfLineExponentialDefect F ≤ d →
        |criticalHalfLineArithmeticRemainder F| < ε := by
  have he : 0 < ε / 8 := div_pos hε (by norm_num)
  obtain ⟨dp, hdp, hp⟩ := exists_primeSum_small_of_excess he
  obtain ⟨dc, hdc, hc⟩ := exists_kernel_pairing_sq_small_of_excess
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) abs_cosh_half_le_exp he
  obtain ⟨ds, hds, hs⟩ := exists_kernel_pairing_sq_small_of_excess
    (Real.continuous_sinh.comp (continuous_id.div_const 2)) abs_sinh_half_le_exp he
  refine ⟨min dp (min dc ds), lt_min hdp (lt_min hdc hds), ?_⟩
  intro F hF hm hd
  have hpF := hp hF hm (hd.trans (min_le_left _ _))
  have hcF := hc hF hm (hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsF := hs hF hm (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  change coshHalfMoment F ^ 2 < ε / 8 at hcF
  change sinhHalfMoment F ^ 2 < ε / 8 at hsF
  apply abs_lt.mpr
  dsimp only [criticalHalfLineArithmeticRemainder]
  constructor
  · nlinarith only [hpF, hsF, le_abs_self (primeSum F), sq_nonneg (coshHalfMoment F), hε]
  · nlinarith only [hpF, hcF, neg_abs_le (primeSum F), sq_nonneg (sinhHalfMoment F), hε]

#print axioms CriticalHalfLineEnergyDomain.kernel_pairing_sq_le_excess
#print axioms exists_kernel_pairing_sq_small_of_excess
#print axioms exists_arithmeticRemainder_small_of_excess

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
