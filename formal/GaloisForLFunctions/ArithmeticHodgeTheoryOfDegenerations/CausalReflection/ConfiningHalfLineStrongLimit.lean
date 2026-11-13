import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementLogarithmicCost
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementDilation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineArithmeticBounds

/-!
# Strong confinement of the actual half-line ground state

The correlation deficit gives a logarithmic lower cost, while compressed
compact profiles attain the same leading cost. The retained exponential
excess then confines every minimizer to a two-sided inverse-strength scale.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri BiScaleUncertainty

private theorem logarithmic_penalty_lower {p d : ℝ} (hp : 0 < p) (hd : 0 < d) :
    1 + Real.log p ≤ p * d - Real.log d := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hp hd)
  rw [Real.log_mul hp.ne' hd.ne'] at h
  linarith only [h]

private theorem logarithmic_penalty_sublevel {z Q : ℝ} (hz : 0 < z)
    (hQ : z - Real.log z ≤ Q) :
    Real.exp (-Q) ≤ z ∧ z ≤ 2 * (Q + Real.log 2 + 1) := by
  constructor
  · have h : -Q ≤ Real.log z := by linarith only [hQ, hz]
    simpa only [Real.exp_log hz] using Real.exp_le_exp.mpr h
  · have h := Real.log_le_sub_one_of_pos (div_pos hz (by norm_num : (0 : ℝ) < 2))
    rw [Real.log_div hz.ne' (by norm_num)] at h
    linarith only [hQ, h]

private theorem confinement_exp_cost_bound {a : ℝ} (ha1 : 1 ≤ a) :
    Real.exp (8 / a) ≤ Real.exp 8 ∧ a * (Real.exp (8 / a) - 1) ≤ 8 * Real.exp 8 := by
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have ht : 8 / a ≤ 8 := (div_le_iff₀ ha).mpr (by linarith only [ha1])
  have hmono := Real.exp_le_exp.mpr ht
  refine ⟨hmono, ?_⟩
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(8 / a)))
    (Real.exp_pos (8 / a)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have hcost : Real.exp (8 / a) - 1 ≤ (8 / a) * Real.exp (8 / a) := by
    nlinarith only [h]
  calc
    _ ≤ a * ((8 / a) * Real.exp (8 / a)) := mul_le_mul_of_nonneg_left hcost ha.le
    _ = 8 * Real.exp (8 / a) := by field_simp [ha.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by norm_num)

/-- The lower energy estimate retains the exponential excess as a free variable. -/
theorem criticalHalfLineFullEnergy_log_defect_lower :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ (R : ℝ) {F : ℝ → ℝ},
      CriticalHalfLineEnergyDomain F → (∫ u, F u ^ 2) = 1 →
      criticalAliasCoefficient R + (criticalAliasCoefficient R - C) *
        criticalHalfLineExponentialDefect F - Real.log (criticalHalfLineExponentialDefect F) - B ≤
          criticalHalfLineFullEnergy R F := by
  obtain ⟨C, hC, hrem⟩ := criticalHalfLineFullEnergy_arch_remainder_bound
  let g := 2 * gammaHardyPhaseRate 0
  refine ⟨C, 2 * C + |g| + 5 / 2, hC, by positivity, ?_⟩
  intro R F hF hm
  have h := (abs_le.mp (hrem R hF)).1
  have harch := hF.archForm_eq_biScaleLevyEnergy
  have hcost := hF.biScaleLevyEnergy_log_defect_lower hm
  have hd : criticalHalfLineExponentialDefect F =
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) - 1 := by
    rw [criticalHalfLineExponentialDefect, hm]
  rw [hm] at h harch
  change archForm F = g * 1 + biScaleLevyEnergy F at harch
  rw [hd] at hcost ⊢
  nlinarith only [h, harch, hcost, neg_abs_le g]

/-- Compressed compact profiles give the matching logarithmic upper bound. -/
theorem criticalHalfLineGroundEnergy_logarithmic_upper :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧ ∀ R : ℝ, 0 < R → A ≤ criticalAliasCoefficient R →
      criticalHalfLineGroundEnergy R ≤ criticalAliasCoefficient R +
        Real.log (criticalAliasCoefficient R) + K := by
  obtain ⟨A, C₀, hA, htrial⟩ := exists_unit_halfLine_logarithmic_dilates
  obtain ⟨C, hC, hrem⟩ := criticalHalfLineFullEnergy_arch_remainder_bound
  let g := 2 * gammaHardyPhaseRate 0
  let K := |g| + |C₀| + 8 * Real.exp 8 + C * (1 + Real.exp 8)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨A, K, hA, hK, ?_⟩
  intro R hR hAR
  let a := criticalAliasCoefficient R
  have ha : 0 < a := criticalAliasCoefficient_positive hR
  have ha1 : 1 ≤ a := hA.trans hAR
  obtain ⟨F, hF, hm, hW, hJ⟩ := htrial a hAR
  have he := criticalHalfLineGroundEnergy_le hR hF hm
  have h := (abs_le.mp (hrem R hF)).2
  have harch := hF.archForm_eq_biScaleLevyEnergy
  rw [hm] at h harch
  change archForm F = g * 1 + biScaleLevyEnergy F at harch
  obtain ⟨hexp, hcost⟩ := confinement_exp_cost_bound ha1
  have hWexp := hW.trans hexp
  have hconf := (mul_le_mul_of_nonneg_left (sub_le_sub_right hW 1) ha.le).trans hcost
  have herr := mul_le_mul_of_nonneg_left (add_le_add_left hWexp 1) hC
  change criticalHalfLineGroundEnergy R ≤ a + Real.log a + K
  dsimp only [K]
  nlinarith only [he, h, harch, hJ, hconf, herr, le_abs_self g, le_abs_self C₀]

/-- Strong confinement has coefficient-one logarithmic excess and inverse-strength width. -/
theorem criticalHalfLineGroundEnergy_strong_confinement :
    ∃ A K c C : ℝ, 1 ≤ A ∧ 0 ≤ K ∧ 0 < c ∧ 0 < C ∧
      ∀ R : ℝ, 0 < R → A ≤ criticalAliasCoefficient R →
        |criticalHalfLineGroundEnergy R - criticalAliasCoefficient R -
          Real.log (criticalAliasCoefficient R)| ≤ K ∧
        ∀ F : ℝ → ℝ, IsHalfLineEnergyMinimizer R F →
          c ≤ criticalAliasCoefficient R * criticalHalfLineExponentialDefect F ∧
          criticalAliasCoefficient R * criticalHalfLineExponentialDefect F ≤ C := by
  obtain ⟨C₀, B, hC₀, hB, hlower⟩ := criticalHalfLineFullEnergy_log_defect_lower
  obtain ⟨A₀, K₀, hA₀, hK₀, hupper⟩ := criticalHalfLineGroundEnergy_logarithmic_upper
  let Q := Real.log 2 + K₀ + B
  have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith only [hl2, hK₀, hB]
  let A := max A₀ (2 * C₀ + 2)
  let K := max K₀ (B + Real.log 2)
  refine ⟨A, K, Real.exp (-Q), 4 * (Q + Real.log 2 + 1),
    hA₀.trans (le_max_left _ _), hK₀.trans (le_max_left _ _), Real.exp_pos _,
    by positivity, ?_⟩
  intro R hR hAR
  let a := criticalAliasCoefficient R
  let p := a - C₀
  have ha : 0 < a := criticalAliasCoefficient_positive hR
  have hlarge : 2 * C₀ + 2 ≤ a := (le_max_right _ _).trans hAR
  have hp : 0 < p := by dsimp only [p]; linarith only [hlarge, hC₀]
  have hpa : a / 2 ≤ p := by dsimp only [p]; linarith only [hlarge]
  have hpa' : p ≤ a := by dsimp only [p]; linarith only [hC₀]
  have hloga : Real.log a - Real.log 2 ≤ Real.log p := by
    have h := Real.log_le_log (half_pos ha) hpa
    rwa [Real.log_div ha.ne' (by norm_num)] at h
  have hU := hupper R hR ((le_max_left _ _).trans hAR)
  have hL : a + Real.log a - (B + Real.log 2) ≤ criticalHalfLineGroundEnergy R := by
    obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
    have hd := hF.1.exponential_defect_pos (hF.2.1.symm ▸ zero_lt_one)
    have h := hlower R hF.1 hF.2.1
    rw [hF.2.2] at h
    have hpen := logarithmic_penalty_lower hp hd
    change a + p * criticalHalfLineExponentialDefect F -
      Real.log (criticalHalfLineExponentialDefect F) - B ≤ _ at h
    linarith only [h, hpen, hloga]
  constructor
  · apply abs_le.mpr
    have hK1 : K₀ ≤ K := le_max_left _ _
    have hK2 : B + Real.log 2 ≤ K := le_max_right _ _
    constructor <;> linarith only [hU, hL, hK1, hK2]
  · intro F hF
    let d := criticalHalfLineExponentialDefect F
    have hd : 0 < d := hF.1.exponential_defect_pos (hF.2.1.symm ▸ zero_lt_one)
    have h := hlower R hF.1 hF.2.1
    rw [hF.2.2] at h
    change a + p * d - Real.log d - B ≤ criticalHalfLineGroundEnergy R at h
    have hpen : p * d - Real.log (p * d) ≤ Q := by
      rw [Real.log_mul hp.ne' hd.ne']
      dsimp only [Q]
      linarith only [h, hU, hloga]
    obtain ⟨hzlo, hzhi⟩ := logarithmic_penalty_sublevel (mul_pos hp hd) hpen
    have hmlo := mul_le_mul_of_nonneg_right hpa' hd.le
    have hmhi := mul_le_mul_of_nonneg_right hpa hd.le
    constructor
    · exact hzlo.trans hmlo
    · change a * d ≤ _
      linarith only [hmhi, hzhi]

#print axioms criticalHalfLineFullEnergy_log_defect_lower
#print axioms criticalHalfLineGroundEnergy_logarithmic_upper
#print axioms criticalHalfLineGroundEnergy_strong_confinement

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
