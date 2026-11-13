import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningLogarithmicLimit

/-!
# Exact mass and width scales under strong confinement

Affine variational comparisons bound each minimizing exponential mass
between two secants of the ground energy. Its logarithmic asymptotic fixes
the scaled excess at one and the scaled physical first moment at one eighth.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

private theorem lower_scaled_secant {a b : ℝ} (ha : 0 < a) (hb : 1 < b)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F) :
    (Real.log b + renormalizedConfiningGroundEnergy (b * a) -
      renormalizedConfiningGroundEnergy a) / (b - 1) ≤
      a * criticalHalfLineExponentialDefect F := by
  have hb0 := zero_lt_one.trans hb
  have hba := mul_pos hb0 ha
  have ht := criticalHalfLineGroundEnergy_le (confiningHalfLineRatio_pos hba) hF.1 hF.2.1
  rw [criticalHalfLineFullEnergy_change_ratio (confiningHalfLineRatio (b * a))
    (confiningHalfLineRatio a) hF.1, hF.2.2,
    criticalAliasCoefficient_confiningHalfLineRatio hba,
    criticalAliasCoefficient_confiningHalfLineRatio ha] at ht
  apply (div_le_iff₀ (sub_pos.mpr hb)).mpr
  dsimp only [renormalizedConfiningGroundEnergy, criticalHalfLineExponentialDefect]
  rw [Real.log_mul hb0.ne' ha.ne', hF.2.1]
  nlinarith only [ht]

private theorem positive_secant_denominator {b : ℝ} (hb : 1 < b) : 0 < 1 - 1 / b := by
  have hb0 := zero_lt_one.trans hb
  have he : 1 - 1 / b = (b - 1) / b := by field_simp [hb0.ne'] <;> ring
  rw [he]
  exact div_pos (sub_pos.mpr hb) hb0

private theorem upper_scaled_secant {a b : ℝ} (ha : 0 < a) (hb : 1 < b)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F) :
    a * criticalHalfLineExponentialDefect F ≤
      (Real.log b + renormalizedConfiningGroundEnergy a -
        renormalizedConfiningGroundEnergy (a / b)) / (1 - 1 / b) := by
  have hb0 := zero_lt_one.trans hb
  have hab := div_pos ha hb0
  have ht := criticalHalfLineGroundEnergy_le (confiningHalfLineRatio_pos hab) hF.1 hF.2.1
  rw [criticalHalfLineFullEnergy_change_ratio (confiningHalfLineRatio (a / b))
    (confiningHalfLineRatio a) hF.1, hF.2.2,
    criticalAliasCoefficient_confiningHalfLineRatio hab,
    criticalAliasCoefficient_confiningHalfLineRatio ha] at ht
  apply (le_div_iff₀ (positive_secant_denominator hb)).mpr
  dsimp only [renormalizedConfiningGroundEnergy, criticalHalfLineExponentialDefect]
  rw [Real.log_div ha.ne' hb0.ne', hF.2.1]
  simp only [div_eq_mul_inv, one_mul] at ht ⊢
  nlinarith only [ht]

private theorem logarithmic_secant_bounds {b : ℝ} (hb : 1 < b) :
    1 / b ≤ Real.log b / (b - 1) ∧ Real.log b / (1 - 1 / b) ≤ b := by
  have hb0 := zero_lt_one.trans hb
  have hlo := Real.log_le_sub_one_of_pos (inv_pos.mpr hb0)
  rw [Real.log_inv] at hlo
  have hhi := Real.log_le_sub_one_of_pos hb0
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
    have he : (1 / b) * (b - 1) = 1 - 1 / b := by field_simp [hb0.ne'] <;> ring
    rw [he]
    simpa only [one_div] using (show 1 - b⁻¹ ≤ Real.log b by linarith only [hlo])
  · apply (div_le_iff₀ (positive_secant_denominator hb)).mpr
    have he : b * (1 - 1 / b) = b - 1 := by field_simp [hb0.ne'] <;> ring
    rw [he]
    exact hhi

/-- Logarithmic ground-energy asymptotics force the scaled excess of every minimizer to one. -/
theorem exists_minimizer_scaled_excess_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {a : ℝ}, A ≤ a → ∀ {F : ℝ → ℝ},
      IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F →
      |a * criticalHalfLineExponentialDefect F - 1| < ε := by
  let b : ℝ := 1 + ε / 2
  have hb : 1 < b := by dsimp only [b]; linarith only [hε]
  have hb0 := zero_lt_one.trans hb
  have hscale : Tendsto (fun a : ℝ => b * a) atTop atTop :=
    tendsto_id.const_mul_atTop hb0
  have hdivide : Tendsto (fun a : ℝ => a / b) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_id.const_mul_atTop (inv_pos.mpr hb0))
  have hc : Tendsto (fun _ : ℝ => Real.log b) atTop (𝓝 (Real.log b)) := tendsto_const_nhds
  have hl := ((hc.add (tendsto_renormalizedConfiningGroundEnergy.comp hscale)).sub
    tendsto_renormalizedConfiningGroundEnergy).div_const (b - 1)
  have hu := ((hc.add tendsto_renormalizedConfiningGroundEnergy).sub
    (tendsto_renormalizedConfiningGroundEnergy.comp hdivide)).div_const (1 - 1 / b)
  simp only [add_sub_cancel_right] at hl hu
  have hel := (Metric.tendsto_nhds.mp hl) (ε / 2) (half_pos hε)
  have heu := (Metric.tendsto_nhds.mp hu) (ε / 2) (half_pos hε)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hel.and heu)
  refine ⟨max 1 A, le_max_left _ _, ?_⟩
  intro a ha F hF
  have ha0 := zero_lt_one.trans_le ((le_max_left _ _).trans ha)
  obtain ⟨hlclose, huclose⟩ := hA a ((le_max_right _ _).trans ha)
  rw [Real.dist_eq] at hlclose huclose
  have hlower := lower_scaled_secant ha0 hb hF
  have hupper := upper_scaled_secant ha0 hb hF
  obtain ⟨hloglo, hloghi⟩ := logarithmic_secant_bounds hb
  have hbinv : 1 - ε / 2 < 1 / b := by
    apply (lt_div_iff₀ hb0).mpr
    dsimp only [b]
    nlinarith only [sq_pos_of_pos (half_pos hε)]
  have hbval : b = 1 + ε / 2 := rfl
  have hlc := (abs_lt.mp hlclose).1
  have huc := (abs_lt.mp huclose).2
  apply abs_lt.mpr
  constructor <;> linarith only [hlower, hupper, hloglo, hloghi, hbinv, hbval, hlc, huc]

/-- The physical width of every minimizing line has the exact limiting scale `1/(8a)`. -/
theorem exists_minimizer_scaled_firstMoment_near_one_eighth {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {a : ℝ}, A ≤ a → ∀ {F : ℝ → ℝ},
      IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F →
      |a * criticalHalfLineFirstMoment F - 1 / 8| < ε := by
  have he : 0 < 4 * ε := by positivity
  obtain ⟨A₀, hA₀, hexcess⟩ := exists_minimizer_scaled_excess_near_one he
  obtain ⟨A₁, hA₁, hsoft⟩ := exists_minimizer_softLogarithmic_error_small he
  refine ⟨max A₀ A₁, hA₀.trans (le_max_left _ _), ?_⟩
  intro a ha F hF
  have ha₀ := (le_max_left _ _).trans ha
  have ha₁ := (le_max_right _ _).trans ha
  have ha0 := zero_lt_one.trans_le (hA₀.trans ha₀)
  have hx := abs_lt.mp (hexcess ha₀ hF)
  obtain ⟨hq, hp, hsum⟩ := hsoft ha₁ hF
  rw [firstMoment_rescaledConfiningProfile ha0] at hp hsum
  apply abs_lt.mpr
  constructor <;> linarith only [hx.1, hx.2, hq, hp, hsum, hε]

theorem confiningHalfLineRatio_aliasCoefficient {R : ℝ} (hR : 0 < R) :
    confiningHalfLineRatio (criticalAliasCoefficient R) = R := by
  rw [confiningHalfLineRatio, criticalAliasCoefficient_eq_div R]
  have hk : criticalAliasCoefficient 1 ≠ 0 :=
    (criticalAliasCoefficient_positive zero_lt_one).ne'
  field_simp [hk, hR.ne']

/-- Strong confinement has a universal logarithmic floor and exact excess and width scales. -/
theorem universal_softLogarithmic_confinement_limit {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ R : ℝ, 0 < R → A ≤ criticalAliasCoefficient R →
      |criticalHalfLineGroundEnergy R - criticalAliasCoefficient R -
        Real.log (criticalAliasCoefficient R) - softLogarithmicHalfLineGroundEnergy| < ε ∧
      ∀ F : ℝ → ℝ, IsHalfLineEnergyMinimizer R F →
        |softLogarithmicHalfLineEnergy (rescaledConfiningProfile (criticalAliasCoefficient R) F) -
          softLogarithmicHalfLineGroundEnergy| < ε ∧
        |criticalAliasCoefficient R * criticalHalfLineExponentialDefect F - 1| < ε ∧
        |criticalAliasCoefficient R * criticalHalfLineFirstMoment F - 1 / 8| < ε := by
  obtain ⟨A₀, henergy⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp tendsto_renormalizedConfiningGroundEnergy) ε hε)
  obtain ⟨A₁, hA₁, hsoft⟩ := exists_minimizer_softLogarithmic_error_small hε
  obtain ⟨A₂, _, hexcess⟩ := exists_minimizer_scaled_excess_near_one hε
  obtain ⟨A₃, _, hmoment⟩ := exists_minimizer_scaled_firstMoment_near_one_eighth hε
  refine ⟨max A₁ (max A₂ (max A₃ A₀)), hA₁.trans (le_max_left _ _), ?_⟩
  intro R hR hA
  have h₁ : A₁ ≤ criticalAliasCoefficient R := (le_max_left _ _).trans hA
  have ht : max A₂ (max A₃ A₀) ≤ criticalAliasCoefficient R := (le_max_right _ _).trans hA
  have h₂ : A₂ ≤ criticalAliasCoefficient R := (le_max_left _ _).trans ht
  have hu : max A₃ A₀ ≤ criticalAliasCoefficient R := (le_max_right _ _).trans ht
  have h₃ : A₃ ≤ criticalAliasCoefficient R := (le_max_left _ _).trans hu
  have h₀ : A₀ ≤ criticalAliasCoefficient R := (le_max_right _ _).trans hu
  have hratio := confiningHalfLineRatio_aliasCoefficient hR
  constructor
  · simpa only [Real.dist_eq, renormalizedConfiningGroundEnergy, hratio] using
      henergy (criticalAliasCoefficient R) h₀
  · intro F hF
    have hf : IsHalfLineEnergyMinimizer (confiningHalfLineRatio (criticalAliasCoefficient R)) F := by
      rwa [hratio]
    obtain ⟨hq, hp, hs⟩ := hsoft h₁ hf
    refine ⟨?_, hexcess h₂ hf, hmoment h₃ hf⟩
    rw [abs_of_nonneg hq]
    linarith only [hp, hs]

#print axioms exists_minimizer_scaled_excess_near_one
#print axioms exists_minimizer_scaled_firstMoment_near_one_eighth
#print axioms universal_softLogarithmic_confinement_limit
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
