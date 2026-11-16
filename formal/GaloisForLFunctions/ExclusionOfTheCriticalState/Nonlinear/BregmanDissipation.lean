import GaloisForLFunctions.ExclusionOfTheCriticalState.TheGammaPairingInLevyForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaContractions
import GaloisForLFunctions.HilbertMetric.Probability.BregmanDissipation

/-!
# A bounded nonlinear Bregman test of the critical state

The symmetrized Bregman identity turns the Gamma jump pairing with
`arctan ∘ F` into a nonnegative dissipation. The contraction theorem
places this test in the actual energy domain. Its jump energy is bounded
above by that of `F` and below by that of `arctan ∘ F`. At a critical
state, the full weak equation identifies this dissipation with an explicit
balance of prime, pole, mass, and confinement terms.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower
open HilbertMetric.Probability

/-- The bounded monotone test is admissible for every actual energy-domain profile. -/
theorem domain_arctan {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    CriticalHalfLineEnergyDomain (Real.arctan ∘ F) :=
  hF.comp_contraction arctan_contraction Real.arctan_zero

/-- Gamma jump dissipation of the arctangent test. -/
def arctanLevyDissipation (F : ℝ → ℝ) : ℝ := levyMixed F (Real.arctan ∘ F)

/-- The nonlinear jump pairing is exactly the sum of the two oriented Bregman remainders. -/
theorem arctanLevyDissipation_eq_bregman (F : ℝ → ℝ) :
    arctanLevyDissipation F =
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u,
        (scalarBregman arctanPotential (F u) (F (u + x)) +
          scalarBregman arctanPotential (F (u + x)) (F u)) := by
  unfold arctanLevyDissipation levyMixed
  congr 1
  funext x
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun u => (arctanBregman_symm _ _).symm

private theorem integrable_arctanJump {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    Integrable fun u => (F u - F (u + x)) *
      (Real.arctan (F u) - Real.arctan (F (u + x))) := by
  have ht := (domain_arctan hF).memLp_real
  exact integrable_mul_of_memLp (hF.memLp_real.sub (memLp_two_shift hF.memLp_real x))
    (ht.sub (memLp_two_shift ht x))

private theorem integral_arctanJump_bounds {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    (∫ u, (Real.arctan (F u) - Real.arctan (F (u + x))) ^ 2) ≤
      (∫ u, (F u - F (u + x)) * (Real.arctan (F u) - Real.arctan (F (u + x)))) ∧
    (∫ u, (F u - F (u + x)) * (Real.arctan (F u) - Real.arctan (F (u + x)))) ≤
      ∫ u, (F u - F (u + x)) ^ 2 := by
  have ht := (domain_arctan hF).memLp_real
  have hi := integrable_arctanJump hF x
  constructor
  · exact integral_mono (integrable_sq_of_memLp (ht.sub (memLp_two_shift ht x))) hi
      (fun u => (arctan_jump_bounds (F u) (F (u + x))).1)
  · exact integral_mono hi
      (integrable_sq_of_memLp (hF.memLp_real.sub (memLp_two_shift hF.memLp_real x)))
      (fun u => (arctan_jump_bounds (F u) (F (u + x))).2)

/-- Absolute convergence of the nonlinear jump pairing follows from the existing energy. -/
theorem integrableOn_arctanDissipation {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    IntegrableOn (fun x : ℝ => archLevyDensity x * ∫ u,
      (F u - F (u + x)) * (Real.arctan (F u) - Real.arctan (F (u + x)))) (Ioi 0) := by
  have hm : Measurable (fun p : ℝ × ℝ => (F p.2 - F (p.2 + p.1)) *
      (Real.arctan (F p.2) - Real.arctan (F (p.2 + p.1)))) := by
    have hf := hF.meas
    fun_prop
  refine hF.integrableOn_levyIntegrand.mono'
    (measurable_archLevyDensity.aestronglyMeasurable.mul
      hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hnonneg : 0 ≤ ∫ u, (F u - F (u + x)) *
      (Real.arctan (F u) - Real.arctan (F (u + x))) :=
    integral_nonneg fun u => (sq_nonneg _).trans (arctan_jump_bounds _ _).1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos hx).le hnonneg)]
  exact mul_le_mul_of_nonneg_left (integral_arctanJump_bounds hF x).2
    (archLevyDensity_pos hx).le

/-- The nonlinear dissipation lies between the two genuine finite jump energies. -/
theorem arctanLevyDissipation_bounds {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    levyEnergy (Real.arctan ∘ F) ≤ arctanLevyDissipation F ∧
      arctanLevyDissipation F ≤ levyEnergy F := by
  have hi := integrableOn_arctanDissipation hF
  constructor
  · apply integral_mono_ae (domain_arctan hF).integrableOn_levyIntegrand hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_le_mul_of_nonneg_left (integral_arctanJump_bounds hF x).1
      (archLevyDensity_pos hx).le
  · apply integral_mono_ae hi hF.integrableOn_levyIntegrand
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_le_mul_of_nonneg_left (integral_arctanJump_bounds hF x).2
      (archLevyDensity_pos hx).le

theorem arctanLevyDissipation_nonneg (F : ℝ → ℝ) : 0 ≤ arctanLevyDissipation F := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (archLevyDensity_pos hx).le
    (integral_nonneg fun u => (sq_nonneg _).trans (arctan_jump_bounds _ _).1)

/-- Signed terms which the nonlinear Gamma dissipation must balance. -/
def arctanArithmeticBalance (R : ℝ) (F : ℝ → ℝ) : ℝ :=
  (primeMixedForm F (Real.arctan ∘ F) + primeMixedForm (Real.arctan ∘ F) F) / 2 -
    (2 * coshHalfMoment F * coshHalfMoment (Real.arctan ∘ F) -
      2 * sinhHalfMoment F * sinhHalfMoment (Real.arctan ∘ F)) -
    2 * gammaHardyPhaseRate 0 * (∫ u, F u * Real.arctan (F u)) -
    criticalAliasCoefficient R * (∫ u in Iio 0, F u * Real.arctan (F u) * Real.exp (-(8 * u)))

/-- The admissible nonlinear test gives an exact identity in the full state equation. -/
theorem criticalState_arctan_balance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    arctanLevyDissipation F = arctanArithmeticBalance W₀ F := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF (domain_arctan hd)
  rw [criticalHalfLineMixedEnergy, gammaMixedForm_eq_levy hd (domain_arctan hd)] at hw
  unfold arctanLevyDissipation arctanArithmeticBalance
  simp only [Function.comp_apply] at hw ⊢
  linarith only [hw]

/-- Every state in the unconditional alternative obeys the nonlinear dissipation constraint. -/
theorem riemannHypothesis_or_criticalState_bregman_balance :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      CriticalHalfLineEnergyDomain (Real.arctan ∘ F) ∧
      arctanLevyDissipation F = arctanArithmeticBalance W₀ F ∧
      0 ≤ arctanArithmeticBalance W₀ F ∧
      levyEnergy (Real.arctan ∘ F) ≤ arctanArithmeticBalance W₀ F ∧
      arctanArithmeticBalance W₀ F ≤ levyEnergy F := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · have hd := criticalHalfLineEnergyDomain_of_groundState hF
    have he := criticalState_arctan_balance hW ht hF
    have hb := arctanLevyDissipation_bounds hd
    exact Or.inr ⟨W₀, F, hW, ht, hF, domain_arctan hd, he,
      he ▸ arctanLevyDissipation_nonneg F, he ▸ hb.1, he ▸ hb.2⟩

#print axioms domain_arctan
#print axioms arctanLevyDissipation_eq_bregman
#print axioms integrableOn_arctanDissipation
#print axioms arctanLevyDissipation_bounds
#print axioms riemannHypothesis_or_criticalState_bregman_balance

end GaloisForLFunctions.ExclusionOfTheCriticalState
end
