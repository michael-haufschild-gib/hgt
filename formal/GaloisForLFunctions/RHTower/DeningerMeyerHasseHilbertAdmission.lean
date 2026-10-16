import GaloisForLFunctions.RHTower.DeningerMeyerHasseMoments
import GaloisForLFunctions.RHTower.DeningerArithmeticJetHilbertRigging
import GaloisForLFunctions.RHTower.DeningerMeyerGlobalXiSynthesis
import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass

/-! # Actual Meyer sources enter the full jet Hilbert carrier

All multiplicity-bounded Hasse jets of each original source are square
summable. No additional spectral weights or admission premises occur. The
map descends through the actual Poisson boundary and is faithful by global
Xi synthesis.
-/

noncomputable section
open Complex MeasureTheory Set

namespace RHTower

private def hasseReference : DeningerArithmeticJetHilbert :=
  ⟨fun q => (xiSpectralPoint q)⁻¹, memℓp_gen (by
    simpa [DeningerArithmeticJetCoordinate, DeningerArithmeticJetIndex,
      xiSupportMultiplicity, XiZeroCopy]
      using summable_norm_inv_xiSpectralPoint_sq)⟩

theorem deningerMeyerHasseMoment_divisor_bound
    (g : DeningerMeyerStrongLogTarget) (q : XiZeroCopy) :
    ‖deningerMeyerHasseMoment g q.2.val (q.1 : ℂ)‖ ≤
      deningerMeyerHasseSourceCost g * ‖(xiSpectralPoint q)⁻¹‖ := by
  have hp : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hb := deningerMeyerHasseMoment_decay g q.2.val hs.1.le hs.2.le
  have hn : ‖xiSpectralPoint q‖ ≤ 1 + ‖(q.1 : ℂ)‖ := by
    rw [xiSpectralPoint_eq_support, xiSpectralPointSupport, norm_mul,
      norm_neg, Complex.norm_I, mul_one]
    have h := norm_sub_le (q.1 : ℂ) (1 / 2)
    norm_num at h
    linarith
  rw [norm_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  nlinarith [norm_nonneg (deningerMeyerHasseMoment g q.2.val (q.1 : ℂ))]

/-- Native admission of the full Hasse packet, including every repeated-zero slot. -/
theorem deningerMeyerHasseMoment_memℓp (g : DeningerMeyerStrongLogTarget) :
    Memℓp (fun q : DeningerArithmeticJetCoordinate =>
      deningerMeyerHasseMoment g q.2.val (q.1 : ℂ)) 2 := by
  apply (lp.memℓp ((deningerMeyerHasseSourceCost g : ℂ) • hasseReference)).mono'
  intro q
  change ‖deningerMeyerHasseMoment g q.2.val (q.1 : ℂ)‖ ≤
    ‖(deningerMeyerHasseSourceCost g : ℂ) * (xiSpectralPoint q)⁻¹‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (deningerMeyerHasseSourceCost_nonneg g)]
  exact deningerMeyerHasseMoment_divisor_bound g q

def deningerMeyerHasseJet (u : DeningerMeyerStrongLogCohomology)
    (q : DeningerArithmeticJetCoordinate) : ℂ :=
  deningerMeyerXiSupportJetEvaluationLM q.1 q.2 u / (q.2.val.factorial : ℂ)

@[simp] theorem deningerMeyerHasseJet_mk (g : DeningerMeyerStrongLogTarget)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseJet (Submodule.Quotient.mk g) q =
      deningerMeyerHasseMoment g q.2.val (q.1 : ℂ) := rfl

theorem deningerMeyerHasseJet_memℓp (u : DeningerMeyerStrongLogCohomology) :
    Memℓp (deningerMeyerHasseJet u) 2 := by
  induction u using Submodule.Quotient.induction_on with
  | H g => exact deningerMeyerHasseMoment_memℓp g

/-- The canonical Hilbert realization uses the actual source jets, normalized only by factorials. -/
def deningerMeyerHasseHilbertLM :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun u := ⟨deningerMeyerHasseJet u, deningerMeyerHasseJet_memℓp u⟩
  map_add' u v := by
    apply lp.ext
    funext q
    simp [deningerMeyerHasseJet, add_div]
  map_smul' c u := by
    apply lp.ext
    funext q
    simp [deningerMeyerHasseJet, mul_div_assoc]

@[simp] theorem deningerMeyerHasseHilbertLM_apply (u : DeningerMeyerStrongLogCohomology)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseHilbertLM u q = deningerMeyerHasseJet u q := rfl

theorem deningerMeyerHasseHilbertLM_injective :
    Function.Injective deningerMeyerHasseHilbertLM := by
  intro u v h
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho j
  have hj := congrArg (fun x : DeningerArithmeticJetHilbert => x ⟨rho, j⟩) h
  change deningerMeyerXiSupportJetEvaluationLM rho j u / (j.val.factorial : ℂ) =
    deningerMeyerXiSupportJetEvaluationLM rho j v / (j.val.factorial : ℂ) at hj
  have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  exact (div_left_inj' hf).mp hj

/-- One fixed source cost controls the complete Hilbert packet. -/
theorem deningerMeyerHasseHilbertLM_source_bound (g : DeningerMeyerStrongLogTarget) :
    ‖deningerMeyerHasseHilbertLM (Submodule.Quotient.mk g)‖ ≤
      deningerMeyerHasseSourceCost g * ‖hasseReference‖ := by
  have hb : ‖deningerMeyerHasseHilbertLM (Submodule.Quotient.mk g)‖ ≤
      ‖(deningerMeyerHasseSourceCost g : ℂ) • hasseReference‖ := by
    apply lp.norm_mono (by norm_num)
    intro q
    change ‖deningerMeyerHasseMoment g q.2.val (q.1 : ℂ)‖ ≤
      ‖(deningerMeyerHasseSourceCost g : ℂ) * (xiSpectralPoint q)⁻¹‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (deningerMeyerHasseSourceCost_nonneg g)]
    exact deningerMeyerHasseMoment_divisor_bound g q
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (deningerMeyerHasseSourceCost_nonneg g)] using hb

theorem deningerMeyerHasseHilbertLM_exists_source_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : DeningerMeyerStrongLogTarget,
      ‖deningerMeyerHasseHilbertLM (Submodule.Quotient.mk g)‖ ≤
        C * deningerMeyerHasseSourceCost g := by
  exact ⟨‖hasseReference‖, norm_nonneg _, fun g => by
    simpa only [mul_comm] using deningerMeyerHasseHilbertLM_source_bound g⟩

end RHTower
