import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.QuantitativeBregmanBalance
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExactJumpBoundaryControl

/-!
# Exact and logarithmic boundary constraints on the Bregman balance

The full Lévy tail multiplies each of the three positive terminal
moments. It yields a strictly stronger coefficient than the first
exponential mode. Summing the first two moments bounds the signed
arithmetic balance below by the terminal integral of `F * atan(F)`.
For `0 < d ≤ 1`, the same estimate controls this integral with the
logarithmic weight `log(2/d)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower WeilLevyPoleGauss

/-- Each Bregman gap controls its terminal moment with the exact Lévy tail coefficient. -/
theorem arctanBoundaryMoment_exact_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) {d : ℝ} (hd : 0 < d) :
    archLevyAntideriv d * arctanBoundaryMoment i d F ≤ arctanGapEnergy i F := by
  rw [arctanGapEnergy_eq_integral hF i]
  exact hF.jump_boundary_exact_lower (arctanGapKernel_nonneg i)
    (fun x _ => integrable_arctanGapKernel hF i x) (integrableOn_arctanGapKernel hF i) hd

/-- The first two terminal moments add up to the nonlinear mixed moment. -/
theorem arctanBoundaryMoment_zero_add_one {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (d : ℝ) :
    arctanBoundaryMoment 0 d F + arctanBoundaryMoment 1 d F =
      ∫ u in Ioo (-d) 0, F u * Real.arctan (F u) := by
  unfold arctanBoundaryMoment
  rw [← integral_add (integrableOn_arctanBoundaryMoment hF 0 d)
    (integrableOn_arctanBoundaryMoment hF 1 d)]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    change (Real.arctan (F u) - Real.arctan 0) ^ 2 +
      ((F u - 0) * (Real.arctan (F u) - Real.arctan 0) -
        (Real.arctan (F u) - Real.arctan 0) ^ 2) = F u * Real.arctan (F u)
    rw [Real.arctan_zero, sub_zero, sub_zero]
    ring

/-- Every terminal gap is positive and satisfies the exact boundary constraint. -/
theorem criticalState_arctan_exact_boundary_balance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (i : Fin 3)
    {d : ℝ} (hd : 0 < d) :
    0 < arctanBoundaryMoment i d F ∧
      archLevyAntideriv d * arctanBoundaryMoment i d F ≤
        ![levyEnergy (Real.arctan ∘ F),
          arctanArithmeticBalance W₀ F - levyEnergy (Real.arctan ∘ F),
          levyEnergy F - arctanArithmeticBalance W₀ F] i := by
  refine ⟨criticalState_arctanBoundaryMoment_pos hW ht hF i hd, ?_⟩
  have h := arctanBoundaryMoment_exact_lower (criticalHalfLineEnergyDomain_of_groundState hF) i hd
  simpa only [arctanGapEnergy, criticalState_arctan_balance hW ht hF] using h

/-- The exact Lévy coefficient gives a strictly larger positive bound than the first mode. -/
theorem criticalState_arctan_boundary_coefficient_improves {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (i : Fin 3)
    {d : ℝ} (hd : 0 < d) :
    (2 * Real.exp (-d / 2)) * arctanBoundaryMoment i d F <
      archLevyAntideriv d * arctanBoundaryMoment i d F :=
  mul_lt_mul_of_pos_right (archLevyAntideriv_gt_firstMode hd)
    (criticalState_arctanBoundaryMoment_pos hW ht hF i hd)

/-- The arithmetic balance pays the exact Lévy tail times a positive nonlinear terminal moment. -/
theorem criticalState_arctan_balance_exact_terminal_lower {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {d : ℝ} (hd : 0 < d) :
    0 < archLevyAntideriv d * (∫ u in Ioo (-d) 0, F u * Real.arctan (F u)) ∧
      archLevyAntideriv d * (∫ u in Ioo (-d) 0, F u * Real.arctan (F u)) ≤
        arctanArithmeticBalance W₀ F := by
  rw [← arctanBoundaryMoment_zero_add_one (criticalHalfLineEnergyDomain_of_groundState hF) d]
  obtain ⟨hp0, h0⟩ := criticalState_arctan_exact_boundary_balance hW ht hF 0 hd
  obtain ⟨hp1, h1⟩ := criticalState_arctan_exact_boundary_balance hW ht hF 1 hd
  change archLevyAntideriv d * arctanBoundaryMoment 0 d F ≤
    levyEnergy (Real.arctan ∘ F) at h0
  change archLevyAntideriv d * arctanBoundaryMoment 1 d F ≤
    arctanArithmeticBalance W₀ F - levyEnergy (Real.arctan ∘ F) at h1
  refine ⟨mul_pos (archLevyAntideriv_pos hd) (add_pos hp0 hp1), ?_⟩
  rw [mul_add]
  linarith only [h0, h1]

/-- Finite Bregman energy bounds all three terminal moments with a logarithmic weight. -/
theorem arctanBoundaryMoment_logarithmic_bound {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) :
    Real.log (2 / d) * arctanBoundaryMoment i d F ≤ 2 * arctanGapEnergy i F := by
  have hn : 0 ≤ arctanBoundaryMoment i d F :=
    integral_nonneg fun u => arctanGapKernel_nonneg i (F u) 0
  have hc := mul_le_mul_of_nonneg_right (log_two_div_le_twice_archLevyAntideriv hd hd1) hn
  have he := arctanBoundaryMoment_exact_lower hF i hd
  linarith only [hc, he]

/-- The signed arithmetic balance bounds the nonlinear mass in every short terminal collar. -/
theorem criticalState_arctan_balance_logarithmic_terminal_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) :
    Real.log (2 / d) * (∫ u in Ioo (-d) 0, F u * Real.arctan (F u)) ≤
      2 * arctanArithmeticBalance W₀ F := by
  have hD := criticalHalfLineEnergyDomain_of_groundState hF
  rw [← arctanBoundaryMoment_zero_add_one hD d, mul_add]
  have h0 := arctanBoundaryMoment_logarithmic_bound hD 0 hd hd1
  have h1 := arctanBoundaryMoment_logarithmic_bound hD 1 hd hd1
  change Real.log (2 / d) * arctanBoundaryMoment 0 d F ≤
    2 * levyEnergy (Real.arctan ∘ F) at h0
  change Real.log (2 / d) * arctanBoundaryMoment 1 d F ≤
    2 * (arctanLevyDissipation F - levyEnergy (Real.arctan ∘ F)) at h1
  rw [criticalState_arctan_balance hW ht hF] at h1
  linarith only [h0, h1]

/-- The unconditional alternative includes every exact terminal constraint at every positive scale. -/
theorem riemannHypothesis_or_criticalState_exact_bregman_boundary_balance :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ d : ℝ, 0 < d → ∀ i : Fin 3,
        0 < arctanBoundaryMoment i d F ∧
        archLevyAntideriv d * arctanBoundaryMoment i d F ≤
          ![levyEnergy (Real.arctan ∘ F),
            arctanArithmeticBalance W₀ F - levyEnergy (Real.arctan ∘ F),
            levyEnergy F - arctanArithmeticBalance W₀ F] i := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      fun d hd i => criticalState_arctan_exact_boundary_balance hW ht hF i hd⟩

#print axioms criticalState_arctan_boundary_coefficient_improves
#print axioms criticalState_arctan_balance_exact_terminal_lower
#print axioms criticalState_arctan_balance_logarithmic_terminal_bound
#print axioms riemannHypothesis_or_criticalState_exact_bregman_boundary_balance

end GaloisForLFunctions.ExclusionOfTheCriticalState
end
