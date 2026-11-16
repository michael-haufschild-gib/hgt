import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.ExactBregmanBoundaryBalance
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.VanishingJumpBoundaryCost

/-!
# Positive Bregman boundary costs vanish on shrinking collars

Every finite-energy half-line profile has vanishing exact and logarithmic
boundary costs. This holds for each Bregman defect, the mixed moment
`F * atan(F)`, and the square mass. For a critical state the three costs
remain strictly positive at every scale, but no positive lower bound
persists on all sufficiently small collars.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower WeilLevyPoleGauss

/-- Finite Bregman energy makes each exact terminal cost vanish at the endpoint. -/
theorem arctanBoundaryMoment_exact_cost_tendsto_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) :
    Tendsto (fun d : ℝ => archLevyAntideriv d * arctanBoundaryMoment i d F)
      (𝓝[>] 0) (𝓝 0) :=
  hF.jump_boundary_exact_tendsto_zero (arctanGapKernel_nonneg i)
    (fun x _ => integrable_arctanGapKernel hF i x) (integrableOn_arctanGapKernel hF i)

/-- The terminal Bregman moments decay faster than the reciprocal logarithmic scale. -/
theorem arctanBoundaryMoment_logarithmic_cost_tendsto_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) :
    Tendsto (fun d : ℝ => Real.log (2 / d) * arctanBoundaryMoment i d F)
      (𝓝[>] 0) (𝓝 0) :=
  logarithmic_moment_tendsto_zero_of_exact_cost
    (M := fun d => arctanBoundaryMoment i d F)
    (fun _ _ => integral_nonneg fun u => arctanGapKernel_nonneg i (F u) 0)
    (arctanBoundaryMoment_exact_cost_tendsto_zero hF i)

/-- The mixed terminal moment has vanishing cost even with the full Lévy tail coefficient. -/
theorem arctan_mixed_terminal_exact_cost_tendsto_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun d : ℝ => archLevyAntideriv d *
      (∫ u in Ioo (-d) 0, F u * Real.arctan (F u))) (𝓝[>] 0) (𝓝 0) := by
  have h := (arctanBoundaryMoment_exact_cost_tendsto_zero hF 0).add
    (arctanBoundaryMoment_exact_cost_tendsto_zero hF 1)
  simp only [add_zero] at h
  apply Filter.Tendsto.congr' (f₁ := fun d : ℝ =>
    archLevyAntideriv d * arctanBoundaryMoment 0 d F +
      archLevyAntideriv d * arctanBoundaryMoment 1 d F) ?_ h
  exact Eventually.of_forall fun d => by
    dsimp only
    rw [← mul_add, arctanBoundaryMoment_zero_add_one hF d]

/-- The logarithmically weighted mixed terminal moment vanishes throughout the energy domain. -/
theorem arctan_mixed_terminal_logarithmic_cost_tendsto_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun d : ℝ => Real.log (2 / d) *
      (∫ u in Ioo (-d) 0, F u * Real.arctan (F u))) (𝓝[>] 0) (𝓝 0) := by
  apply logarithmic_moment_tendsto_zero_of_exact_cost ?_
    (arctan_mixed_terminal_exact_cost_tendsto_zero hF)
  intro d _
  change 0 ≤ ∫ u in Ioo (-d) 0, F u * Real.arctan (F u)
  rw [← arctanBoundaryMoment_zero_add_one hF d]
  exact add_nonneg (integral_nonneg fun u => arctanGapKernel_nonneg 0 (F u) 0)
    (integral_nonneg fun u => arctanGapKernel_nonneg 1 (F u) 0)

/-- Summing the three defects gives vanishing exact boundary cost for ordinary square mass. -/
theorem terminal_square_exact_cost_tendsto_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun d : ℝ => archLevyAntideriv d * (∫ u in Ioo (-d) 0, F u ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  have h := ((arctanBoundaryMoment_exact_cost_tendsto_zero hF 0).add
    (arctanBoundaryMoment_exact_cost_tendsto_zero hF 1)).add
      (arctanBoundaryMoment_exact_cost_tendsto_zero hF 2)
  simp only [add_zero] at h
  apply Filter.Tendsto.congr' (f₁ := fun d : ℝ =>
    archLevyAntideriv d * arctanBoundaryMoment 0 d F +
      archLevyAntideriv d * arctanBoundaryMoment 1 d F +
      archLevyAntideriv d * arctanBoundaryMoment 2 d F) ?_ h
  exact Eventually.of_forall fun d => by
    dsimp only
    rw [← mul_add, ← mul_add, arctanBoundaryMoment_sum hF d]

/-- The terminal square mass is little-o of the reciprocal logarithmic scale. -/
theorem terminal_square_logarithmic_cost_tendsto_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun d : ℝ => Real.log (2 / d) * (∫ u in Ioo (-d) 0, F u ^ 2))
      (𝓝[>] 0) (𝓝 0) :=
  logarithmic_moment_tendsto_zero_of_exact_cost
    (M := fun d => ∫ u in Ioo (-d) 0, F u ^ 2)
    (fun _ _ => integral_nonneg fun u => sq_nonneg (F u))
    (terminal_square_exact_cost_tendsto_zero hF)

/-- A critical state's boundary cost is positive at every scale and arbitrarily small near zero. -/
theorem criticalState_arctan_boundary_cost_arbitrarily_small {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d < ε ∧
      0 < archLevyAntideriv d * arctanBoundaryMoment i d F ∧
      archLevyAntideriv d * arctanBoundaryMoment i d F < ε := by
  have hlim := arctanBoundaryMoment_exact_cost_tendsto_zero
    (criticalHalfLineEnergyDomain_of_groundState hF) i
  have hp : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := self_mem_nhdsWithin
  have hs : ∀ᶠ d : ℝ in 𝓝[>] 0, d < ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  obtain ⟨d, hd, hdε, hcε⟩ := (hp.and (hs.and (hlim.eventually_lt_const hε))).exists
  exact ⟨d, hd, hdε, mul_pos (archLevyAntideriv_pos hd)
    (criticalState_arctanBoundaryMoment_pos hW ht hF i hd), hcε⟩

/-- No positive boundary floor can hold on every sufficiently small collar of a critical state. -/
theorem criticalState_no_uniform_positive_arctan_boundary_floor {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (i : Fin 3) :
    ¬ ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ d : ℝ, 0 < d → d < r →
      c ≤ archLevyAntideriv d * arctanBoundaryMoment i d F := by
  rintro ⟨r, c, hr, hc, hfloor⟩
  obtain ⟨d, hd, hdr, _, hdc⟩ :=
    criticalState_arctan_boundary_cost_arbitrarily_small hW ht hF i (lt_min hr hc)
  exact (not_lt_of_ge (hfloor d hd (lt_of_lt_of_le hdr (min_le_left r c))))
    (lt_of_lt_of_le hdc (min_le_right r c))

/-- The unconditional alternative retains positive moments and both vanishing boundary costs. -/
theorem riemannHypothesis_or_criticalState_vanishing_bregman_boundary_cost :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ i : Fin 3,
        (∀ d : ℝ, 0 < d → 0 < arctanBoundaryMoment i d F) ∧
        Tendsto (fun d : ℝ => archLevyAntideriv d * arctanBoundaryMoment i d F)
          (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun d : ℝ => Real.log (2 / d) * arctanBoundaryMoment i d F)
          (𝓝[>] 0) (𝓝 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · refine Or.inr ⟨W₀, F, hW, ht, hF, fun i => ?_⟩
    exact ⟨fun d hd => criticalState_arctanBoundaryMoment_pos hW ht hF i hd,
      arctanBoundaryMoment_exact_cost_tendsto_zero (criticalHalfLineEnergyDomain_of_groundState hF) i,
      arctanBoundaryMoment_logarithmic_cost_tendsto_zero (criticalHalfLineEnergyDomain_of_groundState hF) i⟩

#print axioms terminal_square_logarithmic_cost_tendsto_zero
#print axioms arctan_mixed_terminal_logarithmic_cost_tendsto_zero
#print axioms criticalState_arctan_boundary_cost_arbitrarily_small
#print axioms criticalState_no_uniform_positive_arctan_boundary_floor
#print axioms riemannHypothesis_or_criticalState_vanishing_bregman_boundary_cost

end GaloisForLFunctions.ExclusionOfTheCriticalState
end
