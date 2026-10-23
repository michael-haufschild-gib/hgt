import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# Uniform constants discharged in `GaloisForLFunctions.HTGeometry`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/

open Complex Filter MeasureTheory Metric Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `abs_deriv_smoothTransition_comp_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem abs_deriv_smoothTransition_comp_le_uniform :
    ∃ (Λ : ℝ), ∀ (A : ℝ → ℝ) (A' : ℝ) (M : ℝ) (L : ℝ), HasDerivAt A A' L → |A'| ≤ M →
      |deriv (fun t => Real.smoothTransition (A t)) L| ≤ Λ * M := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro A A' M L hA hM
  apply abs_deriv_smoothTransition_comp_le <;> assumption

/-- `norm_mellin_shortBump_le_decay` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_deriv_shortBumpProfile`. -/
theorem norm_mellin_shortBump_le_decay_uniform :
    ∃ (M : ℝ), ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ (s : ℂ), s.re ≤ 2 → s ≠ 0 → s ≠ -1 →
      ‖mellin (fun u => (shortBump δ u : ℂ)) s‖ ≤ 8 * M / (δ * (‖s‖ * ‖s + 1‖)) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_deriv_shortBumpProfile
  refine ⟨M, ?_⟩
  intro δ hδ hδ1 s hs hs0 hs1
  apply norm_mellin_shortBump_le_decay <;> assumption

/-- `norm_mellin_shortBump_le_lorentz` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_deriv_shortBumpProfile`. -/
theorem norm_mellin_shortBump_le_lorentz_uniform :
    ∃ (M : ℝ), ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ (σ : ℝ) (t : ℝ), 0 < σ → σ ≤ 2 →
      ‖mellin (fun u => (shortBump δ u : ℂ)) (σ + t * I)‖ ≤ (4 + 16 * M) * δ / (1 + δ ^ 2 * t ^ 2) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_deriv_shortBumpProfile
  refine ⟨M, ?_⟩
  intro δ hδ hδ1 σ t hσ hσ2
  apply norm_mellin_shortBump_le_lorentz <;> assumption

/-- `norm_shiftedIntegrand_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_deriv_shortBumpProfile`. -/
theorem norm_shiftedIntegrand_le_uniform :
    ∃ (M : ℝ), ∀ (E : ℂ → ℂ) (C : ℝ), (∀ σ t : ℝ, 1 / 2 < σ → σ ≤ 2 → ‖E (σ + t * I)‖ ≤ C * Real.log (|t| + 3) / (σ - 1 / 2)) → ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ (x : ℝ), 0 < x → ∀ (σ : ℝ), 1 / 2 < σ → σ ≤ 2 → ∀ (y : ℝ),
      ‖(x : ℂ) ^ ((σ : ℂ) + y * I) * mellin (fun u => (shortBump δ u : ℂ)) (σ + y * I) * E (σ + y * I)‖ ≤ x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) * (C * Real.log (|y| + 3) / (σ - 1 / 2)) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_deriv_shortBumpProfile
  refine ⟨M, ?_⟩
  intro E C hE δ hδ hδ1 x hx σ hσ hσ2 y
  apply norm_shiftedIntegrand_le <;> assumption

end GaloisForLFunctions.HTGeometry
