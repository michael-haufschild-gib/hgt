import GaloisForLFunctions.HTGeometry.ClockProbePointwiseVacuity

/-!
# Audit of the two probe conditions

The pointwise condition `LocalProbesOn` was shown to be empty. The condition the determination
theorems actually rest on, `NoCommonZero`, is audited here and is *not* empty: it can fail, and when
it fails determination fails with it.

The witness is a degenerate wave operator whose only solution is the zero function. Then every
potential has the same solution space, so the solution space cannot pin the potential — and indeed
two visibly different potentials share it.

Together with the oscillatory and Riccati cases, where the condition holds, this shows
`NoCommonZero` is two-sided: satisfiable and falsifiable, hence a genuine hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A degenerate wave operator, used to audit the conditions. -/
def identityWave : (ℝ → ℝ) → (ℝ → ℝ) := id

theorem solvesPotentialWave_identityWave_iff (potential u : ℝ → ℝ) :
    SolvesPotentialWave identityWave potential u ↔ ∀ x, (1 + potential x) * u x = 0 := by
  constructor
  · intro h x
    have := h x
    simp only [identityWave, id] at this
    linarith [this]
  · intro h x
    have := h x
    simp only [identityWave, id]
    linarith [this]

/-- With no root of `1 + V`, the degenerate operator has only the zero solution. -/
theorem solutionSet_identityWave_eq_singleton {potential : ℝ → ℝ}
    (hV : ∀ x, 1 + potential x ≠ 0) :
    solutionSet identityWave potential = {0} := by
  ext u
  rw [mem_solutionSet_iff, solvesPotentialWave_identityWave_iff]
  constructor
  · intro h
    funext x
    rcases mul_eq_zero.mp (h x) with hz | hz
    · exact absurd hz (hV x)
    · simpa using hz
  · intro h x
    rw [h]
    simp

/-- **`NoCommonZero` can fail.** -/
theorem not_noCommonZero_identityWave {potential : ℝ → ℝ}
    (hV : ∀ x, 1 + potential x ≠ 0) :
    ¬ NoCommonZero identityWave potential := by
  intro hno
  obtain ⟨u, hu, hux⟩ := hno 0
  rw [solutionSet_identityWave_eq_singleton hV] at hu
  simp only [Set.mem_singleton_iff] at hu
  rw [hu] at hux
  exact hux rfl

/-- **When it fails, the solution space does not determine the potential.** Two visibly different
potentials share the same solution space. -/
theorem exists_ne_potential_with_eq_solutionSet :
    ∃ potential₁ potential₂ : ℝ → ℝ,
      potential₁ ≠ potential₂ ∧
        solutionSet identityWave potential₁ = solutionSet identityWave potential₂ := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
  · intro hEq
    have := congrFun hEq 0
    norm_num at this
  · rw [solutionSet_identityWave_eq_singleton (fun x => by norm_num),
      solutionSet_identityWave_eq_singleton (fun x => by norm_num)]

/-- **`NoCommonZero` is two-sided.** It holds in the oscillatory case and fails in the degenerate
one, so it is a genuine hypothesis and not a formality. -/
theorem noCommonZero_satisfiable_and_falsifiable :
    (∃ k : ℝ, NoCommonZero secondDeriv (fun _ => k ^ (2 : ℕ))) ∧
      (∃ potential : ℝ → ℝ, ¬ NoCommonZero identityWave potential) :=
  ⟨⟨1, noCommonZero_oscillatory 1⟩,
    ⟨fun _ => 0, not_noCommonZero_identityWave (fun x => by norm_num)⟩⟩

end GaloisForLFunctions.HTGeometry
