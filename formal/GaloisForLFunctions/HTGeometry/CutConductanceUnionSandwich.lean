import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-!
# The contiguous-cut conductance sandwich

The conductance of a family of interaction blocks is the least block size.  A single block below a
third of a threshold already forces the conductance below it, and a conductance below a threshold
forces some block below it, so the law of the conductance is sandwiched between one block law at
the reduced threshold and the union of all block laws at the threshold.  No independence between
blocks is used.
-/

open MeasureTheory Matrix

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Conductance

variable {Θ : Type*} {E : Type*} [Fintype E] [Nonempty E]

/-- The contiguous-cut conductance: the least block size. -/
def cutConductance (nrm : E → Θ → ℝ) (θ : Θ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun e => nrm e θ

theorem cutConductance_le (nrm : E → Θ → ℝ) (θ : Θ) (e : E) :
    cutConductance nrm θ ≤ nrm e θ :=
  Finset.inf'_le _ (Finset.mem_univ e)

theorem exists_le_of_cutConductance_le {nrm : E → Θ → ℝ} {θ : Θ} {x : ℝ}
    (h : cutConductance nrm θ ≤ x) : ∃ e, nrm e θ ≤ x := by
  obtain ⟨e, -, he⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := E)) fun e => nrm e θ
  exact ⟨e, he ▸ h⟩

/-- A single small block forces a small conductance. -/
theorem subset_setOf_cutConductance_le {nrm rho : E → Θ → ℝ}
    (hup : ∀ e θ, nrm e θ ≤ 3 * rho e θ) (e₀ : E) (x : ℝ) :
    {θ | rho e₀ θ ≤ x / 3} ⊆ {θ | cutConductance nrm θ ≤ x} := by
  intro θ hθ
  have hθ' : rho e₀ θ ≤ x / 3 := hθ
  have h2 : 3 * rho e₀ θ ≤ x := by linarith
  exact le_trans (cutConductance_le nrm θ e₀) (le_trans (hup e₀ θ) h2)

/-- A small conductance forces some small block. -/
theorem setOf_cutConductance_le_subset {nrm rho : E → Θ → ℝ}
    (hlow : ∀ e θ, rho e θ ≤ nrm e θ) (x : ℝ) :
    {θ | cutConductance nrm θ ≤ x} ⊆ ⋃ e : E, {θ | rho e θ ≤ x} := by
  intro θ hθ
  obtain ⟨e, he⟩ := exists_le_of_cutConductance_le hθ
  exact Set.mem_iUnion.mpr ⟨e, le_trans (hlow e θ) he⟩

variable [MeasurableSpace Θ]

/-- **The contiguous-cut conductance sandwich.**  No independence between blocks is used. -/
theorem measure_cutConductance_sandwich (μ : Measure Θ) {nrm rho : E → Θ → ℝ}
    (hlow : ∀ e θ, rho e θ ≤ nrm e θ) (hup : ∀ e θ, nrm e θ ≤ 3 * rho e θ)
    (e₀ : E) (x : ℝ) :
    μ {θ | rho e₀ θ ≤ x / 3} ≤ μ {θ | cutConductance nrm θ ≤ x} ∧
      μ {θ | cutConductance nrm θ ≤ x} ≤ ∑ e : E, μ {θ | rho e θ ≤ x} := by
  refine ⟨measure_mono (subset_setOf_cutConductance_le hup e₀ x), ?_⟩
  refine le_trans (measure_mono (setOf_cutConductance_le_subset hlow x)) ?_
  refine le_trans (measure_iUnion_le _) ?_
  exact le_of_eq (tsum_fintype _)

end Conductance

section PauliBlocks

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {Θ : Type*} {E : Type*} [Fintype E] [Nonempty E]

/-- The Euclidean coefficient length of one interaction block. -/
def blockRadius (J : E → Θ → (σ → Option (Fin 3)) → ℂ) (e : E) (θ : Θ) : ℝ :=
  Real.sqrt (∑ P, ‖J e θ P‖ ^ 2)

/-- The interaction block of one edge. -/
def blockMatrix (J : E → Θ → (σ → Option (Fin 3)) → ℂ) (e : E) (θ : Θ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  ∑ P, J e θ P • finitePauliMatrix P

theorem blockRadius_le_norm_blockMatrix (J : E → Θ → (σ → Option (Fin 3)) → ℂ) (e : E) (θ : Θ) :
    blockRadius J e θ ≤ ‖blockMatrix J e θ‖ :=
  le_opNorm_pauliCombination (J e θ)

theorem norm_blockMatrix_le (J : E → Θ → (σ → Option (Fin 3)) → ℂ)
    (S : Finset (σ → Option (Fin 3))) (hcard : S.card = 9)
    (hJ : ∀ e θ, ∀ P ∉ S, J e θ P = 0) (e : E) (θ : Θ) :
    ‖blockMatrix J e θ‖ ≤ 3 * blockRadius J e θ := by
  have h := opNorm_pauliCombination_le_sqrt_card S (J e θ) (hJ e θ)
  rw [hcard] at h
  have h3 : Real.sqrt ((9 : ℕ) : ℝ) = 3 := by
    rw [show ((9 : ℕ) : ℝ) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h3] at h
  exact h

variable [MeasurableSpace Θ]

/-- **The contiguous-cut conductance sandwich for two-site Pauli blocks.**  With nine Pauli
orientations on each edge, the conductance law is sandwiched between one edge law at a third of the
threshold and the sum of all edge laws at the threshold. -/
theorem measure_cutConductance_pauliBlocks_sandwich (μ : Measure Θ)
    (J : E → Θ → (σ → Option (Fin 3)) → ℂ)
    (S : Finset (σ → Option (Fin 3))) (hcard : S.card = 9)
    (hJ : ∀ e θ, ∀ P ∉ S, J e θ P = 0) (e₀ : E) (x : ℝ) :
    μ {θ | blockRadius J e₀ θ ≤ x / 3} ≤
        μ {θ | cutConductance (fun e θ => ‖blockMatrix J e θ‖) θ ≤ x} ∧
      μ {θ | cutConductance (fun e θ => ‖blockMatrix J e θ‖) θ ≤ x} ≤
        ∑ e : E, μ {θ | blockRadius J e θ ≤ x} :=
  measure_cutConductance_sandwich μ (blockRadius_le_norm_blockMatrix J)
    (norm_blockMatrix_le J S hcard hJ) e₀ x

end PauliBlocks

end GaloisForLFunctions.HTGeometry
