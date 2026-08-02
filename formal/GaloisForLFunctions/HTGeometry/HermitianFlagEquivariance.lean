import GaloisForLFunctions.HTGeometry.HermitianDegenerationFlag

/-!
# The degeneration flag is equivariant

Conjugating a direction by an observer symmetry moves its degeneration flag by that symmetry, and
scalars act trivially.  So the assignment of a flag to a direction intertwines the conjugation
action on directions with the action of the projective observer group on the building.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Conjugation moves eigenspaces by the conjugating map.** -/
theorem eigenspace_conj (g : E ≃ₗ[ℂ] E) (T : E →ₗ[ℂ] E) (μ : ℂ) :
    Module.End.eigenspace ((g : E →ₗ[ℂ] E) ∘ₗ T ∘ₗ (g.symm : E →ₗ[ℂ] E)) μ
      = (Module.End.eigenspace T μ).map (g : E →ₗ[ℂ] E) := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, LinearMap.comp_apply, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    have hg : g (T (g.symm x)) = μ • x := h
    have h2 := congrArg (fun y => g.symm y) hg
    simpa [map_smul] using h2
  · rintro ⟨y, hy, rfl⟩
    show g (T (g.symm (g y))) = μ • g y
    rw [g.symm_apply_apply, hy, map_smul]

/-- **The degeneration flag is equivariant**: conjugating a direction moves its flag by the
conjugating symmetry. -/
theorem eigenSum_conj (g : E ≃ₗ[ℂ] E) (T : E →ₗ[ℂ] E) (c : ℝ) :
    eigenSum ((g : E →ₗ[ℂ] E) ∘ₗ T ∘ₗ (g.symm : E →ₗ[ℂ] E)) c
      = (eigenSum T c).map (g : E →ₗ[ℂ] E) := by
  rw [eigenSum, eigenSum, Submodule.map_iSup]
  refine iSup_congr fun μ => ?_
  rw [Submodule.map_iSup]
  exact iSup_congr fun _ => eigenspace_conj g T (μ : ℂ)

/-- **Scalars act trivially on directions.**  Conjugating by a nonzero multiple of a symmetry is
conjugating by the symmetry, so the flag is acted on by the *projective* observer group. -/
theorem conj_smul_eq (g : E ≃ₗ[ℂ] E) {a : ℂ} (ha : a ≠ 0) (T : E →ₗ[ℂ] E) :
    ((a • (g : E →ₗ[ℂ] E)) ∘ₗ T ∘ₗ (a⁻¹ • (g.symm : E →ₗ[ℂ] E)))
      = (g : E →ₗ[ℂ] E) ∘ₗ T ∘ₗ (g.symm : E →ₗ[ℂ] E) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
  rw [inv_mul_cancel₀ ha, one_smul]

end GaloisForLFunctions.HTGeometry
