import GaloisForLFunctions.HeckeKreinToeplitz.Index.ClosedFiniteNegativeSubspaces
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeCoefficients

/-!
# Radicals of subspaces with finitely many negative directions

The radical lies in the finite remainder of the positive orthogonal
splitting. Form-isometries preserving the subspace in both directions
preserve this radical.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Vectors of `W` orthogonal to every vector of `W`. -/
def restrictedRadical (W : Submodule ℂ (H × E)) : Submodule ℂ (H × E) :=
  W ⊓ ⨅ w : W, (pairingLinear (w : H × E)).ker

theorem mem_restrictedRadical (W : Submodule ℂ (H × E)) (v : H × E) :
    v ∈ restrictedRadical W ↔ v ∈ W ∧ ∀ w ∈ W, pairing w v = 0 := by
  change (v ∈ W ∧ v ∈ ⨅ w : W, (pairingLinear (w : H × E)).ker) ↔ _
  rw [Submodule.mem_iInf]
  exact and_congr_right fun _ => ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w w.property⟩

theorem restrictedRadical_le_finitePart (W : Submodule ℂ (H × E)) :
    restrictedRadical W ≤ finitePart W := by
  intro v hv
  obtain ⟨hvW, ho⟩ := (mem_restrictedRadical W v).mp hv
  refine ⟨hvW, (Submodule.mem_orthogonal (positiveKernel W) v.1).mpr ?_⟩
  intro u hu
  have h := ho (u, 0) hu
  simpa only [pairing, inner_zero_left, sub_zero] using h

instance finiteDimensional_restrictedRadical [FiniteDimensional ℂ E]
    (W : Submodule ℂ (H × E)) : FiniteDimensional ℂ (restrictedRadical W) :=
  Module.Finite.of_injective (Submodule.inclusion (restrictedRadical_le_finitePart W))
    (Submodule.inclusion_injective _)

theorem restrictedRadical_square (W : Submodule ℂ (H × E))
    {v : H × E} (hv : v ∈ restrictedRadical W) : pairing v v = 0 := by
  obtain ⟨hvW, ho⟩ := (mem_restrictedRadical W v).mp hv
  exact ho v hvW

/-- Two-sided invariance of `W` makes its restricted radical invariant. -/
theorem map_mem_restrictedRadical (W : Submodule ℂ (H × E))
    (T : (H × E) ≃L[ℂ] (H × E)) (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (hf : ∀ v ∈ W, T v ∈ W) (hb : ∀ v ∈ W, T.symm v ∈ W)
    {v : H × E} (hv : v ∈ restrictedRadical W) : T v ∈ restrictedRadical W := by
  obtain ⟨hvW, ho⟩ := (mem_restrictedRadical W v).mp hv
  refine (mem_restrictedRadical W (T v)).mpr ⟨hf v hvW, ?_⟩
  intro w hw
  have h := hT (T.symm w) v
  rw [T.apply_symm_apply] at h
  rw [h]
  exact ho (T.symm w) (hb w hw)

#print axioms restrictedRadical_le_finitePart
#print axioms map_mem_restrictedRadical

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
