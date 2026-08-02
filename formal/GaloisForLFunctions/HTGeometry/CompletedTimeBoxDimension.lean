import GaloisForLFunctions.HTGeometry.PhaseTorusEmbeddingDimension
import GaloisForLFunctions.HTGeometry.DiagonalScalingBiLipschitz
import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus

/-!
# The completed time of a frequency packet has the box dimension of its rank

The completed time of a finite frequency packet is the range of an injective integer homomorphism
from a presenting torus of dimension the rational rank of the packet.  Embedding it coordinatewise
in the plane is bi-Lipschitz, and a bi-Lipschitz image of a phase torus has the box dimension of
that torus.  Hence the embedded completed time has Minkowski dimension exactly the rational rank of
the packet.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Completed-orbit dimension.**  The embedded completed time of a finite frequency packet has
box dimension the rational rank of the packet. -/
theorem exists_hasBoxDim_embedded_completedTime (omega : d → ℝ) :
    ∃ k : ℕ, (k : ℝ) = (Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) : ℝ) ∧
      HasBoxDim (torusEmbed '' closure (Set.range (finiteClockPhasePoint omega))) (k : ℝ) := by
  obtain ⟨k, gamma, M, A, hindep, -, -, hM, hA, hrank⟩ := exists_frequency_integer_basis omega
  have hclosure : closure (Set.range (finiteClockPhasePoint omega))
      = Set.range (torusIntegerHom M) :=
    closure_range_finiteClockPhasePoint_eq omega gamma M hindep hM
  have hinj : Function.Injective (torusIntegerHom M) := torusIntegerHom_injective M A hA
  refine ⟨k, by exact_mod_cast hrank, ?_⟩
  rw [hclosure, ← Set.range_comp]
  have hdim := hasBoxDim_range_torusEmbed_comp (k := Fin k) M hinj
  rwa [Fintype.card_fin] at hdim

/-- **Completed-orbit dimension for a rescaled readout.**  Reading the completed time through a
fixed nonzero diagonal rescaling — which is what a weighted reporter family does to the phase
tuple — does not change its Minkowski dimension. -/
theorem exists_hasBoxDim_scaled_completedTime (omega : d → ℝ) {c : d → ℂ} (hc : ∀ i, c i ≠ 0) :
    ∃ k : ℕ, (k : ℝ) = (Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) : ℝ) ∧
      HasBoxDim ((diagScale c ∘ torusEmbed) '' closure (Set.range (finiteClockPhasePoint omega)))
        (k : ℝ) := by
  obtain ⟨k, gamma, M, A, hindep, -, -, hM, hA, hrank⟩ := exists_frequency_integer_basis omega
  have hclosure : closure (Set.range (finiteClockPhasePoint omega))
      = Set.range (torusIntegerHom M) :=
    closure_range_finiteClockPhasePoint_eq omega gamma M hindep hM
  have hinj : Function.Injective (torusIntegerHom M) := torusIntegerHom_injective M A hA
  refine ⟨k, by exact_mod_cast hrank, ?_⟩
  rw [hclosure, ← Set.range_comp]
  have hdim := hasBoxDim_range_diagScale_comp (k := Fin k) M hinj hc
  rw [Fintype.card_fin] at hdim
  have hassoc : diagScale c ∘ torusEmbed ∘ torusIntegerHom M
      = (diagScale c ∘ torusEmbed) ∘ torusIntegerHom M := rfl
  rwa [hassoc] at hdim

end

end GaloisForLFunctions.HTGeometry
