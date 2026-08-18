import GaloisForLFunctions.HTGeometry.SplitFibreChartData

/-!
# A global section of the complex-point covering

The parameter line is simply connected and locally path connected, so the covering of complex
points of a finite free `ℂ[X]`-algebra with split fibres admits a global continuous section.  This
is step (b) of the general simple connectedness of the affine line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **A global continuous section.**  The parameter line is simply connected, so the covering of
complex points admits a section. -/
theorem exists_continuous_section_of_splitFibres [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n) :
    ∃ σ : ℂ → AlgSpec B, Continuous σ ∧ ∀ s : ℂ, AlgSpec.proj B (σ s) = s := by
  classical
  obtain ⟨χ, hproj, -, -⟩ := h 0
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ :=
    (isCoveringMap_proj_of_splitFibres hn e h).existsUnique_continuousMap_lifts
      (ContinuousMap.id ℂ) (0 : ℂ) (χ ⟨0, hn⟩) (hproj _)
  exact ⟨F, F.continuous, fun s => congrFun hFlift s⟩

end

end GaloisForLFunctions.HTGeometry
