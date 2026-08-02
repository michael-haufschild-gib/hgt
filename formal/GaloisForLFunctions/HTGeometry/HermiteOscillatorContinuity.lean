import GaloisForLFunctions.HTGeometry.HermiteHamiltonian

/-!
# The oscillator seminorms are continuous on the Schwartz space

Each oscillator seminorm is the `L²` norm composed with a continuous linear map of Schwartz
spaces, so it is continuous.  A continuous seminorm on a space presented by a family of seminorms
is bounded by a constant times a finite supremum of that family, so every oscillator seminorm is
bounded by finitely many Schwartz seminorms.

This is the easy half of the comparison between the two presentations of the Schwartz topology.

* `oscillatorSeminormFamily` : the oscillator seminorms as a seminorm family.
* `oscillatorSeminorm_continuous` : **each of them is continuous.**
* `oscillatorSeminorm_le_schwartzSeminorm` : **each is bounded by finitely many Schwartz
  seminorms.**
-/

open scoped Real SchwartzMap ENNReal NNReal
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- The oscillator seminorms, as a seminorm family indexed by the power of the Hamiltonian. -/
def oscillatorSeminormFamily : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ := oscillatorSeminorm

theorem oscillatorSeminormFamily_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    oscillatorSeminormFamily k f = ‖((hamiltonianCLM^[k]) f).toLp 2 volume‖ :=
  oscillatorSeminorm_apply k f

/-- **The oscillator seminorms are continuous**: each is the `L²` norm of the image of a
continuous linear map. -/
theorem oscillatorSeminorm_continuous (k : ℕ) : Continuous (oscillatorSeminorm k) := by
  have hfun : ⇑(oscillatorSeminorm k)
      = fun f : 𝓢(ℝ, ℂ) =>
        ‖((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).comp (hamiltonianPowCLM k)) f‖ := by
    funext f
    rw [oscillatorSeminorm_apply]
    show _ = ‖SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (hamiltonianPowCLM k f)‖
    rw [SchwartzMap.toLpCLM_apply, hamiltonianPowCLM_apply]
  rw [hfun]
  exact (ContinuousLinearMap.continuous _).norm

/-- **Every oscillator seminorm is bounded by finitely many Schwartz seminorms.**  This is one of
the two comparisons that identify the oscillator presentation of the Schwartz topology with the
usual one. -/
theorem oscillatorSeminorm_le_schwartzSeminorm (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), C ≠ 0 ∧
      oscillatorSeminorm k ≤ C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
  Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) _ (oscillatorSeminorm_continuous k)

end GaloisForLFunctions

end
