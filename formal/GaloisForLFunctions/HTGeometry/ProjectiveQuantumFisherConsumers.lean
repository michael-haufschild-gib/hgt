import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue
import GaloisForLFunctions.HTGeometry.ThermalKrylovDeterminant
import GaloisForLFunctions.HTGeometry.TwoChannelRobertson

/-!
# Direct consumers of projective quantum-Fisher values

This file connects the projective Gram value to two existing general HTGeometry theorem surfaces:

* the two-generator Robertson inequality;
* the first nontrivial thermal Krylov/Hankel determinant.

Both are exact value identifications.  No positivity hypothesis, dynamics, or zeta specialization
is added.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The right side of the three-vector Robertson inequality is the vacuum norm times the
projective quantum tangent energy of the two generator channels. -/
theorem twoChannelRobertsonGram_projectiveQuantumTangent
    (f g h : E) :
    inner ℝ f g ^ 2 * inner ℝ h h -
          2 * inner ℝ f g * inner ℝ f h * inner ℝ g h +
          inner ℝ f h ^ 2 * inner ℝ g g ≤
      ‖f‖ ^ 2 * projectiveGramTangentEnergy g h := by
  calc
    inner ℝ f g ^ 2 * inner ℝ h h -
          2 * inner ℝ f g * inner ℝ f h * inner ℝ g h +
          inner ℝ f h ^ 2 * inner ℝ g g ≤
        inner ℝ f f *
          (inner ℝ g g * inner ℝ h h - inner ℝ g h ^ 2) :=
      twoChannelRobertsonGram f g h
    _ = ‖f‖ ^ 2 * projectiveGramTangentEnergy g h := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      simp [projectiveGramTangentEnergy, Real.norm_eq_abs, sq_abs]

/-- The quantum-Fisher projective value of the first two finite thermal Krylov vectors is exactly
the first nontrivial thermal Hankel determinant. -/
theorem thermalKrylovProjectiveTangentEnergy_eq_firstDeterminant
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) :
    projectiveGramTangentEnergy
        (thermalKrylovVector intensity energy 0)
        (thermalKrylovVector intensity energy 1) =
      thermalEvenGapMoment intensity energy 0 *
          thermalEvenGapMoment intensity energy 2 -
        thermalEvenGapMoment intensity energy 1 ^ 2 := by
  exact projectiveGramTangentEnergy_eq_firstKrylovDeterminant
    (thermalEvenGapMoment intensity energy)
    (thermalKrylovVector intensity energy)
    (inner_thermalKrylovVector intensity energy hintensity)

end

end HTGeometry
