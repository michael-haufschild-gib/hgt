import GaloisForLFunctions.HTGeometry.ScalarProperDifferentialSubfield
import GaloisForLFunctions.HTGeometry.ScalarJetClockCharacter

/-!
# The proper differential subfield is clock-invariant

The concrete proper differential subfield `C⟨y'⟩ = differentialAdjoin C {y'}` (with `y' = X_{(),1}`) is
invariant under the jet-scaling clock.  Indeed the clock sends each differential jet generator
`y^(n)` to the scalar multiple `λ^n·y^(n)` (`clockDilationFieldEquiv_differentialJet`), which stays in
the subfield since the subfield contains its generators and all `C`-scalars.  Hence for every nonzero
`λ` the clock `ρ_λ` maps `C⟨y'⟩` into itself.

Together with the properness `differentialAdjoin_differentialJet_one_ne_top`, this exhibits `C⟨y'⟩` as
a concrete *proper clock-invariant differential subfield* strictly between `C` and `C⟨y⟩`, with a
charged (weight-`1`) clock-eigenvector generator — a non-vacuous witness for the central object of the
clock-character law.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- **Clock-invariance.**  For every nonzero `λ`, the jet-scaling clock maps the proper differential
subfield `C⟨y'⟩` into itself. -/
theorem clockDilationFieldEquiv_mem_differentialAdjoin_differentialJet_one
    (lam : C) (hlam : lam ≠ 0) {z : ScalarDifferentialField C}
    (hz : z ∈ differentialAdjoin C {differentialJet 1 (scalarDifferentialGenerator C)}) :
    clockDilationFieldEquiv lam hlam z
      ∈ differentialAdjoin C {differentialJet 1 (scalarDifferentialGenerator C)} := by
  have hle : differentialAdjoin C {differentialJet 1 (scalarDifferentialGenerator C)}
      ≤ (differentialAdjoin C {differentialJet 1 (scalarDifferentialGenerator C)}).comap
          (clockDilationFieldEquiv lam hlam).toAlgHom := by
    unfold differentialAdjoin
    rw [IntermediateField.adjoin_le_iff]
    intro s hs
    show clockDilationFieldEquiv lam hlam s
      ∈ IntermediateField.adjoin C
          (differentialJetSet {differentialJet 1 (scalarDifferentialGenerator C)})
    simp only [differentialJetSet, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs
    obtain ⟨w, rfl, m, hms⟩ := hs
    rw [← hms, differentialJet_differentialJet_one, clockDilationFieldEquiv_differentialJet]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    rw [← differentialJet_differentialJet_one]
    exact IntermediateField.subset_adjoin _ _
      ⟨differentialJet 1 (scalarDifferentialGenerator C), rfl, m, rfl⟩
  exact hle hz

end

end GaloisForLFunctions
