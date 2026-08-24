import GaloisForLFunctions.HTGeometry.TranscendentalProfileCountableFamily
import GaloisForLFunctions.HTGeometry.PencilLineRestriction

/-!
# Finite-restriction Hasse principle for joint hypertranscendence

Every algebraic differential relation uses only finitely many members of a family.  Consequently
joint hypertranscendence is exactly a finite-local property: it holds globally if and only if it
holds on every nonempty finite restriction.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A family is jointly hypertranscendental exactly when all its nonempty finite subfamilies are
jointly hypertranscendental. -/
theorem jointlyHypertranscendental_finite_restrictions_hasse_iff
    {ι : Type} [DecidableEq ι] [Nonempty ι] (f : ι → ℂ → ℂ) :
    JointlyHypertranscendental f ↔
      ∀ S : Finset ι, S.Nonempty → JointlyHypertranscendental (fun i : S => f i) := by
  constructor
  · intro hf S _
    exact _root_.GaloisForLFunctions.HTGeometry.jointlyHypertranscendental_comp_injective f
      (fun i : S => (i : ι)) Subtype.val_injective hf
  · exact jointlyHypertranscendental_of_finite_restrictions f

end


end GaloisForLFunctions
