import GaloisForLFunctions.HTGeometry.GammaHypertranscendental

/-!
# The zero relation realizes the gamma power-relation interface

A gamma power relation is a cleared polynomial identity in the gamma powers.  The zero family of
coefficients is one, so the hypertranscendence no-go is a statement about nonzero relations rather
than an empty hypothesis.
-/

namespace GaloisForLFunctions

theorem gammaPowerRel_zero (m D : ℕ) :
    GammaPowerRel m D (fun _ => 0) := by
  refine ⟨1, one_ne_zero, fun _ => 0, ?_, ?_⟩
  · intro k _
    simp
  · intro z _
    simp

end GaloisForLFunctions
