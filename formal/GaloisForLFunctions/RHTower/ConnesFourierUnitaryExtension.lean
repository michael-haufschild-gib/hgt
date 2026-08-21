import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Unitary extension to the Hilbert completion

§VII Lemma 1(b) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The Fourier transform is defined on the Bruhat–Schwartz space, which is only a dense subspace of
the adele class Hilbert space.  Once it is known to be isometric for the orbit form of §VII (11),
the passage to `L²(X_S)` is the standard extension of a densely defined isometry: an isometric
linear equivalence of a pre-Hilbert space extends uniquely to a unitary of its completion, and
the extension agrees with the original map on the dense subspace.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The unitary extension.**  An isometric linear automorphism of a pre-Hilbert space extends
to a unitary of its Hilbert completion. -/
def connesCompletionUnitary (F : E ≃ₗᵢ[ℂ] E) :
    UniformSpace.Completion E ≃ₗᵢ[ℂ] UniformSpace.Completion E :=
  F.toLinearEquiv.extendOfIsometry
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun t => by
      calc ‖(UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
              (F.toLinearEquiv t)‖
          = ‖F t‖ := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).norm_map _
        _ = ‖t‖ := F.norm_map t
        _ = ‖(UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap t‖ :=
            ((UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).norm_map t).symm)

@[simp] theorem connesCompletionUnitary_coe (F : E ≃ₗᵢ[ℂ] E) (t : E) :
    connesCompletionUnitary F (t : UniformSpace.Completion E)
      = ((F t : E) : UniformSpace.Completion E) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ t

end

end GaloisForLFunctions.RHTower
