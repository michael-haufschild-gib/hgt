import GaloisForLFunctions.BiScaleUncertainty.Spectral.EvenGridQuantumWalk
import GaloisForLFunctions.HTGeometry.FiniteClockOrbitAsymmetry

/-!
# Leakage-free quantum returns on arithmetic tent grids

The compressed four-step return is an actual state return. Unitarity
preserves the input norm, while orthogonality splits the output norm into
its retained and escaped components. Exact recovery of the retained
component forces the escaped component to vanish.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open scoped RealInnerProductSpace

/-- Both grid reflections preserve norm, hence their product is unitary. -/
theorem evenGridWalk_adjoint_mul_self (n : ℕ) :
    (evenGridWalk n).adjoint * evenGridWalk n = 1 := by
  have hi (d : ℕ) : IsIdempotentElem (coprimeProjector d) := by
    apply ContinuousLinearMap.ext
    intro v
    exact coprimeProjection_idempotent d v
  exact HTGeometry.twoProjectionQuantumWalk_adjoint_mul_self
    (coprimeProjector 0) (coprimeProjector (n+1)) (hi 0) (hi (n+1))
    (coprimeProjector_adjoint 0) (coprimeProjector_adjoint (n+1))

/-- Every fourth step returns each grid state exactly, with zero leakage into its complement. -/
theorem evenGridWalk_four_mul_apply (n k : ℕ) (v : Velocity) :
    (evenGridWalk n ^ (4*k)) (coprimeProjector (n+1) v) = coprimeProjector (n+1) v := by
  let x := coprimeProjector (n+1) v
  let y := (evenGridWalk n ^ (4*k)) x
  have hproj : coprimeProjection (n+1) y = x := by
    exact congrArg (fun A : Velocity →L[ℝ] Velocity => A v)
      (evenGridWalk_four_mul_compression n k)
  have ho := inner_extension_projection_residual (n+1) (coprimeCoefficients (n+1) y) y
  rw [← coprimeProjection_eq_extension, hproj, inner_sub_right,
    real_inner_self_eq_norm_sq] at ho
  have hn : ‖y‖ ^ 2 = ‖x‖ ^ 2 :=
    HTGeometry.norm_pow_apply_sq_eq_of_adjoint_mul_self
      (evenGridWalk n) (4*k) (evenGridWalk_adjoint_mul_self n) x
  have hz : ‖y - x‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_comm]
    linarith only [ho, hn]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_adjoint_mul_self
#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_four_mul_apply
