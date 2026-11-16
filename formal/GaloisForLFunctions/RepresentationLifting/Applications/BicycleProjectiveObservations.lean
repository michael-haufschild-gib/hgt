import GaloisForLFunctions.RepresentationLifting.Trace.ProjectiveTraceDuality
import GaloisForLFunctions.RepresentationLifting.Applications.BicycleTrace

/-!
# Trace-zero observations recover bicycle coefficients away from the origin

The scalar trace of every binary bicycle convolution on an even torus is zero.
Nevertheless trace-zero matrix tests recover all coefficients except the
delta mass at the origin, which acts as the scalar identity. Pivot normalization
removes precisely that coefficient and retains the other boundary data.
-/

namespace GaloisForLFunctions.RepresentationLifting

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]

omit [Fintype G] in
/-- A bicycle convolution is scalar exactly when supported at the origin. -/
theorem bicycleConvolutionMatrix_eq_scalar_iff (a : G → ZMod 2) (c : ZMod 2) :
    bicycleConvolutionMatrix a = c • (1 : Matrix G G (ZMod 2)) ↔
      ∀ x, a x = if x = 0 then c else 0 := by
  constructor
  · intro h x
    simpa [bicycleConvolutionMatrix, Matrix.one_apply] using
      congrArg (fun M => M x 0) h
  · intro h
    ext x y
    simp [bicycleConvolutionMatrix, h, Matrix.one_apply, sub_eq_zero]

/-- Trace-zero tests are blind exactly to the origin coefficient. -/
theorem bicycle_traceZero_annihilator_iff (a : G → ZMod 2) :
    (∀ B : traceZeroMatrices (ZMod 2) G,
      (bicycleConvolutionMatrix a * B.val).trace = 0) ↔
      ∀ x, x ≠ 0 → a x = 0 := by
  rw [traceZero_annihilator_iff (0 : G)]
  constructor
  · rintro ⟨c, hc⟩ x hx
    simpa only [if_neg hx] using (bicycleConvolutionMatrix_eq_scalar_iff a c).mp hc x
  · intro h
    refine ⟨a 0, (bicycleConvolutionMatrix_eq_scalar_iff a (a 0)).mpr ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, h x hx]

omit [Fintype G] in
/-- Every nonzero displacement coefficient survives projective normalization. -/
theorem bicycle_projective_coefficient (a : G → ZMod 2) (x : G) :
    matrixPivotRepresentative 0 (bicycleConvolutionMatrix a) x 0 =
      if x = 0 then 0 else a x := by
  by_cases hx : x = 0 <;>
    simp [matrixPivotRepresentative, bicycleConvolutionMatrix, hx]

/-- Two bicycle operators have the same trace-zero observations precisely when
all coefficients away from the origin agree. -/
theorem bicycle_traceZero_observations_eq_iff (a b : G → ZMod 2) :
    (∀ B : traceZeroMatrices (ZMod 2) G,
      (bicycleConvolutionMatrix a * B.val).trace =
        (bicycleConvolutionMatrix b * B.val).trace) ↔
      ∀ x, x ≠ 0 → a x = b x := by
  have hsub : bicycleConvolutionMatrix (a - b) =
      bicycleConvolutionMatrix a - bicycleConvolutionMatrix b := rfl
  have h := bicycle_traceZero_annihilator_iff (a - b)
  simpa only [hsub, Matrix.sub_mul, Matrix.trace_sub, sub_eq_zero, Pi.sub_apply] using h

#print axioms bicycle_traceZero_annihilator_iff
#print axioms bicycle_projective_coefficient
#print axioms bicycle_traceZero_observations_eq_iff

end GaloisForLFunctions.RepresentationLifting
