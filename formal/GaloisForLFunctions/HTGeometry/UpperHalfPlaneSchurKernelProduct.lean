import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence

/-!
# Product cocycle for upper-half-plane Schur kernels

The literal Schur defect kernel is a multiplicative cocycle.  Recursive
iteration gives an exact ordered finite-factor correlation cascade without
analytic or positivity assumptions.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact two-factor Schur-defect cocycle. -/
theorem upperHalfPlaneSchurKernel_mul (f g : ℂ → ℂ) (z w : ℂ) :
    upperHalfPlaneSchurKernel (fun u => f u * g u) z w =
      upperHalfPlaneSchurKernel f z w +
        f z * conj (f w) * upperHalfPlaneSchurKernel g z w := by
  unfold upperHalfPlaneSchurKernel
  rw [map_mul]
  ring

/-- Ordered finite product cascade associated with literal upper-half-plane
Schur defect kernels. -/
def upperHalfPlaneSchurKernelProductCascade
    (fs : List (ℂ → ℂ)) (z w : ℂ) : ℂ :=
  match fs with
  | [] => 0
  | f :: tail => upperHalfPlaneSchurKernel f z w +
      f z * conj (f w) *
        upperHalfPlaneSchurKernelProductCascade tail z w

/-- Exact Schur kernel of a finite ordered product equals its recursive
factor-by-factor correlation cascade. -/
theorem upperHalfPlaneSchurKernel_productList
    (fs : List (ℂ → ℂ)) (z w : ℂ) :
    upperHalfPlaneSchurKernel
        (fun u => (fs.map fun f => f u).prod) z w =
      upperHalfPlaneSchurKernelProductCascade fs z w := by
  induction fs with
  | nil => simp [upperHalfPlaneSchurKernelProductCascade,
      upperHalfPlaneSchurKernel]
  | cons f fs ih =>
      change upperHalfPlaneSchurKernel
          (fun u => f u * (fs.map fun g => g u).prod) z w = _
      rw [upperHalfPlaneSchurKernel_mul, ih]
      rfl

end
end GaloisForLFunctions.HTGeometry
