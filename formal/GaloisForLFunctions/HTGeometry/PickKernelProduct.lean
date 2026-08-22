import GaloisForLFunctions.HTGeometry.PrimeResiduePickInertia

/-!
# Product rule for Nevanlinna--Pick difference kernels

The difference Pick kernel is a derivation for pointwise products, with the
second factor evaluated at the left node and the conjugated first factor at
the right node.  This algebraic bridge is reusable by any factorized
half-plane or Euler-product construction.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- The Nevanlinna--Pick difference kernel of a pointwise product splits into its two factors. -/
theorem pickKernel_mul (f g : ℂ → ℂ) (z w : ℂ) :
    pickKernel (fun ζ => f ζ * g ζ) z w =
      g z * pickKernel f z w + starRingEnd ℂ (f w) * pickKernel g z w := by
  unfold pickKernel
  rw [map_mul]
  ring

end

end GaloisForLFunctions.HTGeometry
