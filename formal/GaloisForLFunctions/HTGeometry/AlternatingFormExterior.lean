import GaloisForLFunctions.HTGeometry.MultilinearFiniteDimensional
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Alternating forms on a coordinate space are the exterior power

An alternating form of degree `k` on a finite coordinate space is a linear functional on the `k`-th
exterior power of that space, and the exterior power is free on the `k`-element sets of coordinates,
so it is isomorphic to its own dual.  Composing with the identification of alternating maps with
continuous alternating maps gives an isomorphism between the continuous alternating forms of degree
`k` and the `k`-th exterior power.

* `alternatingFormExteriorEquiv` : the continuous alternating forms of degree `k` on `Fin r → 𝕜`
  are the `k`-th exterior power of `Fin r → 𝕜`.
-/

namespace GaloisForLFunctions.HTGeometry

section ExteriorIdentification

variable {𝕜 : Type*} [RCLike 𝕜]

open Module

/-- **The continuous alternating forms of degree `k` on a finite coordinate space are the `k`-th
exterior power of that space.**  Both are free on the `k`-element sets of coordinates: an
alternating form is a functional on the exterior power, and the exterior power of a free module is
free on the increasing selections of basis vectors. -/
noncomputable def alternatingFormExteriorEquiv (𝕜 : Type*) [RCLike 𝕜] (r k : ℕ) :
    ((Fin r → 𝕜) [⋀^Fin k]→L[𝕜] 𝕜) ≃ₗ[𝕜] ⋀[𝕜]^k (Fin r → 𝕜) := by
  classical
  exact ((continuousAlternatingEquiv 𝕜 r (Fin k) 𝕜).symm.trans
    exteriorPower.alternatingMapLinearEquiv).trans
    ((((Pi.basisFun 𝕜 (Fin r)).exteriorPower k).dualBasis).equiv
      ((Pi.basisFun 𝕜 (Fin r)).exteriorPower k) (Equiv.refl _))

end ExteriorIdentification

end GaloisForLFunctions.HTGeometry
