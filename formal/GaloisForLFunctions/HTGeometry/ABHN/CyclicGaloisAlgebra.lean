import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2

/-!
# Cyclic Galois specialization of the twisted cyclic-algebra carrier

This module specializes the raw skew quotient to the automorphism group of `L/K`.  In the intended
finite cyclic Galois case, its parameter comes from `K`, its degree is `finrank K L`, and its skew
automorphism is the chosen Galois generator.  The resulting relations are the algebraic input for
the map from cyclic degree-two cohomology to Brauer classes.

It does not yet prove that the quotient is a finite-dimensional central simple `K`-algebra.  That
requires the remaining all-polynomial normal form, centrality, and simplicity arguments.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)]

/-- The raw cyclic algebra attached to the cyclic automorphism group and a base-field parameter.
In its intended finite cyclic Galois use, this is the usual cyclic-algebra carrier. -/
noncomputable abbrev cyclicGaloisAlgebra (a : K) :=
  CyclicAlgebra (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L) (algebraMap K L a)

/-- The image of the cyclic generator in the Galois cyclic algebra. -/
noncomputable abbrev cyclicGaloisAlgebraX (a : K) : cyclicGaloisAlgebra K L a :=
  cyclicAlgebraX (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L) (algebraMap K L a)

/-- The image of a coefficient from `L` in the Galois cyclic algebra. -/
noncomputable abbrev cyclicGaloisAlgebraC (a : K) (b : L) : cyclicGaloisAlgebra K L a :=
  cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) b

/-- The prospective base-field coefficient map.  Upgrading it to an `Algebra K` structure waits
for the proof that its image commutes with every quotient element. -/
noncomputable def cyclicGaloisAlgebraBaseRingHom (a : K) :
    K →+* cyclicGaloisAlgebra K L a :=
  (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a)).comp (algebraMap K L)

/-- Evaluation of the prospective base-field map is the named embedded coefficient. -/
theorem cyclicGaloisAlgebraBaseRingHom_apply (a b : K) :
    cyclicGaloisAlgebraBaseRingHom K L a b =
      cyclicGaloisAlgebraC K L a (algebraMap K L b) := rfl

/-- The Galois cyclic generator satisfies its degree relation. -/
theorem cyclicGaloisAlgebraX_pow (a : K) :
    cyclicGaloisAlgebraX K L a ^ Module.finrank K L =
      cyclicGaloisAlgebraC K L a (algebraMap K L a) := by
  exact cyclicAlgebraX_pow L (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a)

/-- The cyclic generator commutes with coefficients embedded from the base field. -/
theorem cyclicGaloisAlgebraX_mul_baseC (a b : K) :
    cyclicGaloisAlgebraX K L a * cyclicGaloisAlgebraC K L a (algebraMap K L b) =
      cyclicGaloisAlgebraC K L a (algebraMap K L b) * cyclicGaloisAlgebraX K L a := by
  rw [cyclicAlgebraX_mul_cyclicAlgebraC]
  simp

end GaloisForLFunctions.HTGeometry.ABHN
