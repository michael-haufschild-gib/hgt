import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPerfectionDense
import GaloisForLFunctions.HTGeometry.AdicCompletionTopology

/-!
# Density of `lim_{()^p} A` in `lim_{()^p} Â`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.8(a)
(`t125`).

The structure map of an adic completion has dense image for the projective limit topology, so if
every element of `A` is a `p`-th power the induced map of perfections has dense image as well.
-/

namespace RHTower

open Perfection HTGeometry

variable {A : Type*} [CommRing A] {p : ℕ}

/-- **Deninger, Proposition 14.8(a) (`t125`).**  If every element of `A` is a `p`-th power then the
image of `lim_{()^p} A` in `lim_{()^p} Â` is dense. -/
theorem deningerPerfection_denseRange_adicCompletion (I : Ideal A)
    (hp : ∀ a : A, ∃ b : A, b ^ p = a) :
    DenseRange (mapMonoidHom p
      (algebraMap A (AdicCompletion I A)).toMonoidHom) :=
  deningerPerfection_denseRange_mapMonoidHom hp _ (denseRange_algebraMap_adicCompletion I)

end RHTower
