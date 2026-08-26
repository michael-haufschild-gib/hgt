import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Co-Lie functoriality for bijective bialgebra morphisms

A bijective bialgebra morphism induces an injective map on co-Lie modules.  The proof transports
point derivations through the inverse algebra equivalence and uses the universal duality between
point derivations and linear functionals on the co-Lie module.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

noncomputable section

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Bialgebra k A] [Bialgebra k B]

/-- Evaluation of the co-Lie functional corresponding to a point derivation. -/
theorem pointDerivationEquiv_apply_d (D : pointDerivations k A) (a : A) :
    pointDerivationEquiv D (d k A a) = D.1 a := by
  simp [pointDerivationEquiv, d_apply, toAug_coe,
    PointDerivation.map_algebraMap D.2]

/-- A bijective bialgebra morphism induces an injective map on co-Lie modules. -/
theorem coLieMap_injective_of_bijective (f : A →ₐc[k] B)
    (hf : Function.Bijective f) : Function.Injective (coLieMap f) := by
  let e : A ≃ₐc[k] B := BialgEquiv.ofBijective f hf
  have hcomp : e.symm.toBialgHom.comp f = BialgHom.id k A := by
    apply BialgHom.ext
    intro a
    exact e.symm_apply_apply a
  intro x y hxy
  have hxy' := congrArg (coLieMap e.symm.toBialgHom) hxy
  have hleft (z : coLie k A) :
      coLieMap e.symm.toBialgHom (coLieMap f z) = z := by
    change ((coLieMap e.symm.toBialgHom).comp (coLieMap f)) z = z
    rw [← coLieMap_comp, hcomp, coLieMap_id, LinearMap.id_apply]
  rw [hleft x, hleft y] at hxy'
  exact hxy'

end
end GaloisForLFunctions.HTGeometry.AffineGroupScheme
