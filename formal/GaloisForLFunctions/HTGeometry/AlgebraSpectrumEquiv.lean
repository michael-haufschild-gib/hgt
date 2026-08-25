import GaloisForLFunctions.HTGeometry.AlgebraSpectrumTopology

/-!
# Functoriality of complex algebra spectra under algebra equivalences

The complex-point topology is pointwise convergence.  Precomposition by a complex-algebra map is
therefore continuous, and an algebra equivalence induces a contravariant homeomorphism.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AlgSpec

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra ℂ B] [Algebra ℂ C]

/-- Contravariant transport of complex points by a complex-algebra map. -/
def precomp (f : B →ₐ[ℂ] C) (chi : AlgSpec C) : AlgSpec B :=
  chi.comp f

theorem continuous_precomp (f : B →ₐ[ℂ] C) : Continuous (precomp f) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi fun b => continuous_eval (f b)

/-- A complex-algebra equivalence induces the contravariant homeomorphism on complex points. -/
def homeomorphOfAlgEquiv (e : B ≃ₐ[ℂ] C) : AlgSpec C ≃ₜ AlgSpec B where
  toFun := precomp e.toAlgHom
  invFun := precomp e.symm.toAlgHom
  left_inv chi := by
    apply DFunLike.ext _ _
    intro c
    change chi (e (e.symm c)) = chi c
    rw [e.apply_symm_apply]
  right_inv chi := by
    apply DFunLike.ext _ _
    intro b
    change chi (e.symm (e b)) = chi b
    rw [e.symm_apply_apply]
  continuous_toFun := continuous_precomp e.toAlgHom
  continuous_invFun := continuous_precomp e.symm.toAlgHom

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
