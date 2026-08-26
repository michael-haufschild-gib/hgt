import GaloisForLFunctions.HTGeometry.PrincipalOpenAdjoinRootPresentation

/-!
# Algebra equivalence for a localized algebra map

An algebra map which realizes module localization is not merely a linear localization: ordinary
tensor scalar extension is canonically algebra-equivalent to its target.  This upgrades the module
interface used by principal-open spreading to the algebra interface used by fibres.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

/-- A localized algebra map identifies ordinary tensor scalar extension with the localized target
as algebras. -/
noncomputable def localizedAlgebraTensorEquiv
    (R : Type*) [CommRing R]
    (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T]
    (B : Type*) [CommRing B] [Algebra R B]
    (N : Type*) [CommRing N] [Algebra R N] [Algebra T N] [IsScalarTower R T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule S fN.toLinearMap] :
    TensorProduct R T B ≃ₐ[T] N := by
  let tB : B →ₗ[R] TensorProduct R T B := TensorProduct.mk R T B 1
  let eLin : TensorProduct R T B ≃ₗ[R] N :=
    IsLocalizedModule.linearEquiv S tB fN.toLinearMap
  let h : TensorProduct R T B →ₐ[T] N :=
    Algebra.TensorProduct.lift (Algebra.ofId T N) fN (fun _ _ => mul_comm _ _)
  have heq : h.toLinearMap.restrictScalars R = eLin.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S tB fN.toLinearMap
    apply LinearMap.ext
    intro b
    change h (tB b) = eLin (tB b)
    rw [IsLocalizedModule.linearEquiv_apply]
    change h ((1 : T) ⊗ₜ[R] b) = fN b
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  apply AlgEquiv.ofBijective h
  change Function.Bijective ⇑(h.toLinearMap.restrictScalars R)
  rw [heq]
  exact eLin.bijective

/-- A split field fibre of a localized algebra is also the split field fibre of every earlier
scalar extension. -/
theorem nonempty_split_baseChange_of_localizedAlgebra
    (R : Type*) [CommRing R]
    (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization M T]
    (k : Type*) [Field k] [Algebra R k] [Algebra S k] [Algebra T k]
    [IsScalarTower R S k] [IsScalarTower R T k] [IsScalarTower S T k]
    (B : Type*) [CommRing B] [Algebra R B]
    (N : Type*) [CommRing N] [Algebra R N] [Algebra T N] [IsScalarTower R T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule M fN.toLinearMap]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((TensorProduct T k N) ≃ₐ[k] (ι → k))) :
    Nonempty ((TensorProduct S k (TensorProduct R S B)) ≃ₐ[k] (ι → k)) := by
  obtain ⟨e⟩ := hsplit
  exact ⟨(Algebra.TensorProduct.cancelBaseChange R S k k B).trans
    (Algebra.TensorProduct.cancelBaseChange R T k k B).symm |>.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl)
      (localizedAlgebraTensorEquiv R M T B N fN)) |>.trans e⟩

end GaloisForLFunctions.HTGeometry
