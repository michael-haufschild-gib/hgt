import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie

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
  let e : A ≃ₐ[k] B := AlgEquiv.ofBijective f.toAlgHom hf
  intro x y hxy
  by_contra hne
  let C := Module.Free.chooseBasis k (coLie k A)
  have hre : C.repr (x - y) ≠ 0 := by
    intro h
    apply hne
    apply sub_eq_zero.mp
    exact C.repr.injective (by simpa using h)
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hre
  let phi : coLie k A →ₗ[k] k := C.coord j
  let DA : pointDerivations k A := (pointDerivationEquiv).symm phi
  have hcounit (b : B) : Coalgebra.counit (R := k) (e.symm b : A) =
      Coalgebra.counit (R := k) b := by
    rw [← counit_bialgHom f (e.symm b)]
    congr 1
    exact e.apply_symm_apply b
  let DBlin : B →ₗ[k] k := (DA : A →ₗ[k] k).comp e.symm.toLinearMap
  have hDB : DBlin ∈ pointDerivations k B := by
    intro a b
    change DA.1 (e.symm (a * b)) = _
    rw [map_mul, DA.2, hcounit, hcounit]
    rfl
  let DB : pointDerivations k B := ⟨DBlin, hDB⟩
  let psi : coLie k B →ₗ[k] k := pointDerivationEquiv DB
  have hfun := congrArg (fun z => psi z) hxy
  obtain ⟨a, ha⟩ := d_surjective x
  obtain ⟨b, hb⟩ := d_surjective y
  have hphx : psi (coLieMap f x) = phi x := by
    rw [← ha, coLieMap_d, pointDerivationEquiv_apply_d]
    change DA.1 (e.symm (f a)) = phi (d k A a)
    rw [show e.symm (f a) = a by exact e.symm_apply_apply a]
    have he := congrArg (fun q => q (d k A a))
      ((pointDerivationEquiv).apply_symm_apply phi)
    rw [pointDerivationEquiv_apply_d] at he
    exact he
  have hphy : psi (coLieMap f y) = phi y := by
    rw [← hb, coLieMap_d, pointDerivationEquiv_apply_d]
    change DA.1 (e.symm (f b)) = phi (d k A b)
    rw [show e.symm (f b) = b by exact e.symm_apply_apply b]
    have he := congrArg (fun q => q (d k A b))
      ((pointDerivationEquiv).apply_symm_apply phi)
    rw [pointDerivationEquiv_apply_d] at he
    exact he
  have hphi : phi x = phi y := by
    rw [← hphx, ← hphy]
    exact hfun
  apply hj
  change phi (x - y) = 0
  rw [map_sub, hphi, sub_self]

end
end GaloisForLFunctions.HTGeometry.AffineGroupScheme
