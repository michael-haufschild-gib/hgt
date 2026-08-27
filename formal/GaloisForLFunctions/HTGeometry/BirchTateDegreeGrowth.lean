import GaloisForLFunctions.HTGeometry.FiniteCompositumPowerIndependence

/-!
# Degree growth across coefficient-field extension

Cyclotomic degree growth is the arithmetic input proving that the square of the absolute
cyclotomic character cannot be trivial over a number field. This module supplies the required
coefficient-field bound over an arbitrary field tower.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

/-- Extending coefficients from `K` to `F` can lower the degree of an integral element by at most
`[F : K]`. -/
theorem minpoly_natDegree_tower_lower_bound [FiniteDimensional K F]
    (x : L) (hxK : IsIntegral K x) :
    (minpoly K x).natDegree ≤
      Module.finrank K F * (minpoly F x).natDegree := by
  let A : IntermediateField K L := IntermediateField.adjoin K {x}
  let B : IntermediateField F L := IntermediateField.adjoin F {x}
  have hxF : IsIntegral F x := hxK.tower_top
  letI : FiniteDimensional K A := IntermediateField.adjoin.finiteDimensional hxK
  letI : FiniteDimensional F B := IntermediateField.adjoin.finiteDimensional hxF
  letI : IsScalarTower K F B := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact IsScalarTower.algebraMap_apply K F L r)
  letI : Module.Finite K B := Module.Finite.trans F B
  have hAmem : ∀ z : L, z ∈ A → z ∈ B := fun z hz =>
    mem_adjoin_singleton_of_isScalarTower x z hz
  let toB : A →ₐ[K] B :=
    { toFun := fun z => Subtype.mk z.1 (hAmem z.1 z.2)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hfin : Module.finrank K A ≤ Module.finrank K B :=
    LinearMap.finrank_le_finrank_of_injective (f := toB.toLinearMap) toB.injective
  have htower := Module.finrank_mul_finrank K F B
  rw [← IntermediateField.adjoin.finrank hxK,
    ← IntermediateField.adjoin.finrank hxF]
  exact hfin.trans_eq htower.symm

end GaloisForLFunctions.HTGeometry
