import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdeleHaar

/-!
# Finite local-field cylinders in the elliptic adeles

Allowing denominators at finitely many places gives an open additive
subgroup. Its topology is exactly the product of those completed fields
and the compact product of all remaining local integer rings.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Filter Set
open scoped RestrictedProduct
noncomputable section

/-- Finite adeles integral outside a prescribed finite set. -/
def finiteAdeleCylinder (S : Finset FinitePlace) : AddSubgroup FiniteAdeles where
  carrier := {a | ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers K}
  zero_mem' v _ := zero_mem _
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  neg_mem' ha v hv := neg_mem (ha v hv)

/-- The finitely many unrestricted completed fields. -/
abbrev FiniteCylinderFields (S : Finset FinitePlace) :=
  (v : S) → v.1.adicCompletion K

/-- The compact product of the remaining local integer rings. -/
abbrev FiniteCylinderTail (S : Finset FinitePlace) :=
  (v : {v : FinitePlace // v ∉ S}) → v.1.adicCompletionIntegers K

instance finiteCylinderTail_compact (S : Finset FinitePlace) :
    CompactSpace (FiniteCylinderTail S) := Pi.compactSpace

private theorem cylinder_cofinite (S : Finset FinitePlace) :
    cofinite ≤ Filter.principal {v : FinitePlace | v ∉ S} := by
  apply Filter.le_principal_iff.mpr
  apply Filter.eventually_cofinite.mpr
  apply S.finite_toSet.subset
  intro v hv
  change v ∈ S
  exact not_not.mp hv

private def cylinderAssemblyFunction (S : Finset FinitePlace)
    (x : FiniteCylinderFields S × FiniteCylinderTail S) (v : FinitePlace) :
    v.adicCompletion K := by
  classical
  exact if h : v ∈ S then x.1 ⟨v, h⟩ else (x.2 ⟨v, h⟩ : v.adicCompletion K)

private def cylinderPrincipalAssembly (S : Finset FinitePlace)
    (x : FiniteCylinderFields S × FiniteCylinderTail S) :
    Πʳ (v : FinitePlace), [v.adicCompletion K, v.adicCompletionIntegers K]_[
      Filter.principal {v : FinitePlace | v ∉ S}] :=
  ⟨cylinderAssemblyFunction S x, by
    intro v hv
    change cylinderAssemblyFunction S x v ∈ v.adicCompletionIntegers K
    rw [cylinderAssemblyFunction, dif_neg hv]
    exact (x.2 ⟨v, hv⟩).property⟩

/-- Assemble the finite unrestricted coordinates and all integral tail coordinates. -/
def finiteCylinderAssembly (S : Finset FinitePlace) :
    FiniteCylinderFields S × FiniteCylinderTail S →+ finiteAdeleCylinder S where
  toFun x := ⟨RestrictedProduct.inclusion _ _ (cylinder_cofinite S)
    (cylinderPrincipalAssembly S x), by
      intro v hv
      change cylinderAssemblyFunction S x v ∈ v.adicCompletionIntegers K
      rw [cylinderAssemblyFunction, dif_neg hv]
      exact (x.2 ⟨v, hv⟩).property⟩
  map_zero' := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    change cylinderAssemblyFunction S 0 v = 0
    unfold cylinderAssemblyFunction
    split <;> rfl
  map_add' x y := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    change cylinderAssemblyFunction S (x + y) v =
      cylinderAssemblyFunction S x v + cylinderAssemblyFunction S y v
    unfold cylinderAssemblyFunction
    split <;> rfl

/-- The cylinder has precisely the expected finite-field and integral-tail coordinates. -/
def finiteAdeleCylinderEquiv (S : Finset FinitePlace) :
    FiniteCylinderFields S × FiniteCylinderTail S ≃+ finiteAdeleCylinder S where
  toFun := finiteCylinderAssembly S
  invFun a := (fun v => a.1 v.1, fun v => ⟨a.1 v.1, a.property v.1 v.property⟩)
  left_inv x := by
    apply Prod.ext
    · funext v
      change cylinderAssemblyFunction S x v.1 = x.1 v
      rw [cylinderAssemblyFunction, dif_pos v.property]
    · funext v
      apply Subtype.ext
      change cylinderAssemblyFunction S x v.1 = (x.2 v : v.1.adicCompletion K)
      rw [cylinderAssemblyFunction, dif_neg v.property]
  right_inv a := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    change cylinderAssemblyFunction S _ v = a.1 v
    unfold cylinderAssemblyFunction
    split <;> rfl
  map_add' := (finiteCylinderAssembly S).map_add

private theorem continuous_cylinderPrincipalAssembly (S : Finset FinitePlace) :
    Continuous (cylinderPrincipalAssembly S) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  change Continuous (fun x => cylinderAssemblyFunction S x v)
  classical
  by_cases hv : v ∈ S
  · have h := (continuous_apply ⟨v, hv⟩).comp
      (continuous_fst : Continuous (Prod.fst :
        FiniteCylinderFields S × FiniteCylinderTail S → FiniteCylinderFields S))
    simpa only [Function.comp_apply, cylinderAssemblyFunction, dif_pos hv] using h
  · have h := continuous_subtype_val.comp ((continuous_apply ⟨v, hv⟩).comp
      (continuous_snd : Continuous (Prod.snd :
        FiniteCylinderFields S × FiniteCylinderTail S → FiniteCylinderTail S)))
    simpa only [Function.comp_apply, cylinderAssemblyFunction, dif_neg hv] using h

/-- Coordinate assembly is a homeomorphism for the actual restricted-product topology. -/
def finiteAdeleCylinderHomeomorph (S : Finset FinitePlace) :
    FiniteCylinderFields S × FiniteCylinderTail S ≃ₜ finiteAdeleCylinder S where
  toEquiv := (finiteAdeleCylinderEquiv S).toEquiv
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact (RestrictedProduct.continuous_inclusion (cylinder_cofinite S)).comp
      (continuous_cylinderPrincipalAssembly S)
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val
    · apply continuous_pi
      intro v
      apply continuous_induced_rng.mpr
      exact (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val

/-- Finite local-field cylinders are open inside the actual finite adeles. -/
theorem finiteAdeleCylinder_isOpen (S : Finset FinitePlace) :
    IsOpen (finiteAdeleCylinder S : Set FiniteAdeles) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (fun v : FinitePlace => Valued.isOpen_valuationSubring (v.adicCompletion K))

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finiteAdeleCylinderHomeomorph
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finiteAdeleCylinder_isOpen
