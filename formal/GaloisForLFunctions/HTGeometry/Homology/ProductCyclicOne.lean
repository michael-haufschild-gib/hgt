import GaloisForLFunctions.HTGeometry.Homology.CyclicOneFunctor

/-!
# Cyclic degree one of a product algebra

The inclusions of the two orthogonal ideals induce maps on cyclic homology.
Mixed tensors are explicit Hochschild boundaries, so the two projections and
the sum of the inclusions are inverse linear maps.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- Project ordinary cyclic homology to the two algebra factors. -/
def cyclicOneProductTo : CyclicOne (A × B) →ₗ[ℂ] CyclicOne A × CyclicOne B :=
  (cyclicOneMap (AlgHom.fst ℂ A B).toNonUnitalAlgHom).prod
    (cyclicOneMap (AlgHom.snd ℂ A B).toNonUnitalAlgHom)

/-- Include the two factors as orthogonal ideals and add their cyclic classes. -/
def cyclicOneProductFrom : CyclicOne A × CyclicOne B →ₗ[ℂ] CyclicOne (A × B) :=
  (cyclicOneMap (NonUnitalAlgHom.inl ℂ A B)).coprod
    (cyclicOneMap (NonUnitalAlgHom.inr ℂ A B))

@[simp] theorem cyclicOneProductTo_class (a b : A × B) :
    cyclicOneProductTo (cyclicClass a b) =
      (cyclicClass a.1 b.1, cyclicClass a.2 b.2) := by
  change (cyclicOneMap (AlgHom.fst ℂ A B).toNonUnitalAlgHom (cyclicClass a b),
    cyclicOneMap (AlgHom.snd ℂ A B).toNonUnitalAlgHom (cyclicClass a b)) = _
  rw [cyclicOneMap_class, cyclicOneMap_class]
  rfl

/-- A tensor joining orthogonal factors is a Hochschild boundary. -/
@[simp] theorem cyclicClass_mixed_left (a : A) (b : B) :
    cyclicClass (a, 0) (0, b) = 0 := by
  have h : cyclicClass (a, (0 : B)) (0, b) - cyclicClass (a, (0 : B)) (0, 0) +
      cyclicClass ((0 : A), (0 : B)) (1, 0) = 0 := by
    simpa using cyclicClass_boundary (a, (0 : B)) (1, (0 : B)) (0, b)
  change cyclicClass (a, (0 : B)) (0, b) - cyclicClass (a, (0 : B)) (0 : A × B) +
    cyclicClass (0 : A × B) (1, 0) = 0 at h
  simpa only [cyclicClass_zero_left, cyclicClass_zero_right, sub_zero, add_zero] using h

@[simp] theorem cyclicClass_mixed_right (a : A) (b : B) :
    cyclicClass (0, b) (a, 0) = 0 := by
  rw [cyclicClass_swap, cyclicClass_mixed_left, neg_zero]

/-- Every product-algebra class is the sum of its two unmixed components. -/
theorem cyclicClass_product_reduction (a b : A × B) :
    cyclicClass a b = cyclicClass (a.1, (0 : B)) (b.1, 0) +
      cyclicClass ((0 : A), a.2) (0, b.2) := by
  have ha : a = (a.1, 0) + (0, a.2) := by ext <;> simp
  have hb : b = (b.1, 0) + (0, b.2) := by ext <;> simp
  calc
    cyclicClass a b = cyclicClass ((a.1, 0) + (0, a.2))
        ((b.1, 0) + (0, b.2)) := congrArg₂ cyclicClass ha hb
    _ = _ := by simp only [cyclicClass_add_left, cyclicClass_add_right,
      cyclicClass_mixed_left, cyclicClass_mixed_right, add_zero, zero_add]

@[simp] theorem cyclicOneProductTo_inl (x : CyclicOne A) :
    cyclicOneProductTo (cyclicOneMap (NonUnitalAlgHom.inl ℂ A B) x) = (x, 0) := by
  have h : (cyclicOneProductTo (A := A) (B := B)).comp
      (cyclicOneMap (NonUnitalAlgHom.inl ℂ A B)) =
      (LinearMap.id : CyclicOne A →ₗ[ℂ] CyclicOne A).prod 0 := by
    apply cyclicOne_linearMap_ext
    intro a b
    simp only [LinearMap.comp_apply, cyclicOneMap_class, cyclicOneProductTo_class]
    change (cyclicClass a b, cyclicClass (0 : B) 0) = (cyclicClass a b, 0)
    rw [cyclicClass_zero_left]
  exact LinearMap.congr_fun h x

@[simp] theorem cyclicOneProductTo_inr (x : CyclicOne B) :
    cyclicOneProductTo (cyclicOneMap (NonUnitalAlgHom.inr ℂ A B) x) = (0, x) := by
  have h : (cyclicOneProductTo (A := A) (B := B)).comp
      (cyclicOneMap (NonUnitalAlgHom.inr ℂ A B)) =
      (0 : CyclicOne B →ₗ[ℂ] CyclicOne A).prod LinearMap.id := by
    apply cyclicOne_linearMap_ext
    intro a b
    simp only [LinearMap.comp_apply, cyclicOneMap_class, cyclicOneProductTo_class]
    change (cyclicClass (0 : A) 0, cyclicClass a b) = (0, cyclicClass a b)
    rw [cyclicClass_zero_left]
  exact LinearMap.congr_fun h x

theorem cyclicOneProduct_to_from :
    (cyclicOneProductTo (A := A) (B := B)).comp cyclicOneProductFrom = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change cyclicOneProductTo (cyclicOneMap (NonUnitalAlgHom.inl ℂ A B) x +
    cyclicOneMap (NonUnitalAlgHom.inr ℂ A B) y) = (x,y)
  rw [map_add, cyclicOneProductTo_inl, cyclicOneProductTo_inr]
  simp

theorem cyclicOneProduct_from_to :
    (cyclicOneProductFrom (A := A) (B := B)).comp cyclicOneProductTo = LinearMap.id := by
  apply cyclicOne_linearMap_ext
  intro a b
  simp only [LinearMap.comp_apply, cyclicOneProductTo_class, LinearMap.id_apply]
  change cyclicOneMap (NonUnitalAlgHom.inl ℂ A B) (cyclicClass a.1 b.1) +
    cyclicOneMap (NonUnitalAlgHom.inr ℂ A B) (cyclicClass a.2 b.2) = cyclicClass a b
  rw [cyclicOneMap_class, cyclicOneMap_class]
  exact (cyclicClass_product_reduction a b).symm

/-- Ordinary cyclic degree one preserves a finite product of complex algebras. -/
def cyclicOneProductEquiv : CyclicOne (A × B) ≃ₗ[ℂ] CyclicOne A × CyclicOne B :=
  { cyclicOneProductTo with
    invFun := cyclicOneProductFrom
    left_inv := fun x => LinearMap.congr_fun cyclicOneProduct_from_to x
    right_inv := fun x => LinearMap.congr_fun cyclicOneProduct_to_from x }

@[simp] theorem cyclicOneProductEquiv_class (a b : A × B) :
    cyclicOneProductEquiv (cyclicClass a b) =
      (cyclicClass a.1 b.1, cyclicClass a.2 b.2) := cyclicOneProductTo_class a b

#print axioms cyclicOneProductEquiv
#print axioms cyclicClass_mixed_left
end GaloisForLFunctions.RHTower.SquareZeroCyclic
