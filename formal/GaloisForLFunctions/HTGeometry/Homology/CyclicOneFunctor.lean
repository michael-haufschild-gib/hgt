import GaloisForLFunctions.HTGeometry.Homology.AlternatingCyclicMoments
import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# Degree-one cyclic classes and functoriality

Two-tensor classes satisfy the Hochschild boundary relation and antisymmetry.
Classes with a scalar factor vanish. Multiplicative linear maps preserve these
relations without preserving the unit, so algebra isomorphisms induce cyclic
homology isomorphisms and orthogonal-ideal inclusions can be used in decompositions.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {A B : Type*} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B]

/-- Tensoring on the right by a fixed algebra element is linear. -/
def pairLinearLeft (b : A) : A →ₗ[ℂ] CyclicBarTensor ℂ A 1 where
  toFun a := pair a b
  map_add' a c := by
    have h (z : A) : Function.update ![a,b] 0 z = ![z,b] := by
      ext i; fin_cases i <;> simp
    simpa only [pair, h] using
      (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_add ![a,b] 0 a c
  map_smul' c a := by
    change pair (c • a) b = c • pair a b
    have h (z : A) : Function.update ![a,b] 0 z = ![z,b] := by
      ext i; fin_cases i <;> simp
    simpa only [pair, h] using
      (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_smul ![a,b] 0 c a

@[simp] theorem pair_add_left (a b c : A) : pair (a+b) c = pair a c + pair b c :=
  (pairLinearLeft c).map_add a b

@[simp] theorem pair_add_right (a b c : A) : pair a (b+c) = pair a b + pair a c :=
  (pairLinearRight a).map_add b c

@[simp] theorem pair_smul_left (z : ℂ) (a b : A) : pair (z • a) b = z • pair a b :=
  (pairLinearLeft b).map_smul z a

@[simp] theorem pair_smul_right (z : ℂ) (a b : A) : pair a (z • b) = z • pair a b :=
  (pairLinearRight a).map_smul z b

@[simp] theorem pair_zero_left (b : A) : pair 0 b = 0 := (pairLinearLeft b).map_zero

/-- The ordinary cyclic class of a two-tensor. -/
def cyclicClass (a b : A) : CyclicOne A :=
  (cyclicRelations (A := A)).mkQ (pair a b)

@[simp] theorem cyclicClass_add_left (a b c : A) :
    cyclicClass (a+b) c = cyclicClass a c + cyclicClass b c := by
  simp only [cyclicClass, pair_add_left, map_add]

@[simp] theorem cyclicClass_add_right (a b c : A) :
    cyclicClass a (b+c) = cyclicClass a b + cyclicClass a c := by
  simp only [cyclicClass, pair_add_right, map_add]

@[simp] theorem cyclicClass_smul_left (z : ℂ) (a b : A) :
    cyclicClass (z • a) b = z • cyclicClass a b := by
  simp only [cyclicClass, pair_smul_left, map_smul]

@[simp] theorem cyclicClass_smul_right (z : ℂ) (a b : A) :
    cyclicClass a (z • b) = z • cyclicClass a b := by
  simp only [cyclicClass, pair_smul_right, map_smul]

@[simp] theorem cyclicClass_zero_left (b : A) : cyclicClass 0 b = 0 := by
  simp only [cyclicClass, pair_zero_left, map_zero]

@[simp] theorem cyclicClass_zero_right (a : A) : cyclicClass a 0 = 0 := by
  simp only [cyclicClass, pair_zero_right, map_zero]

/-- The Hochschild boundary relation holds in the ordinary cyclic quotient. -/
theorem cyclicClass_boundary (a b c : A) :
    cyclicClass (a*b) c - cyclicClass a (b*c) + cyclicClass (c*a) b = 0 := by
  have h : (cyclicRelations (A := A)).mkQ (boundaryTwo (triple a b c)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
      ((show LinearMap.range (boundaryTwo (A := A)) ≤ cyclicRelations from le_sup_left) ⟨_, rfl⟩)
  simpa only [boundaryTwo_triple, map_add, map_sub, cyclicClass] using h

/-- Signed rotation makes the two-tensor class antisymmetric. -/
theorem cyclicClass_rotation (a b : A) : cyclicClass a b + cyclicClass b a = 0 := by
  have h : pair a b + pair b a ∈ cyclicRelations := by
    apply (show LinearMap.range (LinearMap.id +
      (cyclicBarRotate (R := ℂ) (A := A) 1).toLinearMap) ≤ cyclicRelations from le_sup_right)
    exact ⟨pair a b, by simp only [LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, rotate_pair]⟩
  have hz : (cyclicRelations (A := A)).mkQ (pair a b + pair b a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr h
  simpa only [map_add, cyclicClass] using hz

theorem cyclicClass_swap (a b : A) : cyclicClass b a = -cyclicClass a b :=
  eq_neg_iff_add_eq_zero.mpr (cyclicClass_rotation b a)

@[simp] theorem cyclicClass_self (a : A) : cyclicClass a a = 0 := by
  have h : (2 : ℂ) • cyclicClass a a = 0 := by
    simpa only [two_smul ℂ] using cyclicClass_rotation a a
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

@[simp] theorem cyclicClass_one_right (a : A) : cyclicClass a 1 = 0 := by
  simpa only [one_mul, mul_one, sub_self, zero_add] using cyclicClass_boundary a 1 1

@[simp] theorem cyclicClass_one_left (a : A) : cyclicClass 1 a = 0 := by
  rw [cyclicClass_swap, cyclicClass_one_right, neg_zero]

/-- A linear map from cyclic degree one is determined by two-tensor classes. -/
theorem cyclicOne_linearMap_ext {W : Type*} [AddCommGroup W] [Module ℂ W]
    {f g : CyclicOne A →ₗ[ℂ] W}
    (h : ∀ a b, f (cyclicClass a b) = g (cyclicClass a b)) : f = g := by
  have he : f.comp (cyclicRelations (A := A)).mkQ =
      g.comp (cyclicRelations (A := A)).mkQ := by
    apply PiTensorProduct.ext
    ext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    change f ((cyclicRelations (A := A)).mkQ (PiTensorProduct.tprod ℂ x)) =
      g ((cyclicRelations (A := A)).mkQ (PiTensorProduct.tprod ℂ x))
    rw [hx]
    exact h _ _
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (cyclicRelations (A := A)).mkQ_surjective q
  exact LinearMap.congr_fun he x

/-- The linear map underlying a possibly nonunital algebra homomorphism. -/
def cyclicHomLinear (f : A →ₙₐ[ℂ] B) : A →ₗ[ℂ] B where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smul f

/-- Applying a linear map to each factor of a cyclic-bar tensor. -/
def cyclicChainMap (f : A →ₗ[ℂ] B) (n : ℕ) :
    CyclicBarTensor ℂ A n →ₗ[ℂ] CyclicBarTensor ℂ B n :=
  PiTensorProduct.map (fun _ => f)

@[simp] theorem cyclicChainMap_pair (f : A →ₗ[ℂ] B) (a b : A) :
    cyclicChainMap f 1 (pair a b) = pair (f a) (f b) := by
  rw [cyclicChainMap, pair, PiTensorProduct.map_tprod]
  congr 1
  ext i; fin_cases i <;> rfl

@[simp] theorem cyclicChainMap_triple (f : A →ₗ[ℂ] B) (a b c : A) :
    cyclicChainMap f 2 (triple a b c) = triple (f a) (f b) (f c) := by
  rw [cyclicChainMap, triple, PiTensorProduct.map_tprod]
  congr 1
  ext i; fin_cases i <;> rfl

private theorem cyclicChainMap_boundary (f : A →ₙₐ[ℂ] B) :
    ((cyclicRelations (A := B)).mkQ.comp
      (cyclicChainMap (cyclicHomLinear f) 1)).comp boundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x
  change (cyclicRelations (A := B)).mkQ
    (cyclicChainMap (cyclicHomLinear f) 1 (boundaryTwo (PiTensorProduct.tprod ℂ x))) = 0
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]
  change (cyclicRelations (A := B)).mkQ
    (cyclicChainMap (cyclicHomLinear f) 1 (boundaryTwo (triple _ _ _))) = 0
  rw [boundaryTwo_triple]
  simp only [map_add, map_sub, cyclicChainMap_pair]
  change cyclicClass (f (x 0 * x 1)) (f (x 2)) -
    cyclicClass (f (x 0)) (f (x 1 * x 2)) +
    cyclicClass (f (x 2 * x 0)) (f (x 1)) = 0
  simp only [map_mul]
  exact cyclicClass_boundary _ _ _

private theorem cyclicChainMap_rotation (f : A →ₙₐ[ℂ] B) :
    ((cyclicRelations (A := B)).mkQ.comp (cyclicChainMap (cyclicHomLinear f) 1)).comp
      (LinearMap.id + (cyclicBarRotate (R := ℂ) (A := A) 1).toLinearMap) = 0 := by
  apply PiTensorProduct.ext
  ext x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  change (cyclicRelations (A := B)).mkQ (cyclicChainMap (cyclicHomLinear f) 1
    (PiTensorProduct.tprod ℂ x + cyclicBarRotate (R := ℂ) 1 (PiTensorProduct.tprod ℂ x))) = 0
  rw [hx]
  change (cyclicRelations (A := B)).mkQ (cyclicChainMap (cyclicHomLinear f) 1
    (pair _ _ + cyclicBarRotate (R := ℂ) 1 (pair _ _))) = 0
  rw [rotate_pair]
  simp only [map_add, cyclicChainMap_pair]
  exact cyclicClass_rotation _ _

/-- Multiplicative linear maps preserve ordinary cyclic relations; preserving the unit is unnecessary. -/
def cyclicOneMap (f : A →ₙₐ[ℂ] B) : CyclicOne A →ₗ[ℂ] CyclicOne B :=
  (cyclicRelations (A := A)).liftQ
    ((cyclicRelations (A := B)).mkQ.comp (cyclicChainMap (cyclicHomLinear f) 1)) (by
      apply sup_le
      · rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun (cyclicChainMap_boundary f) x
      · rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun (cyclicChainMap_rotation f) x)

@[simp] theorem cyclicOneMap_class (f : A →ₙₐ[ℂ] B) (a b : A) :
    cyclicOneMap f (cyclicClass a b) = cyclicClass (f a) (f b) := by
  change (cyclicRelations (A := B)).mkQ (cyclicChainMap (cyclicHomLinear f) 1 (pair a b)) = _
  rw [cyclicChainMap_pair]
  rfl

/-- Algebra isomorphisms induce isomorphisms of actual ordinary cyclic degree one. -/
def cyclicOneEquiv (e : A ≃ₐ[ℂ] B) : CyclicOne A ≃ₗ[ℂ] CyclicOne B :=
  { cyclicOneMap e.toAlgHom.toNonUnitalAlgHom with
    invFun := cyclicOneMap e.symm.toAlgHom.toNonUnitalAlgHom
    left_inv := by
      have h : (cyclicOneMap e.symm.toAlgHom.toNonUnitalAlgHom).comp
          (cyclicOneMap e.toAlgHom.toNonUnitalAlgHom) = LinearMap.id := by
        apply cyclicOne_linearMap_ext
        intro a b
        simp only [LinearMap.comp_apply, cyclicOneMap_class, LinearMap.id_apply]
        change cyclicClass (e.symm (e a)) (e.symm (e b)) = cyclicClass a b
        rw [e.symm_apply_apply, e.symm_apply_apply]
      exact fun x => LinearMap.congr_fun h x
    right_inv := by
      have h : (cyclicOneMap e.toAlgHom.toNonUnitalAlgHom).comp
          (cyclicOneMap e.symm.toAlgHom.toNonUnitalAlgHom) = LinearMap.id := by
        apply cyclicOne_linearMap_ext
        intro a b
        simp only [LinearMap.comp_apply, cyclicOneMap_class, LinearMap.id_apply]
        change cyclicClass (e (e.symm a)) (e (e.symm b)) = cyclicClass a b
        rw [e.apply_symm_apply, e.apply_symm_apply]
      exact fun x => LinearMap.congr_fun h x }

@[simp] theorem cyclicOneEquiv_class (e : A ≃ₐ[ℂ] B) (a b : A) :
    cyclicOneEquiv e (cyclicClass a b) = cyclicClass (e a) (e b) :=
  cyclicOneMap_class _ _ _

#print axioms cyclicClass_boundary
#print axioms cyclicOneEquiv
end GaloisForLFunctions.RHTower.SquareZeroCyclic
