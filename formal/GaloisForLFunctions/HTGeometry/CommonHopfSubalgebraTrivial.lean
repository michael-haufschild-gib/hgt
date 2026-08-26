import GaloisForLFunctions.HTGeometry.SymmetricHopfGroupLike
import GaloisForLFunctions.HTGeometry.AffineExponentialCrossHomFinite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Common Hopf subalgebras of group and symmetric algebras

Over a field, a commutative Hopf algebra that embeds into both a group algebra and a symmetric
algebra contains only scalars.  The proof first shows that every grading monomial occurring in the
group-algebra image has a group-like preimage, by contracting one leg of the comultiplication
against its coefficient functional.  Its symmetric-algebra image is then a group-like element and
hence equals one.  Injectivity eliminates every nonzero grading degree.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k C : Type*} [Field k] [CommRing C] [HopfAlgebra k C]

/-- Contract the right tensor factor against a linear functional. -/
noncomputable def rightSlice (φ : C →ₗ[k] k) : C ⊗[k] C →ₗ[k] C :=
  (TensorProduct.rid k C).toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.id (R := k) (M := C)) φ

@[simp] theorem rightSlice_tmul (φ : C →ₗ[k] k) (x y : C) :
    rightSlice φ (x ⊗ₜ[k] y) = φ y • x := by
  simp [rightSlice]

/-- Slicing after mapping both tensor factors is the mapped slice against the pulled-back
functional. -/
theorem rightSlice_map {D : Type*} [CommRing D] [HopfAlgebra k D]
    (f : C →ₗ[k] D) (φ : D →ₗ[k] k) (t : C ⊗[k] C) :
    rightSlice φ (TensorProduct.map f f t) =
      f (rightSlice (φ.comp f) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul x y => simp [rightSlice]

variable {M : Type*} [AddCommGroup M]

/-- Coefficient extraction on an additive group algebra, as a linear functional. -/
noncomputable def agaCoeff (m : M) : AddMonoidAlgebra k M →ₗ[k] k :=
  { toFun := fun x => x.coeff m
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

omit [AddCommGroup M] in
@[simp] theorem agaCoeff_apply (m : M) (x : AddMonoidAlgebra k M) :
    agaCoeff m x = x.coeff m := by
  rfl

/-- Pair two coefficient functionals after identifying the tensor square with the product group
algebra. -/
noncomputable def agaCoeffPair (a b : M)
    (t : AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k M) : k :=
  ((AddMonoidAlgebra.tensorEquiv k) t).coeff (a, b)

/-- Comultiplication of an additive group algebra is supported on the diagonal. -/
theorem agaCoeffPair_comul [DecidableEq M]
    (x : AddMonoidAlgebra k M) (a b : M) :
    agaCoeffPair a b (Coalgebra.comul (R := k) x) =
      if a = b then x.coeff a else 0 := by
  classical
  simpa [agaCoeffPair] using
    (AlgebraicGroupCrossHomFinite.tensorEquiv_comul_coeff k x a b)

/-- Slicing group-algebra comultiplication against one coefficient extracts exactly its diagonal
monomial. -/
theorem rightSlice_agaCoeff_comul (x : AddMonoidAlgebra k M) (m : M) :
    rightSlice (agaCoeff m) (Coalgebra.comul (R := k) x) =
      x.coeff m • AddMonoidAlgebra.single m 1 := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      exact (add_smul (x.coeff m) (y.coeff m)
        (AddMonoidAlgebra.single m (1 : k))).symm
  | single a c =>
      rw [AddMonoidAlgebra.comul_single]
      by_cases ham : m = a
      · subst a
        simp [rightSlice]
      · simp [rightSlice, ham]

/-- Contracting a tensor before an additive-group-algebra map is coefficientwise the same as
mapping both legs and then extracting the corresponding coefficient pair. -/
theorem coeff_map_rightSlice
    (f : C →ₐc[k] AddMonoidAlgebra k M) (t : C ⊗[k] C) (a b : M) :
    agaCoeff a
        (f (rightSlice ((agaCoeff b).comp f.toLinearMap) t)) =
      agaCoeffPair a b
        (TensorProduct.map f.toLinearMap f.toLinearMap t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [agaCoeffPair]
  | add x y hx hy => simpa [agaCoeffPair] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [rightSlice_tmul]
      change agaCoeff a (f (((f y).coeff b) • x)) = _
      rw [map_smul, map_smul]
      change (f y).coeff b * (f x).coeff a = _
      rw [TensorProduct.map_tmul]
      change (f y).coeff b * (f x).coeff a =
        ((AddMonoidAlgebra.tensorEquiv k) (f x ⊗ₜ[k] f y)).coeff (a, b)
      rw [AlgebraicGroupCrossHomFinite.tensorEquiv_tmul_coeff]
      exact mul_comm _ _

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- An injective bialgebra morphism reflects group-like elements. -/
theorem isGroupLike_of_injective_map
    {A B : Type*} [CommRing A] [CommRing B] [Bialgebra k A] [Bialgebra k B]
    (f : A →ₐc[k] B) (hf : Function.Injective f)
    {x : A} (hx : IsGroupLikeElem k (f x)) : IsGroupLikeElem k x := by
  constructor
  · have h := DFunLike.congr_fun (BialgHom.counitAlgHom_comp f) x
    change Coalgebra.counit (R := k) (f x) = Coalgebra.counit (R := k) x at h
    exact h ▸ hx.counit_eq_one
  · apply TensorProduct.map_injective_of_flat_flat f.toLinearMap f.toLinearMap hf hf
    change TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) x) =
      TensorProduct.map f.toLinearMap f.toLinearMap (x ⊗ₜ[k] x)
    have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) x
    change TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) x) = Coalgebra.comul (R := k) (f x) at hmap
    rw [hmap, TensorProduct.map_tmul, hx.comul_eq_tmul_self]
    rfl

/-- Every grading monomial occurring in the image of an injective Hopf map into a group algebra
already has a group-like preimage. -/
theorem exists_groupLike_preimage_of_coeff_ne_zero
    (f : C →ₐc[k] AddMonoidAlgebra k M) (hf : Function.Injective f)
    (x : C) (m : M) (hm : (f x).coeff m ≠ 0) :
    ∃ y : C, IsGroupLikeElem k y ∧ f y = AddMonoidAlgebra.single m 1 := by
  classical
  let c : k := (f x).coeff m
  let φ : C →ₗ[k] k := (agaCoeff m).comp f.toLinearMap
  let y : C := c⁻¹ • rightSlice φ (Coalgebra.comul (R := k) x)
  have hfy : f y = AddMonoidAlgebra.single m 1 := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro a
    change agaCoeff a (f y) = agaCoeff a (AddMonoidAlgebra.single m 1)
    rw [show y = c⁻¹ • rightSlice φ (Coalgebra.comul (R := k) x) by rfl,
      map_smul, map_smul]
    change c⁻¹ * agaCoeff a
      (f (rightSlice φ (Coalgebra.comul (R := k) x))) = _
    rw [coeff_map_rightSlice]
    have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) x
    change TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) x) = Coalgebra.comul (R := k) (f x) at hmap
    rw [hmap, agaCoeffPair_comul]
    by_cases ham : a = m
    · subst a
      simp [c, hm]
    · simp [ham]
  refine ⟨y, ?_, hfy⟩
  have hcounit : Coalgebra.counit (R := k) y = 1 := by
    have h := DFunLike.congr_fun (BialgHom.counitAlgHom_comp f) y
    change Coalgebra.counit (R := k) (f y) = Coalgebra.counit (R := k) y at h
    rw [hfy, AddMonoidAlgebra.counit_single] at h
    simpa using h.symm
  refine ⟨hcounit, ?_⟩
  apply TensorProduct.map_injective_of_flat_flat f.toLinearMap f.toLinearMap hf hf
  change TensorProduct.map f.toLinearMap f.toLinearMap
      (Coalgebra.comul (R := k) y) =
    TensorProduct.map f.toLinearMap f.toLinearMap (y ⊗ₜ[k] y)
  have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) y
  change TensorProduct.map f.toLinearMap f.toLinearMap
      (Coalgebra.comul (R := k) y) = Coalgebra.comul (R := k) (f y) at hmap
  rw [hmap, TensorProduct.map_tmul]
  change Coalgebra.comul (R := k) (f y) = f y ⊗ₜ[k] f y
  rw [hfy]
  change Coalgebra.comul (R := k) (AddMonoidAlgebra.single m (1 : k)) =
    AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] AddMonoidAlgebra.single m (1 : k)
  rw [AddMonoidAlgebra.comul_single]
  simp

/-- A commutative Hopf algebra embedding into both a group algebra and a symmetric algebra
contains only scalars. -/
theorem exists_eq_algebraMap_of_injective_group_symmetric
    {V ι : Type*} [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V)
    (f : C →ₐc[k] AddMonoidAlgebra k M) (hf : Function.Injective f)
    (g : C →ₐc[k] SymmetricAlgebra k V) (hg : Function.Injective g)
    (x : C) :
    ∃ c : k, x = algebraMap k C c := by
  classical
  have hoff : ∀ m : M, m ≠ 0 → (f x).coeff m = 0 := by
    intro m hm
    by_contra hcoeff
    obtain ⟨y, hy, hfy⟩ :=
      exists_groupLike_preimage_of_coeff_ne_zero f hf x m hcoeff
    have hgy : IsGroupLikeElem k (g y) := hy.map g
    have hgy1 : g y = 1 := symmetric_groupLike_eq_one b (g y) hgy
    have hy1 : y = 1 := by
      apply hg
      simpa using hgy1
    have hsingle : AddMonoidAlgebra.single m (1 : k) = 1 := by
      rw [← hfy, hy1, map_one]
    have hcoeffm := congrArg (fun z : AddMonoidAlgebra k M => z.coeff m) hsingle
    have : m = 0 := by
      by_contra hm'
      rw [AddMonoidAlgebra.one_def] at hcoeffm
      simp [hm'] at hcoeffm
    exact hm this
  refine ⟨(f x).coeff 0, hf ?_⟩
  change f x = f.toAlgHom (algebraMap k C ((f x).coeff 0))
  rw [f.toAlgHom.commutes]
  change f x = AddMonoidAlgebra.single 0 ((f x).coeff 0)
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · simp [hoff m hm, hm]

/-- Under the same two embeddings, the scalar map onto the common Hopf algebra is surjective. -/
theorem algebraMap_surjective_of_injective_group_symmetric
    {V ι : Type*} [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V)
    (f : C →ₐc[k] AddMonoidAlgebra k M) (hf : Function.Injective f)
    (g : C →ₐc[k] SymmetricAlgebra k V) (hg : Function.Injective g) :
    Function.Surjective (algebraMap k C) := by
  intro x
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_injective_group_symmetric b f hf g hg x
  exact ⟨c, hc.symm⟩

/-- Injective group-algebra and symmetric-algebra Hopf-coordinate images intersect only in the
same scalar.  This constructs the common-factor conclusion directly inside the ambient Hopf
algebra, without requiring a pre-existing Hopf structure on the set-theoretic image intersection. -/
theorem group_symmetric_image_intersection_eq_scalars
    {H V ι : Type*} [CommRing H] [HopfAlgebra k H]
    [AddCommGroup V] [Module k V]
    (basis : Module.Basis ι k V)
    (f : AddMonoidAlgebra k M →ₐc[k] H) (hf : Function.Injective f)
    (g : SymmetricAlgebra k V →ₐc[k] H) (hg : Function.Injective g)
    (a : AddMonoidAlgebra k M) (b : SymmetricAlgebra k V)
    (hab : f a = g b) :
    ∃ c : k, a = algebraMap k (AddMonoidAlgebra k M) c ∧
      b = algebraMap k (SymmetricAlgebra k V) c := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective f.toLinearMap
    (LinearMap.ker_eq_bot.mpr hf)
  have hlf : ∀ x, l (f.toLinearMap x) = x := by
    intro x
    have h := DFunLike.congr_fun hl x
    simpa using h
  have hoff : ∀ m : M, m ≠ 0 → a.coeff m = 0 := by
    intro m hm
    by_contra hcoeff
    let c : k := a.coeff m
    let φ : H →ₗ[k] k := (agaCoeff m).comp l
    let y : H := c⁻¹ • rightSlice φ (Coalgebra.comul (R := k) (f a))
    have hφ : φ.comp f.toLinearMap = agaCoeff m := by
      apply LinearMap.ext
      intro x
      change (agaCoeff m) (l (f.toLinearMap x)) = (agaCoeff m) x
      rw [hlf]
    have hfcom := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) a
    change TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) a) = Coalgebra.comul (R := k) (f a) at hfcom
    have hyf : y = f (AddMonoidAlgebra.single m 1) := by
      rw [show y = c⁻¹ • rightSlice φ (Coalgebra.comul (R := k) (f a)) by rfl,
        ← hfcom, rightSlice_map, hφ, rightSlice_agaCoeff_comul]
      rw [← map_smul]
      simp [c, hcoeff]
      rfl
    let b' : SymmetricAlgebra k V :=
      c⁻¹ • rightSlice (φ.comp g.toLinearMap) (Coalgebra.comul (R := k) b)
    have hgcom := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom g) b
    change TensorProduct.map g.toLinearMap g.toLinearMap
        (Coalgebra.comul (R := k) b) = Coalgebra.comul (R := k) (g b) at hgcom
    have hyg : y = g b' := by
      rw [show y = c⁻¹ • rightSlice φ (Coalgebra.comul (R := k) (f a)) by rfl,
        hab, ← hgcom, rightSlice_map]
      simp [b']
      rfl
    have hmono : IsGroupLikeElem k (AddMonoidAlgebra.single m (1 : k)) := by
      constructor
      · simp
      · simp [AddMonoidAlgebra.comul_single]
    have hy : IsGroupLikeElem k y := by
      rw [hyf]
      exact hmono.map f
    have hgb' : IsGroupLikeElem k (g b') := by
      rw [← hyg]
      exact hy
    have hb' : IsGroupLikeElem k b' := isGroupLike_of_injective_map g hg hgb'
    have hb'1 : b' = 1 := symmetric_groupLike_eq_one basis b' hb'
    have hfmono : f (AddMonoidAlgebra.single m (1 : k)) = 1 := by
      rw [← hyf, hyg, hb'1, map_one]
    have hmono1 : AddMonoidAlgebra.single m (1 : k) = 1 := by
      apply hf
      simpa using hfmono
    have hmcoeff := congrArg
      (fun z : AddMonoidAlgebra k M => z.coeff m) hmono1
    rw [AddMonoidAlgebra.one_def] at hmcoeff
    have hleft : (AddMonoidAlgebra.single m (1 : k)).coeff m = 1 := by simp
    have hright : (Finsupp.single (0 : M) (1 : k)) m = 0 := by simp [hm]
    exact one_ne_zero (hleft.symm.trans (hmcoeff.trans hright))
  let c : k := a.coeff 0
  have ha : a = algebraMap k (AddMonoidAlgebra k M) c := by
    change a = AddMonoidAlgebra.single 0 c
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    by_cases hm : m = 0
    · subst m
      simp [c]
    · simp [hoff m hm, hm]
  refine ⟨c, ha, ?_⟩
  apply hg
  calc
    g b = f a := hab.symm
    _ = f (algebraMap k (AddMonoidAlgebra k M) c) := by rw [ha]
    _ = algebraMap k H c := f.toAlgHom.commutes c
    _ = g (algebraMap k (SymmetricAlgebra k V) c) := (g.toAlgHom.commutes c).symm

end

end GaloisForLFunctions.HTGeometry
