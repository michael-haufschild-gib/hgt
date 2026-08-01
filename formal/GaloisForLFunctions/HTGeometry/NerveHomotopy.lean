import GaloisForLFunctions.HTGeometry.NerveProductComparison
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
# A functor out of a cylinder is a simplicial homotopy of nerves

The two-element linear order is the categorical interval, and its nerve is the standard `1`-simplex.
A functor out of `C × [1]` therefore gives a map `nerve C ⊗ Δ[1] ⟶ nerve D`, whose two ends are the
nerves of the two restrictions: a simplicial homotopy.

Applied to a deformation retraction of a poset — a monotone retraction together with a monotone
homotopy to the identity — this makes the nerve of the poset simplicially homotopy equivalent to the
nerve of its image.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial SSet

universe u

/-- The categorical interval: the two-element linear order. -/
abbrev catInterval : Type u := ULift.{u} (Fin 2)

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- The inclusion of `C` into the cylinder at a chosen end. -/
def cylinderIncl (C : Type u) [SmallCategory C] (i : catInterval.{u}) :
    CategoryTheory.Functor C (C × catInterval.{u}) :=
  (CategoryTheory.Functor.id C).prod' ((CategoryTheory.Functor.const C).obj i)

/-- **The nerve of the interval is the standard `1`-simplex.** -/
noncomputable def intervalIso :
    (Δ[1] : SSet.{u}) ≅ nerveFunctor.obj (Cat.of catInterval.{u}) :=
  stdSimplex.isoNerve.{u} 1

/-- **The nerve of a constant functor is a constant simplicial map.** -/
theorem nerveFunctor_map_const (d : D) :
    nerveFunctor.map ((CategoryTheory.Functor.const C).obj d).toCatHom
      = SSet.const (X := nerveFunctor.obj (Cat.of C)) (Y := nerveFunctor.obj (Cat.of D))
        (ComposableArrows.mk₀ d) := by
  ext n x
  rfl

/-- **The initial vertex of the standard `1`-simplex is the initial object of the interval.** -/
theorem intervalIso_hom_app_zero :
    intervalIso.{u}.hom.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
      = ComposableArrows.mk₀ (ULift.up (0 : Fin 2)) :=
  ComposableArrows.ext₀ rfl

/-- **The final vertex of the standard `1`-simplex is the final object of the interval.** -/
theorem intervalIso_hom_app_one :
    intervalIso.{u}.hom.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)
      = ComposableArrows.mk₀ (ULift.up (1 : Fin 2)) :=
  ComposableArrows.ext₀ rfl

/-- The nerve of the cylinder inclusion, followed by the comparison map, is the inclusion of one end
of the tensor of the nerve with the nerve of the interval. -/
theorem cylinderIncl_comp_comparison (i : catInterval.{u}) :
    nerveFunctor.map (cylinderIncl C i).toCatHom ≫ nerveProductComparison C catInterval.{u}
      = lift (𝟙 (nerveFunctor.obj (Cat.of C)))
          (SSet.const (X := nerveFunctor.obj (Cat.of C))
            (Y := nerveFunctor.obj (Cat.of catInterval.{u})) (ComposableArrows.mk₀ i)) := by
  rw [nerveProductComparison, comp_lift, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 1

/-- A monotone map out of a product of preordered types, as a functor out of the product category.
The two product structures on a pair of preorders — the preorder on the product and the product of
the two categories — are not the same, and it is the latter that a cylinder is built from. -/
def prodPreorderFunctor {α β γ : Type u} [Preorder α] [Preorder β] [Preorder γ]
    (H : α × β →o γ) : CategoryTheory.Functor (α × β) γ where
  obj := H
  map f := CategoryTheory.homOfLE
    (H.monotone ⟨CategoryTheory.leOfHom f.1, CategoryTheory.leOfHom f.2⟩)

/-- **A functor out of a cylinder is a simplicial homotopy between the nerves of its two ends.** -/
noncomputable def nerveHomotopy (H : CategoryTheory.Functor (C × catInterval.{u}) D) :
    SSet.Homotopy
      (nerveFunctor.map ((cylinderIncl C (ULift.up 0)).comp H).toCatHom)
      (nerveFunctor.map ((cylinderIncl C (ULift.up 1)).comp H).toCatHom) where
  h := (nerveFunctor.obj (Cat.of C) ◁ intervalIso.{u}.hom)
    ≫ nerveTensorMap C catInterval.{u} D H
  h₀ := by
    have hend : ι₀ ≫ (nerveFunctor.obj (Cat.of C) ◁ intervalIso.{u}.hom)
        = nerveFunctor.map (cylinderIncl C (ULift.up 0)).toCatHom
          ≫ nerveProductComparison C catInterval.{u} := by
      rw [cylinderIncl_comp_comparison, ι₀, lift_whiskerLeft, SSet.const_comp,
        intervalIso_hom_app_zero]
      rfl
    rw [← Category.assoc, hend, nerveTensorMap, Category.assoc,
      ← Category.assoc (nerveProductComparison C catInterval.{u}), IsIso.hom_inv_id,
      Category.id_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  rel := by
    ext n ⟨x, y⟩
    exact x.2.elim
  h₁ := by
    have hend : ι₁ ≫ (nerveFunctor.obj (Cat.of C) ◁ intervalIso.{u}.hom)
        = nerveFunctor.map (cylinderIncl C (ULift.up 1)).toCatHom
          ≫ nerveProductComparison C catInterval.{u} := by
      rw [cylinderIncl_comp_comparison, ι₁, lift_whiskerLeft, SSet.const_comp,
        intervalIso_hom_app_one]
      rfl
    rw [← Category.assoc, hend, nerveTensorMap, Category.assoc,
      ← Category.assoc (nerveProductComparison C catInterval.{u}), IsIso.hom_inv_id,
      Category.id_comp, ← CategoryTheory.Functor.map_comp]
    rfl

/-! ## Deformation retracts -/

/-- **A strong deformation retraction of simplicial sets**: a retraction that is a section on the
nose, together with a simplicial homotopy from the identity to the other composite. -/
structure SSetDeformationRetract (X Y : SSet.{u}) where
  /-- The inclusion of the retract. -/
  incl : Y ⟶ X
  /-- The retraction. -/
  retr : X ⟶ Y
  /-- The retraction is a left inverse of the inclusion on the nose. -/
  incl_retr : incl ≫ retr = 𝟙 Y
  /-- The other composite is homotopic to the identity. -/
  homotopy : SSet.Homotopy (𝟙 X) (retr ≫ incl)

/-- **A deformation retract induces an isomorphism on simplicial homology**, in every degree and
with any coefficients: the retraction is inverted by the inclusion because one composite is the
identity on the nose and the other is homotopic to it. -/
noncomputable def SSetDeformationRetract.homologyIso {X Y : SSet.{u}}
    (d : SSetDeformationRetract X Y) {C : Type*} [Category C] [Limits.HasCoproducts.{u} C]
    [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ) :
    X.homology R n ≅ Y.homology R n where
  hom := SSet.homologyMap d.retr R n
  inv := SSet.homologyMap d.incl R n
  hom_inv_id := by
    rw [← SSet.homologyMap_comp, ← d.homotopy.congr_homologyMap R n, SSet.homologyMap_id]
  inv_hom_id := by
    rw [← SSet.homologyMap_comp, d.incl_retr, SSet.homologyMap_id]

/-- **An order isomorphism is an isomorphism of the associated categories.** -/
def orderIsoCatIso {α β : Type u} [Preorder α] [Preorder β] (e : α ≃o β) :
    Cat.of α ≅ Cat.of β where
  hom := (Monotone.functor e.monotone).toCatHom
  inv := (Monotone.functor e.symm.monotone).toCatHom
  hom_inv_id := by
    refine Cat.ext ?_
    show (Monotone.functor e.monotone).comp (Monotone.functor e.symm.monotone)
      = CategoryTheory.Functor.id α
    exact CategoryTheory.Functor.ext (fun a => e.symm_apply_apply a)
      (fun _ _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    refine Cat.ext ?_
    show (Monotone.functor e.symm.monotone).comp (Monotone.functor e.monotone)
      = CategoryTheory.Functor.id β
    exact CategoryTheory.Functor.ext (fun b => e.apply_symm_apply b)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- **Order-isomorphic posets have isomorphic nerves.** -/
noncomputable def orderIsoNerveIso {α β : Type u} [Preorder α] [Preorder β] (e : α ≃o β) :
    nerveFunctor.obj (Cat.of α) ≅ nerveFunctor.obj (Cat.of β) :=
  nerveFunctor.mapIso (orderIsoCatIso e)

/-! ## Dimension and homology vanishing -/

/-- **Homology vanishes above the dimension.**  A simplicial set with no nondegenerate simplices in
degree `d` or above has zero homology there, with any coefficients: the normalized chain complex
vanishes in those degrees and computes the same homology. -/
theorem isZero_homology_of_hasDimensionLT (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d]
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) (hn : d ≤ n) : Limits.IsZero (X.homology R n) := by
  refine Limits.IsZero.of_iso ?_ ((X.homotopyEquivNormalizedChainComplex R).toHomologyIso n)
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d hn)

/-- **A bound on strict chains bounds the dimension of the nerve.**  A nondegenerate `n`-simplex of
the nerve of a partial order is a strictly increasing family of `n + 1` elements, so a poset whose
strict chains have at most `m` members has a nerve of dimension below `m`. -/
theorem hasDimensionLT_nerve_of_chain_bound {P : Type u} [PartialOrder P] (m : ℕ)
    (hbound : ∀ (n : ℕ) (f : Fin (n + 1) → P), StrictMono f → n + 1 ≤ m) :
    SSet.HasDimensionLT (nerveFunctor.obj (Cat.of P)) m where
  degenerate_eq_top n hn := by
    rw [Set.top_eq_univ, Set.eq_univ_iff_forall]
    intro s
    by_contra hs
    have hnd : s ∈ (nerve P).nonDegenerate n :=
      (SSet.mem_nonDegenerate_iff_notMem_degenerate (X := nerve P) s).2 hs
    have := hbound n _
      ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono (X := P) (n := n) s).1 hnd)
    omega

/-! ## Connectedness -/

/-- **Comparable vertices are joined by an edge of the nerve.** -/
def nerveEdgeOfLE {P : Type u} [PartialOrder P] {a b : P} (h : a ≤ b) :
    SSet.Edge (X := nerve P) (ComposableArrows.mk₀ a) (ComposableArrows.mk₀ b) :=
  ⟨ComposableArrows.mk₁ (CategoryTheory.homOfLE h), ComposableArrows.ext₀ rfl,
    ComposableArrows.ext₀ rfl⟩

/-- **Comparable vertices lie in the same connected component.** -/
theorem pi0_mk_eq_of_comparable {P : Type u} [PartialOrder P] {a b : P} (h : a ≤ b ∨ b ≤ a) :
    SSet.π₀.mk (X := nerve P) (ComposableArrows.mk₀ a)
      = SSet.π₀.mk (X := nerve P) (ComposableArrows.mk₀ b) := by
  rcases h with h | h
  · exact SSet.π₀.sound (nerveEdgeOfLE h)
  · exact (SSet.π₀.sound (nerveEdgeOfLE h)).symm

/-- **A poset in which any two elements are joined by a zigzag of comparabilities has a connected
nerve.** -/
theorem isPreconnected_nerve_of_zigzag {P : Type u} [PartialOrder P]
    (h : ∀ a b : P, Relation.ReflTransGen (fun x y : P => x ≤ y ∨ y ≤ x) a b) :
    SSet.IsPreconnected (nerve P) := by
  have key : ∀ a b : P, SSet.π₀.mk (X := nerve P) (ComposableArrows.mk₀ a)
      = SSet.π₀.mk (X := nerve P) (ComposableArrows.mk₀ b) := by
    intro a b
    induction h a b with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (pi0_mk_eq_of_comparable hstep)
  constructor
  intro x y
  induction x with
  | mk x =>
    induction y with
    | mk y =>
      rw [show x = ComposableArrows.mk₀ (x.obj 0) from ComposableArrows.ext₀ rfl,
        show y = ComposableArrows.mk₀ (y.obj 0) from ComposableArrows.ext₀ rfl]
      exact key _ _

/-- **Zigzag connectedness passes to the opposite order.** -/
theorem zigzag_orderDual {α : Type u} [PartialOrder α]
    (h : ∀ a b : α, Relation.ReflTransGen (fun x y : α => x ≤ y ∨ y ≤ x) a b) (a b : αᵒᵈ) :
    Relation.ReflTransGen (fun x y : αᵒᵈ => x ≤ y ∨ y ≤ x) a b :=
  Relation.ReflTransGen.mono
    (p := fun x y : α => y ≤ x ∨ x ≤ y) (fun _ _ hxy => Or.symm hxy) _ _
    (h (OrderDual.ofDual a) (OrderDual.ofDual b))

end GaloisForLFunctions.HTGeometry
