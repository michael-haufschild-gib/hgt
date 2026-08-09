import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Relative law fibres under serial composition

This file formalizes the relative-fibre law in two complementary models.

* For pointed types, the homotopy fibre is the dependent pair of a source point and a path to the
  distinguished target point.  The fibre of the canonical map
  `fib (g ∘ f) → fib g` is canonically `fib f`.
* In the stable tangent model of cochain complexes, the shifted mapping-cone construction gives the
  exact triangle of the three relative fibres.  This is the octahedral composition triangle already
  proved in mathlib, shifted from cofibres to fibres.

The source-loss, parallel-repair, exact-cancellation, and split-inclusion counterexample clauses of
the paper card are also proved below.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.RelativeLawFiber

open CategoryTheory CategoryTheory.Limits

universe u v

/-! ## Pointed homotopy fibres -/

namespace PointedModel

/-- Homotopy fibre of a pointed map, represented as points equipped with a path to the basepoint. -/
def fiber {X Y : Pointed.{u}} (f : X ⟶ Y) : Pointed.{u} :=
  Pointed.of (⟨X.point, f.map_point⟩ : {x : X // f.toFun x = Y.point})

@[simp]
theorem fiber_point_val {X Y : Pointed.{u}} (f : X ⟶ Y) :
    (fiber f).point.1 = X.point :=
  rfl

/-- The canonical map `fib (g ∘ f) → fib g` induced by `f`. -/
def fiberMap {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (f ≫ g) ⟶ fiber g where
  toFun x := ⟨f.toFun x.1, by simpa using x.2⟩
  map_point := by
    apply Subtype.ext
    exact f.map_point

@[simp]
theorem fiberMap_apply_val {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : fiber (f ≫ g)) :
    (fiberMap f g x).1 = f.toFun x.1 :=
  rfl

/-- Canonical identification of `fib (fib(g ∘ f) → fib g)` with `fib f`.

This is the pointed-type realization of the serial relative-fibre sequence
`fib f → fib (g ∘ f) → fib g`.
-/
def fiberFiberMapEquiv {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (fiberMap f g) ≃ fiber f where
  toFun x := ⟨x.1.1, by
    have h := congrArg Subtype.val x.2
    exact h⟩
  invFun x := ⟨⟨x.1, by
      change g.toFun (f.toFun x.1) = Z.point
      rw [x.2, g.map_point]⟩, by
        apply Subtype.ext
        exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The serial relative-fibre equivalence preserves the distinguished point. -/
@[simp]
theorem fiberFiberMapEquiv_point {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberFiberMapEquiv f g (fiber (fiberMap f g)).point = (fiber f).point := by
  apply Subtype.ext
  rfl

/-- Pointed isomorphism form of the serial relative-fibre theorem. -/
def fiberFiberMapIso {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (fiberMap f g) ≅ fiber f :=
  Pointed.Iso.mk (fiberFiberMapEquiv f g) (fiberFiberMapEquiv_point f g)

end PointedModel

/-! ## Stable tangent exact triangle -/

namespace StableTangent

open CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [HasZeroObject C]

/-- Stable relative fibre of a cochain map: the mapping cone shifted by `-1`. -/
noncomputable abbrev fiber {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    HomotopyCategory C (ComplexShape.up ℤ) :=
  (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (-1 : ℤ)).obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone f))

/-- The octahedral composition triangle, shifted from cofibres to relative fibres. -/
noncomputable def relativeFiberTriangle {X Y Z : CochainComplex C ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (Triangle.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (-1 : ℤ)).obj
    (CochainComplex.mappingConeCompTriangleh f g)

/-- The stable tangent relative-fibre sequence is a distinguished, hence exact, triangle. -/
theorem relativeFiberTriangle_distinguished {X Y Z : CochainComplex C ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeFiberTriangle f g ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  exact Triangle.shift_distinguished _
    (HomotopyCategory.mappingConeCompTriangleh_distinguished f g) (-1 : ℤ)

/-- If the composite is an isomorphism, its mapping cone is zero in the homotopy category. -/
theorem isZero_mappingCone_comp_of_isIso {X Y Z : CochainComplex C ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso (f ≫ g)] :
    IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone (f ≫ g))) := by
  let T := CochainComplex.mappingCone.triangleh (f ≫ g)
  have hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
    HomotopyCategory.mappingCone_triangleh_distinguished (f ≫ g)
  apply Triangle.isZero₃_of_isIso₁ T hT
  change IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (f ≫ g))
  infer_instance

/-- Exact cancellation boundary: if `g ∘ f` is an isomorphism, then
`fib g ≃ (fib f)[1]`.  The displayed isomorphism is the connecting morphism of the shifted
octahedral triangle.
-/
noncomputable def cancellationIso {X Y Z : CochainComplex C ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso (f ≫ g)] :
    (relativeFiberTriangle f g).obj₃ ≅
      ((relativeFiberTriangle f g).obj₁)⟦(1 : ℤ)⟧ := by
  have hzeroCone := isZero_mappingCone_comp_of_isIso f g
  have hzero : IsZero (relativeFiberTriangle f g).obj₂ := by
    exact (CategoryTheory.shiftFunctor
      (HomotopyCategory C (ComplexShape.up ℤ)) (-1 : ℤ)).map_isZero hzeroCone
  have hT := relativeFiberTriangle_distinguished f g
  haveI : IsIso (relativeFiberTriangle f g).mor₃ :=
    (Triangle.isZero₂_iff_isIso₃ (relativeFiberTriangle f g) hT).1 hzero
  exact asIso (relativeFiberTriangle f g).mor₃

end StableTangent

/-! ## Source loss and parallel repair -/

section SourceLoss

variable {A B D : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass D]

/-- A source class killed by the first pointed additive observer stays killed after every serial
observer. -/
theorem sourceLoss_irreversible (f : A →+ B) (g : B →+ D) (x : A)
    (hx : f x = 0) : (g.comp f) x = 0 := by
  simp [hx]

end SourceLoss

section ParallelRepair

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable {I : Type*} {W : I → Type*}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- Joint map of a parallel observer family. -/
def jointMap (f : ∀ i, V →ₗ[k] W i) : V →ₗ[k] (∀ i, W i) where
  toFun x i := f i x
  map_add' x y := by ext i; exact map_add (f i) x y
  map_smul' a x := by ext i; exact map_smul (f i) a x

/-- Kernel of the joint observer is exactly the intersection of the component kernels. -/
theorem mem_ker_jointMap_iff (f : ∀ i, V →ₗ[k] W i) (x : V) :
    x ∈ LinearMap.ker (jointMap f) ↔ ∀ i, x ∈ LinearMap.ker (f i) := by
  change (fun i ↦ f i x) = 0 ↔ ∀ i, f i x = 0
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- Submodule form of the parallel-repair identity. -/
theorem ker_jointMap (f : ∀ i, V →ₗ[k] W i) :
    LinearMap.ker (jointMap f) = ⨅ i, LinearMap.ker (f i) := by
  ext x
  simp only [Submodule.mem_iInf]
  exact mem_ker_jointMap_iff f x

/-- Parallel observers separate source classes exactly when their kernel intersection is zero. -/
theorem jointMap_injective_iff (f : ∀ i, V →ₗ[k] W i) :
    Function.Injective (jointMap f) ↔ (⨅ i, LinearMap.ker (f i)) = ⊥ := by
  constructor
  · intro hf
    apply le_antisymm
    · intro x hx
      have hzero : jointMap f x = 0 := by
        apply (mem_ker_jointMap_iff f x).2
        simpa only [Submodule.mem_iInf] using hx
      have : x = 0 := hf (by simpa using hzero)
      exact this ▸ Submodule.zero_mem ⊥
    · exact bot_le
  · intro h x y hxy
    have hmem : x - y ∈ ⨅ i, LinearMap.ker (f i) := by
      rw [← ker_jointMap]
      change jointMap f (x - y) = 0
      rw [map_sub, hxy, sub_self]
    rw [h] at hmem
    have hsub : x - y = 0 := by simpa using hmem
    exact sub_eq_zero.mp hsub

end ParallelRepair

/-! ## Hostile split-inclusion countermodel -/

namespace SplitCountermodel

variable (k : Type*) [Field k]

/-- Inclusion that adds one observer-created target direction. -/
def inclusion : k →ₗ[k] k × k where
  toFun x := (x, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Retraction that removes the excess target direction. -/
def projection : k × k →ₗ[k] k where
  toFun x := x.1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Serial composition cancels the observer-created excess exactly. -/
@[simp]
theorem projection_comp_inclusion :
    (projection k).comp (inclusion k) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rfl

/-- The inclusion is not surjective. -/
theorem inclusion_not_surjective : ¬ Function.Surjective (inclusion k) := by
  intro h
  obtain ⟨x, hx⟩ := h (0, 1)
  have := congrArg Prod.snd hx
  simp only [inclusion] at this
  have hzeroone : (0 : k) = 1 := this
  exact zero_ne_one hzeroone

/-- The projection is not injective. -/
theorem projection_not_injective : ¬ Function.Injective (projection k) := by
  intro h
  have hx := h (show projection k (0, 0) = projection k (0, 1) by rfl)
  have := congrArg Prod.snd hx
  simp only at this
  have hzeroone : (0 : k) = 1 := this
  exact zero_ne_one hzeroone

/-- Exact hostile boundary: the composite is an equivalence although neither stage is. -/
theorem splitCancellation :
    (projection k).comp (inclusion k) = LinearMap.id ∧
      ¬ Function.Surjective (inclusion k) ∧
      ¬ Function.Injective (projection k) :=
  ⟨projection_comp_inclusion k, inclusion_not_surjective k, projection_not_injective k⟩

end SplitCountermodel

end HTGeometry.NomologicalHomotopyGeometry.RelativeLawFiber
