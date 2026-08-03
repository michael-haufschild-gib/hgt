import GaloisForLFunctions.RHTower.CyclicModuleCokernel
import GaloisForLFunctions.RHTower.KRealClosedCokernel
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closed-range cokernels of Real cyclic modules

The CCM relative cyclic module is the quotient by the topological closure of the restriction
range, degree by degree.  This file supplies that operation exactly.  A topology is placed on
every degree of a cyclic module; all simplicial maps and cyclic rotations are required to be
continuous.  Naturality maps restriction ranges into restriction ranges, and continuity then
maps their closures into their closures.  Hence every cyclic operator descends to the closed
cokernel and all Connes relations remain valid.

If the target Real/quaternionic involutions are continuous, their structures descend as well.
This is a cyclic-module cokernel, not an algebra quotient: no multiplication is asserted on the
quotient.  The separate two-sidedness theorem in `KRealCyclicModule` is the exact gate for any
such assertion.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower
namespace CyclicModule

/-- Compatible topologies and continuous structure maps on a complex cyclic module. -/
structure Topology (X : CyclicModule ℂ) where
  topology : ∀ j : SimplexCategoryGenRelᵒᵖ, TopologicalSpace (X.simplicial.obj j)
  continuousAdd : ∀ j,
    @ContinuousAdd (X.simplicial.obj j) (topology j) inferInstance
  continuousSMul : ∀ j,
    @ContinuousSMul ℂ (X.simplicial.obj j) inferInstance inferInstance
      (topology j)
  simplicial_continuous : ∀ {j k} (g : j ⟶ k),
    @Continuous (X.simplicial.obj j) (X.simplicial.obj k)
      (topology j) (topology k) (X.simplicial.map g)
  cyclic_continuous : ∀ n,
    @Continuous (X.simplicial.degree n) (X.simplicial.degree n)
      (topology (.op (.mk n))) (topology (.op (.mk n))) (X.cyclic n)

namespace Topology

/-- Closure of a cyclic morphism's range in one target degree. -/
def closedRange {X Y : CyclicModule ℂ} (f : Hom X Y) (TY : Topology Y)
    (j : SimplexCategoryGenRelᵒᵖ) : Submodule ℂ (Y.simplicial.obj j) := by
  letI := TY.topology j
  letI := TY.continuousAdd j
  letI := TY.continuousSMul j
  exact (LinearMap.range (f.simplicial.app j).hom).topologicalClosure

end Topology

/-- Degreewise closed-range quotient of the underlying simplicial object. -/
def Hom.closedCokernelSimplicial {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) : PresentedSimplicialObject (ModuleCat ℂ) where
  obj j := ModuleCat.of ℂ (Y.simplicial.obj j ⧸ TY.closedRange f j)
  map {j k} g := ModuleCat.ofHom <|
    (TY.closedRange f j).mapQ (TY.closedRange f k)
      (Y.simplicial.map g).hom (by
        letI := TY.topology j
        letI := TY.continuousAdd j
        letI := TY.continuousSMul j
        letI := TY.topology k
        letI := TY.continuousAdd k
        letI := TY.continuousSMul k
        intro y hy
        have hm : Set.MapsTo (Y.simplicial.map g)
            (LinearMap.range (f.simplicial.app j).hom)
            (LinearMap.range (f.simplicial.app k).hom) := by
          intro z hz
          obtain ⟨x, rfl⟩ := hz
          refine ⟨X.simplicial.map g x, ?_⟩
          have h := f.simplicial.naturality g
          simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x
        exact hm.closure (TY.simplicial_continuous g) hy)
  map_id j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := (TY.closedRange f j).mkQ_surjective q
    change (TY.closedRange f j).mkQ (Y.simplicial.map (𝟙 j) y) =
      (TY.closedRange f j).mkQ y
    rw [Y.simplicial.map_id]
    rfl
  map_comp {i j k} g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := (TY.closedRange f i).mkQ_surjective q
    change (TY.closedRange f k).mkQ (Y.simplicial.map (g ≫ h) y) =
      (TY.closedRange f k).mkQ (Y.simplicial.map h (Y.simplicial.map g y))
    rw [Y.simplicial.map_comp]
    rfl

/-- Natural quotient projection to the closed simplicial cokernel. -/
def Hom.closedCokernelProjection {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) :
    Y.simplicial ⟶ f.closedCokernelSimplicial TY where
  app j := ModuleCat.ofHom (TY.closedRange f j).mkQ
  naturality {j k} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl

/-- Cyclic rotation induced on the degreewise closed cokernel. -/
def Hom.closedCokernelCyclic {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (n : ℕ) :
    (f.closedCokernelSimplicial TY).degree n ⟶
      (f.closedCokernelSimplicial TY).degree n :=
  ModuleCat.ofHom <| (TY.closedRange f (.op (.mk n))).mapQ
    (TY.closedRange f (.op (.mk n))) (Y.cyclic n).hom (by
      letI := TY.topology (.op (.mk n))
      letI := TY.continuousAdd (.op (.mk n))
      letI := TY.continuousSMul (.op (.mk n))
      intro y hy
      have hm : Set.MapsTo (Y.cyclic n)
          (LinearMap.range (f.simplicial.app (.op (.mk n))).hom)
          (LinearMap.range (f.simplicial.app (.op (.mk n))).hom) := by
        intro z hz
        obtain ⟨x, rfl⟩ := hz
        refine ⟨X.cyclic n x, ?_⟩
        have h := f.cyclic_naturality n
        simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x
      exact hm.closure (TY.cyclic_continuous n) hy)

@[simp]
theorem Hom.closedCokernelCyclic_mkQ {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (n : ℕ) (y : Y.simplicial.degree n) :
    f.closedCokernelCyclic TY n
        ((TY.closedRange f (.op (.mk n))).mkQ y) =
      (TY.closedRange f (.op (.mk n))).mkQ (Y.cyclic n y) :=
  rfl

/-- Iterated cyclic rotation descends through topological closure. -/
theorem Hom.closedCokernelCyclic_iterate_mkQ {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (n k : ℕ)
    (y : Y.simplicial.degree n) :
    categoricalEndIterate (f.closedCokernelCyclic TY n) k
        ((TY.closedRange f (.op (.mk n))).mkQ y) =
      (TY.closedRange f (.op (.mk n))).mkQ
        (categoricalEndIterate (Y.cyclic n) k y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [categoricalEndIterate]
      change f.closedCokernelCyclic TY n
          (categoricalEndIterate (f.closedCokernelCyclic TY n) k
            ((TY.closedRange f (.op (.mk n))).mkQ y)) = _
      rw [ih]
      rfl

/-- Closed-range cokernel in the category of complex cyclic modules. -/
def Hom.closedCokernel {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) : CyclicModule ℂ where
  simplicial := f.closedCokernelSimplicial TY
  cyclic := f.closedCokernelCyclic TY
  cyclic_order n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := (TY.closedRange f (.op (.mk n))).mkQ_surjective q
    change categoricalEndIterate (f.closedCokernelCyclic TY n) (n + 1)
        ((TY.closedRange f (.op (.mk n))).mkQ y) = _
    rw [f.closedCokernelCyclic_iterate_mkQ, Y.cyclic_order]
    rfl
  cyclic_face_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (TY.closedRange f (.op (.mk (n + 1)))).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_face_zero n)) y
    exact congrArg (TY.closedRange f (.op (.mk n))).mkQ hy
  cyclic_face_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (TY.closedRange f (.op (.mk (n + 1)))).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_face_succ n i)) y
    exact congrArg (TY.closedRange f (.op (.mk n))).mkQ hy
  cyclic_degeneracy_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := (TY.closedRange f (.op (.mk n))).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_degeneracy_zero n)) y
    exact congrArg (TY.closedRange f (.op (.mk (n + 1)))).mkQ hy
  cyclic_degeneracy_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := (TY.closedRange f (.op (.mk n))).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_degeneracy_succ n i)) y
    exact congrArg (TY.closedRange f (.op (.mk (n + 1)))).mkQ hy

/-- Continuity of a degreewise Real/quaternionic structure. -/
structure KRealTopology {odd : Bool} {X : CyclicModule ℂ}
    (KX : KReal odd X) (TX : Topology X) : Prop where
  real_continuous : ∀ n,
    @Continuous (X.simplicial.degree n) (X.simplicial.degree n)
      (TX.topology (.op (.mk n))) (TX.topology (.op (.mk n)))
      (KX.real n).sigma

/-- Real/quaternionic structure on the closed cyclic cokernel. -/
def KRealHom.closedCokernelKReal {odd : Bool} {X Y : CyclicModule ℂ}
    {KX : KReal odd X} {KY : KReal odd Y} (f : KRealHom KX KY)
    (TY : Topology Y) (hTY : KRealTopology KY TY) :
    KReal odd (f.toHom.closedCokernel TY) where
  real n := by
    letI := TY.topology (.op (.mk n))
    letI := TY.continuousAdd (.op (.mk n))
    letI := TY.continuousSMul (.op (.mk n))
    exact KRealStructure.closedCokernel
      (KX.real n) (KY.real n) (f.degree n) (hTY.real_continuous n)
  face_naturality n i q := by
    obtain ⟨y, rfl⟩ :=
      (TY.closedRange f.toHom (.op (.mk (n + 1)))).mkQ_surjective q
    change
      (TY.closedRange f.toHom (.op (.mk n))).mkQ
          ((KY.real n).sigma (Y.simplicial.δ i y)) =
        (TY.closedRange f.toHom (.op (.mk n))).mkQ
          (Y.simplicial.δ i ((KY.real (n + 1)).sigma y))
    rw [KY.face_naturality]
  degeneracy_naturality n i q := by
    obtain ⟨y, rfl⟩ :=
      (TY.closedRange f.toHom (.op (.mk n))).mkQ_surjective q
    change
      (TY.closedRange f.toHom (.op (.mk (n + 1)))).mkQ
          ((KY.real (n + 1)).sigma (Y.simplicial.σ i y)) =
        (TY.closedRange f.toHom (.op (.mk (n + 1)))).mkQ
          (Y.simplicial.σ i ((KY.real n).sigma y))
    rw [KY.degeneracy_naturality]
  cyclic_naturality n q := by
    obtain ⟨y, rfl⟩ :=
      (TY.closedRange f.toHom (.op (.mk n))).mkQ_surjective q
    change
      (TY.closedRange f.toHom (.op (.mk n))).mkQ
          ((KY.real n).sigma (Y.cyclic n y)) =
        (TY.closedRange f.toHom (.op (.mk n))).mkQ
          (Y.cyclic n ((KY.real n).sigma y))
    rw [KY.cyclic_naturality]

end CyclicModule
end RHTower
end GaloisForLFunctions
