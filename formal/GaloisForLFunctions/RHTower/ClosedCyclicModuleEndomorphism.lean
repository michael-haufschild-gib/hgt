import GaloisForLFunctions.RHTower.ClosedCyclicModuleCokernel

/-!
# Continuous equivariant endomorphisms of closed cyclic cokernels

If cyclic endomorphisms of source and target intertwine a cyclic morphism, and
the target endomorphism is continuous degreewise, then it preserves the
closure of the range and descends to the exact closed cokernel.  The descended
maps retain full simplicial and cyclic naturality.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower.CyclicModule

/-- Degreewise quotient map induced by a continuous equivariant target
endomorphism. -/
def Hom.closedCokernelEndDegree {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (s : Hom X X) (t : Hom Y Y)
    (heq : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n))
          (s.simplicial.app (.op (.mk n)) x) =
        t.simplicial.app (.op (.mk n))
          (f.simplicial.app (.op (.mk n)) x))
    (ht : ∀ n,
      @Continuous (Y.simplicial.degree n) (Y.simplicial.degree n)
        (TY.topology (.op (.mk n))) (TY.topology (.op (.mk n)))
        (t.simplicial.app (.op (.mk n))))
    (n : ℕ) :
    (f.closedCokernel TY).simplicial.degree n →ₗ[ℂ]
      (f.closedCokernel TY).simplicial.degree n :=
  (TY.closedRange f (.op (.mk n))).mapQ
    (TY.closedRange f (.op (.mk n)))
    (t.simplicial.app (.op (.mk n))).hom (by
      letI := TY.topology (.op (.mk n))
      letI := TY.continuousAdd (.op (.mk n))
      letI := TY.continuousSMul (.op (.mk n))
      intro y hy
      have hm : Set.MapsTo (t.simplicial.app (.op (.mk n)))
          (LinearMap.range (f.simplicial.app (.op (.mk n))).hom)
          (LinearMap.range (f.simplicial.app (.op (.mk n))).hom) := by
        intro z hz
        obtain ⟨x, rfl⟩ := hz
        exact ⟨s.simplicial.app (.op (.mk n)) x, heq n x⟩
      exact hm.closure (ht n) hy)

@[simp]
theorem Hom.closedCokernelEndDegree_mkQ {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (s : Hom X X) (t : Hom Y Y)
    (heq : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n))
          (s.simplicial.app (.op (.mk n)) x) =
        t.simplicial.app (.op (.mk n))
          (f.simplicial.app (.op (.mk n)) x))
    (ht : ∀ n,
      @Continuous (Y.simplicial.degree n) (Y.simplicial.degree n)
        (TY.topology (.op (.mk n))) (TY.topology (.op (.mk n)))
        (t.simplicial.app (.op (.mk n))))
    (n : ℕ) (y : Y.simplicial.degree n) :
    f.closedCokernelEndDegree TY s t heq ht n
        ((TY.closedRange f (.op (.mk n))).mkQ y) =
      (TY.closedRange f (.op (.mk n))).mkQ
        (t.simplicial.app (.op (.mk n)) y) :=
  rfl

/-- Component over every object of the presented simplex category. -/
def Hom.closedCokernelEndComponent {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (s : Hom X X) (t : Hom Y Y)
    (heq : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n))
          (s.simplicial.app (.op (.mk n)) x) =
        t.simplicial.app (.op (.mk n))
          (f.simplicial.app (.op (.mk n)) x))
    (ht : ∀ n,
      @Continuous (Y.simplicial.degree n) (Y.simplicial.degree n)
        (TY.topology (.op (.mk n))) (TY.topology (.op (.mk n)))
        (t.simplicial.app (.op (.mk n)))) :
    ∀ a : SimplexCategoryGenRel,
      (f.closedCokernel TY).simplicial.obj (.op a) ⟶
        (f.closedCokernel TY).simplicial.obj (.op a) :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom (f.closedCokernelEndDegree TY s t heq ht n)

@[simp]
theorem Hom.closedCokernelEndComponent_mk {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (s : Hom X X) (t : Hom Y Y)
    (heq : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n))
          (s.simplicial.app (.op (.mk n)) x) =
        t.simplicial.app (.op (.mk n))
          (f.simplicial.app (.op (.mk n)) x))
    (ht : ∀ n,
      @Continuous (Y.simplicial.degree n) (Y.simplicial.degree n)
        (TY.topology (.op (.mk n))) (TY.topology (.op (.mk n)))
        (t.simplicial.app (.op (.mk n)))) (n : ℕ) :
    f.closedCokernelEndComponent TY s t heq ht (.mk n) =
      ModuleCat.ofHom (f.closedCokernelEndDegree TY s t heq ht n) :=
  rfl

/-- Continuous equivariant cyclic endomorphism descended through the exact
closed range. -/
def Hom.closedCokernelEnd {X Y : CyclicModule ℂ}
    (f : Hom X Y) (TY : Topology Y) (s : Hom X X) (t : Hom Y Y)
    (heq : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n))
          (s.simplicial.app (.op (.mk n)) x) =
        t.simplicial.app (.op (.mk n))
          (f.simplicial.app (.op (.mk n)) x))
    (ht : ∀ n,
      @Continuous (Y.simplicial.degree n) (Y.simplicial.degree n)
        (TY.topology (.op (.mk n))) (TY.topology (.op (.mk n)))
        (t.simplicial.app (.op (.mk n)))) :
    Hom (f.closedCokernel TY) (f.closedCokernel TY) where
  simplicial :=
    { app := fun j => f.closedCokernelEndComponent TY s t heq ht j.unop
      naturality := by
        intro j k g
        rcases j with ⟨j⟩
        induction j using SimplexCategoryGenRel.rec with
        | _ j =>
          rcases k with ⟨k⟩
          induction k using SimplexCategoryGenRel.rec with
          | _ k =>
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro q
            simp only [ModuleCat.comp_apply, Opposite.unop_op,
              f.closedCokernelEndComponent_mk]
            obtain ⟨y, rfl⟩ :=
              (TY.closedRange f (.op (.mk j))).mkQ_surjective q
            change (TY.closedRange f (.op (.mk k))).mkQ
                (t.simplicial.app (.op (.mk k))
                  (Y.simplicial.map g y)) =
              (TY.closedRange f (.op (.mk k))).mkQ
                (Y.simplicial.map g
                  (t.simplicial.app (.op (.mk j)) y))
            have h := t.simplicial.naturality g
            exact congrArg (TY.closedRange f (.op (.mk k))).mkQ
              (DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) y) }
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    simp only [ModuleCat.comp_apply, Opposite.unop_op,
      f.closedCokernelEndComponent_mk]
    obtain ⟨y, rfl⟩ :=
      (TY.closedRange f (.op (.mk n))).mkQ_surjective q
    change (TY.closedRange f (.op (.mk n))).mkQ
        (t.simplicial.app (.op (.mk n)) (Y.cyclic n y)) =
      (TY.closedRange f (.op (.mk n))).mkQ
        (Y.cyclic n (t.simplicial.app (.op (.mk n)) y))
    have h := t.cyclic_naturality n
    exact congrArg (TY.closedRange f (.op (.mk n))).mkQ
      (DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) y)

end GaloisForLFunctions.RHTower.CyclicModule
