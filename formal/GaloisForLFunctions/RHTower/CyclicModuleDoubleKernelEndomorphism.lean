import GaloisForLFunctions.RHTower.CyclicModuleDoubleKernel

/-!
# Endomorphisms of cyclic double kernels

A cyclic endomorphism of an ambient module restricts to an intersection of two
cyclic kernels as soon as it preserves each kernel degreewise.  This is the
exact functoriality needed for the nonunital and two-endpoint stages of the CCM
source; no algebra structure on the kernel is assumed.
-/

noncomputable section

open CategoryTheory

universe u v

namespace GaloisForLFunctions.RHTower.CyclicModule

variable {R : Type u} [CommRing R]

/-- Degreewise restriction of a cyclic endomorphism to a double kernel. -/
def Hom.doubleKernelEndDegree {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (h : Hom X X)
    (hf : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n)) x = 0 →
        f.simplicial.app (.op (.mk n))
          (h.simplicial.app (.op (.mk n)) x) = 0)
    (hg : ∀ n (x : X.simplicial.degree n),
      g.simplicial.app (.op (.mk n)) x = 0 →
        g.simplicial.app (.op (.mk n))
          (h.simplicial.app (.op (.mk n)) x) = 0) :
    ∀ j : SimplexCategoryGenRelᵒᵖ,
      (f.doubleKernel g).simplicial.obj j →ₗ[R]
        (f.doubleKernel g).simplicial.obj j
  | .op (.mk n) =>
    { toFun := fun x => ⟨h.simplicial.app (.op (.mk n)) x.1, by
        rw [f.mem_doubleKernelSubmodule_iff]
        have hx := (f.mem_doubleKernelSubmodule_iff g (.op (.mk n)) x.1).mp x.2
        exact ⟨hf n x.1 hx.1, hg n x.1 hx.2⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (h.simplicial.app (.op (.mk n))).hom x.1 y.1
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact map_smul (h.simplicial.app (.op (.mk n))).hom r x.1 }

@[simp]
theorem Hom.doubleKernelEndDegree_coe {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (h : Hom X X)
    (hf : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n)) x = 0 →
        f.simplicial.app (.op (.mk n))
          (h.simplicial.app (.op (.mk n)) x) = 0)
    (hg : ∀ n (x : X.simplicial.degree n),
      g.simplicial.app (.op (.mk n)) x = 0 →
        g.simplicial.app (.op (.mk n))
          (h.simplicial.app (.op (.mk n)) x) = 0)
    (n : ℕ) (x : (f.doubleKernel g).simplicial.degree n) :
    (f.doubleKernelEndDegree g h hf hg (.op (.mk n)) x).1 =
      h.simplicial.app (.op (.mk n)) x.1 :=
  rfl

/-- A kernel-preserving cyclic endomorphism restricted to the exact double
kernel cyclic module. -/
def Hom.doubleKernelEnd {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (h : Hom X X)
    (hf : ∀ n (x : X.simplicial.degree n),
      f.simplicial.app (.op (.mk n)) x = 0 →
        f.simplicial.app (.op (.mk n))
          (h.simplicial.app (.op (.mk n)) x) = 0)
    (hg : ∀ n (x : X.simplicial.degree n),
      g.simplicial.app (.op (.mk n)) x = 0 →
        g.simplicial.app (.op (.mk n))
          (h.simplicial.app (.op (.mk n)) x) = 0) :
    Hom (f.doubleKernel g) (f.doubleKernel g) where
  simplicial :=
    { app := fun j => ModuleCat.ofHom
        (f.doubleKernelEndDegree g h hf hg j)
      naturality := by
        intro j k q
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact DFunLike.congr_fun
          (ModuleCat.hom_ext_iff.mp (h.simplicial.naturality q)) x.1 }
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (h.cyclic_naturality n)) x.1

end GaloisForLFunctions.RHTower.CyclicModule
