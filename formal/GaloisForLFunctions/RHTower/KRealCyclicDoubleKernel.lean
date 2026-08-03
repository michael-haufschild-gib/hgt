import GaloisForLFunctions.RHTower.CyclicModuleDoubleKernel

/-!
# Real structure on a double kernel of cyclic morphisms

The degreewise intersection of kernels of two Real-equivariant cyclic morphisms inherits the Real
structure of its source.  All simplicial and cyclic compatibility laws are inherited by subtype
extensionality.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower.CyclicModule

variable {odd : Bool} {X Y Z : CyclicModule ℂ}

/-- Real structure on one degree of the intersection of two equivariant cyclic kernels. -/
def doubleKernelDegreeKReal
    (KX : KReal odd X) (KY : KReal odd Y) (KZ : KReal odd Z)
    (f : KRealHom KX KY) (g : KRealHom KX KZ) (n : ℕ) :
    KRealStructure odd
      ((f.toHom.doubleKernel g.toHom).simplicial.degree n) where
  sigma :=
    { toFun := fun x => ⟨(KX.real n).sigma x.1, by
          have hx := (f.toHom.mem_doubleKernelSubmodule_iff
            g.toHom (.op (.mk n)) x.1).mp x.2
          rw [f.toHom.mem_doubleKernelSubmodule_iff]
          constructor
          · rw [← f.real_naturality n x.1, hx.1, map_zero]
          · rw [← g.real_naturality n x.1, hx.2, map_zero]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (KX.real n).sigma (x.1 + y.1) =
          (KX.real n).sigma x.1 + (KX.real n).sigma y.1
        exact map_add (KX.real n).sigma x.1 y.1
      map_smul' := by
        intro z x
        apply Subtype.ext
        change (KX.real n).sigma (z • x.1) =
          star z • (KX.real n).sigma x.1
        exact (KX.real n).sigma.map_smulₛₗ z x.1 }
  sq x := by
    apply Subtype.ext
    change (KX.real n).sigma ((KX.real n).sigma x.1) =
      (kRealParityAction odd x).1
    rw [(KX.real n).sq]
    cases odd <;> rfl

/-- A degreewise double kernel of equivariant cyclic morphisms is a Real cyclic module. -/
def doubleKernelKReal
    (KX : KReal odd X) (KY : KReal odd Y) (KZ : KReal odd Z)
    (f : KRealHom KX KY) (g : KRealHom KX KZ) :
    KReal odd (f.toHom.doubleKernel g.toHom) where
  real n := doubleKernelDegreeKReal KX KY KZ f g n
  face_naturality n i x := by
    apply Subtype.ext
    exact KX.face_naturality n i x.1
  degeneracy_naturality n i x := by
    apply Subtype.ext
    exact KX.degeneracy_naturality n i x.1
  cyclic_naturality n x := by
    apply Subtype.ext
    exact KX.cyclic_naturality n x.1

end GaloisForLFunctions.RHTower.CyclicModule
