import GaloisForLFunctions.HTGeometry.FreeCoproductKernel
import GaloisForLFunctions.HTGeometry.SimplicialAugmentation

/-!
# Degree-zero homology as a free object, and free kernels

Degree-zero homology of a simplicial set is the coproduct of copies of the coefficients indexed by
the connected components, and a map of simplicial sets induces on it the map of coproducts attached
to the induced map of components.  Consequently the kernel of a map induced in degree zero is free:
it is the kernel of a map of coproducts induced by a map of index sets.

The kernel is what a Mayer--Vietoris argument produces in degree one, so this is the statement that
turns a cover by contractible pieces into freeness of the first homology.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-! ## Dropping a monomorphism from a kernel -/

section Forks

/-- If `l ≫ m = f` with `m` a monomorphism, then a kernel of `f` is a kernel of `l`. -/
def isKernelOfCompMono {X Y Z : C} {f : X ⟶ Y} (l : X ⟶ Z) (m : Z ⟶ Y) [Mono m] (h : l ≫ m = f)
    {s : KernelFork f} (hs : IsLimit s) :
    IsLimit (KernelFork.ofι (Fork.ι s) (show Fork.ι s ≫ l = 0 from
      zero_of_comp_mono m (by rw [Category.assoc, h]; exact KernelFork.condition s))) := by
  have hcond : ∀ c : KernelFork l, Fork.ι c ≫ f = 0 := fun c => by
    rw [← h, ← Category.assoc, KernelFork.condition c, Limits.zero_comp]
  exact Fork.IsLimit.mk _
    (fun c => hs.lift (KernelFork.ofι (Fork.ι c) (hcond c)))
    (fun c => hs.fac (KernelFork.ofι (Fork.ι c) (hcond c)) WalkingParallelPair.zero)
    (fun c n hn => Fork.IsLimit.hom_ext hs
      (hn.trans (hs.fac (KernelFork.ofι (Fork.ι c) (hcond c)) WalkingParallelPair.zero).symm))

end Forks

/-! ## Degree-zero homology and components -/

section

variable [CategoryWithHomology C] {X Y : SSet.{w}} (R : C)

/-- **Degree-zero homology takes a map of simplicial sets to the map of coproducts induced by the
map of components.** -/
theorem homologyMap_zero_comp_homology₀Iso (f : X ⟶ Y) :
    SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom
      = (X.homology₀Iso R).hom ≫ sigmaMapFun (SSet.mapπ₀ f) R := by
  refine homology₀_hom_ext R fun x => ?_
  rw [← Category.assoc, zeroCycle_comp_homologyMap, zeroCycle_comp_homology₀Iso, ← Category.assoc,
    zeroCycle_comp_homology₀Iso, ι_sigmaMapFun, SSet.mapπ₀_mk]

/-- **Degree-zero homology is free**: it is the coproduct of copies of the coefficients indexed by
the connected components. -/
theorem isFreeOver_homology_zero (X : SSet.{w}) (R : C) :
    IsFreeOver.{v, u, w} R (X.homology R 0) :=
  ⟨SSet.π₀ X, ⟨X.homology₀Iso R⟩⟩

/-- **The kernel of a map induced in degree-zero homology, with its index set**: the components of
the source that are not the chosen representative of their image component. -/
noncomputable def kernelIsoSigmaKerIndexHomologyZero (f : X ⟶ Y) {Z : C}
    (k : Z ⟶ X.homology R 0) (w : k ≫ SSet.homologyMap f R 0 = 0)
    (hk : IsLimit (KernelFork.ofι k w)) :
    Z ≅ ∐ fun _ : sigmaKerIndex (SSet.mapπ₀ f) => R := by
  have hcomm : (X.homology₀Iso R).hom ≫ sigmaMapFun (SSet.mapπ₀ f) R
      = SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom :=
    (homologyMap_zero_comp_homology₀Iso R f).symm
  have hw : (k ≫ (X.homology₀Iso R).hom) ≫ sigmaMapFun (SSet.mapπ₀ f) R = 0 := by
    rw [Category.assoc, hcomm, ← Category.assoc, w, Limits.zero_comp]
  refine kernelIsoSigmaKerIndex (SSet.mapπ₀ f) R (k ≫ (X.homology₀Iso R).hom) hw ?_
  exact IsKernel.ofIso _ hk (KernelFork.ofι (k ≫ (X.homology₀Iso R).hom) hw)
    (X.homology₀Iso R) (Y.homology₀Iso R) (Iso.refl _) hcomm (Category.id_comp _)

/-- **The kernel of a map induced in degree-zero homology is free.**  It is the kernel of the map of
coproducts attached to the induced map of components. -/
theorem isFreeOver_of_isLimit_kernelFork_homologyMap_zero (f : X ⟶ Y) {Z : C}
    (k : Z ⟶ X.homology R 0) (w : k ≫ SSet.homologyMap f R 0 = 0)
    (hk : IsLimit (KernelFork.ofι k w)) : IsFreeOver.{v, u, w} R Z := by
  have hcomm : (X.homology₀Iso R).hom ≫ sigmaMapFun (SSet.mapπ₀ f) R
      = SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom :=
    (homologyMap_zero_comp_homology₀Iso R f).symm
  have hw : (k ≫ (X.homology₀Iso R).hom) ≫ sigmaMapFun (SSet.mapπ₀ f) R = 0 := by
    rw [Category.assoc, hcomm, ← Category.assoc, w, Limits.zero_comp]
  refine isFreeOver_of_isLimit_kernelFork (SSet.mapπ₀ f) R (k ≫ (X.homology₀Iso R).hom) hw ?_
  exact IsKernel.ofIso _ hk (KernelFork.ofι (k ≫ (X.homology₀Iso R).hom) hw)
    (X.homology₀Iso R) (Y.homology₀Iso R) (Iso.refl _) hcomm (Category.id_comp _)

end

end GaloisForLFunctions.HTGeometry
