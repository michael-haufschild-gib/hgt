import GaloisForLFunctions.HTGeometry.Buildings.AugmentedSteinberg
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-!
# Free coefficient modules for parabolic flag layers

Categorical freeness of building homology gives an actual module basis
by identifying the coproduct with a direct sum. Finite tensor products
of the augmented flag Steinberg modules are therefore free over every
commutative coefficient ring, and hence flat. One-dimensional layers
are tensor units and may be removed without changing the module.

These are the coefficient modules in the tensor-product definition of
the parabolic Steinberg module of Ash--Gunnells, arXiv:2611.03303, §2.
Flatness supplies the tensor-exactness input used in their §6 comparison.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe u

variable {k K V : Type u} [CommRing k] [Field K] [AddCommGroup V] [Module K V]

/-- A coproduct of coefficient modules is free in the ordinary module-theoretic sense. -/
theorem moduleFree_of_isFreeOver (M : ModuleCat.{u} k)
    (h : IsFreeOver.{u, u + 1, u} (ModuleCat.of k k) M) : Module.Free k M := by
  classical
  obtain ⟨I, ⟨e⟩⟩ := h
  let d := ModuleCat.coprodIsoDirectSum (fun _ : I => ModuleCat.of k k)
  exact Module.Free.of_equiv (e ≪≫ d).toLinearEquiv.symm

/-- Flag-interval homology is a free module over any commutative coefficient ring. -/
theorem moduleFree_flagIntervalHomology (A B : Submodule K V) (n : ℕ) :
    Module.Free k (↑((nerve (flagInterval A B)).homology (ModuleCat.of k k) n : ModuleCat.{u} k)) :=
  moduleFree_of_isFreeOver _ (isFreeOver_flagIntervalHomology A B (ModuleCat.of k k) n)

/-- The augmented flag Steinberg object with its actual coefficient-module structure. -/
noncomputable abbrev flagSteinbergCoefficient (k : Type u) [CommRing k]
    (A B : Submodule K V) : ModuleCat.{u} k :=
  augmentedFlagSteinbergModule A B (ModuleCat.of k k)

/-- The reduced convention gives free Steinberg modules in every layer dimension. -/
theorem moduleFree_augmentedFlagSteinberg (A B : Submodule K V) :
    Module.Free k (flagSteinbergCoefficient k A B) :=
  moduleFree_of_isFreeOver _ (isFreeOver_augmentedFlagSteinbergModule A B (ModuleCat.of k k))

/-- The tensor of Steinberg factors for a finite list of flag layers. -/
noncomputable def parabolicSteinbergTensor (k : Type u) [CommRing k] :
    List (Submodule K V × Submodule K V) → ModuleCat.{u} k
  | [] => ModuleCat.of k k
  | (A, B) :: layers => ModuleCat.of k (TensorProduct k
      (flagSteinbergCoefficient k A B)
      (parabolicSteinbergTensor k layers))

/-- No characteristic or invertibility assumption is needed for the tensor's freeness. -/
theorem moduleFree_parabolicSteinbergTensor (layers : List (Submodule K V × Submodule K V)) :
    Module.Free k (parabolicSteinbergTensor k layers) := by
  induction layers with
  | nil => exact inferInstanceAs (Module.Free k k)
  | cons layer layers ih =>
    rcases layer with ⟨A, B⟩
    haveI := ih
    haveI := moduleFree_augmentedFlagSteinberg (k := k) A B
    exact inferInstanceAs (Module.Free k (TensorProduct k
      (flagSteinbergCoefficient k A B)
      (parabolicSteinbergTensor k layers)))

/-- Parabolic Steinberg coefficients are flat over the coefficient ring. -/
theorem flat_parabolicSteinbergTensor (layers : List (Submodule K V × Submodule K V)) :
    Module.Flat k (parabolicSteinbergTensor k layers) := by
  haveI := moduleFree_parabolicSteinbergTensor (k := k) layers
  infer_instance

/-- A rank-one layer is neutral in the tensor product. -/
noncomputable def parabolicSteinbergTensorRankOneIso [FiniteDimensional K V]
    (A B : Submodule K V) (layers : List (Submodule K V × Submodule K V))
    (h : Module.finrank K (flagLayer A B) = 1) :
    parabolicSteinbergTensor k ((A, B) :: layers) ≅ parabolicSteinbergTensor k layers :=
  ((TensorProduct.congr (augmentedFlagSteinbergRankOneIso A B (ModuleCat.of k k) h).toLinearEquiv
      (LinearEquiv.refl k (parabolicSteinbergTensor k layers))).trans
    (TensorProduct.lid k (parabolicSteinbergTensor k layers))).toModuleIso

/-- The parabolic module attached to all successive layers of a finite flag. -/
noncomputable def finiteFlagSteinbergModule {n : ℕ} (A : Fin (n + 1) →o Submodule K V) :
    ModuleCat.{u} k :=
  parabolicSteinbergTensor k (List.ofFn (fun i : Fin n => (A i.castSucc, A i.succ)))

/-- Every finite flag has a free parabolic Steinberg module, including rank-one stages. -/
theorem moduleFree_finiteFlagSteinberg {n : ℕ} (A : Fin (n + 1) →o Submodule K V) :
    Module.Free k (finiteFlagSteinbergModule (k := k) A) :=
  moduleFree_parabolicSteinbergTensor _

end GaloisForLFunctions.HTGeometry
