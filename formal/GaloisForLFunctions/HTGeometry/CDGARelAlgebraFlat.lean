import GaloisForLFunctions.HTGeometry.CDGARelTensorAlgebraMap
import GaloisForLFunctions.HTGeometry.CDGARelSemiFreeFlat

/-!
# Derived base change over a base algebra, at the algebra level

Restriction of scalars turns a morphism of algebras over a base algebra into a morphism of modules
over it, so the flatness of a semi-free right factor — proved for modules — gives base change for the
relative tensor product of algebras.  This is the form the statement takes when the derived tensor
product is computed by a semi-free resolution.

* `HTGeometry.relTensorMapLeft_restrictHom_freeTower_isQuasiIso` : a tower of free cells.
* `HTGeometry.relTensorMapLeft_restrictHom_semifree_isQuasiIso` : its colimit.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R]
  {Wc : ℕ → Type w} [∀ n, AddCommGroup (Wc n)] [∀ n, Module R (Wc n)]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {X' : ℕ → Type w} [∀ n, AddCommGroup (X' n)] [∀ n, Module R (X' n)]
  {C : CDGAStructure R Wc} {A : CDGAStructure R X} {A' : CDGAStructure R X'}

variable (f : CDGAHom C A) (f' : CDGAHom C A') (φ : CDGAHom A A')
  (hcomm : ∀ (n : ℕ) (c : Wc n), φ.toFun n (f.toFun n c) = f'.toFun n c)

/-- **Base change over a base algebra against a tower of free cells.** -/
theorem relTensorMapLeft_restrictHom_freeTower_isQuasiIso (u : CDGAUnit C)
    (hA : CDGAModuleUnital u f.restrictModule) (hA' : CDGAModuleUnital u f'.restrictModule)
    (hφ : (f.restrictHom f' φ hcomm).IsQuasiIsoFull)
    {V₀ : Type w} [AddCommGroup V₀] [Module R V₀]
    {ι₀ : Type w} [DecidableEq ι₀] (b₀ : Module.Basis ι₀ R V₀) (k₀ : ℕ)
    {V : ℕ → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {ι : ℕ → Type w} [∀ i, DecidableEq (ι i)]
    (bb : ∀ i, Module.Basis (ι i) R (V i)) (deg : ℕ → ℕ)
    (τ : ∀ (i : ℕ)
      (S : CDGAModuleStructure C
        (towerCarrier (FreeCellCarrier Wc V₀ k₀) (fun i => FreeCellCarrier Wc (V i) (deg i)) i)),
      CDGATwist S (freeCellModule C (V i) (deg i))) (i : ℕ) :
    CDGAModuleHom.IsQuasiIso (relTensorMapLeft (f.restrictHom f' φ hcomm)
      (towerMod (freeCellModule C V₀ k₀) (fun i => freeCellModule C (V i) (deg i)) τ i)) :=
  (relTensorMapLeft_freeTower_isQuasiIsoFull f.restrictModule f'.restrictModule u hA hA'
    (f.restrictHom f' φ hcomm) hφ b₀ k₀ bb deg τ i).2

/-- **Base change over a base algebra against a semi-free module.** -/
theorem relTensorMapLeft_restrictHom_semifree_isQuasiIso (u : CDGAUnit C)
    (hA : CDGAModuleUnital u f.restrictModule) (hA' : CDGAModuleUnital u f'.restrictModule)
    (hφ : (f.restrictHom f' φ hcomm).IsQuasiIsoFull)
    {V₀ : Type w} [AddCommGroup V₀] [Module R V₀]
    {ι₀ : Type w} [DecidableEq ι₀] (b₀ : Module.Basis ι₀ R V₀) (k₀ : ℕ)
    {V : ℕ → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {ιc : ℕ → Type w} [∀ i, DecidableEq (ιc i)]
    (bb : ∀ i, Module.Basis (ιc i) R (V i)) (deg : ℕ → ℕ)
    (τ : ∀ (i : ℕ)
      (S : CDGAModuleStructure C
        (towerCarrier (FreeCellCarrier Wc V₀ k₀) (fun i => FreeCellCarrier Wc (V i) (deg i)) i)),
      CDGATwist S (freeCellModule C (V i) (deg i))) :
    CDGAModuleHom.IsQuasiIso (relTensorMapLeft (f.restrictHom f' φ hcomm)
      (towerColim (freeCellModule C V₀ k₀) (fun i => freeCellModule C (V i) (deg i)) τ)) :=
  (relTensorMapLeft_freeTowerColim_isQuasiIsoFull f.restrictModule f'.restrictModule u hA hA'
    (f.restrictHom f' φ hcomm) hφ b₀ k₀ bb deg τ).2

end GaloisForLFunctions.HTGeometry
