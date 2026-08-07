import GaloisForLFunctions.HTGeometry.CDGARelFreeCellInvariance
import GaloisForLFunctions.HTGeometry.CDGACellTowerColimit
import GaloisForLFunctions.HTGeometry.CDGARelTensorColimit

/-!
# Semi-free modules are flat for the tensor product over the algebra

A semi-free module is the colimit of a tower of free cells.  Tensoring over the algebra preserves
full quasi-isomorphisms at every stage of such a tower, and it commutes with the colimit, so it
preserves them for the colimit as well.

* `HTGeometry.relTensorMapLeft_freeTowerColim_isQuasiIsoFull` : `− ⊗_A F` preserves full
  quasi-isomorphisms for a semi-free `F`.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')

/-- **A semi-free module is flat for the tensor product over the algebra.**  A tower of free cells
is invariant at every stage, and the tensor product over the algebra commutes with the colimit. -/
theorem relTensorMapLeft_freeTowerColim_isQuasiIsoFull (u : CDGAUnit A)
    (hP : CDGAModuleUnital u P) (hP' : CDGAModuleUnital u P') (φ : CDGAModuleHom P P')
    (hφ : φ.IsQuasiIsoFull)
    {V₀ : Type w} [AddCommGroup V₀] [Module R V₀]
    {ι₀ : Type w} [Fintype ι₀] [DecidableEq ι₀] (b₀ : Module.Basis ι₀ R V₀) (k₀ : ℕ)
    {V : ℕ → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {ιc : ℕ → Type w} [∀ i, Fintype (ιc i)] [∀ i, DecidableEq (ιc i)]
    (b : ∀ i, Module.Basis (ιc i) R (V i)) (deg : ℕ → ℕ)
    (τ : ∀ (i : ℕ)
      (S : CDGAModuleStructure A
        (towerCarrier (FreeCellCarrier X V₀ k₀) (fun i => FreeCellCarrier X (V i) (deg i)) i)),
      CDGATwist S (freeCellModule A (V i) (deg i))) :
    CDGAModuleHom.IsQuasiIsoFull (relTensorMapLeft φ
      (towerColim (freeCellModule A V₀ k₀) (fun i => freeCellModule A (V i) (deg i)) τ)) :=
  relTensorMapLeft_colim_isQuasiIsoFull P
    (fun i _ h => towerTrans (freeCellModule A V₀ k₀)
      (fun i => freeCellModule A (V i) (deg i)) τ i h) P' φ
    (fun i => relTensorMapLeft_freeTower_isQuasiIsoFull P P' u hP hP' φ hφ b₀ k₀ b deg τ i)

end GaloisForLFunctions.HTGeometry
