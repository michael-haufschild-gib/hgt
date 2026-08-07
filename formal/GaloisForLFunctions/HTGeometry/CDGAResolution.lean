import GaloisForLFunctions.HTGeometry.CDGADGStage
import GaloisForLFunctions.HTGeometry.CDGARelFreeCellInvariance
import GaloisForLFunctions.HTGeometry.CDGARelTensorColimit
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Semi-free resolutions

Starting from the free cell on the cocycles of degree zero and attaching, at every stage, the free
cell on the cocycles of the target together with the classes the comparison kills, one obtains a
semi-free module and a quasi-isomorphism from it to the target.  Tensoring that resolution over the
algebra preserves full quasi-isomorphisms, because every stage is a twisted extension by a free
cell and the tensor product commutes with the colimit.

* `HTGeometry.resolutionBase`, `HTGeometry.resolution` : the resolution.
* `HTGeometry.resolutionMap_isQuasiIso` : it is a quasi-isomorphism.
* `HTGeometry.relTensorMapLeft_resolution_isQuasiIsoFull` : it is flat.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (P : CDGAModuleStructure A M)

/-- The starting stage of a resolution: the free cell on the cocycles of degree zero. -/
noncomputable def resolutionBase : DGStage A P where
  carrier n := FreeCellCarrier (R := R) X (cocycleCellCoeff P 0) 0 n
  group _ := inferInstance
  smul _ := inferInstance
  str := freeCellModule A (cocycleCellCoeff P 0) 0
  cmp := cocycleCover P 0

variable {u : CDGAUnit A}

theorem resolutionBase_unital : CDGAModuleUnital u (resolutionBase P).str :=
  freeCell_unital u (cocycleCellCoeff P 0) 0

/-- **The semi-free resolution of a differential graded module.** -/
noncomputable def resolution : CDGAModuleStructure A
    (colimModuleDeg (fun i _ h => killTrans P (resolutionBase P) i h)) :=
  killColim P (resolutionBase P)

/-- **The comparison from the resolution.** -/
noncomputable def resolutionMap : CDGAModuleHom (resolution P) P :=
  killColimMap P (resolutionBase P)

/-- **A differential graded module over a unital algebra has a semi-free resolution.** -/
theorem resolutionMap_isQuasiIso (hP : CDGAModuleUnital u P) :
    (resolutionMap P).IsQuasiIso :=
  killColimMap_isQuasiIso P (resolutionBase P) (resolutionBase_unital P) hP

theorem resolutionMap_cocyclesMap_zero_surjective (hP : CDGAModuleUnital u P) :
    Function.Surjective ((resolutionMap P).cocyclesMap 0) :=
  killColimMap_cocyclesMap_zero_surjective P (resolutionBase P) (resolutionBase_unital P) hP

section Flat

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (Q : CDGAModuleStructure A M) (Q' : CDGAModuleStructure A M')
  (φ : CDGAModuleHom Q Q')

/-- **Every stage of a resolution is flat.**  Each stage is a twisted extension of the previous one
by a free cell, and both are invariant. -/
theorem killSeq_flat (S : CDGAModuleStructure A N) (s₀ : DGStage A S)
    (h₀ : (relTensorMapLeft φ s₀.str).IsQuasiIsoFull) (u : CDGAUnit A)
    (hQ : CDGAModuleUnital u Q) (hQ' : CDGAModuleUnital u Q') (hφ : φ.IsQuasiIsoFull) :
    ∀ j, (relTensorMapLeft φ (killSeq S s₀ j).str).IsQuasiIsoFull
  | 0 => h₀
  | (j + 1) => by
      classical
      exact relTensorMapLeft_twisted_isQuasiIsoFull Q Q' (killSeq S s₀ j).str
        (freeCellModule A (cellCoeff S (killSeq S s₀ j) (Nat.unpair j).2) (Nat.unpair j).2) φ
        (freeCellTwist (killSeq S s₀ j).str (Nat.unpair j).2
          (cellW S (killSeq S s₀ j) (Nat.unpair j).2)
          (cellW_cocycle S (killSeq S s₀ j) (Nat.unpair j).2))
        (killSeq_flat S s₀ h₀ u hQ hQ' hφ j)
        (relTensorMapLeft_freeCell_isQuasiIsoFull Q Q' u hQ hQ' φ hφ
          (Finsupp.basisSingleOne (ι := cellIndex S (killSeq S s₀ j) (Nat.unpair j).2) (R := R))
          (Nat.unpair j).2)

/-- **A semi-free resolution is flat for the tensor product over the algebra.** -/
theorem relTensorMapLeft_killColim_isQuasiIsoFull (S : CDGAModuleStructure A N)
    (s₀ : DGStage A S) (h₀ : (relTensorMapLeft φ s₀.str).IsQuasiIsoFull) (u : CDGAUnit A)
    (hQ : CDGAModuleUnital u Q) (hQ' : CDGAModuleUnital u Q') (hφ : φ.IsQuasiIsoFull) :
    (relTensorMapLeft φ (killColim S s₀)).IsQuasiIsoFull :=
  relTensorMapLeft_colim_isQuasiIsoFull Q (fun i _ h => killTrans S s₀ i h) Q' φ
    (killSeq_flat Q Q' φ S s₀ h₀ u hQ hQ' hφ)

/-- **The semi-free resolution is flat for the tensor product over the algebra.** -/
theorem relTensorMapLeft_resolution_isQuasiIsoFull (u : CDGAUnit A)
    (hQ : CDGAModuleUnital u Q) (hQ' : CDGAModuleUnital u Q') (hφ : φ.IsQuasiIsoFull) :
    (relTensorMapLeft φ (resolution P)).IsQuasiIsoFull := by
  classical
  exact relTensorMapLeft_killColim_isQuasiIsoFull Q Q' φ P (resolutionBase P)
    (relTensorMapLeft_freeCell_isQuasiIsoFull Q Q' u hQ hQ' φ hφ
      (Finsupp.basisSingleOne (ι := P.cocycles 0) (R := R)) 0) u hQ hQ' hφ

end Flat

end GaloisForLFunctions.HTGeometry
