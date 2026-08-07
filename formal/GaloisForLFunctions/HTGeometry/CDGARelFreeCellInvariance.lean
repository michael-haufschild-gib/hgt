import GaloisForLFunctions.HTGeometry.CDGARelTensorShiftHom
import GaloisForLFunctions.HTGeometry.CDGARelTensorConstHom
import GaloisForLFunctions.HTGeometry.CDGARelTensorUnit
import GaloisForLFunctions.HTGeometry.CDGAFreeCoefficients

/-!
# Free cells are invariant for the tensor product over the algebra

Tensoring a free cell over the algebra with a full quasi-isomorphism again gives a full
quasi-isomorphism.  A free cell is the shift of the algebra tensored with a coefficient module, and
each of the three operations is handled by an equivalence natural in the module argument: the shift
and the constant coefficients pass through the tensor product over the algebra, and what is left is
the algebra tensored over itself, which the unitor identifies with the module.

* `HTGeometry.relTensorMapLeft_freeCell_isQuasiIsoFull` : `− ⊗_A (A[−k] ⊗ V)` preserves full
  quasi-isomorphisms.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')

/-- **Tensoring a free cell over the algebra preserves full quasi-isomorphisms.** -/
theorem relTensorMapLeft_freeCell_isQuasiIsoFull (u : CDGAUnit A)
    (hP : CDGAModuleUnital u P) (hP' : CDGAModuleUnital u P') (φ : CDGAModuleHom P P')
    (hφ : φ.IsQuasiIsoFull) {V : Type w} [AddCommGroup V] [Module R V]
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V) (k : ℕ) :
    (relTensorMapLeft φ (freeCellModule A V k)).IsQuasiIsoFull := by
  have h0 : (relTensorMapLeft φ (CDGAStructure.selfModule A)).IsQuasiIsoFull :=
    relTensorMapLeft_selfModule_isQuasiIsoFull P P' u hP hP' φ hφ
  have h1 : (tensorConstMap (relTensorMapLeft φ (CDGAStructure.selfModule A)) V).IsQuasiIsoFull :=
    tensorConstMap_isQuasiIsoFull _ h0 b
  have h2 : ((relTensorMapLeft φ (tensorConstModule (CDGAStructure.selfModule A) V)).comp
      (relTensorConstHom P (CDGAStructure.selfModule A) (V := V))).IsQuasiIsoFull := by
    rw [relTensorConstHom_naturality P P' (CDGAStructure.selfModule A) φ]
    exact CDGAModuleHom.IsQuasiIsoFull.comp
      (relTensorConstHom_isQuasiIsoFull P' (CDGAStructure.selfModule A)) h1
  have h3 : (relTensorMapLeft φ
      (tensorConstModule (CDGAStructure.selfModule A) V)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_comp_left h2
      (relTensorConstHom_isQuasiIsoFull P (CDGAStructure.selfModule A))
  have h4 : (shiftMap (relTensorMapLeft φ
      (tensorConstModule (CDGAStructure.selfModule A) V)) k).IsQuasiIsoFull :=
    shiftMap_isQuasiIsoFull _ h3 k
  have h5 : ((relTensorShiftHom P' (tensorConstModule (CDGAStructure.selfModule A) V) k).comp
      (relTensorMapLeft φ
        (shiftModule (tensorConstModule (CDGAStructure.selfModule A) V) k))).IsQuasiIsoFull := by
    rw [relTensorShiftHom_naturality P P'
      (tensorConstModule (CDGAStructure.selfModule A) V) k φ]
    exact CDGAModuleHom.IsQuasiIsoFull.comp h4
      (relTensorShiftHom_isQuasiIsoFull P (tensorConstModule (CDGAStructure.selfModule A) V) k)
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h5
    (relTensorShiftHom_isQuasiIsoFull P' (tensorConstModule (CDGAStructure.selfModule A) V) k)

end GaloisForLFunctions.HTGeometry
