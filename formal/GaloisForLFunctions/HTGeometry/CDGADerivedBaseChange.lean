import GaloisForLFunctions.HTGeometry.CDGAResolution
import GaloisForLFunctions.HTGeometry.CDGALeftUnitor

/-!
# Derived base change along an equivalence

The derived tensor product is computed by resolving one factor by a semi-free module.  Base change
along a full quasi-isomorphism of the other factor is then again a quasi-isomorphism, and base
change along an equivalence with the algebra itself recovers the module: the two facts a derived
base-change argument composes.

* `HTGeometry.derivedBaseChange_unit` : `C ⊗^{L}_A K ≃ K` when `C` is equivalent to `A`.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- The derived tensor product of a module with the resolution of another, as a comparison to that
other module. -/
noncomputable def derivedBaseChangeMap (C : CDGAModuleStructure A N)
    (φ : CDGAModuleHom C (CDGAStructure.selfModule A)) (K : CDGAModuleStructure A M) :
    CDGAModuleHom (relTensorModule C (resolution K)) K :=
  ((resolutionMap K).comp (relLeftUnitorHom (resolution K))).comp
    (relTensorMapLeft φ (resolution K))

/-- **Base change along an equivalence with the algebra recovers the module.**  This is the derived
statement `C ⊗^{L}_A K ≃ K` for a module `C` equivalent to the algebra: the resolution computes the
derived tensor product, base change along the equivalence is an equivalence because the resolution
is semi-free, and the left unitor identifies `A ⊗_A F` with `F`. -/
theorem derivedBaseChange_unit (C : CDGAModuleStructure A N)
    (φ : CDGAModuleHom C (CDGAStructure.selfModule A)) (u : CDGAUnit A)
    (hC : CDGAModuleUnital u C) (hφ : φ.IsQuasiIsoFull) (K : CDGAModuleStructure A M)
    (hK : CDGAModuleUnital u K) :
    (derivedBaseChangeMap C φ K).IsQuasiIso := by
  have hbase : (relTensorMapLeft φ (resolution K)).IsQuasiIsoFull :=
    relTensorMapLeft_resolution_isQuasiIsoFull K C (CDGAStructure.selfModule A) φ u hC
      (selfModule_unital u) hφ
  have hunit : (relLeftUnitorHom (resolution K)).IsQuasiIsoFull :=
    relLeftUnitorHom_isQuasiIsoFull (resolution K) u (resolution_unital K u)
  exact CDGAModuleHom.IsQuasiIso.comp
    (CDGAModuleHom.IsQuasiIso.comp (resolutionMap_isQuasiIso K hK) hunit.2) hbase.2

end GaloisForLFunctions.HTGeometry
