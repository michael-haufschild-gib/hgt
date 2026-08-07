import GaloisForLFunctions.HTGeometry.CDGAUnitor

/-!
# Tensoring over the algebra with the algebra preserves quasi-isomorphisms

The unitor is natural in the module, so the square comparing `− ⊗_A A` with the identity commutes.
Both horizontal maps are full quasi-isomorphisms when the algebra has a unit acting as the identity,
so two out of three gives the base case of invariance for the tensor product over the algebra.

* `HTGeometry.relUnitorHom_naturality` : the unitor is natural.
* `HTGeometry.relTensorMapLeft_selfModule_isQuasiIsoFull` : `− ⊗_A A` preserves full
  quasi-isomorphisms.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')

/-- The unitor is natural in the module. -/
theorem unitorToₗ_tensorMapLeft (φ : CDGAModuleHom P P') (n : ℕ)
    (f : TensorCarrier (R := R) M X n) :
    unitorToₗ P' n ((tensorMapLeft φ (CDGAStructure.selfModule A)).mapₗ n f)
      = φ.mapₗ n (unitorToₗ P n f) := by
  have hf := tensorCarrier_eq_sum_single (N := X) f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨a, c⟩, hq⟩ := q
  induction (f ⟨(a, c), hq⟩) using TensorProduct.induction_on with
  | zero => rw [tensorSingle_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul m x =>
      show unitorToₗ P' n ((tensorMapLeft φ (CDGAStructure.selfModule A)).toFun n
          (tensorSingle (N := X) ⟨(a, c), hq⟩ (m ⊗ₜ[R] x))) = _
      rw [tensorMapLeft_tensorSingle, TensorProduct.map_tmul, unitorToₗ_tensorSingle,
        unitorToₗ_tensorSingle, rightActₗ_tmul, rightActₗ_tmul]
      show ((-1 : R)) ^ (c * a) • P'.act (show c + a = n by omega) x (φ.toFun a m)
        = φ.toFun n (((-1 : R)) ^ (c * a) • P.act (show c + a = n by omega) x m)
      rw [φ.map_smul, φ.map_act]
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, map_add, map_add, hz, hz']

/-- **The unitor is natural**, as a square of maps of differential graded modules. -/
theorem relUnitorHom_naturality (φ : CDGAModuleHom P P') :
    φ.comp (relUnitorHom P)
      = (relUnitorHom P').comp (relTensorMapLeft φ (CDGAStructure.selfModule A)) :=
  CDGAModuleHom.hom_ext fun n f => by
    refine Quotient.inductionOn' f fun z => ?_
    exact (unitorToₗ_tensorMapLeft P P' φ n z).symm

/-- **Tensoring over the algebra with the algebra preserves full quasi-isomorphisms.**  This is the
base case of invariance for the tensor product over the algebra: the two unitors are full
quasi-isomorphisms, so two out of three transfers the property across the square. -/
theorem relTensorMapLeft_selfModule_isQuasiIsoFull (u : CDGAUnit A)
    (hP : CDGAModuleUnital u P) (hP' : CDGAModuleUnital u P') (φ : CDGAModuleHom P P')
    (hφ : φ.IsQuasiIsoFull) :
    (relTensorMapLeft φ (CDGAStructure.selfModule A)).IsQuasiIsoFull := by
  have h1 : (φ.comp (relUnitorHom P)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.comp hφ (relUnitorHom_isQuasiIsoFull P u hP)
  rw [relUnitorHom_naturality P P' φ] at h1
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h1 (relUnitorHom_isQuasiIsoFull P' u hP')

/-- Conversely, if tensoring over the algebra with the algebra is a full quasi-isomorphism then so
was the original map. -/
theorem isQuasiIsoFull_of_relTensorMapLeft_selfModule (u : CDGAUnit A)
    (hP : CDGAModuleUnital u P) (hP' : CDGAModuleUnital u P') (φ : CDGAModuleHom P P')
    (hφ : (relTensorMapLeft φ (CDGAStructure.selfModule A)).IsQuasiIsoFull) :
    φ.IsQuasiIsoFull := by
  have h1 : ((relUnitorHom P').comp
      (relTensorMapLeft φ (CDGAStructure.selfModule A))).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.comp (relUnitorHom_isQuasiIsoFull P' u hP') hφ
  rw [← relUnitorHom_naturality P P' φ] at h1
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_left h1 (relUnitorHom_isQuasiIsoFull P u hP)

end GaloisForLFunctions.HTGeometry
