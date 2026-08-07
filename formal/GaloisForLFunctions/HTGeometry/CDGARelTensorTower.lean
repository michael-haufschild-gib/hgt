import GaloisForLFunctions.HTGeometry.CDGARelTensorTwist
import GaloisForLFunctions.HTGeometry.CDGADerivedTensor
import GaloisForLFunctions.HTGeometry.CDGACellTower

/-!
# Invariance of the tensor product over the algebra along a tower of cell attachments

The comparison `relTensorProdRightHom` is natural in the tensored factor, so the argument that
proved invariance for the tensor product over the ground ring runs again over the quotient: conjugate
the comparison, apply the two-sided cell-attachment theorem, and induct up the tower.

* `HTGeometry.relTensorTwistR_compat` : the comparison intertwines the descended twists.
* `HTGeometry.relTensorProdRightHom_naturality` : it is natural in the tensored factor.
* `HTGeometry.relTensorMapLeft_twisted_isQuasiIsoFull` : one cell.
* `HTGeometry.relTensorMapLeft_tower_isQuasiIsoFull` : a whole tower.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {C : ℕ → Type w} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]

section Naturality

variable (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')
  (Q : CDGAModuleStructure A N) (Qc : CDGAModuleStructure A C)

/-- The comparison intertwines the descended twists. -/
theorem relTensorTwistR_compat (φ : CDGAModuleHom P P') (t : CDGATwist Q Qc) (n : ℕ)
    (v : RelTensorCarrier P Qc n) :
    (relTensorMapLeft φ Q).toFun (n + 1) ((relTensorTwistR P Q Qc t).τ n v)
      = (relTensorTwistR P' Q Qc t).τ n ((relTensorMapLeft φ Qc).toFun n v) := by
  refine Quotient.inductionOn' v fun z => ?_
  exact congrArg (Submodule.Quotient.mk)
    (tensorMapLeft_tensorSigmaR φ Q Qc (fun k => t.τₗ k) n z)

set_option maxHeartbeats 1000000 in
/-- **The comparison is natural in the tensored factor.** -/
theorem relTensorProdRightHom_naturality (φ : CDGAModuleHom P P') (t : CDGATwist Q Qc) :
    (relTensorProdRightHom P' Q Qc t).comp
        (relTensorMapLeft φ (CDGAModuleStructure.twisted Q Qc t))
      = (CDGAModuleHom.twistedMap₂ (relTensorTwistR P Q Qc t) (relTensorTwistR P' Q Qc t)
          (relTensorMapLeft φ Q) (relTensorMapLeft φ Qc)
          (relTensorTwistR_compat P P' Q Qc φ t)).comp (relTensorProdRightHom P Q Qc t) := by
  refine CDGAModuleHom.hom_ext fun n f => ?_
  refine Quotient.inductionOn' f fun z => ?_
  have hnat := congrArg
    (fun H : CDGAModuleHom (tensorModule P (CDGAModuleStructure.twisted Q Qc t))
        (CDGAModuleStructure.twisted (tensorModule P' Q) (tensorModule P' Qc)
          (tensorTwistR P' t)) => H.toFun n z)
    (tensorProdRightHom_naturality P P' φ t)
  show relTensorProdRightMap P' Q Qc n ((tensorMapLeft φ
      (CDGAModuleStructure.twisted Q Qc t)).toFun n z) = _
  rw [relTensorProdRightMap_apply]
  refine Prod.ext ?_ ?_
  · exact congrArg (Submodule.Quotient.mk) (congrArg Prod.fst hnat)
  · exact congrArg (Submodule.Quotient.mk) (congrArg Prod.snd hnat)

/-- **Tensoring over the algebra against a cell attachment preserves full quasi-isomorphisms.** -/
theorem relTensorMapLeft_twisted_isQuasiIsoFull (φ : CDGAModuleHom P P') (t : CDGATwist Q Qc)
    (hbase : (relTensorMapLeft φ Q).IsQuasiIsoFull)
    (hcell : (relTensorMapLeft φ Qc).IsQuasiIsoFull) :
    (relTensorMapLeft φ (CDGAModuleStructure.twisted Q Qc t)).IsQuasiIsoFull := by
  have hΦ : (relTensorProdRightHom P Q Qc t).IsQuasiIsoFull :=
    relTensorProdRightHom_isQuasiIsoFull P Q Qc t
  have hΦ' : (relTensorProdRightHom P' Q Qc t).IsQuasiIsoFull :=
    relTensorProdRightHom_isQuasiIsoFull P' Q Qc t
  have h2 : (CDGAModuleHom.twistedMap₂ (relTensorTwistR P Q Qc t) (relTensorTwistR P' Q Qc t)
      (relTensorMapLeft φ Q) (relTensorMapLeft φ Qc)
      (relTensorTwistR_compat P P' Q Qc φ t)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.twistedMap₂ (relTensorTwistR_compat P P' Q Qc φ t) hbase hcell
  have hcomp := CDGAModuleHom.IsQuasiIsoFull.comp h2 hΦ
  rw [← relTensorProdRightHom_naturality P P' Q Qc φ t] at hcomp
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right hcomp hΦ'

end Naturality

section Tower

variable (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')
  {Mb : ℕ → Type w} [∀ n, AddCommGroup (Mb n)] [∀ n, Module R (Mb n)]
  {Cc : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (Cc i n)] [∀ i n, Module R (Cc i n)]

/-- **The tensor product over the algebra against a semi-free module is invariant.** -/
theorem relTensorMapLeft_tower_isQuasiIsoFull (φ : CDGAModuleHom P P')
    (Q₀ : CDGAModuleStructure A Mb) (cellMod : ∀ i, CDGAModuleStructure A (Cc i))
    (τ : ∀ (i : ℕ) (S : CDGAModuleStructure A (towerCarrier Mb Cc i)), CDGATwist S (cellMod i))
    (h₀ : (relTensorMapLeft φ Q₀).IsQuasiIsoFull)
    (hcell : ∀ i, (relTensorMapLeft φ (cellMod i)).IsQuasiIsoFull) :
    ∀ i, (relTensorMapLeft φ (towerMod Q₀ cellMod τ i)).IsQuasiIsoFull := by
  intro i
  induction i with
  | zero => exact h₀
  | succ j ih =>
      exact relTensorMapLeft_twisted_isQuasiIsoFull P P' (towerMod Q₀ cellMod τ j) (cellMod j) φ
        (τ j (towerMod Q₀ cellMod τ j)) ih (hcell j)

end Tower

end GaloisForLFunctions.HTGeometry
