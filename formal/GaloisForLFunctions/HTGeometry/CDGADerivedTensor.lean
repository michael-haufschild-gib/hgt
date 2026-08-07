import GaloisForLFunctions.HTGeometry.CDGATensor
import GaloisForLFunctions.HTGeometry.CDGACellInvariance
import GaloisForLFunctions.HTGeometry.CDGACellTower
import GaloisForLFunctions.HTGeometry.CDGATensorLeft

/-!
# The derived tensor product against a cell attachment

Tensoring is exact on each bidegree but not on cohomology, so a quasi-isomorphism `P → P'` does not
in general induce one on `P ⊗ Q`.  It does when `Q` is built by attaching cells, because then the
comparison can be filtered: distributivity turns `P ⊗ (Q ⊕ C)` into a cell attachment of `P ⊗ Q`
along the tensored twisting cochain, and the comparison becomes a comparison of cell attachments,
which is handled one cell at a time.

* `HTGeometry.tensorMapLeft_tensorSigmaR` : tensoring intertwines the twisting cochains.
* `HTGeometry.tensorProdRightHom_naturality` : distributivity is natural in the tensored factor.
* `HTGeometry.tensorMapLeft_twisted_isQuasiIsoFull` : **tensoring against a cell attachment
  preserves full quasi-isomorphisms** as soon as it does against the base and against the cell.
* `HTGeometry.tensorMapLeft_tower_isQuasiIsoFull` : **the derived tensor product against a tower of
  cell attachments is invariant** — the statement `⊗^L` names.
* `HTGeometry.tensorMapRight_tower_isQuasiIsoFull` : the same in the other variable.
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
  {Q : CDGAModuleStructure A N} {Qc : CDGAModuleStructure A C}

set_option maxHeartbeats 1000000 in
/-- **Distributivity is natural in the tensored factor.**  Tensoring a cell attachment and then
distributing is the same as distributing and then comparing the two cell attachments. -/
theorem tensorProdRightHom_naturality (φ : CDGAModuleHom P P') (t : CDGATwist Q Qc) :
    (tensorProdRightHom P' Q Qc t).comp
        (tensorMapLeft φ (CDGAModuleStructure.twisted Q Qc t))
      = (CDGAModuleHom.twistedMap₂ (tensorTwistR P t) (tensorTwistR P' t)
          (tensorMapLeft φ Q) (tensorMapLeft φ Qc)
          (tensorTwistR_compat P P' φ t)).comp (tensorProdRightHom P Q Qc t) := by
  refine CDGAModuleHom.hom_ext fun n f => ?_
  rw [CDGAModuleHom.comp_toFun, CDGAModuleHom.comp_toFun, tensorProdRightHom_toFun,
    tensorProdRightHom_toFun, CDGAModuleHom.twistedMap₂_toFun]
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodRight R R (M' a) (N b) (C b)
        (TensorProduct.map (φ.mapₗ a) LinearMap.id (f ⟨(a, b), h⟩))).1
      = TensorProduct.map (φ.mapₗ a) LinearMap.id
          ((TensorProduct.prodRight R R (M a) (N b) (C b) (f ⟨(a, b), h⟩)).1)
    exact prodRight_map_left_fst (φ.mapₗ a) (f ⟨(a, b), h⟩)
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodRight R R (M' a) (N b) (C b)
        (TensorProduct.map (φ.mapₗ a) LinearMap.id (f ⟨(a, b), h⟩))).2
      = TensorProduct.map (φ.mapₗ a) LinearMap.id
          ((TensorProduct.prodRight R R (M a) (N b) (C b) (f ⟨(a, b), h⟩)).2)
    exact prodRight_map_left_snd (φ.mapₗ a) (f ⟨(a, b), h⟩)

/-- **Tensoring against a cell attachment preserves full quasi-isomorphisms.**  The hypotheses are
the same statement for the base and for the cell; this is the inductive step of invariance of the
derived tensor product against a semi-free module. -/
theorem tensorMapLeft_twisted_isQuasiIsoFull (φ : CDGAModuleHom P P') (t : CDGATwist Q Qc)
    (hbase : (tensorMapLeft φ Q).IsQuasiIsoFull)
    (hcell : (tensorMapLeft φ Qc).IsQuasiIsoFull) :
    (tensorMapLeft φ (CDGAModuleStructure.twisted Q Qc t)).IsQuasiIsoFull := by
  have hΦ : (tensorProdRightHom P Q Qc t).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => tensorProdRight_bijective n
  have hΦ' : (tensorProdRightHom P' Q Qc t).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => tensorProdRight_bijective n
  have h2 : (CDGAModuleHom.twistedMap₂ (tensorTwistR P t) (tensorTwistR P' t)
      (tensorMapLeft φ Q) (tensorMapLeft φ Qc) (tensorTwistR_compat P P' φ t)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.twistedMap₂ (tensorTwistR_compat P P' φ t) hbase hcell
  have hcomp := CDGAModuleHom.IsQuasiIsoFull.comp h2 hΦ
  rw [← tensorProdRightHom_naturality P P' φ t] at hcomp
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right hcomp hΦ'

end Naturality

section Tower

variable (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')
  {Mb : ℕ → Type w} [∀ n, AddCommGroup (Mb n)] [∀ n, Module R (Mb n)]
  {Cc : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (Cc i n)] [∀ i n, Module R (Cc i n)]

/-- **The derived tensor product against a semi-free module is invariant.**  Tensoring a full
quasi-isomorphism against every stage of a tower of cell attachments is again one, provided it is at
the bottom of the tower and against each cell.  For a tower whose cells are free the two hypotheses
are automatic, so this is the statement that `− ⊗ S` computes the derived tensor product when `S` is
semi-free: it depends on the source only through its cohomology. -/
theorem tensorMapLeft_tower_isQuasiIsoFull (φ : CDGAModuleHom P P')
    (S₀ : CDGAModuleStructure A Mb) (cellMod : ∀ i, CDGAModuleStructure A (Cc i))
    (τ : ∀ (i : ℕ) (S : CDGAModuleStructure A (towerCarrier Mb Cc i)), CDGATwist S (cellMod i))
    (h₀ : (tensorMapLeft φ S₀).IsQuasiIsoFull)
    (hcell : ∀ i, (tensorMapLeft φ (cellMod i)).IsQuasiIsoFull) :
    ∀ i, (tensorMapLeft φ (towerMod S₀ cellMod τ i)).IsQuasiIsoFull := by
  intro i
  induction i with
  | zero => exact h₀
  | succ j ih =>
      exact tensorMapLeft_twisted_isQuasiIsoFull P P' φ (τ j (towerMod S₀ cellMod τ j)) ih
        (hcell j)

end Tower

section LeftTower

variable {D : ℕ → Type w} [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
  {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]

set_option maxHeartbeats 1000000 in
/-- **Distributivity in the left variable is natural in the tensored factor.** -/
theorem tensorProdLeftHom_naturality (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (Q : CDGAModuleStructure A N) (Q' : CDGAModuleStructure A N') (t : CDGATwist P Pc)
    (ψ : CDGAModuleHom Q Q') :
    (tensorProdLeftHom P Pc Q' t).comp
        (tensorMapRight (CDGAModuleStructure.twisted P Pc t) ψ)
      = (CDGAModuleHom.twistedMap₂ (tensorTwistL t Q) (tensorTwistL t Q')
          (tensorMapRight P ψ) (tensorMapRight Pc ψ)
          (tensorTwistL_compat P Pc Q Q' ψ)).comp (tensorProdLeftHom P Pc Q t) := by
  refine CDGAModuleHom.hom_ext fun n f => ?_
  rw [CDGAModuleHom.comp_toFun, CDGAModuleHom.comp_toFun, tensorProdLeftHom_toFun,
    tensorProdLeftHom_toFun, CDGAModuleHom.twistedMap₂_toFun]
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N' b)
        (TensorProduct.map LinearMap.id (ψ.mapₗ b) (f ⟨(a, b), h⟩))).1
      = TensorProduct.map LinearMap.id (ψ.mapₗ b)
          ((TensorProduct.prodLeft R R (M a) (D a) (N b) (f ⟨(a, b), h⟩)).1)
    exact prodLeft_map_right_fst (ψ.mapₗ b) (f ⟨(a, b), h⟩)
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N' b)
        (TensorProduct.map LinearMap.id (ψ.mapₗ b) (f ⟨(a, b), h⟩))).2
      = TensorProduct.map LinearMap.id (ψ.mapₗ b)
          ((TensorProduct.prodLeft R R (M a) (D a) (N b) (f ⟨(a, b), h⟩)).2)
    exact prodLeft_map_right_snd (ψ.mapₗ b) (f ⟨(a, b), h⟩)


/-- **Tensoring a cell attachment in the left variable preserves full quasi-isomorphisms.** -/
theorem tensorMapRight_twisted_isQuasiIsoFull (P : CDGAModuleStructure A M)
    (Pc : CDGAModuleStructure A D) {Q : CDGAModuleStructure A N}
    {Q' : CDGAModuleStructure A N'} (t : CDGATwist P Pc) (ψ : CDGAModuleHom Q Q')
    (hbase : (tensorMapRight P ψ).IsQuasiIsoFull)
    (hcell : (tensorMapRight Pc ψ).IsQuasiIsoFull) :
    (tensorMapRight (CDGAModuleStructure.twisted P Pc t) ψ).IsQuasiIsoFull := by
  have hΦ : (tensorProdLeftHom P Pc Q t).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => tensorProdLeft_bijective n
  have hΦ' : (tensorProdLeftHom P Pc Q' t).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => tensorProdLeft_bijective n
  have h2 : (CDGAModuleHom.twistedMap₂ (tensorTwistL t Q) (tensorTwistL t Q')
      (tensorMapRight P ψ) (tensorMapRight Pc ψ)
      (tensorTwistL_compat P Pc Q Q' ψ)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.twistedMap₂ (tensorTwistL_compat P Pc Q Q' ψ) hbase hcell
  have hcomp := CDGAModuleHom.IsQuasiIsoFull.comp h2 hΦ
  rw [← tensorProdLeftHom_naturality P Pc Q Q' t ψ] at hcomp
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right hcomp hΦ'

variable {Mb : ℕ → Type w} [∀ n, AddCommGroup (Mb n)] [∀ n, Module R (Mb n)]
  {Cc : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (Cc i n)] [∀ i n, Module R (Cc i n)]

/-- **The derived tensor product against a semi-free module in the left variable is invariant.** -/
theorem tensorMapRight_tower_isQuasiIsoFull {Q : CDGAModuleStructure A N}
    {Q' : CDGAModuleStructure A N'} (ψ : CDGAModuleHom Q Q')
    (P₀ : CDGAModuleStructure A Mb) (cellMod : ∀ i, CDGAModuleStructure A (Cc i))
    (τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier Mb Cc i)), CDGATwist P (cellMod i))
    (h₀ : (tensorMapRight P₀ ψ).IsQuasiIsoFull)
    (hcell : ∀ i, (tensorMapRight (cellMod i) ψ).IsQuasiIsoFull) :
    ∀ i, (tensorMapRight (towerMod P₀ cellMod τ i) ψ).IsQuasiIsoFull := by
  intro i
  induction i with
  | zero => exact h₀
  | succ j ih =>
      exact tensorMapRight_twisted_isQuasiIsoFull (towerMod P₀ cellMod τ j) (cellMod j)
        (τ j (towerMod P₀ cellMod τ j)) ψ ih (hcell j)

end LeftTower

end GaloisForLFunctions.HTGeometry
