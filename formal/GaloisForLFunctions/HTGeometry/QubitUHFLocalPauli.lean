import GaloisForLFunctions.RHTower.PrimeUHFOperatorKOneContinuity
import GaloisForLFunctions.HTGeometry.PathShellDelayFloor
import GaloisForLFunctions.HTGeometry.QubitSnocPauli
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.PauliChainLabels
import GaloisForLFunctions.HTGeometry.ThermodynamicPathFieldSelection

/-!
# Coherent local Pauli operators in the qubit UHF algebra

The finite-stage basis is constructed recursively in the same order as the UHF successor maps.
Consequently, adjoining one physical qubit and tensoring by its identity commutes exactly with
finite-stage inclusion.  Every finite Pauli word therefore defines one norm-one self-adjoint
element of the qubit UHF algebra, independent of how many identity sites are appended.

The final definitions realize the countable onsite and nearest-neighbour path labels as literal
quasi-local UHF observables.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry

open PrimeQuasiLocalCharge

noncomputable section

abbrev qubitLocalDim (_ : ℕ) : ℕ := 2

instance qubitLocalDimPositive : Fact (∀ k, 0 < qubitLocalDim k) :=
  ⟨by intro k; simp [qubitLocalDim]⟩

def finTwoEquivBool : Fin 2 ≃ Bool where
  toFun i := Fin.cases false (fun _ => true) i
  invFun b := cond b 1 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

def qubitAFConfigEquiv : (n : ℕ) →
    Fin (matrixAFStageDimension qubitLocalDim n) ≃ (Fin n → Bool)
  | 0 => by
      simpa only [matrixAFStageDimension_zero] using
        (Equiv.ofUnique (Fin 1) (Fin 0 → Bool))
  | n + 1 =>
      (matrixAFStageSuccIndexEquiv qubitLocalDim n).symm |>.trans
        (Equiv.prodCongr (qubitAFConfigEquiv n) finTwoEquivBool) |>.trans
        (Equiv.prodComm _ _) |>.trans
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool))

theorem qubitAFConfigEquiv_succ_apply (n : ℕ)
    (i : Fin (matrixAFStageDimension qubitLocalDim n)) (b : Fin 2) :
    qubitAFConfigEquiv (n + 1)
        (matrixAFStageSuccIndexEquiv qubitLocalDim n (i, b)) =
      Fin.snoc (qubitAFConfigEquiv n i) (finTwoEquivBool b) := by
  rw [qubitAFConfigEquiv]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Equiv.prodComm_apply, Prod.map, Prod.swap_prod_mk]
  rfl

def qubitStageMatrix (n : ℕ)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    PrimeAFMatrixStageAlgebra qubitLocalDim n :=
  Matrix.reindex (qubitAFConfigEquiv n).symm (qubitAFConfigEquiv n).symm A

theorem qubitStageMatrix_sum {ι : Type*} [Fintype ι]
    (n : ℕ) (A : ι → Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    qubitStageMatrix n (∑ i, A i) = ∑ i, qubitStageMatrix n (A i) := by
  ext x y
  simp [qubitStageMatrix, Matrix.reindex_apply, Matrix.sum_apply]

theorem qubitStageMatrix_smul (n : ℕ) (c : ℂ)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    qubitStageMatrix n (c • A) = c • qubitStageMatrix n A := by
  ext x y
  simp [qubitStageMatrix, Matrix.reindex_apply]

def appendQubitIdentity (n : ℕ)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Matrix (Fin (n + 1) → Bool) (Fin (n + 1) → Bool) ℂ :=
  fun x y => A (Fin.init x) (Fin.init y) *
    if x (Fin.last n) = y (Fin.last n) then 1 else 0

theorem matrixAFStageSuccHom_qubitStageMatrix (n : ℕ)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    matrixAFStageSuccHom qubitLocalDim n (qubitStageMatrix n A) =
      qubitStageMatrix (n + 1) (appendQubitIdentity n A) := by
  ext i j
  rw [show i = matrixAFStageSuccIndexEquiv qubitLocalDim n
      ((matrixAFStageSuccIndexEquiv qubitLocalDim n).symm i) by
        exact (matrixAFStageSuccIndexEquiv qubitLocalDim n).apply_symm_apply i |>.symm]
  rw [show j = matrixAFStageSuccIndexEquiv qubitLocalDim n
      ((matrixAFStageSuccIndexEquiv qubitLocalDim n).symm j) by
        exact (matrixAFStageSuccIndexEquiv qubitLocalDim n).apply_symm_apply j |>.symm]
  rcases (matrixAFStageSuccIndexEquiv qubitLocalDim n).symm i with ⟨i, b⟩
  rcases (matrixAFStageSuccIndexEquiv qubitLocalDim n).symm j with ⟨j, c⟩
  simp only [qubitLocalDim] at b c ⊢
  unfold matrixAFStageSuccHom PrimeQuasiLocalCharge.matrixReindexStarAlgEquiv
    PrimeQuasiLocalCharge.kroneckerOneStarAlgHom
  change Matrix.reindex (matrixAFStageSuccIndexEquiv qubitLocalDim n)
      (matrixAFStageSuccIndexEquiv qubitLocalDim n)
      ((qubitStageMatrix n A) ⊗ₖ
        (1 : Matrix (Fin (qubitLocalDim (n + 1)))
          (Fin (qubitLocalDim (n + 1))) ℂ))
        (matrixAFStageSuccIndexEquiv qubitLocalDim n (i, b))
        (matrixAFStageSuccIndexEquiv qubitLocalDim n (j, c)) = _
  rw [Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  change ((qubitStageMatrix n A) ⊗ₖ
      (1 : Matrix (Fin (qubitLocalDim (n + 1)))
        (Fin (qubitLocalDim (n + 1))) ℂ))
      (i, b) (j, c) =
    appendQubitIdentity n A
      (qubitAFConfigEquiv (n + 1)
        (matrixAFStageSuccIndexEquiv qubitLocalDim n (i, b)))
      (qubitAFConfigEquiv (n + 1)
        (matrixAFStageSuccIndexEquiv qubitLocalDim n (j, c)))
  rw [qubitAFConfigEquiv_succ_apply, qubitAFConfigEquiv_succ_apply]
  simp [qubitStageMatrix, appendQubitIdentity, Matrix.reindex_apply, Matrix.one_apply]

theorem appendQubitIdentity_finitePauliMatrix {n : ℕ}
    (P : Fin n → Option (Fin 3)) :
    appendQubitIdentity n (finitePauliMatrix P) =
      finitePauliMatrix (Fin.snoc P none) := by
  ext x y
  rw [finitePauliMatrix_snoc]
  simp [appendQubitIdentity, Matrix.reindex_apply,
    snocConfig_symm_apply, boolPauliOption, Matrix.one_apply]

theorem matrixAFStageSuccHom_qubitPauli (n : ℕ)
    (P : Fin n → Option (Fin 3)) :
    matrixAFStageSuccHom qubitLocalDim n
        (qubitStageMatrix n (finitePauliMatrix P)) =
      qubitStageMatrix (n + 1) (finitePauliMatrix (Fin.snoc P none)) := by
  rw [matrixAFStageSuccHom_qubitStageMatrix,
    appendQubitIdentity_finitePauliMatrix]

theorem norm_qubitStageMatrix (n : ℕ)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    ‖qubitStageMatrix n A‖ = ‖A‖ := by
  change ‖PrimeQuasiLocalCharge.matrixReindexStarAlgEquiv
      (qubitAFConfigEquiv n).symm A‖ = ‖A‖
  exact StarAlgEquiv.norm_map _ _

def qubitUHFPauli (n : ℕ) (P : Fin n → Option (Fin 3)) :
    PrimeUHFAlgebra qubitLocalDim :=
  matrixAFStageToUHF n (qubitStageMatrix n (finitePauliMatrix P))

theorem qubitUHFPauli_snoc_none (n : ℕ)
    (P : Fin n → Option (Fin 3)) :
    qubitUHFPauli (n + 1) (Fin.snoc P none) = qubitUHFPauli n P := by
  rw [qubitUHFPauli, qubitUHFPauli, ← matrixAFStageSuccHom_qubitPauli]
  exact matrixAFStageToUHF_succ n _

theorem norm_qubitUHFPauli (n : ℕ) (P : Fin n → Option (Fin 3)) :
    ‖qubitUHFPauli n P‖ = 1 := by
  rw [qubitUHFPauli, norm_matrixAFStageToUHF, norm_qubitStageMatrix,
    norm_finitePauliMatrix]

theorem isSelfAdjoint_qubitStagePauli (n : ℕ)
    (P : Fin n → Option (Fin 3)) :
    IsSelfAdjoint (qubitStageMatrix n (finitePauliMatrix P)) := by
  rw [IsSelfAdjoint]
  change star (PrimeQuasiLocalCharge.matrixReindexStarAlgEquiv
      (qubitAFConfigEquiv n).symm (finitePauliMatrix P)) = _
  rw [← map_star, Matrix.star_eq_conjTranspose, finitePauliMatrix_isHermitian]
  rfl

theorem isSelfAdjoint_qubitUHFPauli (n : ℕ)
    (P : Fin n → Option (Fin 3)) :
    IsSelfAdjoint (qubitUHFPauli n P) := by
  rw [IsSelfAdjoint, qubitUHFPauli, ← map_star]
  exact congrArg (matrixAFStageToUHF n)
    (isSelfAdjoint_qubitStagePauli n P).star_eq

def pauliRightExtend {n : ℕ} (P : Fin n → Option (Fin 3)) :
    (r : ℕ) → Fin (n + r) → Option (Fin 3)
  | 0 => P
  | r + 1 => Fin.snoc (pauliRightExtend P r) none

@[simp] theorem pauliRightExtend_zero {n : ℕ}
    (P : Fin n → Option (Fin 3)) :
    pauliRightExtend P 0 = P := rfl

@[simp] theorem pauliRightExtend_succ {n : ℕ}
    (P : Fin n → Option (Fin 3)) (r : ℕ) :
    pauliRightExtend P (r + 1) =
      Fin.snoc (pauliRightExtend P r) none := rfl

theorem qubitUHFPauli_rightExtend {n : ℕ}
    (P : Fin n → Option (Fin 3)) (r : ℕ) :
    qubitUHFPauli (n + r) (pauliRightExtend P r) = qubitUHFPauli n P := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pauliRightExtend_succ]
      have hs := qubitUHFPauli_snoc_none (n + r) (pauliRightExtend P r)
      exact (by simpa only [Nat.add_succ] using hs.trans ih)

theorem snoc_siteLabel_none {n : ℕ} (v : Fin n) (q : Fin 3) :
    Fin.snoc (siteLabel v q) none = siteLabel v.castSucc q := by
  funext j
  cases j using Fin.lastCases with
  | last =>
      have h : Fin.last n ≠ v.castSucc := (Fin.castSucc_ne_last v).symm
      simp [siteLabel, h]
  | cast j =>
      simp [siteLabel, Fin.castSucc_inj]

theorem snoc_pairLabel_none {n : ℕ} (v w : Fin n) (a b : Fin 3) :
    Fin.snoc (pairLabel v w a b) none =
      pairLabel v.castSucc w.castSucc a b := by
  funext j
  cases j using Fin.lastCases with
  | last =>
      have hv : Fin.last n ≠ v.castSucc := (Fin.castSucc_ne_last v).symm
      have hw : Fin.last n ≠ w.castSucc := (Fin.castSucc_ne_last w).symm
      simp [pairLabel, hv, hw]
  | cast j =>
      simp [pairLabel, Fin.castSucc_inj]

theorem pauliRightExtend_siteLabel {n : ℕ} (v : Fin n) (q : Fin 3) (r : ℕ) :
    pauliRightExtend (siteLabel v q) r = siteLabel (Fin.castAdd r v) q := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pauliRightExtend_succ, ih, snoc_siteLabel_none,
        Fin.castSucc_castAdd]

theorem pauliRightExtend_pairLabel {n : ℕ}
    (v w : Fin n) (a b : Fin 3) (r : ℕ) :
    pauliRightExtend (pairLabel v w a b) r =
      pairLabel (Fin.castAdd r v) (Fin.castAdd r w) a b := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pauliRightExtend_succ, ih, snoc_pairLabel_none,
        Fin.castSucc_castAdd, Fin.castSucc_castAdd]

def infinitePathUHFPauli : InfinitePathLabel → PrimeUHFAlgebra qubitLocalDim
  | Sum.inl (s, q) =>
      qubitUHFPauli (s + 1) (siteLabel (Fin.last s) q)
  | Sum.inr (e, ab) =>
      qubitUHFPauli (e + 2)
        (pairLabel (Fin.castSucc (Fin.last e)) (Fin.last (e + 1)) ab.1 ab.2)

theorem norm_infinitePathUHFPauli (i : InfinitePathLabel) :
    ‖infinitePathUHFPauli i‖ = 1 := by
  rcases i with ⟨s, q⟩ | ⟨e, ab⟩ <;>
    simp only [infinitePathUHFPauli, norm_qubitUHFPauli]

theorem isSelfAdjoint_infinitePathUHFPauli (i : InfinitePathLabel) :
    IsSelfAdjoint (infinitePathUHFPauli i) := by
  rcases i with ⟨s, q⟩ | ⟨e, ab⟩ <;>
    exact isSelfAdjoint_qubitUHFPauli _ _

theorem qubitUHFPauli_site_castAdd (s r : ℕ) (q : Fin 3) :
    qubitUHFPauli ((s + 1) + r)
        (siteLabel (Fin.castAdd r (Fin.last s)) q) =
      infinitePathUHFPauli (Sum.inl (s, q)) := by
  rw [← pauliRightExtend_siteLabel]
  exact qubitUHFPauli_rightExtend (siteLabel (Fin.last s) q) r

theorem qubitUHFPauli_edge_castAdd (e r : ℕ) (ab : Fin 3 × Fin 3) :
    qubitUHFPauli ((e + 2) + r)
        (pairLabel
          (Fin.castAdd r (Fin.castSucc (Fin.last e)))
          (Fin.castAdd r (Fin.last (e + 1))) ab.1 ab.2) =
      infinitePathUHFPauli (Sum.inr (e, ab)) := by
  rw [← pauliRightExtend_pairLabel]
  exact qubitUHFPauli_rightExtend
    (pairLabel (Fin.castSucc (Fin.last e)) (Fin.last (e + 1)) ab.1 ab.2) r

/-- A single-site Pauli at any finite stage is exactly the corresponding countable UHF
observable.  The proof peels trailing identity qubits rather than using a noncanonical cast. -/
theorem qubitUHFPauli_siteLabel_eq_infinite :
    ∀ {n : ℕ} (s : Fin n) (q : Fin 3),
      qubitUHFPauli n (siteLabel s q) =
        infinitePathUHFPauli (Sum.inl (s.val, q)) := by
  intro n
  induction n with
  | zero =>
      intro s
      exact Fin.elim0 s
  | succ n ih =>
      intro s q
      refine Fin.lastCases ?_ (fun s => ?_) s
      · rfl
      · rw [← snoc_siteLabel_none, qubitUHFPauli_snoc_none, ih]
        rfl

/-- A nearest-neighbour Pauli pair at any finite stage is exactly the corresponding countable
UHF observable. -/
theorem qubitUHFPauli_adjacentPair_eq_infinite :
    ∀ (n : ℕ) (e : Fin (n + 1)) (ab : Fin 3 × Fin 3),
      qubitUHFPauli (n + 2)
          (pairLabel e.castSucc e.succ ab.1 ab.2) =
        infinitePathUHFPauli (Sum.inr (e.val, ab)) := by
  intro n
  induction n with
  | zero =>
      intro e ab
      fin_cases e
      rfl
  | succ n ih =>
      intro e ab
      refine Fin.lastCases ?_ (fun e => ?_) e
      · rfl
      · have hsucc : e.castSucc.succ = e.succ.castSucc := Fin.ext rfl
        rw [hsucc, ← snoc_pairLabel_none, qubitUHFPauli_snoc_none, ih]
        rfl

end

end GaloisForLFunctions.HTGeometry
