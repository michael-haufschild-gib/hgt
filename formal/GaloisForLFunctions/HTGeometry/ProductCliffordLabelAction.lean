import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordHallSymmetryReduction

/-!
# The Pauli relabelling induced by a product Clifford

Conjugating a single-qubit Pauli by a Clifford returns a scalar multiple of another Pauli, and the
identity is returned exactly when the identity is conjugated.  Choosing that datum once gives a
sitewise relabelling of Pauli labels and a phase; assembling it over the qubits gives the
relabelling induced by a product Clifford, which preserves the support of every label.
-/

open Matrix

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section SingleQubit

/-- The Pauli relabelling induced by one Clifford. -/
def qubitCliffordRelabel (g : QubitTwoDesign.BinaryOctahedral) (p : Option (Fin 3)) :
    Option (Fin 3) :=
  (exists_booleanQubitClifford_conj_boolPauliOption g p).choose

/-- The phase produced by conjugating one Pauli by one Clifford. -/
def qubitCliffordPhase (g : QubitTwoDesign.BinaryOctahedral) (p : Option (Fin 3)) : ℂ :=
  ((exists_booleanQubitClifford_conj_boolPauliOption g p).choose_spec).choose

theorem qubitCliffordRelabel_none_iff (g : QubitTwoDesign.BinaryOctahedral)
    (p : Option (Fin 3)) : qubitCliffordRelabel g p = none ↔ p = none :=
  (((exists_booleanQubitClifford_conj_boolPauliOption g p).choose_spec).choose_spec).1

theorem qubitClifford_conj_boolPauliOption (g : QubitTwoDesign.BinaryOctahedral)
    (p : Option (Fin 3)) :
    booleanQubitClifford g * boolPauliOption p * (booleanQubitClifford g)ᴴ =
      qubitCliffordPhase g p • boolPauliOption (qubitCliffordRelabel g p) :=
  (((exists_booleanQubitClifford_conj_boolPauliOption g p).choose_spec).choose_spec).2

end SingleQubit

section ProductQubit

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The Pauli relabelling induced by a product Clifford. -/
def productCliffordRelabel (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) : σ → Option (Fin 3) :=
  fun s => qubitCliffordRelabel (g s) (P s)

/-- The phase produced by conjugating a Pauli word by a product Clifford. -/
def productCliffordPhase (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) : ℂ :=
  ∏ s, qubitCliffordPhase (g s) (P s)

/-- **A product Clifford preserves the support of every Pauli label.** -/
theorem productCliffordRelabel_none_iff (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) (s : σ) :
    productCliffordRelabel g P s = none ↔ P s = none :=
  qubitCliffordRelabel_none_iff (g s) (P s)

/-- **Conjugation of a Pauli word by a product Clifford.** -/
theorem finiteProductCliffordGate_conj_finitePauliMatrix_relabel
    (g : σ → QubitTwoDesign.BinaryOctahedral) (P : σ → Option (Fin 3)) :
    finiteProductCliffordGate g * finitePauliMatrix P * (finiteProductCliffordGate g)ᴴ =
      productCliffordPhase g P • finitePauliMatrix (productCliffordRelabel g P) := by
  classical
  rw [finiteProductCliffordGate, finitePauliMatrix_eq_finiteLocalMatrix,
    finiteLocalMatrix_conjTranspose, finiteLocalMatrix_mul, finiteLocalMatrix_mul]
  rw [show
    (fun s => booleanQubitClifford (g s) * boolPauliOption (P s) *
      (booleanQubitClifford (g s))ᴴ) =
    (fun s => qubitCliffordPhase (g s) (P s) •
      boolPauliOption (qubitCliffordRelabel (g s) (P s))) by
      funext s
      exact qubitClifford_conj_boolPauliOption (g s) (P s)]
  exact finiteLocalMatrix_pointwise_smul (fun s => qubitCliffordPhase (g s) (P s))
    (fun s => boolPauliOption (qubitCliffordRelabel (g s) (P s)))

theorem finiteProductCliffordGate_mul_conjTranspose
    (g : σ → QubitTwoDesign.BinaryOctahedral) :
    finiteProductCliffordGate g * (finiteProductCliffordGate g)ᴴ = 1 :=
  mul_eq_one_comm.mp (finiteProductCliffordGate_unitary g)

/-- **The conjugation phase is a sign.** -/
theorem productCliffordPhase_sq (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) : (productCliffordPhase g P) ^ (2 : ℕ) = 1 := by
  classical
  set C := finiteProductCliffordGate g with hC
  have hCC : Cᴴ * C = 1 := finiteProductCliffordGate_unitary g
  have hCC' : C * Cᴴ = 1 := finiteProductCliffordGate_mul_conjTranspose g
  have hconj := finiteProductCliffordGate_conj_finitePauliMatrix_relabel g P
  have hsq : (C * finitePauliMatrix P * Cᴴ) * (C * finitePauliMatrix P * Cᴴ) = 1 := by
    calc (C * finitePauliMatrix P * Cᴴ) * (C * finitePauliMatrix P * Cᴴ)
        = C * finitePauliMatrix P * (Cᴴ * C) * finitePauliMatrix P * Cᴴ := by
          simp only [Matrix.mul_assoc]
      _ = C * (finitePauliMatrix P * finitePauliMatrix P) * Cᴴ := by
          rw [hCC]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [finitePauliMatrix_mul_self, Matrix.mul_one, hCC']
  rw [hconj] at hsq
  have hrhs : (productCliffordPhase g P • finitePauliMatrix (productCliffordRelabel g P)) *
      (productCliffordPhase g P • finitePauliMatrix (productCliffordRelabel g P)) =
      ((productCliffordPhase g P) ^ (2 : ℕ)) • (1 : Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, finitePauliMatrix_mul_self, sq]
  rw [hrhs] at hsq
  have hx : (fun _ : σ => false) ∈ (Finset.univ : Finset (FiniteQubitConfiguration σ)) :=
    Finset.mem_univ _
  have hentry := congrFun (congrFun hsq (fun _ : σ => false)) (fun _ : σ => false)
  simpa using hentry

theorem productCliffordPhase_eq_one_or_neg_one (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) :
    productCliffordPhase g P = 1 ∨ productCliffordPhase g P = -1 := by
  have h := productCliffordPhase_sq g P
  have hfac : (productCliffordPhase g P - 1) * (productCliffordPhase g P + 1) = 0 := by
    have : (productCliffordPhase g P) ^ (2 : ℕ) - 1 = 0 := by rw [h]; ring
    linear_combination this
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (by linear_combination h1)

theorem productCliffordPhase_ne_zero (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) : productCliffordPhase g P ≠ 0 := by
  rcases productCliffordPhase_eq_one_or_neg_one g P with h | h <;> rw [h] <;> norm_num

/-- **The induced relabelling is injective.** -/
theorem productCliffordRelabel_injective (g : σ → QubitTwoDesign.BinaryOctahedral) :
    Function.Injective (productCliffordRelabel g) := by
  classical
  intro P Q hPQ
  by_contra hne
  set C := finiteProductCliffordGate g with hC
  have hCC : Cᴴ * C = 1 := finiteProductCliffordGate_unitary g
  have hCC' : C * Cᴴ = 1 := finiteProductCliffordGate_mul_conjTranspose g
  have hP := finiteProductCliffordGate_conj_finitePauliMatrix_relabel g P
  have hQ := finiteProductCliffordGate_conj_finitePauliMatrix_relabel g Q
  rw [hPQ] at hP
  have hmix : C * (productCliffordPhase g Q • finitePauliMatrix P) * Cᴴ =
      C * (productCliffordPhase g P • finitePauliMatrix Q) * Cᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hP, Matrix.mul_smul, Matrix.smul_mul, hQ,
      smul_smul, smul_smul, mul_comm]
  have hcancel : productCliffordPhase g Q • finitePauliMatrix P =
      productCliffordPhase g P • finitePauliMatrix Q := by
    have h1 : Cᴴ * (C * (productCliffordPhase g Q • finitePauliMatrix P) * Cᴴ) * C =
        Cᴴ * (C * (productCliffordPhase g P • finitePauliMatrix Q) * Cᴴ) * C := by
      rw [hmix]
    have hsimp : ∀ X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ,
        Cᴴ * (C * X * Cᴴ) * C = X := by
      intro X
      simp only [Matrix.mul_assoc]
      rw [hCC, Matrix.mul_one, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    rw [hsimp, hsimp] at h1
    exact h1
  have hzero : (∑ L, (if L = P then productCliffordPhase g Q
      else if L = Q then -(productCliffordPhase g P) else 0) • finitePauliMatrix L) = 0 := by
    have hpair : (∑ L, (if L = P then productCliffordPhase g Q
        else if L = Q then -(productCliffordPhase g P) else 0) • finitePauliMatrix L) =
        productCliffordPhase g Q • finitePauliMatrix P +
          (-(productCliffordPhase g P)) • finitePauliMatrix Q := by
      rw [Finset.sum_eq_add_of_mem P Q (Finset.mem_univ P) (Finset.mem_univ Q) hne]
      · rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
      · intro L _ hL
        rw [if_neg hL.1, if_neg hL.2, zero_smul]
    rw [hpair, hcancel, neg_smul]
    simp
  have hli := finitePauliMatrix_linearIndependent (σ := σ)
  have hall := (Fintype.linearIndependent_iff.mp hli) _ hzero
  have hPzero := hall P
  rw [if_pos rfl] at hPzero
  exact productCliffordPhase_ne_zero g Q hPzero

/-- The relabelling as a permutation of Pauli labels. -/
def productCliffordRelabelEquiv (g : σ → QubitTwoDesign.BinaryOctahedral) :
    Equiv.Perm (σ → Option (Fin 3)) :=
  Equiv.ofBijective (productCliffordRelabel g)
    (Finite.injective_iff_bijective.mp (productCliffordRelabel_injective g))

@[simp] theorem productCliffordRelabelEquiv_apply (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) :
    productCliffordRelabelEquiv g P = productCliffordRelabel g P := rfl

end ProductQubit

end GaloisForLFunctions.HTGeometry
