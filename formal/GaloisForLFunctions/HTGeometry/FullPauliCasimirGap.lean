import GaloisForLFunctions.HTGeometry.CollectiveReplicaWeightGap
import GaloisForLFunctions.HTGeometry.FullPauliCollectiveCasimir

/-!
# Completeness of the Pauli family

The four single-qubit Pauli matrices satisfy the completeness relation
`∑_m (σ_m)_{ab}(σ_m)_{cd} = 2 δ_{ad} δ_{bc}`, which is a sixteen-case check.  Taking products over
the register turns it into the `n`-qubit relation with the factor `2^n`, and relabelling the
register index carries it to the matrices used by the collective commutator representation.
-/

open scoped BigOperators Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Completeness

/-- **Single-qubit Pauli completeness.** -/
theorem sum_pauli1_entry_mul (a b c d : Fin 2) :
    (∑ m : Fin 4, QuantumAlg.pauli1 m a b * QuantumAlg.pauli1 m c d)
      = 2 * (if a = d then (1 : ℂ) else 0) * (if b = c then (1 : ℂ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [QuantumAlg.pauli1, QuantumAlg.pauliX, QuantumAlg.pauliY, QuantumAlg.pauliZ,
      Fin.sum_univ_four, Complex.ext_iff] <;> norm_num

/-- **Register Pauli completeness.** -/
theorem sum_pauliStr_entry_mul {n : ℕ} (x y z w : Fin n → Fin 2) :
    (∑ s : Fin n → Fin 4, QuantumAlg.pauliStr s x y * QuantumAlg.pauliStr s z w)
      = (2 : ℂ) ^ n * (if x = w then (1 : ℂ) else 0) * (if y = z then (1 : ℂ) else 0) := by
  classical
  have hterm : ∀ s : Fin n → Fin 4,
      QuantumAlg.pauliStr s x y * QuantumAlg.pauliStr s z w
        = ∏ k : Fin n, (QuantumAlg.pauli1 (s k) (x k) (y k) *
            QuantumAlg.pauli1 (s k) (z k) (w k)) := by
    intro s
    show (∏ k, QuantumAlg.pauli1 (s k) (x k) (y k)) *
        (∏ k, QuantumAlg.pauli1 (s k) (z k) (w k)) = _
    rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  have hfactor : (∑ s : Fin n → Fin 4, ∏ k : Fin n,
      (QuantumAlg.pauli1 (s k) (x k) (y k) * QuantumAlg.pauli1 (s k) (z k) (w k)))
      = ∏ k : Fin n, ∑ m : Fin 4,
          (QuantumAlg.pauli1 m (x k) (y k) * QuantumAlg.pauli1 m (z k) (w k)) := by
    rw [← Fintype.piFinset_univ,
      ← Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 4)))
        (fun k m => QuantumAlg.pauli1 m (x k) (y k) * QuantumAlg.pauli1 m (z k) (w k))]
  rw [hfactor, Finset.prod_congr rfl fun k _ => sum_pauli1_entry_mul (x k) (y k) (z k) (w k)]
  have hsplit : (∏ k : Fin n, (2 * (if x k = w k then (1 : ℂ) else 0) *
      (if y k = z k then (1 : ℂ) else 0)))
      = (∏ _k : Fin n, (2 : ℂ)) * (∏ k : Fin n, (if x k = w k then (1 : ℂ) else 0)) *
        ∏ k : Fin n, (if y k = z k then (1 : ℂ) else 0) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [hsplit, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  · congr 1
    by_cases hxw : x = w
    · rw [if_pos hxw, hxw]
      exact Finset.prod_eq_one fun k _ => if_pos rfl
    · rw [if_neg hxw]
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hxw
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
  · by_cases hyz : y = z
    · rw [if_pos hyz, hyz]
      exact Finset.prod_eq_one fun k _ => if_pos rfl
    · rw [if_neg hyz]
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hyz
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- **Pauli completeness on the reindexed matrices.** -/
theorem sum_pauliMat_entry_mul {n : ℕ} (i j k l : Fin (2 ^ n)) :
    (∑ s : Fin n → Fin 4, QuantumAlg.pauliMat s i j * QuantumAlg.pauliMat s k l)
      = (2 : ℂ) ^ n * (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0) := by
  classical
  have hentry : ∀ s : Fin n → Fin 4, ∀ u v : Fin (2 ^ n),
      QuantumAlg.pauliMat s u v
        = QuantumAlg.pauliStr s (finFunctionFinEquiv.symm u) (finFunctionFinEquiv.symm v) := by
    intro s u v
    rfl
  rw [Finset.sum_congr rfl fun s _ => by rw [hentry s i j, hentry s k l],
    sum_pauliStr_entry_mul]
  congr 1
  · congr 1
    by_cases h : i = l
    · rw [if_pos h, if_pos (by rw [h] : finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm l)]
    · rw [if_neg h, if_neg (fun hh => h (finFunctionFinEquiv.symm.injective hh))]
  · by_cases h : j = k
    · rw [if_pos h, if_pos (by rw [h] : finFunctionFinEquiv.symm j = finFunctionFinEquiv.symm k)]
    · rw [if_neg h, if_neg (fun hh => h (finFunctionFinEquiv.symm.injective hh))]


end Completeness

section Bridge

variable {R : Type*} [Fintype R] [DecidableEq R]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The collective commutator representation of a one-copy matrix. -/
def collRho (R : Type*) [Fintype R] [DecidableEq R] {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℂ) : Matrix ((R → α) × (R → α)) ((R → α) × (R → α)) ℂ :=
  matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α A)

theorem collRho_unit (a b : α) : collRho R (unitMatrix a b) = collGen R a b := rfl

theorem matrix_expand (A : Matrix α α ℂ) : A = ∑ i, ∑ j, A i j • unitMatrix i j := by
  classical
  funext u v
  rw [Matrix.sum_apply]
  have hstep : ∀ i : α, (∑ j, A i j • unitMatrix i j) u v
      = if u = i then A i v else 0 := by
    intro i
    rw [Matrix.sum_apply]
    have hterm : ∀ j : α, (A i j • unitMatrix i j) u v
        = if j = v then (if u = i then A i j else 0) else 0 := by
      intro j
      rw [Matrix.smul_apply, unitMatrix_apply, smul_eq_mul]
      by_cases h1 : u = i
      · by_cases h2 : v = j
        · rw [if_pos ⟨h1, h2⟩, if_pos h2.symm, if_pos h1, mul_one]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => h2 hh.symm), mul_zero]
      · rw [if_neg (fun hh => h1 hh.1), if_neg h1, mul_zero]
        by_cases h2 : j = v <;> simp [h2]
    rw [Finset.sum_congr rfl fun j _ => hterm j,
      Finset.sum_ite_eq' Finset.univ v (fun j => if u = i then A i j else 0)]
    simp
  rw [Finset.sum_congr rfl fun i _ => hstep i,
    Finset.sum_ite_eq Finset.univ u (fun i => A i v)]
  simp

theorem collRho_expand (A : Matrix α α ℂ) :
    collRho R A = ∑ i, ∑ j, A i j • collGen R i j := by
  classical
  have hlin : ∀ (c : ℂ) (M : Matrix α α ℂ), collRho R (c • M) = c • collRho R M := by
    intro c M
    show matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α (c • M))
      = c • matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α M)
    have h1 : finiteReplicaCollectiveMatrix R α (c • M)
        = c • finiteReplicaCollectiveMatrix R α M := by
      have := (finiteReplicaCollectiveMatrixLinear R α).map_smul c M
      exact this
    rw [h1, map_smul]
  have hadd : ∀ M N : Matrix α α ℂ, collRho R (M + N) = collRho R M + collRho R N := by
    intro M N
    show matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α (M + N))
      = matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α M)
        + matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α N)
    have h1 : finiteReplicaCollectiveMatrix R α (M + N)
        = finiteReplicaCollectiveMatrix R α M + finiteReplicaCollectiveMatrix R α N := by
      have := (finiteReplicaCollectiveMatrixLinear R α).map_add M N
      exact this
    rw [h1, map_add]
  have hzero : collRho R (0 : Matrix α α ℂ) = 0 := by
    have h0 : (0 : Matrix α α ℂ) = (0 : ℂ) • (0 : Matrix α α ℂ) := by rw [zero_smul]
    rw [h0, hlin, zero_smul]
  have hsumF : ∀ (s : Finset α) (F : α → Matrix α α ℂ),
      collRho R (∑ k ∈ s, F k) = ∑ k ∈ s, collRho R (F k) := by
    intro s F
    classical
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, hzero]
    | insert k s hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk, hadd, ih]
  conv_lhs => rw [matrix_expand A]
  rw [hsumF]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsumF]
  exact Finset.sum_congr rfl fun j _ => by rw [hlin, collRho_unit]


/-- The four-fold expansion of a product of two collective representations. -/
theorem collRho_mul_expand (A B : Matrix α α ℂ) :
    collRho R A * collRho R B
      = ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (collGen R i j * collGen R k l) := by
  classical
  rw [collRho_expand, collRho_expand, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_smul_comm]

/-- **The Pauli Casimir is the collective matrix-unit Casimir scaled by the one-copy
dimension.** -/
theorem sum_collRho_sq_pauliMat {n : ℕ} :
    (∑ s : Fin n → Fin 4,
        collRho R (QuantumAlg.pauliMat s) * collRho R (QuantumAlg.pauliMat s))
      = ((2 : ℂ) ^ n) • familyCasimir (fun a b : Fin (2 ^ n) => collGen R a b) := by
  classical
  have hmid : ∀ i : Fin (2 ^ n),
      (∑ s : Fin n → Fin 4, ∑ j, ∑ k, ∑ l,
          (QuantumAlg.pauliMat s i j * QuantumAlg.pauliMat s k l) •
            (collGen R i j * collGen R k l))
        = ∑ j, ∑ k, ∑ l,
          (((2 : ℂ) ^ n * (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) •
            (collGen R i j * collGen R k l)) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, sum_pauliMat_entry_mul]
  have hcollapse : ∀ i : Fin (2 ^ n),
      (∑ j, ∑ k, ∑ l,
        (((2 : ℂ) ^ n * (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) •
          (collGen R i j * collGen R k l)))
      = ((2 : ℂ) ^ n) • ∑ j, collGen R i j * collGen R j i := by
    intro i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hk : ∀ k : Fin (2 ^ n), (∑ l,
        (((2 : ℂ) ^ n * (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) •
          (collGen R i j * collGen R k l)))
        = if j = k then ((2 : ℂ) ^ n) • (collGen R i j * collGen R k i) else 0 := by
      intro k
      have hl : ∀ l : Fin (2 ^ n),
          (((2 : ℂ) ^ n * (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0)) •
            (collGen R i j * collGen R k l))
          = if i = l then
              (if j = k then ((2 : ℂ) ^ n) • (collGen R i j * collGen R k l) else 0) else 0 := by
        intro l
        by_cases h1 : i = l
        · by_cases h2 : j = k
          · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
            congr 1
            ring
          · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
            simp
        · rw [if_neg h1, if_neg h1]
          simp
      rw [Finset.sum_congr rfl fun l _ => hl l,
        Finset.sum_ite_eq Finset.univ i
          (fun l => if j = k then ((2 : ℂ) ^ n) • (collGen R i j * collGen R k l) else 0)]
      simp
    rw [Finset.sum_congr rfl fun k _ => hk k,
      Finset.sum_ite_eq Finset.univ j
        (fun k => ((2 : ℂ) ^ n) • (collGen R i j * collGen R k i))]
    simp
  rw [Finset.sum_congr rfl fun s _ =>
      collRho_mul_expand (R := R) (QuantumAlg.pauliMat s) (QuantumAlg.pauliMat s),
    Finset.sum_comm, Finset.sum_congr rfl fun i _ => hmid i,
    Finset.sum_congr rfl fun i _ => hcollapse i, ← Finset.smul_sum]
  rfl


theorem collRho_one : collRho R (1 : Matrix α α ℂ) = 0 := by
  classical
  have hcoll : finiteReplicaCollectiveMatrix R α (1 : Matrix α α ℂ)
      = (Fintype.card R : ℂ) • (1 : Matrix (R → α) (R → α) ℂ) := by
    have hsite : ∀ r : R, finiteTensorSingleSiteMatrix r (1 : Matrix α α ℂ)
        = (1 : Matrix (R → α) (R → α) ℂ) := by
      intro r
      show finiteTensorLocalMatrix (fun s => if s = r then (1 : Matrix α α ℂ) else 1) = 1
      have hfun : (fun s : R => if s = r then (1 : Matrix α α ℂ) else 1)
          = fun _ : R => (1 : Matrix α α ℂ) := by
        funext s
        by_cases h : s = r <;> simp [h]
      rw [hfun]
      exact finiteTensorLocalMatrix_one
    rw [finiteReplicaCollectiveMatrix, Finset.sum_congr rfl fun r _ => hsite r,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  show matrixCommutatorRepresentation (finiteReplicaCollectiveMatrix R α (1 : Matrix α α ℂ)) = 0
  rw [hcoll, map_smul]
  have hone : matrixCommutatorRepresentation (1 : Matrix (R → α) (R → α) ℂ) = 0 := by
    show ((1 : Matrix (R → α) (R → α) ℂ) ⊗ₖ (1 : Matrix (R → α) (R → α) ℂ)
      - (1 : Matrix (R → α) (R → α) ℂ).transpose ⊗ₖ (1 : Matrix (R → α) (R → α) ℂ)) = 0
    rw [Matrix.transpose_one, sub_self]
  rw [hone, smul_zero]

theorem pauliMat_zero_eq_one {n : ℕ} :
    QuantumAlg.pauliMat (0 : Fin n → Fin 4) = 1 := by
  show (QuantumAlg.pauliStr (0 : Fin n → Fin 4)).submatrix finFunctionFinEquiv.symm
      finFunctionFinEquiv.symm = 1
  rw [QuantumAlg.pauliStr_zero]
  funext i j
  rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun hh => h (finFunctionFinEquiv.symm.injective hh)]

/-- **The full-Pauli collective Casimir is the collective matrix-unit Casimir scaled by the
one-copy dimension.** -/
theorem fullPauliCasimir_eq_smul {n : ℕ} :
    (∑ q : NonidentityPauliLabel n, finiteReplicaFullPauliCommutatorMatrix R n q *
        finiteReplicaFullPauliCommutatorMatrix R n q)
      = ((2 : ℂ) ^ n) • familyCasimir (fun a b : Fin (2 ^ n) => collGen R a b) := by
  classical
  have hrho : ∀ s : Fin n → Fin 4,
      finiteReplicaCommutatorMatrixLieHom R (Fin (2 ^ n)) (QuantumAlg.pauliMat s)
        = collRho R (QuantumAlg.pauliMat s) := fun _ => rfl
  have hzero : collRho R (QuantumAlg.pauliMat (0 : Fin n → Fin 4)) *
      collRho R (QuantumAlg.pauliMat (0 : Fin n → Fin 4)) = 0 := by
    rw [pauliMat_zero_eq_one, collRho_one, Matrix.zero_mul]
  have hsub : (∑ q : NonidentityPauliLabel n,
      collRho R (QuantumAlg.pauliMat q.1) * collRho R (QuantumAlg.pauliMat q.1))
      = ∑ s : Fin n → Fin 4,
        collRho R (QuantumAlg.pauliMat s) * collRho R (QuantumAlg.pauliMat s) := by
    have hsplit : (∑ s : Fin n → Fin 4,
        collRho R (QuantumAlg.pauliMat s) * collRho R (QuantumAlg.pauliMat s))
        = (collRho R (QuantumAlg.pauliMat (0 : Fin n → Fin 4)) *
            collRho R (QuantumAlg.pauliMat (0 : Fin n → Fin 4)))
          + ∑ s ∈ Finset.univ.erase (0 : Fin n → Fin 4),
            collRho R (QuantumAlg.pauliMat s) * collRho R (QuantumAlg.pauliMat s) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    rw [hsplit, hzero, zero_add]
    refine (Finset.sum_subtype (Finset.univ.erase (0 : Fin n → Fin 4)) (fun s => ?_)
      (fun s => collRho R (QuantumAlg.pauliMat s) * collRho R (QuantumAlg.pauliMat s))).symm
    simp [Finset.mem_erase]
  rw [Finset.sum_congr rfl fun q _ => by
      show finiteReplicaFullPauliCommutatorMatrix R n q *
        finiteReplicaFullPauliCommutatorMatrix R n q
        = collRho R (QuantumAlg.pauliMat q.1) * collRho R (QuantumAlg.pauliMat q.1)
      rw [finiteReplicaFullPauliCommutatorMatrix, hrho],
    hsub, sum_collRho_sq_pauliMat]

/-- **`(16)`, lower half.**  Every nonzero eigenvalue of the full-Pauli collective Casimir is at
least `2D²` with `D = 2^n`. -/
theorem fullPauliCasimir_eigenvalue_gap {n : ℕ} {lam : ℝ}
    {Y : (R → Fin (2 ^ n)) × (R → Fin (2 ^ n)) → ℂ} (hY : Y ≠ 0)
    (heig : (∑ q : NonidentityPauliLabel n, finiteReplicaFullPauliCommutatorMatrix R n q *
        finiteReplicaFullPauliCommutatorMatrix R n q) *ᵥ Y = (lam : ℂ) • Y) :
    lam = 0 ∨ 2 * ((2 : ℝ) ^ n) ^ (2 : ℕ) ≤ lam := by
  classical
  have hD : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hDC : ((2 : ℂ) ^ n) ≠ 0 := by
    simp only [ne_eq, pow_eq_zero_iff']
    norm_num
  have hsm : ∀ (c : ℂ) (M : Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ) (v : (R → Fin (2 ^ n)) × (R → Fin (2 ^ n)) → ℂ),
      (c • M) *ᵥ v = c • (M *ᵥ v) := by
    intro c M v
    funext i
    show (∑ j, (c • M) i j * v j) = c * ∑ j, M i j * v j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul]; ring
  rw [fullPauliCasimir_eq_smul, hsm] at heig
  have hC : familyCasimir (fun a b : Fin (2 ^ n) => collGen R a b) *ᵥ Y
      = ((lam / (2 : ℝ) ^ n : ℝ) : ℂ) • Y := by
    have hstep : ((2 : ℂ) ^ n) • (familyCasimir (fun a b : Fin (2 ^ n) => collGen R a b) *ᵥ Y)
        = ((2 : ℂ) ^ n) • (((lam / (2 : ℝ) ^ n : ℝ) : ℂ) • Y) := by
      rw [heig, smul_smul]
      congr 1
      push_cast
      field_simp
    exact smul_right_injective _ hDC hstep
  have hcard : (Fintype.card (Fin (2 ^ n)) : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_fin]
    push_cast
    ring
  rcases collectiveCasimir_eigenvalue_gap hY hC with h | h
  · left
    have hz : lam / (2 : ℝ) ^ n = 0 := h
    rcases div_eq_zero_iff.mp hz with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt hD)
  · right
    rw [hcard, le_div_iff₀ hD] at h
    nlinarith [h]

end Bridge



end

end GaloisForLFunctions.HTGeometry
