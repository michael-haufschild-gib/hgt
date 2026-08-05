import GaloisForLFunctions.HTGeometry.TwoLocalPauliLieGeneration
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.SingleQubitDLA
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.OrthogonalDLA

/-!
# Maximal linear coverage by short one-local Pauli words

Every full Pauli basis matrix is a product of at most one single-site Pauli
per occupied qubit.  Consequently words of length at most `n` in one-local
Pauli gates linearly span the entire operator algebra on `n` qubits.

This is an exact obstruction to using linear span, Lie generation, replica
rank, or Hall expansion alone as a circuit-complexity lower bound: maximal
linear coverage coexists with uniformly linear word length.
-/

open scoped BigOperators Matrix

namespace QuantumAlg

noncomputable section

/-- Matrices supported on at most one qubit. -/
def oneLocalPauliMatrices (n : ℕ) :
    Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, pauliWeight4 s ≤ 1 ∧ A = pauliMat s}

theorem pauliMat_zero_eq_one (n : ℕ) :
    pauliMat (0 : Fin n → Fin 4) = 1 := by
  rw [pauliMat, pauliStr_zero, Matrix.submatrix_one_equiv]

theorem pauliWeight4_eq_zero_iff {n : ℕ} (s : Fin n → Fin 4) :
    pauliWeight4 s = 0 ↔ s = 0 := by
  constructor
  · intro h
    funext i
    by_contra hi
    have himem : i ∈ pauliSupport4 s := by simpa using hi
    have hempty : pauliSupport4 s = ∅ := Finset.card_eq_zero.mp h
    rw [hempty] at himem
    simp at himem
  · intro h
    subst s
    simp [pauliWeight4, pauliSupport4]

theorem pauliWeight4_update_zero_of_mem
    {n : ℕ} (s : Fin n → Fin 4) {i : Fin n}
    (hi : i ∈ pauliSupport4 s) :
    pauliWeight4 (Function.update s i 0) + 1 = pauliWeight4 s := by
  rw [pauliWeight4, pauliWeight4, pauliSupport4_update_zero,
    Finset.card_erase_of_mem hi]
  have hpos : 0 < (pauliSupport4 s).card :=
    Finset.card_pos.mpr ⟨i, hi⟩
  omega

theorem pauliWeight4_siteP_of_ne_zero
    {n : ℕ} (i : Fin n) {a : Fin 4} (ha : a ≠ 0) :
    pauliWeight4 (siteP i a) = 1 := by
  rw [pauliWeight4]
  have hs : pauliSupport4 (siteP i a) = {i} := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [pauliSupport4, ha]
    · simp [pauliSupport4, hji, siteP_ne a hji]
  rw [hs]
  simp

theorem pauliXor_update_zero_siteP
    {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    pauliXor (Function.update s i 0) (siteP i (s i)) = s := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [pauliXor, xor4_zero_left]
  · simp [pauliXor, hji, siteP_ne (s i) hji, xor4_zero_right]

@[simp] theorem phase1_zero_left_local (a : Fin 4) : phase1 0 a = 1 := by
  fin_cases a <;> rfl

@[simp] theorem phase1_zero_right_local (a : Fin 4) : phase1 a 0 = 1 := by
  fin_cases a <;> rfl

theorem pauliPhase_update_zero_siteP
    {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    pauliPhase (Function.update s i 0) (siteP i (s i)) = 1 := by
  rw [pauliPhase]
  apply Finset.prod_eq_one
  intro j _hj
  by_cases hji : j = i
  · subst j
    simp [phase1_zero_left_local]
  · simp [hji, siteP_ne (s i) hji, phase1_zero_right_local]

theorem pauliWeight4_le_n {n : ℕ} (s : Fin n → Fin 4) :
    pauliWeight4 s ≤ n := by
  rw [pauliWeight4]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Fintype.card_fin n)

/-- Every Pauli basis matrix is a product of at most its support size many
one-local Pauli matrices. -/
theorem exists_oneLocalPauliWord
    {n : ℕ} (s : Fin n → Fin 4) :
    ∃ w : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      w.length ≤ pauliWeight4 s ∧
      (∀ A ∈ w, A ∈ oneLocalPauliMatrices n) ∧
      w.prod = pauliMat s := by
  classical
  induction hweight : pauliWeight4 s using Nat.strong_induction_on generalizing s with
  | h weight ih =>
      by_cases hzero : weight = 0
      · have hs : s = 0 :=
          (pauliWeight4_eq_zero_iff s).mp (hweight.trans hzero)
        subst s
        refine ⟨[], by simp, by simp, ?_⟩
        simp [pauliMat_zero_eq_one]
      · have hsupport : (pauliSupport4 s).Nonempty := by
          apply Finset.card_pos.mp
          rw [← pauliWeight4, hweight]
          omega
        obtain ⟨i, hi⟩ := hsupport
        let t := Function.update s i 0
        let u := siteP i (s i)
        have hsi : s i ≠ 0 := by simpa using hi
        have htweight : pauliWeight4 t < weight := by
          have hdrop := pauliWeight4_update_zero_of_mem s hi
          change pauliWeight4 (Function.update s i 0) < weight
          omega
        obtain ⟨w, hwlen, hwlocal, hwprod⟩ :=
          ih (pauliWeight4 t) htweight t rfl
        refine ⟨w ++ [pauliMat u], ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]
          have hdrop := pauliWeight4_update_zero_of_mem s hi
          change pauliWeight4 t + 1 = pauliWeight4 s at hdrop
          rw [hweight] at hdrop
          omega
        · intro A hA
          rw [List.mem_append, List.mem_singleton] at hA
          rcases hA with hA | rfl
          · exact hwlocal A hA
          · exact ⟨u, (pauliWeight4_siteP_of_ne_zero i hsi).le, rfl⟩
        · rw [List.prod_append, hwprod]
          simp only [List.prod_singleton]
          rw [pauliMat_mul_closed, pauliPhase_update_zero_siteP,
            one_smul, pauliXor_update_zero_siteP]

/-- Endpoints of words of at most `n` one-local Pauli gates. -/
def oneLocalPauliWordEndpoints (n : ℕ) :
    Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ w : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
    w.length ≤ n ∧
    (∀ B ∈ w, B ∈ oneLocalPauliMatrices n) ∧
    w.prod = A}

theorem pauliMat_mem_oneLocalPauliWordEndpoints
    {n : ℕ} (s : Fin n → Fin 4) :
    pauliMat s ∈ oneLocalPauliWordEndpoints n := by
  obtain ⟨w, hwlen, hwlocal, hwprod⟩ := exists_oneLocalPauliWord s
  exact ⟨w, hwlen.trans (pauliWeight4_le_n s), hwlocal, hwprod⟩

/-- **Linear coverage is not circuit hardness.** Products of at most `n`
one-local Pauli gates already linearly span the full `2^n`-dimensional
operator algebra. -/
theorem span_oneLocalPauliWordEndpoints_eq_top (n : ℕ) :
    Submodule.span ℂ (oneLocalPauliWordEndpoints n) = ⊤ := by
  apply le_antisymm
  · exact (le_top : Submodule.span ℂ (oneLocalPauliWordEndpoints n) ≤ ⊤)
  · rw [← pauliMat_span_top n]
    exact Submodule.span_mono (Set.range_subset_iff.mpr
      pauliMat_mem_oneLocalPauliWordEndpoints)

end

end QuantumAlg
