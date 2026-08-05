import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra

open scoped BigOperators Matrix
open Matrix

namespace QuantumAlg

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Occupied sites of a phase-free Pauli string. -/
def pauliSupport4 {n : ℕ} (s : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.univ.filter fun i => s i ≠ 0

/-- Hamming weight of a phase-free Pauli string. -/
def pauliWeight4 {n : ℕ} (s : Fin n → Fin 4) : ℕ :=
  (pauliSupport4 s).card

@[simp] theorem mem_pauliSupport4 {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    i ∈ pauliSupport4 s ↔ s i ≠ 0 := by
  simp [pauliSupport4]

theorem pauliSupport4_update_zero {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    pauliSupport4 (Function.update s i 0) = (pauliSupport4 s).erase i := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [pauliSupport4]
  · simp [pauliSupport4, hji]

theorem pauliSupport4_update_nonzero {n : ℕ} (s : Fin n → Fin 4)
    (i : Fin n) {a : Fin 4} (ha : a ≠ 0) :
    pauliSupport4 (Function.update s i a) = insert i (pauliSupport4 s) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [pauliSupport4, ha]
  · simp [pauliSupport4, hji]

@[simp] theorem xor4_self_zero (a : Fin 4) : xor4 a a = 0 := by
  have h := xor4_self_left a 0
  simpa [xor4_zero_right] using h

theorem omega4_zero_right (a : Fin 4) : omega4 a 0 = 0 := by
  rw [omega4_comm, omega4_zero_left]

theorem omega4_xor_self_right (a b : Fin 4) :
    omega4 a (xor4 a b) = omega4 a b := by
  rw [omega4_comm a (xor4 a b), omega4_xor_left,
    omega4_self_zero, omega4_comm b a, zero_add]

/-- Every Pauli string of weight at least three is the symplectic sum of a
strictly lighter nonzero string and a nonzero weight-two string that
anticommute. -/
theorem exists_pauliWeightTwo_anticommuting_decomposition
    {n : ℕ} (s : Fin n → Fin 4) (hlarge : 2 < pauliWeight4 s) :
    ∃ t u : Fin n → Fin 4,
      t ≠ 0 ∧ u ≠ 0 ∧
      pauliWeight4 t < pauliWeight4 s ∧ pauliWeight4 u = 2 ∧
      pauliOmega t u = 1 ∧ pauliXor t u = s := by
  classical
  let S := pauliSupport4 s
  have hScard : 2 < S.card := by simpa [S, pauliWeight4] using hlarge
  have hSpos : 0 < S.card := by omega
  obtain ⟨k, hkS⟩ := Finset.card_pos.mp hSpos
  have hErasePos : 0 < (S.erase k).card := by
    rw [Finset.card_erase_of_mem hkS]
    omega
  obtain ⟨i, hiErase⟩ := Finset.card_pos.mp hErasePos
  have hiS : i ∈ S := Finset.mem_of_mem_erase hiErase
  have hik : i ≠ k := Finset.ne_of_mem_erase hiErase
  have hsi : s i ≠ 0 := by simpa [S] using hiS
  have hsk : s k ≠ 0 := by simpa [S] using hkS
  obtain ⟨b, hbomega⟩ := omega4_anticomm_of_ne hsi
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, omega4_zero_right] at hbomega
    norm_num at hbomega
  let t : Fin n → Fin 4 :=
    Function.update (Function.update s k 0) i b
  let u : Fin n → Fin 4 := pauliXor t s
  have ht_i : t i = b := by simp [t]
  have ht_k : t k = 0 := by simp [t, Ne.symm hik]
  have ht_other {j : Fin n} (hji : j ≠ i) (hjk : j ≠ k) : t j = s j := by
    simp [t, hji, hjk]
  have hu_i : u i = xor4 b (s i) := by simp [u, pauliXor, ht_i]
  have hu_k : u k = s k := by simp [u, pauliXor, ht_k, xor4_zero_left]
  have hu_other {j : Fin n} (hji : j ≠ i) (hjk : j ≠ k) : u j = 0 := by
    simp [u, pauliXor, ht_other hji hjk]
  have hbi : xor4 b (s i) ≠ 0 := by
    intro hzero
    have hbs : b = s i := by
      calc b = xor4 (xor4 b (s i)) (s i) := by rw [xor4_xor_self_right]
           _ = s i := by rw [hzero, xor4_zero_left]
    rw [hbs, omega4_self_zero] at hbomega
    norm_num at hbomega
  have htSupport : pauliSupport4 t = S.erase k := by
    rw [show t = Function.update (Function.update s k 0) i b from rfl,
      pauliSupport4_update_nonzero _ i hb0,
      pauliSupport4_update_zero]
    rw [Finset.insert_eq_self.mpr]
    simpa [S] using hiErase
  have huSupport : pauliSupport4 u = {i, k} := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [pauliSupport4, hu_i, hbi]
    · by_cases hjk : j = k
      · subst j
        simp [pauliSupport4, hsk, hu_k]
      · simp [pauliSupport4, hji, hjk, hu_other hji hjk]
  have htne : t ≠ 0 := by
    intro htzero
    have := congrFun htzero i
    simp [ht_i, hb0] at this
  have hune : u ≠ 0 := by
    intro huzero
    have := congrFun huzero k
    simp [hu_k, hsk] at this
  have htWeight : pauliWeight4 t < pauliWeight4 s := by
    rw [pauliWeight4, pauliWeight4, htSupport]
    simpa [S] using Finset.card_erase_lt_of_mem hkS
  have huWeight : pauliWeight4 u = 2 := by
    rw [pauliWeight4, huSupport, Finset.card_pair hik]
  have homega : pauliOmega t u = 1 := by
    rw [pauliOmega]
    rw [Finset.sum_eq_single i]
    · rw [ht_i, hu_i, omega4_xor_self_right, omega4_comm b (s i), hbomega]
    · intro j _ hji
      by_cases hjk : j = k
      · subst j
        rw [ht_k, omega4_zero_left]
      · rw [hu_other hji hjk, omega4_zero_right]
    · exact fun h => absurd (Finset.mem_univ i) h
  have hxor : pauliXor t u = s := by
    change pauliXor t (pauliXor t s) = s
    exact pauliXor_self_left t s
  exact ⟨t, u, htne, hune, htWeight, huWeight, homega, hxor⟩

/-- Hermitian Pauli generators supported on at most two sites. -/
def twoLocalPauliMatrices (n : ℕ) :
    Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4,
    s ≠ 0 ∧ pauliWeight4 s ≤ 2 ∧ A = pauliMat s}

/-- Every nonidentity Pauli string lies in the Lie algebra generated by the
one- and two-site Pauli matrices. -/
theorem pauliMat_mem_lieSpan_twoLocal
    {n : ℕ} (s : Fin n → Fin 4) (hs : s ≠ 0) :
    pauliMat s ∈ dynamicalLieAlgebra (twoLocalPauliMatrices n) := by
  classical
  induction hweight : pauliWeight4 s using Nat.strong_induction_on generalizing s with
  | h w ih =>
      by_cases hsmall : w ≤ 2
      · apply LieSubalgebra.subset_lieSpan
        exact ⟨s, hs, by simpa [hweight] using hsmall, rfl⟩
      · have hlarge : 2 < pauliWeight4 s := by omega
        obtain ⟨t, u, ht, hu, htWeight, huWeight, htu, hxor⟩ :=
          exists_pauliWeightTwo_anticommuting_decomposition s hlarge
        have htmem : pauliMat t ∈ dynamicalLieAlgebra (twoLocalPauliMatrices n) :=
          ih (pauliWeight4 t) (by simpa [hweight] using htWeight) t ht rfl
        have humem : pauliMat u ∈ dynamicalLieAlgebra (twoLocalPauliMatrices n) := by
          apply LieSubalgebra.subset_lieSpan
          exact ⟨u, hu, huWeight.le, rfl⟩
        have hbracket :=
          (dynamicalLieAlgebra (twoLocalPauliMatrices n)).lie_mem htmem humem
        rw [pauliMat_bracket_closed, hxor] at hbracket
        let c := pauliPhase t u - pauliPhase u t
        have hc : c ≠ 0 := pauliPhase_sub_ne_zero htu
        have hscaled :=
          (dynamicalLieAlgebra (twoLocalPauliMatrices n)).smul_mem c⁻¹ hbracket
        simpa [c, hc] using hscaled

/-- The complex dynamical Lie algebra of all one- and two-site Pauli
Hamiltonians is the full traceless matrix algebra on every finite qubit
register. -/
theorem dynamicalLieAlgebra_twoLocalPauliMatrices_eq_tracelessLie (n : ℕ) :
    dynamicalLieAlgebra (twoLocalPauliMatrices n) = tracelessLie (2 ^ n) := by
  apply LieSubalgebra.ext _ _
  intro A
  constructor
  · intro hA
    have hle : dynamicalLieAlgebra (twoLocalPauliMatrices n) ≤ tracelessLie (2 ^ n) := by
      apply dynamicalLieAlgebra_minimal
      rintro _ ⟨s, hs, _hweight, rfl⟩
      change pauliMat s ∈ LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ)
      rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, pauliMat_trace_eq_zero hs]
    exact hle hA
  · intro hA
    let L := dynamicalLieAlgebra (twoLocalPauliMatrices n)
    have hsu : dynamicalLieAlgebra (suGens n) ≤ L := by
      apply dynamicalLieAlgebra_minimal
      rintro _ ⟨s, hs, rfl⟩
      exact L.smul_mem Complex.I (pauliMat_mem_lieSpan_twoLocal s hs)
    have hspan := (suHermBasis n).span_eq
    have hspanle : Submodule.span ℂ (Set.range (suB n)) ≤ L.toSubmodule := by
      rw [show Submodule.span ℂ (Set.range (suB n)) =
          (dynamicalLieAlgebra (suGens n)).toSubmodule by
        simpa [suHermBasis] using hspan]
      exact hsu
    have hLle : L.toSubmodule ≤ (tracelessLie (2 ^ n)).toSubmodule := by
      intro x hx
      have hle : L ≤ tracelessLie (2 ^ n) := by
        apply dynamicalLieAlgebra_minimal
        rintro _ ⟨s, hs, _hweight, rfl⟩
        change pauliMat s ∈ LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ)
        rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, pauliMat_trace_eq_zero hs]
      exact hle hx
    have hfinrank : Module.finrank ℂ (tracelessLie (2 ^ n)).toSubmodule ≤
        Module.finrank ℂ L.toSubmodule := by
      calc
        Module.finrank ℂ (tracelessLie (2 ^ n)).toSubmodule =
            2 ^ n * 2 ^ n - 1 := traceLinearMap_ker_finrank (by positivity)
        _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (suB n))) :=
          (suB_span_finrank n).symm
        _ ≤ Module.finrank ℂ L.toSubmodule := Submodule.finrank_mono hspanle
    have hLeq : L.toSubmodule = (tracelessLie (2 ^ n)).toSubmodule :=
      Submodule.eq_of_le_of_finrank_le hLle hfinrank
    change A ∈ L.toSubmodule
    rw [hLeq]
    exact hA

end

end QuantumAlg
