import GaloisForLFunctions.HTGeometry.OneReplicaLocalPauliPencilFullness
import GaloisForLFunctions.HTGeometry.FiniteDysonHallAtomlessness
import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleFourierDecay
import GaloisForLFunctions.HTGeometry.TwoReplicaPositiveGraphEdgeCasimir
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.PauliStringDLA
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.PauliStringSchur
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Simulation.GSim

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

def optionPauliAxisFinFour : Option (Fin 3) → Fin 4
  | none => 0
  | some a => a.succ

def boundedPauliWordFinFour {n q : ℕ} (P : OneReplicaBoundedPauliWord n q) :
    Fin n → Fin 4 :=
  fun i => optionPauliAxisFinFour (P.1 i)

theorem boundedPauliWordFinFour_ne_zero {n q : ℕ}
    (P : OneReplicaBoundedPauliWord n q) :
    boundedPauliWordFinFour P ≠ 0 := by
  have hweight := (mem_nonidentityPauliWords.mp P.2).1
  rw [pauliWeight_eq_card_pauliSupport] at hweight
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hweight)
  intro hzero
  have hcoord := congr_fun hzero i
  have hactive : P.1 i ≠ none := mem_pauliSupport.mp hi
  cases hPi : P.1 i with
  | none => exact hactive hPi
  | some a =>
      simp [boundedPauliWordFinFour, optionPauliAxisFinFour, hPi] at hcoord

def oneReplicaTracelessPauliHamiltonian {n q : ℕ}
    (P : OneReplicaBoundedPauliWord n q) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  QuantumAlg.pauliMat (boundedPauliWordFinFour P)

theorem oneReplicaTracelessPauliHamiltonian_conjTranspose {n q : ℕ}
    (P : OneReplicaBoundedPauliWord n q) :
    (oneReplicaTracelessPauliHamiltonian P)ᴴ = oneReplicaTracelessPauliHamiltonian P := by
  exact QuantumAlg.pauliMat_isHermitian _

def oneReplicaTracelessPauliAdjointMatrix {n q : ℕ}
    (P : OneReplicaBoundedPauliWord n q) :
    Matrix (Fin (QuantumAlg.suHermBasis n).dim)
      (Fin (QuantumAlg.suHermBasis n).dim) ℂ :=
  (QuantumAlg.suHermBasis n).adMatrix (oneReplicaTracelessPauliHamiltonian P)

theorem dlaHermBasis_adMatrix_conjTranspose_of_hermitian
    {N : ℕ} {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : QuantumAlg.DLAHermBasis gens)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : Aᴴ = A) :
    (b.adMatrix A)ᴴ = b.adMatrix A := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [QuantumAlg.DLAHermBasis.adMatrix]
  change (starRingEnd ℂ) (QuantumAlg.hsInner (b.B j) ⁅A, b.B i⁆) = _
  rw [← QuantumAlg.hsInner_conj_symm]
  exact hsInner_ringCommutator_selfAdjoint A (b.B i) (b.B j) hA

theorem oneReplicaTracelessPauliAdjointMatrix_conjTranspose {n q : ℕ}
    (P : OneReplicaBoundedPauliWord n q) :
    (oneReplicaTracelessPauliAdjointMatrix P)ᴴ =
      oneReplicaTracelessPauliAdjointMatrix P := by
  exact dlaHermBasis_adMatrix_conjTranspose_of_hermitian _ _
    (oneReplicaTracelessPauliHamiltonian_conjTranspose P)

theorem suBasis_adMatrix_eq_rtNinv_mul_pauli_adMatrix
    {n : ℕ} (k a i : Fin (QuantumAlg.suHermBasis n).dim) :
    QuantumAlg.adMatrix (QuantumAlg.suHermBasis n) k a i =
      QuantumAlg.rtNinv n *
        (QuantumAlg.suHermBasis n).adMatrix
          (QuantumAlg.pauliMat ((QuantumAlg.suSchurFamily n).str k)) a i := by
  change QuantumAlg.hsInner ((QuantumAlg.suHermBasis n).B a)
      ⁅(QuantumAlg.suHermBasis n).B k, (QuantumAlg.suHermBasis n).B i⁆ =
    QuantumAlg.rtNinv n * QuantumAlg.hsInner ((QuantumAlg.suHermBasis n).B a)
      ⁅QuantumAlg.pauliMat ((QuantumAlg.suSchurFamily n).str k),
        (QuantumAlg.suHermBasis n).B i⁆
  rw [(QuantumAlg.suSchurFamily n).B_eq k, smul_lie,
    QuantumAlg.hsInner_smul_right]
  rfl

set_option maxHeartbeats 1000000 in
theorem oneReplicaTracelessPauliAdjointMatrix_support
    {n q : ℕ} (P : OneReplicaBoundedPauliWord n q)
    {a i : Fin (QuantumAlg.suHermBasis n).dim}
    (ha : oneReplicaTracelessPauliAdjointMatrix P a i ≠ 0) :
    (QuantumAlg.suSchurFamily n).str a =
      QuantumAlg.pauliXor (boundedPauliWordFinFour P)
        ((QuantumAlg.suSchurFamily n).str i) := by
  let k : Fin (QuantumAlg.suHermBasis n).dim :=
    (QuantumAlg.suSchurFamily n).equiv.symm
      ⟨boundedPauliWordFinFour P, boundedPauliWordFinFour_ne_zero P⟩
  have hk : (QuantumAlg.suSchurFamily n).str k = boundedPauliWordFinFour P := by
    exact (QuantumAlg.suSchurFamily n).str_symm_apply _
  by_contra hsupp
  have hzero := (QuantumAlg.suSchurFamily n).adMatrix_eq_zero
    (k := k) (a := a) (i := i) (by simpa [hk] using hsupp)
  rw [suBasis_adMatrix_eq_rtNinv_mul_pauli_adMatrix] at hzero
  have hscale : QuantumAlg.rtNinv n ≠ 0 := QuantumAlg.rtNinv_ne_zero n
  have hzarb := (mul_eq_zero.mp hzero).resolve_left hscale
  rw [hk] at hzarb
  exact ha (by
    simpa [oneReplicaTracelessPauliAdjointMatrix,
      oneReplicaTracelessPauliHamiltonian] using hzarb)

theorem oneReplicaTracelessPauliAdjointMatrix_subsingletonColumns
    {n q : ℕ} (P : OneReplicaBoundedPauliWord n q) :
    MatrixFamilyHasSubsingletonColumns
      (fun _ : Unit ↦ oneReplicaTracelessPauliAdjointMatrix P) := by
  intro _ i a a' ha ha'
  exact (QuantumAlg.suSchurFamily n).str_injective
    ((oneReplicaTracelessPauliAdjointMatrix_support P ha).trans
      (oneReplicaTracelessPauliAdjointMatrix_support P ha').symm)

def pauliAxisCycle (a : Fin 4) : Fin 4 :=
  if a = 0 then 0 else if a = 1 then 2 else if a = 2 then 3 else 1

theorem pauliAxisCycle_injective : Function.Injective pauliAxisCycle := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [pauliAxisCycle]

theorem pauliAxisCycle_ne_zero {a : Fin 4} (ha : a ≠ 0) :
    pauliAxisCycle a ≠ 0 := by
  fin_cases a <;> simp_all [pauliAxisCycle]

theorem omega4_cycleWitness (a : Fin 4) (ha : a ≠ 0) :
    QuantumAlg.omega4 (QuantumAlg.xor4 (pauliAxisCycle a) a) a = 1 := by
  fin_cases a <;> simp_all [pauliAxisCycle, QuantumAlg.xor4, QuantumAlg.omega4]

theorem cycleWitness_ne_zero (a : Fin 4) (ha : a ≠ 0) :
    QuantumAlg.xor4 (pauliAxisCycle a) a ≠ 0 := by
  fin_cases a <;> simp_all [pauliAxisCycle, QuantumAlg.xor4]

def pauliSupportFinFour {n : ℕ} (z : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ z i ≠ 0

theorem pauliSupportFinFour_nonempty {n : ℕ} {z : Fin n → Fin 4} (hz : z ≠ 0) :
    (pauliSupportFinFour z).Nonempty := by
  by_contra hempty
  apply hz
  funext i
  by_contra hi
  have himem : i ∈ pauliSupportFinFour z :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  exact (by
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at himem
    simp at himem)

noncomputable def pauliFirstNonzeroSite {n : ℕ} (z : Fin n → Fin 4) (hz : z ≠ 0) : Fin n :=
  (pauliSupportFinFour z).min' (pauliSupportFinFour_nonempty hz)

theorem pauliFirstNonzeroSite_ne_zero {n : ℕ} (z : Fin n → Fin 4) (hz : z ≠ 0) :
    z (pauliFirstNonzeroSite z hz) ≠ 0 := by
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (pauliSupportFinFour z) (pauliSupportFinFour_nonempty hz))).2

noncomputable def pauliLabelCycle {n : ℕ} (z : Fin n → Fin 4) (hz : z ≠ 0) :
    Fin n → Fin 4 :=
  Function.update z (pauliFirstNonzeroSite z hz)
    (pauliAxisCycle (z (pauliFirstNonzeroSite z hz)))

theorem pauliLabelCycle_apply_eq_zero_iff {n : ℕ} (z : Fin n → Fin 4) (hz : z ≠ 0)
    (i : Fin n) :
    pauliLabelCycle z hz i = 0 ↔ z i = 0 := by
  by_cases hi : i = pauliFirstNonzeroSite z hz
  · subst i
    simp [pauliLabelCycle, pauliAxisCycle_ne_zero
      (pauliFirstNonzeroSite_ne_zero z hz), pauliFirstNonzeroSite_ne_zero z hz]
  · simp [pauliLabelCycle, hi]

theorem pauliLabelCycle_ne_zero {n : ℕ} (z : Fin n → Fin 4) (hz : z ≠ 0) :
    pauliLabelCycle z hz ≠ 0 := by
  intro hzero
  have h := congr_fun hzero (pauliFirstNonzeroSite z hz)
  exact (pauliAxisCycle_ne_zero (pauliFirstNonzeroSite_ne_zero z hz)) (by
    simpa [pauliLabelCycle] using h)

theorem pauliLabelCycle_injective {n : ℕ}
    {z z' : Fin n → Fin 4} {hz : z ≠ 0} {hz' : z' ≠ 0}
    (hcycle : pauliLabelCycle z hz = pauliLabelCycle z' hz') : z = z' := by
  have hsupp : pauliSupportFinFour z = pauliSupportFinFour z' := by
    ext i
    simp only [pauliSupportFinFour, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hzi hz'i
      apply hzi
      apply (pauliLabelCycle_apply_eq_zero_iff z hz i).mp
      rw [hcycle]
      exact (pauliLabelCycle_apply_eq_zero_iff z' hz' i).mpr hz'i
    · intro hz'i hzi
      apply hz'i
      apply (pauliLabelCycle_apply_eq_zero_iff z' hz' i).mp
      rw [← hcycle]
      exact (pauliLabelCycle_apply_eq_zero_iff z hz i).mpr hzi
  have hfirst : pauliFirstNonzeroSite z hz = pauliFirstNonzeroSite z' hz' := by
    unfold pauliFirstNonzeroSite
    congr
  funext i
  by_cases hi : i = pauliFirstNonzeroSite z hz
  · subst i
    apply pauliAxisCycle_injective
    have happ := congr_fun hcycle (pauliFirstNonzeroSite z hz)
    simpa [pauliLabelCycle, hfirst] using happ
  · have hi' : i ≠ pauliFirstNonzeroSite z' hz' := by simpa [hfirst] using hi
    have happ := congr_fun hcycle i
    simpa [pauliLabelCycle, hi, hi'] using happ

noncomputable def pauliCycleIndex {n : ℕ}
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    Fin (QuantumAlg.suHermBasis n).dim :=
  (QuantumAlg.suSchurFamily n).equiv.symm
    ⟨pauliLabelCycle ((QuantumAlg.suSchurFamily n).str j)
      ((QuantumAlg.suSchurFamily n).str_ne j),
      pauliLabelCycle_ne_zero _ _⟩

theorem str_pauliCycleIndex {n : ℕ} (j : Fin (QuantumAlg.suHermBasis n).dim) :
    (QuantumAlg.suSchurFamily n).str (pauliCycleIndex j) =
      pauliLabelCycle ((QuantumAlg.suSchurFamily n).str j)
        ((QuantumAlg.suSchurFamily n).str_ne j) := by
  exact (QuantumAlg.suSchurFamily n).str_symm_apply _

theorem pauliCycleIndex_injective {n : ℕ} :
    Function.Injective (pauliCycleIndex (n := n)) := by
  intro i j hij
  apply (QuantumAlg.suSchurFamily n).str_injective
  apply pauliLabelCycle_injective
  rw [← str_pauliCycleIndex i, ← str_pauliCycleIndex j, hij]

theorem boundedPauliWordFinFour_oneReplicaLocal {n q : ℕ} (hq : 1 ≤ q)
    (i : Fin n) (a : Fin 3) :
    boundedPauliWordFinFour (oneReplicaLocalBoundedPauliWord hq i a) =
      Function.update (0 : Fin n → Fin 4) i a.succ := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [boundedPauliWordFinFour, optionPauliAxisFinFour,
      oneReplicaLocalBoundedPauliWord, singlePauliAxisLabel]
  · simp [boundedPauliWordFinFour, optionPauliAxisFinFour,
      oneReplicaLocalBoundedPauliWord, singlePauliAxisLabel, hji]

theorem pauliOmega_update_single_left {n : ℕ} (i : Fin n) (a : Fin 4)
    (z : Fin n → Fin 4) :
    QuantumAlg.pauliOmega (Function.update (0 : Fin n → Fin 4) i a) z =
      QuantumAlg.omega4 a (z i) := by
  rw [QuantumAlg.pauliOmega, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji, QuantumAlg.omega4_zero_left]
  · simp

noncomputable def oneReplicaCycleGenerator {n q : ℕ} (hq : 1 ≤ q)
    (j : Fin (QuantumAlg.suHermBasis n).dim) : OneReplicaBoundedPauliWord n q :=
  let z := (QuantumAlg.suSchurFamily n).str j
  let hz := (QuantumAlg.suSchurFamily n).str_ne j
  let i := pauliFirstNonzeroSite z hz
  let a := QuantumAlg.xor4 (pauliAxisCycle (z i)) (z i)
  oneReplicaLocalBoundedPauliWord hq i (a.pred
    (cycleWitness_ne_zero (z i) (pauliFirstNonzeroSite_ne_zero z hz)))

theorem boundedPauliWordFinFour_oneReplicaCycleGenerator {n q : ℕ} (hq : 1 ≤ q)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    boundedPauliWordFinFour (oneReplicaCycleGenerator hq j) =
      Function.update (0 : Fin n → Fin 4)
        (pauliFirstNonzeroSite ((QuantumAlg.suSchurFamily n).str j)
          ((QuantumAlg.suSchurFamily n).str_ne j))
        (QuantumAlg.xor4
          (pauliAxisCycle ((QuantumAlg.suSchurFamily n).str j
            (pauliFirstNonzeroSite ((QuantumAlg.suSchurFamily n).str j)
              ((QuantumAlg.suSchurFamily n).str_ne j))))
          ((QuantumAlg.suSchurFamily n).str j
            (pauliFirstNonzeroSite ((QuantumAlg.suSchurFamily n).str j)
              ((QuantumAlg.suSchurFamily n).str_ne j)))) := by
  rw [oneReplicaCycleGenerator, boundedPauliWordFinFour_oneReplicaLocal]
  rw [Fin.succ_pred]

theorem oneReplicaCycleGenerator_anticomm {n q : ℕ} (hq : 1 ≤ q)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    QuantumAlg.pauliOmega (boundedPauliWordFinFour (oneReplicaCycleGenerator hq j))
      ((QuantumAlg.suSchurFamily n).str j) = 1 := by
  rw [boundedPauliWordFinFour_oneReplicaCycleGenerator,
    pauliOmega_update_single_left]
  exact omega4_cycleWitness _
    (pauliFirstNonzeroSite_ne_zero _ _)

theorem pauliXor_cycleGenerator {n q : ℕ} (hq : 1 ≤ q)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    QuantumAlg.pauliXor (boundedPauliWordFinFour (oneReplicaCycleGenerator hq j))
        ((QuantumAlg.suSchurFamily n).str j) =
      pauliLabelCycle ((QuantumAlg.suSchurFamily n).str j)
        ((QuantumAlg.suSchurFamily n).str_ne j) := by
  let z := (QuantumAlg.suSchurFamily n).str j
  let hz := (QuantumAlg.suSchurFamily n).str_ne j
  let i := pauliFirstNonzeroSite z hz
  change QuantumAlg.pauliXor (boundedPauliWordFinFour (oneReplicaCycleGenerator hq j)) z =
    pauliLabelCycle z hz
  rw [boundedPauliWordFinFour_oneReplicaCycleGenerator]
  change QuantumAlg.pauliXor
      (Function.update (0 : Fin n → Fin 4) i
        (QuantumAlg.xor4 (pauliAxisCycle (z i)) (z i))) z =
    Function.update z i (pauliAxisCycle (z i))
  funext k
  by_cases hki : k = i
  · subst k
    rw [QuantumAlg.pauliXor, Function.update_self, Function.update_self]
    exact QuantumAlg.xor4_xor_self_right (pauliAxisCycle (z i)) (z i)
  · rw [QuantumAlg.pauliXor, Function.update_of_ne hki,
      Function.update_of_ne hki, Pi.zero_apply, QuantumAlg.xor4_zero_left]

set_option maxHeartbeats 1000000 in
theorem oneReplicaTracelessPauliAdjointMatrix_ne_zero_of_support
    {n q : ℕ} (P : OneReplicaBoundedPauliWord n q)
    {a i : Fin (QuantumAlg.suHermBasis n).dim}
    (hsupp : (QuantumAlg.suSchurFamily n).str a =
      QuantumAlg.pauliXor (boundedPauliWordFinFour P)
        ((QuantumAlg.suSchurFamily n).str i))
    (hanti : QuantumAlg.pauliOmega (boundedPauliWordFinFour P)
      ((QuantumAlg.suSchurFamily n).str i) = 1) :
    oneReplicaTracelessPauliAdjointMatrix P a i ≠ 0 := by
  let k : Fin (QuantumAlg.suHermBasis n).dim :=
    (QuantumAlg.suSchurFamily n).equiv.symm
      ⟨boundedPauliWordFinFour P, boundedPauliWordFinFour_ne_zero P⟩
  have hk : (QuantumAlg.suSchurFamily n).str k = boundedPauliWordFinFour P :=
    (QuantumAlg.suSchurFamily n).str_symm_apply _
  have hgeneric := (QuantumAlg.suSchurFamily n).adMatrix_ne_zero
    (k := k) (a := a) (i := i) (by simpa [hk] using hsupp)
    (by simpa [hk] using hanti)
  rw [suBasis_adMatrix_eq_rtNinv_mul_pauli_adMatrix] at hgeneric
  have harbitrary :
      (QuantumAlg.suHermBasis n).adMatrix
        (QuantumAlg.pauliMat ((QuantumAlg.suSchurFamily n).str k)) a i ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hgeneric
    exact hgeneric rfl
  rw [hk] at harbitrary
  simpa [oneReplicaTracelessPauliAdjointMatrix,
    oneReplicaTracelessPauliHamiltonian] using harbitrary

theorem oneReplicaCycleGenerator_entry_ne_zero {n q : ℕ} (hq : 1 ≤ q)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    oneReplicaTracelessPauliAdjointMatrix (oneReplicaCycleGenerator hq j)
      (pauliCycleIndex j) j ≠ 0 := by
  apply oneReplicaTracelessPauliAdjointMatrix_ne_zero_of_support
  · rw [str_pauliCycleIndex, ← pauliXor_cycleGenerator hq j]
  · exact oneReplicaCycleGenerator_anticomm hq j

noncomputable def oneReplicaWeightedTracelessPauliAdjointMatrix {n q : ℕ}
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (P : OneReplicaBoundedPauliWord n q) :
    Matrix (Fin (QuantumAlg.suHermBasis n).dim)
      (Fin (QuantumAlg.suHermBasis n).dim) ℂ :=
  ((Real.sqrt (v P) : ℝ) : ℂ) • oneReplicaTracelessPauliAdjointMatrix P

theorem oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose
    {n q : ℕ} (v : OneReplicaBoundedPauliWord n q → ℝ)
    (P : OneReplicaBoundedPauliWord n q) :
    (oneReplicaWeightedTracelessPauliAdjointMatrix v P)ᴴ =
      oneReplicaWeightedTracelessPauliAdjointMatrix v P := by
  rw [oneReplicaWeightedTracelessPauliAdjointMatrix, conjTranspose_smul,
    oneReplicaTracelessPauliAdjointMatrix_conjTranspose]
  simp

theorem oneReplicaWeightedTracelessPauliAdjointMatrix_subsingletonColumns
    {n q : ℕ} (v : OneReplicaBoundedPauliWord n q → ℝ) :
    MatrixFamilyHasSubsingletonColumns
      (oneReplicaWeightedTracelessPauliAdjointMatrix v) := by
  intro P j i l hi hl
  apply (oneReplicaTracelessPauliAdjointMatrix_subsingletonColumns P) () j i l
  · intro hzero
    apply hi
    simp [oneReplicaWeightedTracelessPauliAdjointMatrix, hzero]
  · intro hzero
    apply hl
    simp [oneReplicaWeightedTracelessPauliAdjointMatrix, hzero]

theorem oneReplicaWeighted_cycle_entry_ne_zero
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    oneReplicaWeightedTracelessPauliAdjointMatrix v (oneReplicaCycleGenerator hq j)
      (pauliCycleIndex j) j ≠ 0 := by
  have hvcycle : v (oneReplicaCycleGenerator hq j) = v₁ := by
    rw [oneReplicaCycleGenerator]
    apply hlocal
  rw [oneReplicaWeightedTracelessPauliAdjointMatrix, Matrix.smul_apply, smul_eq_mul,
    hvcycle]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hv₁)))
    (oneReplicaCycleGenerator_entry_ne_zero hq j)

theorem oneReplicaWeighted_squaredEntryWeight_cycle_pos
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    0 < matrixFamilySquaredEntryWeight
      (oneReplicaWeightedTracelessPauliAdjointMatrix v) (pauliCycleIndex j) j := by
  rw [matrixFamilySquaredEntryWeight]
  apply Finset.sum_pos'
  · intro P _
    exact Complex.normSq_nonneg _
  · refine ⟨oneReplicaCycleGenerator hq j, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.mpr
      (oneReplicaWeighted_cycle_entry_ne_zero hq v v₁ hv₁ hlocal j)

set_option maxHeartbeats 1000000 in
theorem oneReplicaWeighted_finiteWeightHall
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    FiniteWeightHall (matrixFamilySquaredEntryWeight
      (oneReplicaWeightedTracelessPauliAdjointMatrix v)) := by
  apply finiteWeightHall_of_injective_positiveNeighbor _ (pauliCycleIndex (n := n))
    pauliCycleIndex_injective
  intro j
  rw [matrixFamilySquaredEntryWeight_symm _
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)]
  exact oneReplicaWeighted_squaredEntryWeight_cycle_pos hq v v₁ hv₁ hlocal j

theorem oneReplicaWeighted_hasTrivialCommonKernel
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    HasTrivialCommonKernel (oneReplicaWeightedTracelessPauliAdjointMatrix v) := by
  intro x hx
  funext j
  let P := oneReplicaCycleGenerator hq j
  let a := pauliCycleIndex j
  have hedge : oneReplicaWeightedTracelessPauliAdjointMatrix v P a j ≠ 0 :=
    oneReplicaWeighted_cycle_entry_ne_zero hq v v₁ hv₁ hlocal j
  have hrowzero : ∀ p ≠ j,
      oneReplicaWeightedTracelessPauliAdjointMatrix v P a p = 0 := by
    intro p hpj
    by_contra hap
    have hherm := oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v P
    have hap' : oneReplicaWeightedTracelessPauliAdjointMatrix v P p a ≠ 0 := by
      intro hzero
      have hentry := congr_fun (congr_fun hherm a) p
      rw [Matrix.conjTranspose_apply] at hentry
      exact hap (by rw [← hentry, hzero]; simp)
    have haj' : oneReplicaWeightedTracelessPauliAdjointMatrix v P j a ≠ 0 := by
      intro hzero
      have hentry := congr_fun (congr_fun hherm a) j
      rw [Matrix.conjTranspose_apply] at hentry
      exact hedge (by rw [← hentry, hzero]; simp)
    exact hpj ((oneReplicaWeightedTracelessPauliAdjointMatrix_subsingletonColumns v)
      P a p j hap' haj')
  have hsum := hx P a
  rw [Finset.sum_eq_single j] at hsum
  · exact (mul_eq_zero.mp hsum).resolve_left hedge
  · intro p _ hpj
    rw [hrowzero p hpj, zero_mul]
  · simp

theorem oneReplicaWeighted_coordinateSpectralLaw_singleton_zero
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ) (_hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (j : Fin (QuantumAlg.suHermBasis n).dim) (a : ℝ) :
    (freeFockCoordinateSpectralLaw
      (oneReplicaWeightedTracelessPauliAdjointMatrix v)
      (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
      (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal) j : Measure ℝ) {a} = 0 := by
  let A := oneReplicaWeightedTracelessPauliAdjointMatrix v
  have hA : ∀ P, (A P)ᴴ = A P :=
    oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v
  have hker : HasTrivialCommonKernel A :=
    oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal
  have hmono : MatrixFamilyHasSubsingletonColumns A :=
    oneReplicaWeightedTracelessPauliAdjointMatrix_subsingletonColumns v
  have hHall : FiniteWeightHall (matrixFamilySquaredEntryWeight A) :=
    oneReplicaWeighted_finiteWeightHall hq v v₁ hv₁ hlocal
  let μ : Fin (QuantumAlg.suHermBasis n).dim → ProbabilityMeasure ℝ := fun i ↦
    freeFockCoordinateSpectralLaw A hA hker i
  have hzero := probabilityStieltjes_atomless_of_finiteDyson
    (matrixFamilySquaredEntryWeight A)
    (matrixFamilySquaredEntryWeight_symm A hA)
    (matrixFamilySquaredEntryWeight_nonneg A) hHall μ
  apply hzero
  intro i z hz
  simpa [finiteDysonResidual, probabilityStieltjesTransform,
    freeFockCoordinateDysonResidual, freeFockCoordinateStieltjes, μ] using
    freeFockCoordinateDysonResidual_upperHalfPlane A hA hker hmono i z hz

theorem oneReplicaWeighted_coordinateSpectralLaw_absolutelyContinuous
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ) (hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (j : Fin (QuantumAlg.suHermBasis n).dim) :
    (freeFockCoordinateSpectralLaw
      (oneReplicaWeightedTracelessPauliAdjointMatrix v)
      (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
      (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal) j : Measure ℝ) ≪
        volume := by
  exact freeFockCoordinateSpectralLaw_absolutelyContinuous
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal) j
    (oneReplicaWeighted_coordinateSpectralLaw_singleton_zero
      hq v hv v₁ hv₁ hlocal j)

/-! ## Exact scalar law and vacuum-compressed propagator -/

/-- Kargin fullness in its exact rank-nondecreasing form on the traceless operator sector. -/
def OneReplicaWeightedPauliPencilFull {n q : ℕ} (_hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ) : Prop :=
  ∀ U V : Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n))),
    U ≤ oneReplicaTracelessOperatorSubspace (σ := Fin n) →
    (∀ P x, x ∈ U → (oneReplicaWeightedPauliPencil v P).toEuclideanLin x ∈ V) →
    Module.finrank ℂ U ≤ Module.finrank ℂ V

theorem oneReplicaWeightedPauliPencil_full
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    OneReplicaWeightedPauliPencilFull hq v := by
  intro U V hU hUV
  exact oneReplicaWeightedPauliPencil_subspace_finrank
    hq v v₁ hv₁ hlocal U V hU hUV

/-- Exact normalized vacuum trace moment sequence for a positive qubit count. -/
noncomputable def oneReplicaWeightedTraceMoment
    {n q : ℕ} (v : OneReplicaBoundedPauliWord (n + 1) q → ℝ) : ℕ → ℝ := by
  letI : Nonempty (Fin (QuantumAlg.suHermBasis (n + 1)).dim) :=
    ⟨⟨0, QuantumAlg.suHermBasis_dim_pos n⟩⟩
  exact freeFockTraceMoment (oneReplicaWeightedTracelessPauliAdjointMatrix v)

/-- Scalar spectral law of the positive-qubit one-replica free Pauli Hamiltonian.  It is the
uniform coordinate average, hence has exactly the normalized vacuum trace moments. -/
noncomputable def oneReplicaWeightedScalarSpectralLaw
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord (n + 1) q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    ProbabilityMeasure ℝ := by
  letI : Nonempty (Fin (QuantumAlg.suHermBasis (n + 1)).dim) :=
    ⟨⟨0, QuantumAlg.suHermBasis_dim_pos n⟩⟩
  exact freeFockCoordinateAverageSpectralLaw
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)

theorem oneReplicaWeightedScalarSpectralLaw_hasMoments
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord (n + 1) q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    HasHamburgerMoments
      (oneReplicaWeightedTraceMoment v)
      (oneReplicaWeightedScalarSpectralLaw hq v v₁ hv₁ hlocal : Measure ℝ) := by
  letI : Nonempty (Fin (QuantumAlg.suHermBasis (n + 1)).dim) :=
    ⟨⟨0, QuantumAlg.suHermBasis_dim_pos n⟩⟩
  simpa [oneReplicaWeightedTraceMoment, oneReplicaWeightedScalarSpectralLaw] using
    freeFockCoordinateAverageSpectralLaw_hasMoments
      (oneReplicaWeightedTracelessPauliAdjointMatrix v)
      (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
      (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)

theorem oneReplicaWeightedScalarSpectralLaw_carried
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord (n + 1) q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    (oneReplicaWeightedScalarSpectralLaw hq v v₁ hv₁ hlocal : Measure ℝ)
      (Set.Icc
        (-freeFockSpectralRadius (oneReplicaWeightedTracelessPauliAdjointMatrix v))
        (freeFockSpectralRadius (oneReplicaWeightedTracelessPauliAdjointMatrix v)))ᶜ = 0 := by
  letI : Nonempty (Fin (QuantumAlg.suHermBasis (n + 1)).dim) :=
    ⟨⟨0, QuantumAlg.suHermBasis_dim_pos n⟩⟩
  simpa [oneReplicaWeightedScalarSpectralLaw] using
    freeFockCoordinateAverageSpectralLaw_carried
      (oneReplicaWeightedTracelessPauliAdjointMatrix v)
      (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
      (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)

theorem oneReplicaWeightedScalarSpectralLaw_absolutelyContinuous
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord (n + 1) q → ℝ) (hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    (oneReplicaWeightedScalarSpectralLaw hq v v₁ hv₁ hlocal : Measure ℝ) ≪ volume := by
  letI : Nonempty (Fin (QuantumAlg.suHermBasis (n + 1)).dim) :=
    ⟨⟨0, QuantumAlg.suHermBasis_dim_pos n⟩⟩
  simpa [oneReplicaWeightedScalarSpectralLaw] using
    freeFockCoordinateAverageSpectralLaw_absolutelyContinuous
      (oneReplicaWeightedTracelessPauliAdjointMatrix v)
      (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
      (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)
      (oneReplicaWeighted_coordinateSpectralLaw_absolutelyContinuous
        hq v hv v₁ hv₁ hlocal)

/-- Exact vacuum-compressed propagator in the normalized nonidentity Pauli basis. -/
noncomputable def oneReplicaWeightedVacuumCompressedPropagator
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (t : ℝ) : Matrix (Fin (QuantumAlg.suHermBasis n).dim)
      (Fin (QuantumAlg.suHermBasis n).dim) ℂ :=
  freeFockDiagonalVacuumPropagator
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal) t

theorem oneReplicaWeighted_vacuumCoefficient_offdiag
    {n q : ℕ} (v : OneReplicaBoundedPauliWord n q → ℝ)
    {i j : Fin (QuantumAlg.suHermBasis n).dim} (hij : i ≠ j) (m : ℕ) :
    freeFockPower (oneReplicaWeightedTracelessPauliAdjointMatrix v) j m (i, []) = 0 := by
  exact freeFockPower_vacuumCoefficient_offdiag_of_subsingletonColumns
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_subsingletonColumns v) hij m

theorem oneReplicaWeightedVacuumCompressedPropagator_entry_tendsto_zero
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ) (hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (i j : Fin (QuantumAlg.suHermBasis n).dim) :
    Tendsto (fun t ↦
      oneReplicaWeightedVacuumCompressedPropagator hq v v₁ hv₁ hlocal t i j)
      (cocompact ℝ) (𝓝 0) := by
  exact freeFockDiagonalVacuumPropagator_entry_tendsto_zero
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)
    (oneReplicaWeighted_coordinateSpectralLaw_absolutelyContinuous
      hq v hv v₁ hv₁ hlocal) i j

theorem oneReplicaWeightedVacuumCompressedPropagator_matrixCoefficient_tendsto_zero
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ) (hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (x y : Fin (QuantumAlg.suHermBasis n).dim → ℂ) :
    Tendsto (fun t ↦ star x ⬝ᵥ
      (oneReplicaWeightedVacuumCompressedPropagator hq v v₁ hv₁ hlocal t *ᵥ y))
      (cocompact ℝ) (𝓝 0) := by
  exact freeFockDiagonalVacuumPropagator_matrixCoefficient_tendsto_zero
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)
    (oneReplicaWeighted_coordinateSpectralLaw_absolutelyContinuous
      hq v hv v₁ hv₁ hlocal) x y

theorem oneReplicaWeightedVacuumCompressedPropagator_operatorNorm_tendsto_zero
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ) (hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    Tendsto (fun t ↦ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin (QuantumAlg.suHermBasis n).dim))
      (oneReplicaWeightedVacuumCompressedPropagator hq v v₁ hv₁ hlocal t)‖)
      (cocompact ℝ) (𝓝 0) := by
  exact freeFockDiagonalVacuumPropagator_operatorNorm_tendsto_zero
    (oneReplicaWeightedTracelessPauliAdjointMatrix v)
    (oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v)
    (oneReplicaWeighted_hasTrivialCommonKernel hq v v₁ hv₁ hlocal)
    (oneReplicaWeighted_coordinateSpectralLaw_absolutelyContinuous
      hq v hv v₁ hv₁ hlocal)

/-- Unconditional one-replica local-Pauli planar cavity theorem for every positive qubit count. -/
theorem oneReplicaLocalPauliPlanarCavityDecay
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord (n + 1) q → ℝ) (hv : ∀ P, 0 ≤ v P)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁) :
    (∀ P, (oneReplicaWeightedTracelessPauliAdjointMatrix v P)ᴴ =
      oneReplicaWeightedTracelessPauliAdjointMatrix v P) ∧
    OneReplicaWeightedPauliPencilFull hq v ∧
    (oneReplicaWeightedScalarSpectralLaw hq v v₁ hv₁ hlocal : Measure ℝ) ≪ volume ∧
    (∀ i j, Tendsto (fun t ↦
      oneReplicaWeightedVacuumCompressedPropagator hq v v₁ hv₁ hlocal t i j)
      (cocompact ℝ) (𝓝 0)) ∧
    (∀ x y, Tendsto (fun t ↦ star x ⬝ᵥ
      (oneReplicaWeightedVacuumCompressedPropagator hq v v₁ hv₁ hlocal t *ᵥ y))
      (cocompact ℝ) (𝓝 0)) ∧
    Tendsto (fun t ↦ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin (QuantumAlg.suHermBasis (n + 1)).dim))
      (oneReplicaWeightedVacuumCompressedPropagator hq v v₁ hv₁ hlocal t)‖)
      (cocompact ℝ) (𝓝 0) := by
  exact ⟨oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose v,
    oneReplicaWeightedPauliPencil_full hq v v₁ hv₁ hlocal,
    oneReplicaWeightedScalarSpectralLaw_absolutelyContinuous
      hq v hv v₁ hv₁ hlocal,
    oneReplicaWeightedVacuumCompressedPropagator_entry_tendsto_zero
      hq v hv v₁ hv₁ hlocal,
    oneReplicaWeightedVacuumCompressedPropagator_matrixCoefficient_tendsto_zero
      hq v hv v₁ hv₁ hlocal,
    oneReplicaWeightedVacuumCompressedPropagator_operatorNorm_tendsto_zero
      hq v hv v₁ hv₁ hlocal⟩

end

end GaloisForLFunctions.HTGeometry
