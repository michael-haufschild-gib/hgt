import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions
import GaloisForLFunctions.QECLean.Foundations.Basic

/-!
# Nieto 1810 mechanical applications: epsilon-tensor duality

The paper treats epsilon duality as an involution. The corpus's Weyl epsilon matrix instead
squares to minus the identity. This file derives the exact tensor-degree law: an `n`-fold epsilon
contraction squares to `(-1)^n`. Thus even qubit counts have real self/anti-self projectors, while
odd counts carry a complex structure. All results are closed and unconditional.
-/

open Matrix Finset
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.Nieto1810

noncomputable section

/-- Complement every qubit basis label. -/
def qubitComplement {n : ℕ} (a : Quantum.NQubitBasis n) : Quantum.NQubitBasis n :=
  fun i => Fin.rev (a i)

/-- Sign contributed by one row of the two-dimensional epsilon tensor. -/
def epsilonBitSign (a : Fin 2) : ℂ := if a = 0 then 1 else -1

/-- Product sign in the `n`-fold epsilon contraction. -/
def epsilonTensorSign {n : ℕ} (a : Quantum.NQubitBasis n) : ℂ :=
  ∏ i, epsilonBitSign (a i)

/-- Coordinate form of contraction by one Weyl epsilon tensor on every qubit index. -/
def epsilonTensorDual {n : ℕ} (ψ : Quantum.NQubitVec n) : Quantum.NQubitVec n :=
  fun a => epsilonTensorSign a * ψ (qubitComplement a)

@[simp] theorem epsilonTensorDual_zero {n : ℕ} :
    epsilonTensorDual (0 : Quantum.NQubitVec n) = 0 := by
  funext a
  simp [epsilonTensorDual]

theorem epsilonTensorDual_add {n : ℕ} (ψ φ : Quantum.NQubitVec n) :
    epsilonTensorDual (ψ + φ) = epsilonTensorDual ψ + epsilonTensorDual φ := by
  funext a
  simp [epsilonTensorDual, mul_add]

theorem epsilonTensorDual_smul {n : ℕ} (c : ℂ) (ψ : Quantum.NQubitVec n) :
    epsilonTensorDual (c • ψ) = c • epsilonTensorDual ψ := by
  funext a
  simp [epsilonTensorDual]
  ring

theorem epsilonTensorDual_sub {n : ℕ} (ψ φ : Quantum.NQubitVec n) :
    epsilonTensorDual (ψ - φ) = epsilonTensorDual ψ - epsilonTensorDual φ := by
  funext a
  simp [epsilonTensorDual, mul_sub]

@[simp] theorem qubitComplement_involutive {n : ℕ} (a : Quantum.NQubitBasis n) :
    qubitComplement (qubitComplement a) = a := by
  funext i
  simp [qubitComplement]

@[simp] theorem epsilonBitSign_sq (a : Fin 2) : epsilonBitSign a ^ 2 = 1 := by
  fin_cases a <;> norm_num [epsilonBitSign]

@[simp] theorem epsilonBitSign_rev (a : Fin 2) :
    epsilonBitSign (Fin.rev a) = -epsilonBitSign a := by
  fin_cases a <;> norm_num [epsilonBitSign, Fin.rev]

@[simp] theorem epsilonTensorSign_sq {n : ℕ} (a : Quantum.NQubitBasis n) :
    epsilonTensorSign a ^ 2 = 1 := by
  rw [epsilonTensorSign, ← Finset.prod_pow]
  simp

theorem epsilonTensorSign_complement {n : ℕ} (a : Quantum.NQubitBasis n) :
    epsilonTensorSign (qubitComplement a) = (-1 : ℂ) ^ n * epsilonTensorSign a := by
  simp only [epsilonTensorSign, qubitComplement, epsilonBitSign_rev, Finset.prod_neg]
  simp

/-- Exact parity correction to equation (50): the `n`-fold epsilon dual squares to `(-1)^n`. -/
theorem epsilonTensorDual_squared {n : ℕ} (ψ : Quantum.NQubitVec n) :
    epsilonTensorDual (epsilonTensorDual ψ) = (-1 : ℂ) ^ n • ψ := by
  funext a
  simp only [epsilonTensorDual, Pi.smul_apply, smul_eq_mul,
    qubitComplement_involutive, epsilonTensorSign_complement]
  calc
    epsilonTensorSign a * ((-1 : ℂ) ^ n * epsilonTensorSign a * ψ a) =
        (-1 : ℂ) ^ n * epsilonTensorSign a ^ 2 * ψ a := by ring
    _ = (-1 : ℂ) ^ n * ψ a := by rw [epsilonTensorSign_sq, mul_one]

theorem epsilonTensorDual_squared_one (ψ : Quantum.NQubitVec 1) :
    epsilonTensorDual (epsilonTensorDual ψ) = -ψ := by
  simpa using epsilonTensorDual_squared (n := 1) ψ

theorem epsilonTensorDual_squared_two (ψ : Quantum.NQubitVec 2) :
    epsilonTensorDual (epsilonTensorDual ψ) = ψ := by
  simpa using epsilonTensorDual_squared (n := 2) ψ

theorem epsilonTensorDual_squared_three (ψ : Quantum.NQubitVec 3) :
    epsilonTensorDual (epsilonTensorDual ψ) = -ψ := by
  rw [epsilonTensorDual_squared]
  norm_num

theorem epsilonTensorDual_squared_four (ψ : Quantum.NQubitVec 4) :
    epsilonTensorDual (epsilonTensorDual ψ) = ψ := by
  rw [epsilonTensorDual_squared]
  norm_num

/-- `+1` projector for the two-qubit epsilon involution. -/
def epsilonTensorPlusTwo (ψ : Quantum.NQubitVec 2) : Quantum.NQubitVec 2 :=
  (2 : ℂ)⁻¹ • (ψ + epsilonTensorDual ψ)

/-- `-1` projector for the two-qubit epsilon involution. -/
def epsilonTensorMinusTwo (ψ : Quantum.NQubitVec 2) : Quantum.NQubitVec 2 :=
  (2 : ℂ)⁻¹ • (ψ - epsilonTensorDual ψ)

theorem epsilonTensorPlusTwo_selfDual (ψ : Quantum.NQubitVec 2) :
    epsilonTensorDual (epsilonTensorPlusTwo ψ) = epsilonTensorPlusTwo ψ := by
  rw [epsilonTensorPlusTwo, epsilonTensorDual_smul, epsilonTensorDual_add,
    epsilonTensorDual_squared_two]
  congr 1
  exact add_comm _ _

theorem epsilonTensorMinusTwo_antiSelfDual (ψ : Quantum.NQubitVec 2) :
    epsilonTensorDual (epsilonTensorMinusTwo ψ) = -epsilonTensorMinusTwo ψ := by
  rw [epsilonTensorMinusTwo, epsilonTensorDual_smul, epsilonTensorDual_sub,
    epsilonTensorDual_squared_two]
  ext a
  simp
  ring

theorem epsilonTensorTwo_projector_sum (ψ : Quantum.NQubitVec 2) :
    epsilonTensorPlusTwo ψ + epsilonTensorMinusTwo ψ = ψ := by
  ext a
  simp [epsilonTensorPlusTwo, epsilonTensorMinusTwo]
  ring

/-- Entrywise form of the corpus Weyl epsilon matrix. -/
theorem hlsWeylEpsilon_entry (a b : Fin 2) :
    HTGeometry.hlsWeylEpsilon a b =
      if b = Fin.rev a then epsilonBitSign a else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [HTGeometry.hlsWeylEpsilon, epsilonBitSign, Fin.rev]

/-- Literal tensor-index contraction from equation (49). -/
def epsilonTensorContraction {n : ℕ} (ψ : Quantum.NQubitVec n) : Quantum.NQubitVec n :=
  fun a => ∑ b, (∏ i, HTGeometry.hlsWeylEpsilon (a i) (b i)) * ψ b

/-- Full epsilon contraction is exactly signed bitwise complement. -/
theorem epsilonTensorContraction_eq_dual {n : ℕ} (ψ : Quantum.NQubitVec n) :
    epsilonTensorContraction ψ = epsilonTensorDual ψ := by
  classical
  funext a
  rw [epsilonTensorContraction, epsilonTensorDual, Finset.sum_eq_single (qubitComplement a)]
  · congr 1
    simp only [qubitComplement, hlsWeylEpsilon_entry, if_pos, epsilonTensorSign]
  · intro b _ hb
    have hcoordinate : ∃ i, b i ≠ qubitComplement a i := by
      by_contra h
      push Not at h
      exact hb (funext h)
    obtain ⟨i, hi⟩ := hcoordinate
    have hzero : ∏ j, HTGeometry.hlsWeylEpsilon (a j) (b j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hlsWeylEpsilon_entry]
      simp only [qubitComplement] at hi
      simp [hi]
    simp [hzero]
  · intro h
    exact absurd (Finset.mem_univ (qubitComplement a)) h

theorem epsilonTensorContraction_squared {n : ℕ} (ψ : Quantum.NQubitVec n) :
    epsilonTensorContraction (epsilonTensorContraction ψ) = (-1 : ℂ) ^ n • ψ := by
  rw [epsilonTensorContraction_eq_dual, epsilonTensorContraction_eq_dual]
  exact epsilonTensorDual_squared ψ

/-- On one qubit no nonzero `+1` self-dual vector exists. -/
theorem oneQubit_epsilon_selfDual_subspace_trivial :
    {ψ : Quantum.NQubitVec 1 | epsilonTensorDual ψ = ψ} = {0} := by
  ext ψ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have h2 := epsilonTensorDual_squared_one ψ
    rw [h] at h2
    rw [h] at h2
    funext a
    have ha := congrFun h2 a
    simp only [Pi.neg_apply] at ha
    change ψ a = (0 : ℂ)
    exact CharZero.eq_neg_self_iff.mp ha
  · rintro rfl
    funext a
    simp [epsilonTensorDual]

/-- The paper's odd-rank self-duality equation is also trivial on three qubits. -/
theorem threeQubit_epsilon_selfDual_subspace_trivial :
    {ψ : Quantum.NQubitVec 3 | epsilonTensorDual ψ = ψ} = {0} := by
  ext ψ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have h2 := epsilonTensorDual_squared_three ψ
    rw [h] at h2
    rw [h] at h2
    funext a
    have ha := congrFun h2 a
    simp only [Pi.neg_apply] at ha
    change ψ a = (0 : ℂ)
    exact CharZero.eq_neg_self_iff.mp ha
  · rintro rfl
    funext a
    simp [epsilonTensorDual]

/-! ## Corrected one-index Weyl-epsilon projectors -/

theorem weylEpsilon_not_involutive :
    HTGeometry.hlsWeylEpsilon * HTGeometry.hlsWeylEpsilon ≠ 1 := by
  rw [HTGeometry.hlsWeylEpsilon_squared]
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num at h00

theorem weylEpsilon_fourth_power : HTGeometry.hlsWeylEpsilon ^ 4 = 1 := by
  rw [show HTGeometry.hlsWeylEpsilon ^ 4 =
    (HTGeometry.hlsWeylEpsilon * HTGeometry.hlsWeylEpsilon) *
      (HTGeometry.hlsWeylEpsilon * HTGeometry.hlsWeylEpsilon) by noncomm_ring]
  rw [HTGeometry.hlsWeylEpsilon_squared]
  simp

/-- `+i` eigenspace projector for the Weyl epsilon complex structure. -/
def weylEpsilonPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 - Complex.I • HTGeometry.hlsWeylEpsilon)

/-- `-i` eigenspace projector for the Weyl epsilon complex structure. -/
def weylEpsilonMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 + Complex.I • HTGeometry.hlsWeylEpsilon)

theorem weylEpsilon_projector_sum : weylEpsilonPlus + weylEpsilonMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [weylEpsilonPlus, weylEpsilonMinus, HTGeometry.hlsWeylEpsilon]

theorem weylEpsilonPlus_eigen :
    HTGeometry.hlsWeylEpsilon * weylEpsilonPlus = Complex.I • weylEpsilonPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylEpsilonPlus, HTGeometry.hlsWeylEpsilon, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem weylEpsilonMinus_eigen :
    HTGeometry.hlsWeylEpsilon * weylEpsilonMinus = -Complex.I • weylEpsilonMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylEpsilonMinus, HTGeometry.hlsWeylEpsilon, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem weylEpsilonPlus_idempotent : weylEpsilonPlus * weylEpsilonPlus = weylEpsilonPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylEpsilonPlus, HTGeometry.hlsWeylEpsilon, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem weylEpsilonMinus_idempotent : weylEpsilonMinus * weylEpsilonMinus = weylEpsilonMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylEpsilonMinus, HTGeometry.hlsWeylEpsilon, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem weylEpsilon_projectors_orthogonal : weylEpsilonPlus * weylEpsilonMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylEpsilonPlus, weylEpsilonMinus, HTGeometry.hlsWeylEpsilon,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq]

end

end GaloisForLFunctions.Nieto1810
