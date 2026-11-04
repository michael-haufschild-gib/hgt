import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMixedMoments
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.DilationPacketOperator

/-!
# Finite linear combinations in the literal complete form

Packet synthesis preserves sums and scalar multiplication. The complete
matrix is symmetric, so finite charge distributions are evaluated by their
full polarized kernel.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory

/-- Packet synthesis preserves finite sums over arbitrary index sets. -/
theorem packetVector_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ) (N : ℕ) :
    packetVector (fun n => ∑ i ∈ S, F i n) N = ∑ i ∈ S, packetVector (F i) N := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    ext n
    exact zero_div _
  | @insert i S hi ih =>
    simp only [sum_insert hi, packetVector_add, ih]

/-- Symmetry of the complete matrix gives symmetry of its packet pairing. -/
theorem completePacketPairing_symm (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F G : ℕ → ℝ) :
    completePacketPairing φ c N F G = completePacketPairing φ c N G F := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  unfold completePacketPairing
  rw [hs, real_inner_comm]

theorem completePacketPairing_add_left (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F G H : ℕ → ℝ) :
    completePacketPairing φ c N (fun n => F n + G n) H =
      completePacketPairing φ c N F H + completePacketPairing φ c N G H := by
  simp only [completePacketPairing, packetVector_add, map_add, inner_add_left]

theorem completePacketPairing_add_right (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F G H : ℕ → ℝ) :
    completePacketPairing φ c N F (fun n => G n + H n) =
      completePacketPairing φ c N F G + completePacketPairing φ c N F H := by
  simp only [completePacketPairing, packetVector_add, inner_add_right]

theorem completePacketPairing_const_mul_left (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (F G : ℕ → ℝ) (s : ℝ) :
    completePacketPairing φ c N (fun n => s * F n) G = s * completePacketPairing φ c N F G := by
  simp only [completePacketPairing, packetVector_const_mul, map_smul, real_inner_smul_left]

theorem completePacketPairing_const_mul_right (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (F G : ℕ → ℝ) (s : ℝ) :
    completePacketPairing φ c N F (fun n => s * G n) = s * completePacketPairing φ c N F G := by
  simp only [completePacketPairing, packetVector_const_mul, real_inner_smul_right]

theorem completePacketPairing_sum_left {ι : Type*} (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (S : Finset ι) (F : ι → ℕ → ℝ) (G : ℕ → ℝ) :
    completePacketPairing φ c N (fun n => ∑ i ∈ S, F i n) G =
      ∑ i ∈ S, completePacketPairing φ c N (F i) G := by
  induction S using Finset.induction_on with
  | empty =>
    have hz : packetVector (fun _ => 0) N = 0 := by
      ext n
      exact zero_div _
    simp only [sum_empty, completePacketPairing, hz, map_zero, inner_zero_left]
  | @insert i S hi ih =>
    simp only [sum_insert hi, completePacketPairing_add_left, ih]

theorem completePacketPairing_sum_right {ι : Type*} (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (S : Finset ι) (F : ℕ → ℝ) (G : ι → ℕ → ℝ) :
    completePacketPairing φ c N F (fun n => ∑ i ∈ S, G i n) =
      ∑ i ∈ S, completePacketPairing φ c N F (G i) := by
  rw [completePacketPairing_symm, completePacketPairing_sum_left]
  exact sum_congr rfl fun i _ => completePacketPairing_symm φ c N (G i) F

/-- Every finite packet combination is evaluated by its complete polarized kernel. -/
theorem completeWeilEnergy_packet_sum {ι : Type*} (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (S : Finset ι) (F : ι → ℕ → ℝ) :
    completeWeilEnergy φ c N (packetVector (fun n => ∑ i ∈ S, F i n) N) =
      ∑ i ∈ S, ∑ j ∈ S, completePacketPairing φ c N (F i) (F j) := by
  change completePacketPairing φ c N _ _ = _
  rw [completePacketPairing_sum_left]
  exact sum_congr rfl fun i _ => completePacketPairing_sum_right φ c N S (F i) F

#print axioms completeWeilEnergy_packet_sum

end GaloisForLFunctions.ArithmeticCouplingTheory
