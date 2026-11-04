import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationPairing

/-!
# The literal dilation operator in packet coordinates

The Mertens diagonal minus the prime matrix represents the finite dilation
form. Its polarized pairing is therefore the actual Euclidean matrix
pairing, with no asymptotic replacement of the complementary quotient.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory

theorem packetVector_add (N : ℕ) (F G : ℕ → ℝ) :
    packetVector (fun n => F n + G n) N = packetVector F N + packetVector G N := by
  ext n
  change (F n + G n) / Real.sqrt (n : ℕ) =
    F n / Real.sqrt (n : ℕ) + G n / Real.sqrt (n : ℕ)
  exact add_div _ _ _

theorem packetVector_const_mul (N : ℕ) (F : ℕ → ℝ) (s : ℝ) :
    packetVector (fun n => s * F n) N = s • packetVector F N := by
  ext n
  change (s * F n) / Real.sqrt (n : ℕ) = s * (F n / Real.sqrt (n : ℕ))
  ring

theorem packetVector_sum (N : ℕ) (S : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    packetVector (fun n => ∑ m ∈ S, F m n) N = ∑ m ∈ S, packetVector (F m) N := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    ext n
    change (0 : ℝ) / Real.sqrt (n : ℕ) = 0
    exact zero_div _
  | @insert m S hm ih =>
    simp only [sum_insert hm, packetVector_add, ih]

/-- Packet coordinates turn Euclidean pairings into literal harmonic pairings. -/
theorem packetVector_inner (N : ℕ) (F G : ℕ → ℝ) :
    ⟪packetVector F N, packetVector G N⟫ =
      ∑ n ∈ Icc 1 N, F n * G n / (n : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N,
    (G n / Real.sqrt (n : ℕ)) * (F n / Real.sqrt (n : ℕ))) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => (G n / Real.sqrt n) * (F n / Real.sqrt n))]
  apply sum_congr rfl
  intro n _
  rw [div_mul_div_comm, ← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

/-- The exact finite dilation row: Mertens diagonal minus the full prime matrix. -/
def dilationPacketVector (N : ℕ) (F : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  packetVector (fun n => (mertensSum (N / n) + Real.log n) * F n) N -
    Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N)

theorem dilationPacketVector_add (N : ℕ) (F G : ℕ → ℝ) :
    dilationPacketVector N (fun n => F n + G n) =
      dilationPacketVector N F + dilationPacketVector N G := by
  have hd : (fun n => (mertensSum (N / n) + Real.log n) * (F n + G n)) =
      (fun n => (mertensSum (N / n) + Real.log n) * F n +
        (mertensSum (N / n) + Real.log n) * G n) := by funext n; ring
  simp only [dilationPacketVector, hd, packetVector_add, map_add]
  abel

/-- The matrix operator has precisely the nonnegative dilation jump energy. -/
theorem dilationPacketVector_inner_self (N : ℕ) (F : ℕ → ℝ) :
    ⟪dilationPacketVector N F, packetVector F N⟫ = jumpEnergy N F := by
  have hext : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (packetVector F N) n = atomAmplitude F n := fun n hn => by
    simp only [primeHorizonExtension, dif_pos hn]
    rfl
  have hp : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N), packetVector F N⟫ =
      primeDilationForm N F := by
    rw [← atomicWeilForm_primeHorizonExtension, atomicWeilForm_congr hext,
      atomicWeilForm_atomAmplitude]
  rw [dilationPacketVector, inner_sub_left, packetVector_inner, hp, primeDilationForm_eq]
  have hd : (∑ n ∈ Icc 1 N,
      ((mertensSum (N / n) + Real.log n) * F n) * F n / (n : ℝ)) = mertensDiagonal N F := by
    apply sum_congr rfl
    intro n _
    ring
  rw [hd]
  ring

theorem dilationPacketVector_symmetric (N : ℕ) (F G : ℕ → ℝ) :
    ⟪dilationPacketVector N F, packetVector G N⟫ =
      ⟪dilationPacketVector N G, packetVector F N⟫ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (fullPrimeMatrix_isHermitian N)
  have hp :
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N), packetVector G N⟫ =
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector G N), packetVector F N⟫ := by
    rw [hs, real_inner_comm]
  simp only [dilationPacketVector, inner_sub_left, packetVector_inner, hp]
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- Finite polarization identifies the complete dilation row, including its boundary. -/
theorem jumpPairing_eq_inner_dilationPacketVector (N : ℕ) (F G : ℕ → ℝ) :
    jumpPairing N F G = ⟪dilationPacketVector N F, packetVector G N⟫ := by
  have h := jumpPairing_polarization N F G
  rw [← dilationPacketVector_inner_self, ← dilationPacketVector_inner_self,
    ← dilationPacketVector_inner_self, dilationPacketVector_add, packetVector_add] at h
  simp only [inner_add_left, inner_add_right, dilationPacketVector_symmetric N G F] at h
  linarith only [h]

/-- Every Euclidean horizon vector has exact packet coordinates. -/
theorem packetVector_sqrt_extension {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    packetVector (fun n => Real.sqrt n * primeHorizonExtension x n) N = x := by
  ext n
  change (Real.sqrt (n : ℕ) * primeHorizonExtension x n) / Real.sqrt (n : ℕ) = x n
  rw [primeHorizonExtension_coe]
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  field_simp [(Real.sqrt_pos.mpr hn).ne']

#print axioms jumpPairing_eq_inner_dilationPacketVector
#print axioms packetVector_sqrt_extension

end GaloisForLFunctions.ArithmeticCouplingTheory
