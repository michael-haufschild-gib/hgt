import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeDilationRow
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.DilationPacketOperator
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds

/-!
# Exact conductor-complement receiving identity

The dilation row of a finite conductor packet consists of its adjunction
packet and completed prime tail. Orthogonality removes the entire first
term, leaving the tail as the literal mixed receiver. Every complementary
vector is harmonic-pole-neutral, so the complete-form comparison applies.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms ArithmeticIntersectionTheory
  SelectiveMultiscaleArithmeticPositivity ArithmeticEffectivityTheory

/-- Conductor coefficients synthesize the literal Euclidean packet. -/
theorem packetVector_normalizedConductorPacket (Q N : ℕ) (a : ℕ → ℝ) :
    packetVector (normalizedConductorPacket Q a) N =
      ∑ m ∈ Icc 1 Q, a m • ramanujanHorizonVector m N := by
  change packetVector (fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) N = _
  rw [packetVector_sum]
  apply sum_congr rfl
  intro m _
  rw [packetVector_const_mul]
  rfl

/-- Raw and logarithmically normalized conductor vectors span the same space above horizon one. -/
theorem packetVector_conductor_mem {N : ℕ} (hN : 2 ≤ N) (Q : ℕ) (a : ℕ → ℝ) :
    packetVector (normalizedConductorPacket Q a) N ∈ conductorSubspace Q N := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hroot : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have hraw (m : ℕ) : ramanujanHorizonVector m N =
      Real.sqrt (Real.log N) • normalizedRamanujanHorizonVector m N := by
    rw [normalizedRamanujanHorizonVector, smul_smul, mul_inv_cancel₀ hroot, one_smul]
  rw [packetVector_normalizedConductorPacket]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  rw [hraw]
  exact Submodule.smul_mem _ _ (mem_conductorSubspace_normalizedRamanujanHorizonVector hm)

/-- The scalar arithmetic row identity is the exact Euclidean dilation-operator identity. -/
theorem dilationPacketVector_conductor_eq (Q N : ℕ) (a : ℕ → ℝ) :
    dilationPacketVector N (normalizedConductorPacket Q a) =
      packetVector (normalizedConductorPacket Q
        (fun m => (Real.log m + tameDifferent m) * a m)) N +
      packetVector (fun n => completedPrimeDilationTail Q a (N / n) n) N := by
  have hrow (n : PrimeHorizonIndex N) :
      (Matrix.toEuclideanLin (fullPrimeMatrix N)
        (packetVector (normalizedConductorPacket Q a) N)) n =
      ∑ j ∈ Icc 1 N, weilPrimeKernel n j * conductorHorizonProfile Q a j := by
    change (∑ j : PrimeHorizonIndex N, weilPrimeKernel n j * conductorHorizonProfile Q a j) = _
    exact sum_coe_sort (Icc 1 N) (fun j => weilPrimeKernel n j * conductorHorizonProfile Q a j)
  ext n
  change ((ArithmeticCouplingTheory.mertensSum (N / (n : ℕ)) + Real.log (n : ℕ)) *
      normalizedConductorPacket Q a n) / Real.sqrt (n : ℕ) -
        (Matrix.toEuclideanLin (fullPrimeMatrix N)
          (packetVector (normalizedConductorPacket Q a) N)) n =
      normalizedConductorPacket Q (fun m => (Real.log m + tameDifferent m) * a m) n /
        Real.sqrt (n : ℕ) + completedPrimeDilationTail Q a (N / (n : ℕ)) n / Real.sqrt (n : ℕ)
  rw [hrow]
  simpa only [conductorHorizonProfile, poleVector, mul_one_div, mul_div_assoc,
    ArithmeticCouplingTheory.mertensSum, RenormalizedArithmeticPotentialTheory.mertensSum] using
    dilation_packet_row_eq a n.property

/-- Every complementary mixed dilation pairing is exactly the completed receiving tail. -/
theorem jumpPairing_conductor_complement {Q N : ℕ} (hN : 2 ≤ N)
    (a G : ℕ → ℝ) (hG : packetVector G N ∈ (conductorSubspace Q N)ᗮ) :
    jumpPairing N (normalizedConductorPacket Q a) G =
      ∑ n ∈ Icc 1 N, completedPrimeDilationTail Q a (N / n) n * G n / (n : ℝ) := by
  rw [jumpPairing_eq_inner_dilationPacketVector, dilationPacketVector_conductor_eq,
    inner_add_left, Submodule.inner_right_of_mem_orthogonal
      (packetVector_conductor_mem hN Q _) hG, zero_add, packetVector_inner]

/-- The prescribed coherent charge has the same exact tail after harmonic centering. -/
theorem harmonicPrimeCharge_complement_pairing {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 2 ≤ N)
    (t : ℝ) (G : ℕ → ℝ) (hG : packetVector G N ∈ (conductorSubspace Q N)ᗮ) :
    jumpPairing N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) G =
      ∑ n ∈ Icc 1 N,
        completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => t / primePoleScale Q))
          (N / n) n * G n / (n : ℝ) := by
  rw [jumpPairing_conductor_complement hN _ G hG]
  simp only [harmonicPrimeCharge_tail_eq hQ]

/-- The full conductor complement is contained in the literal harmonic-pole hyperplane. -/
theorem harmonic_neutral_of_conductor_complement {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 2 ≤ N)
    (G : ℕ → ℝ) (hG : packetVector G N ∈ (conductorSubspace Q N)ᗮ) :
    ∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0 := by
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hroot : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have hpole : packetVector (fun _ => (1 : ℝ)) N ∈ conductorSubspace Q N := by
    have he : packetVector (fun _ => (1 : ℝ)) N = ramanujanHorizonVector 1 N := by
      ext n
      change 1 / Real.sqrt (n : ℕ) = normalizedRamanujanMode 1 n / Real.sqrt (n : ℕ)
      rw [normalizedRamanujanMode_one]
    rw [he]
    have h := Submodule.smul_mem (conductorSubspace Q N) (Real.sqrt (Real.log N))
      (mem_conductorSubspace_normalizedRamanujanHorizonVector (N := N) h1)
    simpa only [normalizedRamanujanHorizonVector, smul_smul, mul_inv_cancel₀ hroot, one_smul] using h
  have h := Submodule.inner_right_of_mem_orthogonal hpole hG
  simpa only [packetVector_inner, one_mul] using h

#print axioms harmonicPrimeCharge_complement_pairing
#print axioms harmonic_neutral_of_conductor_complement

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
