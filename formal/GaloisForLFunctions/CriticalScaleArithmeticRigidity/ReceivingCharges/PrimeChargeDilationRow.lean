import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge

/-!
# The exact receiver of a finite conductor packet

The dilation Laplacian removes the common Mertens row of the prime matrix.
What remains is the conductor adjunction diagonal and the completed prime
tail. Harmonic pole subtraction changes neither the tail nor the diagonal.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory SignedArithmeticHodgeTheory
  ArithmeticIntersectionTheory SelectiveMultiscaleArithmeticPositivity
  CriticalArithmeticCorrelationTheory ArithmeticEffectivityTheory SuccessorShellArithmetic

private theorem conductor_profile_sum (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    conductorHorizonProfile Q a n =
      ∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n := by
  simp only [conductorHorizonProfile, normalizedConductorPacket, ramanujanPoleProfile,
    sum_div, mul_div_assoc]

private theorem conductor_profile_mul_pole (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    conductorHorizonProfile Q a n = normalizedConductorPacket Q a n * poleVector n := by
  simp only [conductorHorizonProfile, poleVector, mul_one_div]

/-- The prime-matrix residual is its literal row minus the conductor adjunction diagonal. -/
theorem primeResidual_packet_eq_row (Q N n : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) =
      (∑ j ∈ Icc 1 N, weilPrimeKernel n j * conductorHorizonProfile Q a j) -
        (Real.log N - Real.eulerMascheroniConstant) * conductorHorizonProfile Q a n +
          conductorHorizonProfile Q (fun m => (Real.log m + tameDifferent m) * a m) n := by
  have hterm (m : ℕ) : a m * ramanujanPrimeResidual m N n =
      (∑ j ∈ Icc 1 N, weilPrimeKernel n j * (a m * ramanujanPoleProfile m j)) -
        (Real.log N - Real.eulerMascheroniConstant) * (a m * ramanujanPoleProfile m n) +
          ((Real.log m + tameDifferent m) * a m) * ramanujanPoleProfile m n := by
    rw [ramanujanPrimeResidual, ramanujanAdjunctionEnergy, mul_sub, mul_sum]
    have hrow : (∑ j ∈ Icc 1 N, a m * (weilPrimeKernel n j * ramanujanPoleProfile m j)) =
        ∑ j ∈ Icc 1 N, weilPrimeKernel n j * (a m * ramanujanPoleProfile m j) :=
      sum_congr rfl fun _ _ => by ring
    rw [hrow]
    ring
  simp only [hterm, sum_add_distrib, sum_sub_distrib, conductor_profile_sum, mul_sum]
  rw [sum_comm (s := Icc 1 Q) (t := Icc 1 N)]

/-- Every finite dilation row is exactly its adjunction packet plus the receiving tail. -/
theorem dilation_packet_row_eq {Q N n : ℕ} (a : ℕ → ℝ) (hn : n ∈ Icc 1 N) :
    (mertensSum (N / n) + Real.log n) * conductorHorizonProfile Q a n -
      (∑ j ∈ Icc 1 N, weilPrimeKernel n j * conductorHorizonProfile Q a j) =
      conductorHorizonProfile Q (fun m => (Real.log m + tameDifferent m) * a m) n +
        completedPrimeDilationTail Q a (N / n) n * poleVector n := by
  have h := primeResidual_packet_eq_scalar_sub_tail (Q := Q) a hn
  rw [primeResidual_packet_eq_row] at h
  rw [conductor_profile_mul_pole Q a n] at h ⊢
  linear_combination -h

/-- Removing the literal harmonic pole leaves every completed prime tail unchanged. -/
theorem completedPrimeDilationTail_harmonicCentered {Q : ℕ} (hQ : 1 ≤ Q)
    (N : ℕ) (a : ℕ → ℝ) (Y n : ℕ) :
    completedPrimeDilationTail Q (harmonicCenteredCoefficients Q N a) Y n =
      completedPrimeDilationTail Q a Y n := by
  have hsource (b : ℕ → ℝ) :
      (∑ m ∈ Icc 1 Q, b m *
        (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) =
      arithmeticPrimeGenerator Q b n := (arithmeticPrimeGenerator_eq_jet Q b n).symm
  simp only [completedPrimeDilationTail, hsource, arithmeticPrimeGenerator_harmonicCentered]
  congr 1
  apply sum_congr rfl
  intro k _
  simp only [harmonicCenteredCoefficients, normalizedConductorPacket_addConstantConductor hQ]
  ring

/-- The prescribed harmonic-neutral charge has exactly the uncentered coherent receiving tail. -/
theorem harmonicPrimeCharge_tail_eq {Q : ℕ} (hQ : 1 ≤ Q)
    (N Y n : ℕ) (t : ℝ) :
    completedPrimeDilationTail Q (harmonicPrimeChargeCoefficients Q N t) Y n =
      completedPrimeDilationTail Q
        (primeIncidenceCoefficients (fun _ => t / primePoleScale Q)) Y n := by
  rw [harmonicPrimeChargeCoefficients, completedPrimeDilationTail_harmonicCentered hQ]
  congr 1
  funext p
  unfold primeIncidenceCoefficients primeOnly
  split_ifs <;> ring

#print axioms dilation_packet_row_eq
#print axioms completedPrimeDilationTail_harmonicCentered
#print axioms harmonicPrimeCharge_tail_eq

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
