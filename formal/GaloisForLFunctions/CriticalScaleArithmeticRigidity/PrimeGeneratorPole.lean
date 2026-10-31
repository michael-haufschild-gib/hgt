import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeResidual
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimePoleNorm
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.DyadicPoleRigidity
import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodTupleSeriesFromRadicalClosedRows

/-!+# Coherent pole response of the literal prime generator

The convergent Mangoldt-weighted dilation generator has a divisor-jet
description. Complete-period averaging extracts its exact pole row.
Its square-energy bound survives removal of the prime cutoff and retains
the original packet's adjunction energy.
-/

noncomputable section

open Finset Filter Topology ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SuccessorShellArithmetic BezoutValuationIncidence
  CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory

/-- The actual complete Mangoldt-weighted dilation difference. -/
def arithmeticPrimeGenerator (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  completedPrimeDilationTail Q a 0 n

/-- Add a constant conductor without changing any arithmetic excitation coefficient. -/
def addConstantConductor (a : ℕ → ℝ) (t : ℝ) (m : ℕ) : ℝ :=
  if m = 1 then a m + t else a m

/-- Adjusting the constant conductor leaves the exact adjunction energy unchanged. -/
theorem primeAdjunctionMass_addConstantConductor (Q : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    primeAdjunctionMass Q (addConstantConductor a t) = primeAdjunctionMass Q a := by
  apply sum_congr rfl
  intro m _
  by_cases hm : m = 1
  · subst m
    simp [addConstantConductor, tameDifferent]
  · simp only [addConstantConductor, if_neg hm]

theorem arithmeticPrimeGenerator_eq_jet (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q a n =
      ∑ m ∈ Icc 1 Q, a m *
        (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n) := by
  have h0 : Icc 1 (0 : ℕ) = ∅ := by decide
  rw [arithmeticPrimeGenerator, completedPrimeDilationTail, h0, sum_empty, sub_zero]

/-- The literal complete prime generator annihilates the constant conductor. -/
theorem arithmeticPrimeGenerator_addConstantConductor (Q : ℕ) (a : ℕ → ℝ)
    (t : ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q (addConstantConductor a t) n =
      arithmeticPrimeGenerator Q a n := by
  rw [arithmeticPrimeGenerator_eq_jet, arithmeticPrimeGenerator_eq_jet]
  apply sum_congr rfl
  intro m _
  by_cases hm : m = 1
  · subst m
    simp [addConstantConductor, ramanujanLogDivisorJet, tameDifferent]
  · simp only [addConstantConductor, if_neg hm]

theorem packetMean_sum {ι : Type*} (Q : ℕ) (S : Finset ι) (f : ι → ℕ → ℝ) :
    packetMean Q (fun n => ∑ i ∈ S, f i n) = ∑ i ∈ S, packetMean Q (f i) := by
  simp only [packetMean]
  rw [sum_comm, sum_div]

theorem packetMean_const_mul (Q : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    packetMean Q (fun n => c * f n) = c * packetMean Q f := by
  simp only [packetMean, ← mul_sum, mul_div_assoc]

theorem packetMean_div_const (Q : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    packetMean Q (fun n => f n / c) = packetMean Q f / c := by
  simp only [packetMean, ← sum_div]
  ring

/-- Divisor-jet charge is unchanged when its period is repeated to the common packet period. -/
theorem packetMean_divisorJet {Q m : ℕ} (hm : m ∈ Icc 1 Q) :
    packetMean Q (ramanujanLogDivisorJet m) = vonMangoldt m := by
  have hm0 := (mem_Icc.mp hm).1
  have hd : m ∣ Q.factorial := Nat.dvd_factorial hm0 (mem_Icc.mp hm).2
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hQR : (Q.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos Q).ne'
  have hmean := periodMean_ramanujanLogDivisorJet hm0
  rw [div_eq_iff hmR] at hmean
  have hsum := sum_range_mul_of_periodic (ramanujanLogDivisorJet_periodic m) (Q.factorial / m)
  rw [Nat.div_mul_cancel hd, hmean] at hsum
  have hcast : ((Q.factorial / m : ℕ) : ℝ) * m = Q.factorial := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
  rw [packetMean, hsum]
  calc
    _ = ((((Q.factorial / m : ℕ) : ℝ) * m) * vonMangoldt m) / Q.factorial := by ring
    _ = _ := by rw [hcast, mul_div_cancel_left₀ _ hQR]

/-- Every retained nonconstant normalized mode has zero complete-period mean. -/
theorem packetMean_normalizedMode_eq_zero {Q m : ℕ}
    (hm : m ∈ Icc 1 Q) (hm1 : m ≠ 1) :
    packetMean Q (normalizedRamanujanMode m) = 0 := by
  have hm0 := (mem_Icc.mp hm).1
  have hconst (n : ℕ) : ramanujanLagCoefficient 1 n = 1 := by
    simpa only [Nat.totient_one, Nat.cast_one] using
      ramanujanLagCoefficient_of_dvd (one_dvd n)
  have hsum := sum_range_ramanujanLagCoefficient_mul hm0 (show 0 < (1 : ℕ) by decide)
    (Nat.dvd_factorial hm0 (mem_Icc.mp hm).2) (one_dvd Q.factorial)
  simp only [hconst, mul_one, if_neg hm1] at hsum
  simp only [packetMean, normalizedRamanujanMode_eq_coefficient hm0,
    ← sum_div, hsum, zero_div]

/-- Prime-supported input has zero constant conductor before applying the generator. -/
theorem packetMean_primeOnly_eq_zero (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (normalizedConductorPacket Q (primeOnly a)) = 0 := by
  rw [normalizedConductorPacket, packetMean_sum]
  apply sum_eq_zero
  intro m hm
  rw [packetMean_const_mul]
  by_cases hp : m.Prime
  · rw [packetMean_normalizedMode_eq_zero hm hp.ne_one, mul_zero]
  · simp only [primeOnly, if_neg hp, zero_mul]

/-- The actual prime generator produces the exact coherent prime-pole functional. -/
theorem packetMean_arithmeticPrimeGenerator_primeOnly (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (arithmeticPrimeGenerator Q (primeOnly a)) = primePoleResponse Q a := by
  have heq (n : ℕ) : arithmeticPrimeGenerator Q (primeOnly a) n =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, a p *
        (ramanujanLogDivisorJet p n / Real.sqrt (p.totient : ℝ) -
          (Real.log p + tameDifferent p) * normalizedRamanujanMode p n) := by
    rw [arithmeticPrimeGenerator_eq_jet, sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · simp only [primeOnly, if_pos hp]
    · simp only [primeOnly, if_neg hp, zero_mul]
  change packetMean Q (fun n => arithmeticPrimeGenerator Q (primeOnly a) n) = _
  simp only [heq, packetMean_sum, primePoleResponse]
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpQ, hp⟩ := mem_filter.mp hp
  rw [packetMean_const_mul, packetMean_sub, packetMean_div_const,
    packetMean_divisorJet hpQ, packetMean_const_mul,
    packetMean_normalizedMode_eq_zero hpQ hp.ne_one, mul_zero, sub_zero,
    vonMangoldt_apply_prime hp]
  ring

/-- The source pole inequality has exactly the Mertens constant, not a cutoff-independent one. -/
theorem optimal_arithmeticPrimeGenerator_pole_constant_iff {Q : ℕ}
    (hQ : 2 ≤ Q) (C : ℝ) :
    (∀ a : ℕ → ℝ,
      packetMean Q (arithmeticPrimeGenerator Q (primeOnly a)) ^ 2 ≤
        C * primeAdjunctionMass Q (primeOnly a)) ↔ primePoleScale Q ≤ C := by
  simp only [packetMean_arithmeticPrimeGenerator_primeOnly]
  exact optimal_primePoleResponse_constant_iff hQ C

/-- The head estimate passes to the literal complete generator on the finite averaging period. -/
theorem arithmeticPrimeGenerator_period_sq_le (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n => arithmeticPrimeGenerator Q a n ^ 2) ≤
      primeActivityMass Q * primeAdjunctionMass Q a := by
  have hhead (K : ℕ) :
      packetMean Q (fun n => finitePrimeDilationTail Q a 0 K n ^ 2) ≤
        primeActivityMass Q * primeAdjunctionMass Q a := by
    let S := (Icc 1 K).filter (fun k => 0 < k)
    have heq (n : ℕ) : finitePrimeDilationTail Q a 0 K n =
        ∑ m ∈ Icc 1 Q, primeHeadCoefficient Q a S m * normalizedRamanujanMode m n := by
      exact (primeHeadCoefficient_packet Q a S n).symm
    simp only [heq, packetMean]
    rw [sum_range_normalizedRamanujan_packet_sq (Icc 1 Q) (primeHeadCoefficient Q a S)
      Q.factorial (fun m hm => (mem_Icc.mp hm).1)
      (fun m hm => Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2)]
    have hQ : (Q.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos Q).ne'
    rw [mul_div_cancel_left₀ _ hQ]
    exact primeHeadCoefficient_sq_sum_le Q a S
  have hlim : Tendsto
      (fun K => packetMean Q (fun n => finitePrimeDilationTail Q a 0 K n ^ 2)) atTop
      (𝓝 (packetMean Q (fun n => arithmeticPrimeGenerator Q a n ^ 2))) :=
    (tendsto_finsetSum _ fun n _ => (tendsto_finitePrimeDilationTail Q a 0 n).pow 2).div_const
      (Q.factorial : ℝ)
  exact le_of_tendsto hlim (Eventually.of_forall hhead)

/-- Any sector constant for the actual generator must pay its sharp pole-response cost. -/
theorem primePoleScale_le_generator_sector_constant {Q : ℕ} (hQ : 2 ≤ Q)
    (C : ℝ)
    (hC : ∀ a : ℕ → ℝ,
      packetMean Q (fun n => arithmeticPrimeGenerator Q (primeOnly a) n ^ 2) ≤
        C * primeAdjunctionMass Q (primeOnly a)) :
    primePoleScale Q ≤ C := by
  apply (optimal_arithmeticPrimeGenerator_pole_constant_iff hQ C).mp
  intro a
  exact (packetMean_sq_le_mean_sq Q (arithmeticPrimeGenerator Q (primeOnly a))).trans (hC a)

#print axioms packetMean_divisorJet
#print axioms arithmeticPrimeGenerator_addConstantConductor
#print axioms packetMean_primeOnly_eq_zero
#print axioms packetMean_arithmeticPrimeGenerator_primeOnly
#print axioms optimal_arithmeticPrimeGenerator_pole_constant_iff
#print axioms arithmeticPrimeGenerator_period_sq_le
#print axioms primePoleScale_le_generator_sector_constant

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
