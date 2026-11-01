import GaloisForLFunctions.CriticalScaleArithmeticRigidity.AffineWindowEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.DyadicPoleRigidity
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadNorm
import GaloisForLFunctions.BezoutValuationIncidence.SmoothLargeScaleRowsOfEveryOrder

/-!
# A packet's successor gap survives coprime dilation

The exact period energy of a packet minus its successor is at least its
nonconstant coefficient mass. Multiplication by a unit modulo the common
period preserves this gap. Relative affine sampling transfers it to every
window beyond the quadratic conductor horizon.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open BezoutValuationIncidence SuccessorShellArithmetic

/-- The actual successor difference controls every nonconstant conductor, including parity. -/
theorem nonconstantPacketMass_le_successor_energy (Q : ℕ) (a : ℕ → ℝ) :
    nonconstantPacketMass Q a ≤
      packetMean Q (fun n => (conductorPacket Q a (n + 1) - conductorPacket Q a n) ^ 2) := by
  rw [packetMean_shift_error, nonconstantPacketMass]
  apply sum_le_sum
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simp only [ite_true, ramanujanLagCoefficient_of_dvd (one_dvd 1),
      Nat.totient_one, Nat.cast_one, one_mul]
    nlinarith only [sq_nonneg (a 1)]
  by_cases hm2 : m = 2
  · subst m
    have hc : ramanujanLagCoefficient 2 1 = -1 := by
      norm_num [ramanujanLagCoefficient_eq_totient_mul,
        sieveLagMultiplier_eq_moebius_totient_quotient, moebiusReal,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    simp only [if_neg hm1, Nat.totient_two, Nat.cast_one, one_mul, hc]
    nlinarith only [sq_nonneg (a 2)]
  have hm3 : 3 ≤ m := by have := (mem_Icc.mp hm).1; omega
  have hr : sieveLagMultiplier m 1 ≤ 1 / 2 := by
    have h := successorMultiplier_sq_le_quarter hm3
    nlinarith only [h, sq_nonneg (sieveLagMultiplier m 1 - 1 / 2)]
  rw [if_neg hm1, ramanujanLagCoefficient_eq_totient_mul]
  have hpos := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg m.totient)
      (show 0 ≤ 1 - 2 * sieveLagMultiplier m 1 by linarith only [hr]))
    (sq_nonneg (a m))
  nlinarith only [hpos]

private theorem conductorPacket_periodic (Q : ℕ) (a : ℕ → ℝ) :
    Function.Periodic (conductorPacket Q a) Q.factorial := by
  intro n
  unfold conductorPacket
  apply sum_congr rfl
  intro m hm
  congr 1
  unfold ramanujanLagCoefficient
  apply sum_congr rfl
  intro d hd
  simp only [Nat.dvd_add_left ((Nat.dvd_of_mem_divisors hd).trans
    (Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2))]

private theorem conductorPacket_mul_of_coprime {Q p : ℕ}
    (hp : Nat.Coprime Q.factorial p) (a : ℕ → ℝ) (n : ℕ) :
    conductorPacket Q a (p * n) = conductorPacket Q a n := by
  apply sum_congr rfl
  intro m hm
  have hmp : Nat.Coprime m p := Nat.Coprime.of_dvd_left
    (Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2) hp
  have hd := ramanujanLagCoefficient_dilate_reduced (mem_Icc.mp hm).1 p n
  rw [hmp.gcd_eq_one, Nat.div_one] at hd
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  exact congrArg (fun t : ℝ => a m * t) (mul_left_cancel₀ hphi hd)

/-- Coprime dilation permutes the successor observations without changing their period energy. -/
theorem affinePacketEnergy_coprime_successor_eq {Q p : ℕ}
    (hp : Nat.Coprime Q.factorial p) (a : ℕ → ℝ) :
    affinePacketEnergy Q a a p 1 1 0 =
      packetMean Q (fun n => (conductorPacket Q a (n + 1) - conductorPacket Q a n) ^ 2) := by
  have hper := conductorPacket_periodic Q a
  have hdiff : Function.Periodic
      (fun n => (conductorPacket Q a (n + 1) - conductorPacket Q a n) ^ 2) Q.factorial := by
    intro n
    dsimp only
    rw [show n + Q.factorial + 1 = (n + 1) + Q.factorial by omega, hper, hper]
  have hs := sum_range_comp_mul_of_coprime (Nat.factorial_pos Q) hp hdiff
  have he := congrArg (fun t : ℝ => t / (Q.factorial : ℝ)) hs
  simpa only [affinePacketEnergy, affinePacketDifference, one_mul, Nat.add_zero,
    packetMean, conductorPacket_mul_of_coprime hp] using he

/-- Every coprime successor channel retains the full nonconstant-mass floor. -/
theorem nonconstantPacketMass_le_coprime_successor_energy {Q p : ℕ}
    (hp : Nat.Coprime Q.factorial p) (a : ℕ → ℝ) :
    nonconstantPacketMass Q a ≤ affinePacketEnergy Q a a p 1 1 0 := by
  rw [affinePacketEnergy_coprime_successor_eq hp]
  exact nonconstantPacketMass_le_successor_energy Q a

/-- Quadratic sampling preserves the successor gap uniformly in every coprime multiplier. -/
theorem coprime_successor_window_lower {Q p : ℕ} (hQ : 2 ≤ Q)
    (hp : Nat.Coprime Q.factorial p) (a : ℕ → ℝ) (A K : ℕ)
    (hK : (Q : ℝ) * ((Q : ℝ) - 1) ≤ K) :
    ((K : ℝ) - (Q : ℝ) * ((Q : ℝ) - 1)) * nonconstantPacketMass Q a ≤
      ∑ n ∈ Icc (A + 1) (A + K),
        (conductorPacket Q a (p * n + 1) - conductorPacket Q a n) ^ 2 := by
  have hg := mul_le_mul_of_nonneg_left
    (nonconstantPacketMass_le_coprime_successor_energy hp a) (sub_nonneg.mpr hK)
  have hw := affinePacketDifference_window_lower hQ a a p 1 1 0 A K
  simpa only [affinePacketDifference, one_mul, Nat.add_zero] using hg.trans hw

end GaloisForLFunctions.CriticalScaleArithmeticRigidity

#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.nonconstantPacketMass_le_successor_energy
#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.affinePacketEnergy_coprime_successor_eq
#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.nonconstantPacketMass_le_coprime_successor_energy
#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.coprime_successor_window_lower
