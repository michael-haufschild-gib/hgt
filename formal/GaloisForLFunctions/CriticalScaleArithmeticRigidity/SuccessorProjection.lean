import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.AffineShellConductorSelection

/-!
# Exact successor projection of arithmetic packets

A shifted Ramanujan packet splits into its conductor projection and an
orthogonal remainder. The complete-period error against any second packet
is the sum of these two energies, with every mixed coefficient retained.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open BezoutValuationIncidence SuccessorShellArithmetic

/-- A finite packet of the actual Ramanujan conductor modes. -/
def conductorPacket (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 Q, a m * ramanujanLagCoefficient m n

/-- Complete-period mean; the factorial is a common period of every retained conductor. -/
def packetMean (Q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ range Q.factorial, f n) / (Q.factorial : ℝ)

/-- Coefficients of the orthogonal conductor projection after a true integer shift. -/
def shiftProjection (h : ℕ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  a m * sieveLagMultiplier m h

/-- The part of a shifted conductor mode orthogonal to all unshifted conductor modes. -/
def shiftLeakageWeight (m h : ℕ) : ℝ :=
  (m.totient : ℝ) * (1 - sieveLagMultiplier m h ^ 2)

private theorem packet_modulus_dvd {m Q : ℕ} (hm : m ∈ Icc 1 Q) : m ∣ Q.factorial :=
  Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2

theorem packetMean_sub (Q : ℕ) (f g : ℕ → ℝ) :
    packetMean Q (fun n => f n - g n) = packetMean Q f - packetMean Q g := by
  simp only [packetMean, sum_sub_distrib, sub_div]

theorem packetMean_sq_nonneg (Q : ℕ) (f : ℕ → ℝ) :
    0 ≤ packetMean Q (fun n => f n ^ 2) :=
  div_nonneg (sum_nonneg fun n _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- Dilation reaches the constant conductor exactly from divisors of its multiplier. -/
theorem packetMean_dilate (Q : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    packetMean Q (fun n => conductorPacket Q a (k * n)) =
      ∑ m ∈ Icc 1 Q, if m ∣ k then a m * m.totient else 0 := by
  have hquot (m : ℕ) (hm : m ∈ Icc 1 Q) :
      m / Nat.gcd m k = 1 ↔ m ∣ k := by
    constructor
    · intro h
      have he := Nat.div_mul_cancel (Nat.gcd_dvd_left m k)
      rw [h, one_mul] at he
      exact he ▸ Nat.gcd_dvd_right m k
    · intro h
      rw [Nat.gcd_eq_left h, Nat.div_self (mem_Icc.mp hm).1]
  have hmean (m : ℕ) (hm : m ∈ Icc 1 Q) :
      (∑ n ∈ range Q.factorial, ramanujanLagCoefficient m (k * n)) =
      if m ∣ k then (Q.factorial : ℝ) * m.totient else 0 := by
    have he := sum_range_ramanujanLagCoefficient_mul_affine
      (show 0 < (1 : ℕ) by decide) (mem_Icc.mp hm).1
      (one_dvd Q.factorial) (packet_modulus_dvd hm) k 0
    have hconst (n : ℕ) : ramanujanLagCoefficient 1 n = 1 := by
      simpa only [Nat.totient_one, Nat.cast_one] using
        ramanujanLagCoefficient_of_dvd (one_dvd n)
    simpa only [hconst, one_mul, Nat.add_zero, eq_comm (a := 1),
      hquot m hm, ramanujanLagCoefficient_of_dvd (dvd_zero m)] using he
  have he : (∑ n ∈ range Q.factorial, conductorPacket Q a (k * n)) =
      (Q.factorial : ℝ) * ∑ m ∈ Icc 1 Q, if m ∣ k then a m * m.totient else 0 := by
    simp only [conductorPacket]
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [← mul_sum, hmean m hm]
    split_ifs <;> ring
  rw [packetMean, he, mul_div_cancel_left₀]
  exact_mod_cast (Nat.factorial_pos Q).ne'

/-- Shifted packet covariance is diagonal in the conductor, with its true lag coefficient. -/
theorem packetMean_shift_mul (Q : ℕ) (a b : ℕ → ℝ) (i j : ℕ) :
    packetMean Q (fun n => conductorPacket Q a (n + i) * conductorPacket Q b (n + j)) =
      ∑ m ∈ Icc 1 Q, a m * b m * ramanujanLagCoefficient m (Nat.dist i j) := by
  have he :
      (∑ n ∈ range Q.factorial,
        conductorPacket Q a (n + i) * conductorPacket Q b (n + j)) =
      (Q.factorial : ℝ) *
        ∑ m ∈ Icc 1 Q, a m * b m * ramanujanLagCoefficient m (Nat.dist i j) := by
    calc
      _ = ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, a m * b l *
          (∑ n ∈ range Q.factorial,
            ramanujanLagCoefficient m (n + i) * ramanujanLagCoefficient l (n + j)) := by
        simp only [conductorPacket, sum_mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro m _
        rw [sum_comm]
        apply sum_congr rfl
        intro l _
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        ring
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro m hm
        have hentry (l : ℕ) (hl : l ∈ Icc 1 Q) :
            a m * b l *
              (∑ n ∈ range Q.factorial,
                ramanujanLagCoefficient m (n + i) * ramanujanLagCoefficient l (n + j)) =
            if l = m then (Q.factorial : ℝ) *
              (a m * b m * ramanujanLagCoefficient m (Nat.dist i j)) else 0 := by
          rw [sum_range_ramanujanLagCoefficient_shift_mul
            (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
            (packet_modulus_dvd hm) (packet_modulus_dvd hl)]
          by_cases hlm : l = m
          · subst l
            simp only [ite_true]
            ring
          · simp only [if_neg hlm, if_neg (Ne.symm hlm), mul_zero]
        rw [sum_congr rfl hentry, sum_ite_eq', if_pos hm]
  rw [packetMean, he, mul_div_cancel_left₀]
  exact_mod_cast (Nat.factorial_pos Q).ne'

/-- Translation preserves the complete-period packet norm. -/
theorem packetMean_shift_sq (Q : ℕ) (a : ℕ → ℝ) (h : ℕ) :
    packetMean Q (fun n => conductorPacket Q a (n + h) ^ 2) =
      ∑ m ∈ Icc 1 Q, (m.totient : ℝ) * a m ^ 2 := by
  simp only [pow_two, packetMean_shift_mul, Nat.dist_self,
    ramanujanLagCoefficient_of_dvd (dvd_zero _)]
  apply sum_congr rfl
  intro m _
  ring

/-- The complete error against an arbitrary packet, before completion of the square. -/
theorem packetMean_shift_error (Q : ℕ) (a b : ℕ → ℝ) (h : ℕ) :
    packetMean Q (fun n => (conductorPacket Q a (n + h) - conductorPacket Q b n) ^ 2) =
      ∑ m ∈ Icc 1 Q,
        ((m.totient : ℝ) * a m ^ 2 + (m.totient : ℝ) * b m ^ 2 -
          2 * a m * b m * ramanujanLagCoefficient m h) := by
  have he :
      packetMean Q (fun n => (conductorPacket Q a (n + h) - conductorPacket Q b n) ^ 2) =
      packetMean Q (fun n => conductorPacket Q a (n + h) ^ 2) +
        packetMean Q (fun n => conductorPacket Q b (n + 0) ^ 2) -
        2 * packetMean Q (fun n =>
          conductorPacket Q a (n + h) * conductorPacket Q b (n + 0)) := by
    have hcross :
        (∑ n ∈ range Q.factorial,
          2 * conductorPacket Q a (n + h) * conductorPacket Q b n) =
        2 * ∑ n ∈ range Q.factorial,
          conductorPacket Q a (n + h) * conductorPacket Q b n := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    simp only [packetMean, Nat.add_zero, sub_sq,
      sum_add_distrib, sum_sub_distrib, hcross]
    ring
  rw [he, packetMean_shift_sq, packetMean_shift_sq, packetMean_shift_mul, Nat.dist_zero_right]
  rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  ring

/-- Exact orthogonal splitting: approximation error plus the unavoidable successor leakage. -/
theorem packetMean_shift_error_eq_projection_add_leakage
    (Q : ℕ) (a b : ℕ → ℝ) (h : ℕ) :
    packetMean Q (fun n => (conductorPacket Q a (n + h) - conductorPacket Q b n) ^ 2) =
      (∑ m ∈ Icc 1 Q, (m.totient : ℝ) * (b m - shiftProjection h a m) ^ 2) +
        ∑ m ∈ Icc 1 Q, shiftLeakageWeight m h * a m ^ 2 := by
  rw [packetMean_shift_error, ← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  unfold shiftProjection shiftLeakageWeight sieveLagMultiplier
  field_simp [hphi] <;> ring

/-- Every conductor approximation pays the exact transverse energy. -/
theorem packetMean_shift_error_ge_leakage (Q : ℕ) (a b : ℕ → ℝ) (h : ℕ) :
    (∑ m ∈ Icc 1 Q, shiftLeakageWeight m h * a m ^ 2) ≤
      packetMean Q (fun n => (conductorPacket Q a (n + h) - conductorPacket Q b n) ^ 2) := by
  rw [packetMean_shift_error_eq_projection_add_leakage]
  exact le_add_of_nonneg_left (sum_nonneg fun m _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

#print axioms packetMean_shift_error_eq_projection_add_leakage
#print axioms packetMean_shift_error_ge_leakage

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
