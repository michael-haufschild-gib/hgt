import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTail
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeTailPairing

/-!
# Deleting fixed conductor primes preserves the receiving ramp

The omitted prime towers are supported on divisors of the fixed conductor.
Each has remaining mass at most one, so their total cost is bounded
independently of the prime cutoff, quotient and receiving row.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

/-- Coprime restriction is a literal restriction of prime incidence coefficients. -/
theorem fibreRestrict_fibreCharge_eq_incidence (m Q : ℕ) (t : ℝ) :
    fibreRestrict m (fibreCharge m Q t) =
      primeIncidenceCoefficients (fun p => if p ∣ m then 0 else t / fibreScale m Q) := by
  funext p
  by_cases hp : p.Prime <;> by_cases hd : p ∣ m <;>
    simp only [fibreRestrict, fibreCharge, primeIncidenceCoefficients, primeOnly,
      hp, hd, not_true_eq_false, not_false_eq_true, and_true, and_false,
      if_true, if_false, zero_mul, mul_comm]

/-- The removed towers have at most one unit of mass per divisor of the base conductor. -/
theorem abs_fibreTail_sub_coherent_le {m : ℕ} (hm : 0 < m)
    (Q Y n : ℕ) (t : ℝ) :
    |completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n -
      completedPrimeDilationTail Q
        (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) Y n| ≤
      |t / fibreScale m Q| * (m : ℝ) := by
  let P := (Icc 1 Q).filter Nat.Prime
  let bad := P.filter (fun p => p ∣ m)
  let D := ∑ p ∈ bad, if p ∣ n then (0 : ℝ) else primeTowerRemainder p Y
  have hD0 : 0 ≤ D := by
    apply sum_nonneg
    intro p hp
    split_ifs
    · exact le_rfl
    · exact primeTowerRemainder_nonneg (mem_filter.mp (mem_filter.mp hp).1).2 Y
  have hbad : bad ⊆ Icc 1 m := by
    intro p hp
    obtain ⟨hpP, hpm⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(mem_filter.mp hpP).2.pos, Nat.le_of_dvd hm hpm⟩
  have hDm : D ≤ (m : ℝ) := by
    calc
      _ ≤ ∑ p ∈ bad, (1 : ℝ) := sum_le_sum fun p hp => by
        split_ifs
        · exact zero_le_one
        · exact primeTowerRemainder_le_one (mem_filter.mp (mem_filter.mp hp).1).2 Y
      _ ≤ ∑ p ∈ Icc 1 m, (1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hbad (fun _ _ _ => zero_le_one)
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have he : completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n -
      completedPrimeDilationTail Q
        (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) Y n =
      -(t / fibreScale m Q) * D := by
    rw [fibreRestrict_fibreCharge_eq_incidence,
      completedPrimeDilationTail_primeIncidence_eq, completedPrimeDilationTail_primeIncidence_eq]
    dsimp only [D, bad]
    conv_rhs => rw [sum_filter]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hd : p ∣ m <;> by_cases hn : p ∣ n <;>
      simp only [hd, hn, if_true, if_false] <;> ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg hD0]
  exact mul_le_mul_of_nonneg_left hDm (abs_nonneg _)

/-- Every coprime fibre has the same receiving ramp, with a fixed additional error. -/
theorem abs_fibreTail_sub_ramp_le {m Q N n : ℕ}
    (hm : 0 < m) (hQ : 1 ≤ Q) (hn : 1 ≤ n) (hnN : n ≤ N) (t : ℝ) :
    |completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) (N / n) n -
      (t / fibreScale m Q) * max (Real.log Q + Real.log n - Real.log N) 0| ≤
      |t / fibreScale m Q| * (primeChargeRampErrorConstant + m +
        primeDivisorCount ((Icc 1 Q).filter Nat.Prime) n) := by
  have hd := abs_fibreTail_sub_coherent_le hm Q (N / n) n t
  have hr := abs_completedPrimeDilationTail_coherent_sub_ramp_le hQ hn hnN
    (t / fibreScale m Q)
  refine (abs_sub_le _
    (completedPrimeDilationTail Q
      (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) (N / n) n) _).trans
    ((add_le_add hd hr).trans_eq ?_)
  dsimp only [primeChargeRampErrorConstant, primeDivisorCount]
  ring

/-- Coprime deletion preserves a horizon-independent pointwise bound for the prime tail. -/
theorem abs_fibreTail_le_activity {m : ℕ} (hm : 0 < m) (Q Y n : ℕ) (t : ℝ) :
    |completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n| ≤
      |t / fibreScale m Q| * (primeActivityMass Q + m) := by
  have hd := abs_fibreTail_sub_coherent_le hm Q Y n t
  have hc := abs_completedPrimeDilationTail_coherent_le_activity Q Y n (t / fibreScale m Q)
  calc
    _ = |(completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n -
        completedPrimeDilationTail Q
          (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) Y n) +
        completedPrimeDilationTail Q
          (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) Y n| := by
      congr 1
      ring
    _ ≤ |completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n -
        completedPrimeDilationTail Q
          (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) Y n| +
        |completedPrimeDilationTail Q
          (primeIncidenceCoefficients (fun _ => t / fibreScale m Q)) Y n| :=
      abs_add_le _ _
    _ ≤ _ := (add_le_add hd hc).trans_eq (by ring)

#print axioms abs_fibreTail_sub_ramp_le
#print axioms abs_fibreTail_le_activity

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
