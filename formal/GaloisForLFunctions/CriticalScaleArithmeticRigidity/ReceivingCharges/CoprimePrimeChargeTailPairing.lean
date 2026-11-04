import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTailMass
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeLogWindows
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeScales

/-!
# Signed prime-tail pairings in fixed conductor fibres

The tower error costs only the first harmonic incidence moment against a
bounded terminal contrast. Fixed conductor factors preserve that estimate;
the ramp's conductor-product discrepancy costs one cutoff logarithm.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

/-- A bounded contrast tests a pointwise incidence error through its first harmonic moment. -/
theorem abs_primeChargeWindow_pairing_of_incidence_bound {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hN : 1 ≤ N)
    (A B C : ℕ) (F : ℕ → ℝ) {D E : ℝ} (hD : 0 ≤ D)
    (hF : ∀ n ∈ Icc 1 N, |F n| ≤ D * (E + primeDivisorCount P n)) :
    |∑ n ∈ Icc 1 N, F n * primeChargeWindowContrast A B C n / (n : ℝ)| ≤
      D * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) * harmonicMass N *
        (E + ∑ p ∈ P, 1 / (p : ℝ)) := by
  let M := 1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      |F n * primeChargeWindowContrast A B C n / (n : ℝ)| ≤
        (D * M) * ((E + primeDivisorCount P n) / (n : ℝ)) := by
    rw [abs_div, abs_mul, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul (hF n hn) (abs_primeChargeWindowContrast_le A B C n)
        (abs_nonneg _) ((abs_nonneg _).trans (hF n hn))) (Nat.cast_nonneg n)).trans_eq (by ring)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |F n * primeChargeWindowContrast A B C n / (n : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ (D * M) * ∑ n ∈ Icc 1 N, (E + primeDivisorCount P n) / (n : ℝ) := by
      rw [mul_sum]
      exact sum_le_sum hpoint
    _ = (D * M) * (E * harmonicMass N + ∑ n ∈ Icc 1 N, primeDivisorCount P n / (n : ℝ)) := by
      simp only [add_div, sum_add_distrib, harmonicMass, mul_sum, mul_one_div]
    _ ≤ (D * M) * (E * harmonicMass N + harmonicMass N * ∑ p ∈ P, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (primeDivisorCount_harmonic_first_moment_le hP hN)) (mul_nonneg hD hM)
    _ = _ := by dsimp only [M]; ring

/-- Both fixed conductor factors preserve the first-moment tower-error bound. -/
theorem abs_fibreTail_mode_window_sub_ramp_le {m l Q N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (A B C : ℕ) (t : ℝ) :
    |(∑ n ∈ Icc 1 N,
        completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) (N / n) n *
          normalizedRamanujanMode m n * normalizedRamanujanMode l n *
            primeChargeWindowContrast A B C n / (n : ℝ)) -
      (t / fibreScale m Q) * ∑ n ∈ Icc 1 N,
        max (Real.log Q + Real.log n - Real.log N) 0 *
          normalizedRamanujanMode m n * normalizedRamanujanMode l n *
            primeChargeWindowContrast A B C n / (n : ℝ)| ≤
      (|t / fibreScale m Q| * modeBound m * modeBound l) *
        (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) * harmonicMass N *
          (primeChargeRampErrorConstant + m +
            ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  let F (n : ℕ) :=
    (completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) (N / n) n -
      (t / fibreScale m Q) * max (Real.log Q + Real.log n - Real.log N) 0) *
        normalizedRamanujanMode m n * normalizedRamanujanMode l n
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      |F n| ≤ (|t / fibreScale m Q| * modeBound m * modeBound l) *
        (primeChargeRampErrorConstant + m + primeDivisorCount ((Icc 1 Q).filter Nat.Prime) n) := by
    have htail := abs_fibreTail_sub_ramp_le hm hQ (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 t
    have hmabs := abs_le_periodSum hm (normalizedRamanujanMode_periodic hm) n
    have hlabs := abs_le_periodSum hl (normalizedRamanujanMode_periodic hl) n
    rw [F, abs_mul, abs_mul]
    exact (mul_le_mul
      (mul_le_mul htail hmabs (abs_nonneg _) ((abs_nonneg _).trans htail)) hlabs
      (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans htail) (modeBound_pos hm).le)).trans_eq
        (by ring)
  have h := abs_primeChargeWindow_pairing_of_incidence_bound
    (fun p hp => (mem_filter.mp hp).2) hN A B C F
    (mul_nonneg (mul_nonneg (abs_nonneg _) (modeBound_pos hm).le) (modeBound_pos hl).le) hpoint
  have he : (∑ n ∈ Icc 1 N, F n * primeChargeWindowContrast A B C n / (n : ℝ)) =
      (∑ n ∈ Icc 1 N,
        completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) (N / n) n *
          normalizedRamanujanMode m n * normalizedRamanujanMode l n *
            primeChargeWindowContrast A B C n / (n : ℝ)) -
      (t / fibreScale m Q) * ∑ n ∈ Icc 1 N,
        max (Real.log Q + Real.log n - Real.log N) 0 *
          normalizedRamanujanMode m n * normalizedRamanujanMode l n *
            primeChargeWindowContrast A B C n / (n : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by dsimp only [F]; ring
  rwa [he] at h

/-- Fixed excluded primes do not change the vanishing normalized first incidence moment. -/
theorem tendsto_fibreReciprocal_add_div_scale {m : ℕ} (hm : 0 < m) (C : ℝ) :
    Tendsto (fun Q : ℕ =>
      (C + ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) / fibreScale m Q)
      atTop (𝓝 0) := by
  have h := (tendsto_primeReciprocal_add_div_primePoleScale C).mul
    (tendsto_primePoleScale_div_fibreScale hm)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  change ((C + ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) / primePoleScale Q) *
    (primePoleScale Q / fibreScale m Q) = _
  field_simp [(primePoleScale_pos hQ).ne']

#print axioms abs_fibreTail_mode_window_sub_ramp_le
#print axioms tendsto_fibreReciprocal_add_div_scale

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
