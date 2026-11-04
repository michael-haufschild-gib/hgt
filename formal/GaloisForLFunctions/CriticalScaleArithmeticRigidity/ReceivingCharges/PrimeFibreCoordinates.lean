import GaloisForLFunctions.CriticalScaleArithmeticRigidity.FibreChargesSurviveVanishingEnergy

/-!
# Exact simultaneous receiving coordinates

Prime fibres coprime to a common multiple of the receiving conductors have
an exactly diagonal receiving map. Coprime period factorization removes
every nonconstant prime row, leaving the period Gram of the base modes.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory SuccessorShellArithmetic
  ArithmeticIntersectionTheory BezoutValuationIncidence

/-- Complete-period pairing of normalized conductor modes is their Kronecker Gram. -/
theorem packetMean_normalizedMode_mul {m l R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmR : m ≤ R) (hlR : l ≤ R) :
    packetMean R (fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n) =
      if m = l then 1 else 0 := by
  have hgram := sum_range_ramanujanLagCoefficient_mul hm hl
    (Nat.dvd_factorial hm hmR) (Nat.dvd_factorial hl hlR)
  simp only [packetMean, normalizedRamanujanMode_eq_coefficient hm,
    normalizedRamanujanMode_eq_coefficient hl, div_mul_div_comm, ← sum_div, hgram]
  split_ifs with hml
  · subst l
    have hphi : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
    have hfac : (R.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero R
    rw [← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    field_simp [hphi, hfac]
  · rw [zero_div, zero_div]

private theorem mode_period_of_dvd {m M : ℕ} (hm : 0 < m) (hmM : m ∣ M) :
    Function.Periodic (normalizedRamanujanMode m) M := by
  obtain ⟨k, rfl⟩ := hmM
  simpa only [Nat.cast_id, Nat.mul_comm] using (normalizedRamanujanMode_periodic hm).nat_mul k

private theorem source_period_of_dvd {m M : ℕ} (hm : 0 < m) (hmM : m ∣ M) :
    Function.Periodic (normalizedPrimeModeSource m) M := by
  obtain ⟨k, rfl⟩ := hmM
  simpa only [Nat.cast_id, Nat.mul_comm] using (normalizedPrimeModeSource_periodic hm).nat_mul k

private theorem prime_mode_period_sum_zero {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ range p, normalizedRamanujanMode p n) = 0 := by
  have h := sum_range_ramanujanLagCoefficient_mul hp.pos (by omega : 0 < 1)
    (dvd_refl p) (one_dvd p)
  have h1 (n : ℕ) : ramanujanLagCoefficient 1 n = 1 := by
    simpa only [Nat.totient_one, Nat.cast_one] using
      ramanujanLagCoefficient_of_dvd (one_dvd n)
  simp only [h1, mul_one, if_neg hp.ne_one] at h
  simp only [normalizedRamanujanMode_eq_coefficient hp.pos, ← sum_div, h, zero_div]

private theorem prime_source_formula {p : ℕ} (hp : p.Prime) (n : ℕ) :
    normalizedPrimeModeSource p n =
      Real.log p / Real.sqrt (p.totient : ℝ) - tameDifferent p * normalizedRamanujanMode p n := by
  rw [normalizedPrimeModeSource, ramanujanDivisorJet_prime hp,
    normalizedRamanujanMode_eq_coefficient hp.pos]
  ring

/-- A prime coprime to all base conductors transfers charge only to its own base mode. -/
theorem prime_fibre_receiving_coordinate {M m l p R : ℕ}
    (hM : 0 < M) (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M)
    (hp : p.Prime) (hpM : ¬ p ∣ M) (hR : M * p ≤ R) :
    packetMean R (fun n =>
      primePoleWitness p * normalizedPrimeModeSource (m * p) n * normalizedRamanujanMode l n) =
      (if m = l then 1 else 0) * (Real.log p / p) := by
  have hMp : M.Coprime p := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpM)
  have hmp : m.Coprime p := Nat.coprime_comm.mp
    (hp.coprime_iff_not_dvd.mpr (fun h => hpM (h.trans hmM)))
  have hMR : M ≤ R := (Nat.le_mul_of_pos_right M hp.pos).trans hR
  have hmR := (Nat.le_of_dvd hM hmM).trans hMR
  have hlR := (Nat.le_of_dvd hM hlM).trans hMR
  let F := fun n => normalizedPrimeModeSource m n * normalizedRamanujanMode l n -
    tameDifferent p * (normalizedRamanujanMode m n * normalizedRamanujanMode l n)
  have hF : Function.Periodic F M := by
    intro n
    dsimp only [F]
    rw [source_period_of_dvd hm hmM n, mode_period_of_dvd hl hlM n,
      mode_period_of_dvd hm hmM n]
  have hzero := packetMean_mul_eq_zero_of_coprime hM hp.pos hMp
    (Nat.dvd_factorial (Nat.mul_pos hM hp.pos) hR) hF
    (normalizedRamanujanMode_periodic hp.pos) (prime_mode_period_sum_zero hp)
  have hpoint (n : ℕ) :
      normalizedPrimeModeSource (m * p) n * normalizedRamanujanMode l n =
        (Real.log p / Real.sqrt (p.totient : ℝ)) *
          (normalizedRamanujanMode m n * normalizedRamanujanMode l n) +
        F n * normalizedRamanujanMode p n := by
    rw [normalizedPrimeModeSource_mul_of_coprime hm hp.pos hmp, prime_source_formula hp]
    dsimp only [F]
    ring
  simp only [mul_assoc, hpoint, packetMean_const_mul, packetMean_add, hzero,
    add_zero, packetMean_normalizedMode_mul hm hl hmR hlR]
  have hs : Real.sqrt (p.totient : ℝ) ≠ 0 := (sqrt_totient_prime_pos hp).ne'
  rw [primePoleWitness]
  field_simp [hs]

/-- Incidence weights placed on one conductor fibre inside a common cutoff. -/
def primeFibreIncidenceCoefficients (P : Finset ℕ) (m : ℕ) (b : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ p ∈ P, if c = m * p then b p * primePoleWitness p else 0

/-- Every finite common-coprime prime fibre has an exactly diagonal receiving map. -/
theorem primeFibreIncidence_receiving_coordinates {M m l R : ℕ}
    (hM : 0 < M) (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M)
    (P : Finset ℕ) (b : ℕ → ℝ) (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ M ∧ M * p ≤ R) :
    packetMean R (fun n =>
      arithmeticPrimeGenerator R (primeFibreIncidenceCoefficients P m b) n *
        normalizedRamanujanMode l n) =
      (if m = l then 1 else 0) * ∑ p ∈ P, b p * (Real.log p / p) := by
  have hmMle := Nat.le_of_dvd hM hmM
  have hpoint (n : ℕ) :
      arithmeticPrimeGenerator R (primeFibreIncidenceCoefficients P m b) n *
        normalizedRamanujanMode l n =
      ∑ p ∈ P, b p * (primePoleWitness p * normalizedPrimeModeSource (m * p) n *
        normalizedRamanujanMode l n) := by
    rw [arithmeticPrimeGenerator_eq_modeSource]
    simp only [primeFibreIncidenceCoefficients, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    have hmpR : m * p ∈ Icc 1 R := mem_Icc.mpr
      ⟨Nat.mul_pos hm (hP p hp).1.pos, (Nat.mul_le_mul_right p hmMle).trans (hP p hp).2.2⟩
    rw [sum_ite_eq', if_pos hmpR]
    ring
  simp only [hpoint, packetMean_sum, packetMean_const_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [prime_fibre_receiving_coordinate hM hm hl hmM hlM (hP p hp).1
    (hP p hp).2.1 (hP p hp).2.2]
  ring

#print axioms packetMean_normalizedMode_mul
#print axioms prime_fibre_receiving_coordinate
#print axioms primeFibreIncidence_receiving_coordinates

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
