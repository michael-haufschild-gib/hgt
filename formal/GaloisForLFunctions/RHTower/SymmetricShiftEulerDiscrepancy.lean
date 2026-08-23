import GaloisForLFunctions.RHTower.SymmetricShiftPrimeEulerAbscissa

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A strictly positive real symmetric-shift parameter, represented in data rather than as a premise. -/
abbrev SymmetricPositiveShift := {a : ℝ // 0 < a}

/-- The first-prime logarithmic Euler discrepancy of the symmetric shift. -/
def symmetricShiftEulerPrimeDiscrepancy (a : SymmetricPositiveShift) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ a.1 + (p : ℝ) ^ (-a.1) - 2

/-- The first-prime discrepancy is a positive square divided by the dominant branch. -/
theorem symmetricShiftEulerPrimeDiscrepancy_eq_sq_div
    (a : SymmetricPositiveShift) (p : Nat.Primes) :
    symmetricShiftEulerPrimeDiscrepancy a p =
      (((p : ℝ) ^ a.1 - 1) ^ 2) / ((p : ℝ) ^ a.1) := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast p.property.pos
  unfold symmetricShiftEulerPrimeDiscrepancy
  rw [Real.rpow_neg hp.le]
  field_simp [Real.rpow_pos_of_pos hp a.1]
  ring

/-- The first-prime symmetric-shift discrepancy is nonnegative. -/
theorem symmetricShiftEulerPrimeDiscrepancy_nonneg
    (a : SymmetricPositiveShift) (p : Nat.Primes) :
    0 ≤ symmetricShiftEulerPrimeDiscrepancy a p := by
  rw [symmetricShiftEulerPrimeDiscrepancy_eq_sq_div]
  exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)

/-- The discrepancy never exceeds its dominant `p^a` branch. -/
theorem symmetricShiftEulerPrimeDiscrepancy_le_dominant
    (a : SymmetricPositiveShift) (p : Nat.Primes) :
    symmetricShiftEulerPrimeDiscrepancy a p ≤ (p : ℝ) ^ a.1 := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast p.property.pos
  have hpone : (1 : ℝ) ≤ p := by
    exact_mod_cast p.property.one_le
  have hmain : 1 ≤ (p : ℝ) ^ a.1 := Real.one_le_rpow hpone a.2.le
  have hrecip : (p : ℝ) ^ (-a.1) ≤ 1 := by
    rw [Real.rpow_neg hp.le]
    exact (inv_le_one₀ (Real.rpow_pos_of_pos hp _)).mpr hmain
  unfold symmetricShiftEulerPrimeDiscrepancy
  linarith

/-- The first-prime discrepancy dominates a fixed positive multiple of `p^a`. -/
theorem symmetricShiftEulerPrimeDiscrepancy_ge_scaled_dominant
    (a : SymmetricPositiveShift) (p : Nat.Primes) :
    (1 - (2 : ℝ) ^ (-a.1)) ^ 2 * (p : ℝ) ^ a.1 ≤
      symmetricShiftEulerPrimeDiscrepancy a p := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast p.property.pos
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast p.property.two_le
  have htail : (p : ℝ) ^ (-a.1) ≤ (2 : ℝ) ^ (-a.1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith [a.2])
  have htwo : (2 : ℝ) ^ (-a.1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [a.2])
  have hleft : 0 ≤ 1 - (2 : ℝ) ^ (-a.1) := by linarith
  have hright : 1 - (2 : ℝ) ^ (-a.1) ≤ 1 - (p : ℝ) ^ (-a.1) := by linarith
  have hsquares : (1 - (2 : ℝ) ^ (-a.1)) ^ 2 ≤
      (1 - (p : ℝ) ^ (-a.1)) ^ 2 := by
    rw [sq_le_sq₀ hleft (by linarith)]
    exact hright
  have hident : symmetricShiftEulerPrimeDiscrepancy a p =
      (p : ℝ) ^ a.1 * (1 - (p : ℝ) ^ (-a.1)) ^ 2 := by
    unfold symmetricShiftEulerPrimeDiscrepancy
    rw [Real.rpow_neg hp.le]
    field_simp [Real.rpow_pos_of_pos hp _]
    ring
  calc
    (1 - (2 : ℝ) ^ (-a.1)) ^ 2 * (p : ℝ) ^ a.1 =
        (p : ℝ) ^ a.1 * (1 - (2 : ℝ) ^ (-a.1)) ^ 2 := by ring
    _ ≤ (p : ℝ) ^ a.1 * (1 - (p : ℝ) ^ (-a.1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquares (Real.rpow_nonneg hp.le _)
    _ = symmetricShiftEulerPrimeDiscrepancy a p := hident.symm

/-- The positive first-prime discrepancy weighted at real abscissa `σ`. -/
def symmetricShiftEulerPrimeDiscrepancyTerm
    (a : SymmetricPositiveShift) (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  symmetricShiftEulerPrimeDiscrepancy a p * (p : ℝ) ^ (-sigma)

/-- The weighted first-prime discrepancy is nonnegative. -/
theorem symmetricShiftEulerPrimeDiscrepancyTerm_nonneg
    (a : SymmetricPositiveShift) (sigma : ℝ) (p : Nat.Primes) :
    0 ≤ symmetricShiftEulerPrimeDiscrepancyTerm a sigma p := by
  unfold symmetricShiftEulerPrimeDiscrepancyTerm
  exact mul_nonneg (symmetricShiftEulerPrimeDiscrepancy_nonneg a p)
    (Real.rpow_nonneg (by positivity) _)

/-- Absolute summability wall of a real `p^{a-σ}` prime branch. -/
theorem summable_symmetricShiftEulerPrimeBranch_real_iff
    (a sigma : ℝ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (a - sigma)) ↔ 1 + a < sigma := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- The full first-prime symmetric-shift discrepancy has exact abscissa `1+a`. -/
theorem summable_symmetricShiftEulerPrimeDiscrepancyTerm_iff
    (a : SymmetricPositiveShift) (sigma : ℝ) :
    Summable (fun p : Nat.Primes => symmetricShiftEulerPrimeDiscrepancyTerm a sigma p) ↔
      1 + a.1 < sigma := by
  let C : ℝ := (1 - (2 : ℝ) ^ (-a.1)) ^ 2
  have hCpos : 0 < C := by
    have htwo : (2 : ℝ) ^ (-a.1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [a.2])
    exact sq_pos_of_pos (sub_pos.mpr htwo)
  have hbranch_eq (p : Nat.Primes) :
      (p : ℝ) ^ (a.1 - sigma) = (p : ℝ) ^ a.1 * (p : ℝ) ^ (-sigma) := by
    rw [← Real.rpow_add (by exact_mod_cast p.property.pos)]
    congr 1
  constructor
  · intro hsum
    have hscaled : Summable (fun p : Nat.Primes => C * (p : ℝ) ^ (a.1 - sigma)) := by
      refine Summable.of_nonneg_of_le
        (fun p => mul_nonneg hCpos.le (Real.rpow_nonneg (by positivity) _)) ?_ hsum
      intro p
      rw [hbranch_eq]
      unfold symmetricShiftEulerPrimeDiscrepancyTerm
      simpa [C, mul_assoc] using
        mul_le_mul_of_nonneg_right
          (symmetricShiftEulerPrimeDiscrepancy_ge_scaled_dominant a p)
          (Real.rpow_nonneg (by positivity) _)
    have hbranch : Summable (fun p : Nat.Primes => (p : ℝ) ^ (a.1 - sigma)) := by
      have hdiv := hscaled.div_const C
      refine hdiv.congr fun p => ?_
      field_simp [hCpos.ne']
    exact (summable_symmetricShiftEulerPrimeBranch_real_iff a.1 sigma).mp hbranch
  · intro hsigma
    have hbranch :=
      (summable_symmetricShiftEulerPrimeBranch_real_iff a.1 sigma).mpr hsigma
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hbranch
    · exact symmetricShiftEulerPrimeDiscrepancyTerm_nonneg a sigma p
    · unfold symmetricShiftEulerPrimeDiscrepancyTerm
      rw [hbranch_eq]
      exact mul_le_mul_of_nonneg_right
        (symmetricShiftEulerPrimeDiscrepancy_le_dominant a p)
        (Real.rpow_nonneg (by positivity) _)

end

end GaloisForLFunctions.RHTower
