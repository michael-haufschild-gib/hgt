import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3Coefficient
import GaloisForLFunctions.RHTower.Sieve.PrimeDivisorWeightedMean

/-!
# Literal Matomäki--Teräväinen `c₂,n` endpoint coefficient

The source's `c₂,n` is the difference between upper- and lower-end prime blocks created when the
adic block family is aligned with `[z₀,z₁)`.  This file retains both finite prime families and the
actual sifting level attached to each prime.  Its weighted mean is reduced to reciprocal mass of
the two endpoint families; no bounded-coefficient or divisor multiplicity is suppressed.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- One endpoint contribution with the source's unrestricted divisor variable. -/
def mtC2BoundaryCoefficient
    (α : ℕ → ℂ) (S : Finset ℕ) (level : ℕ → ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ S, if q ∣ n then
    ∑ m ∈ (n / q).divisors, α m * (rho ((n / q) / m) (level q) : ℂ)
  else 0

/-- Literal endpoint discrepancy: upper spill minus lower spill. -/
def mtC2Coefficient
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ)
    (level : ℕ → ℕ) (n : ℕ) : ℂ :=
  mtC2BoundaryCoefficient α upperSpill level n -
    mtC2BoundaryCoefficient α lowerSpill level n

/-- One endpoint coefficient is bounded by divisor multiplicity times its prime-divisor count. -/
theorem norm_mtC2BoundaryCoefficient_le
    (α : ℕ → ℂ) (S : Finset ℕ) (level : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC2BoundaryCoefficient α S level n‖ ≤
      B * (n.divisors.card : ℝ) * primeDivisorCount S n := by
  unfold mtC2BoundaryCoefficient primeDivisorCount
  calc
    ‖∑ q ∈ S, if q ∣ n then
        ∑ m ∈ (n / q).divisors, α m * (rho ((n / q) / m) (level q) : ℂ)
      else 0‖ ≤
        ∑ q ∈ S, ‖if q ∣ n then
          ∑ m ∈ (n / q).divisors, α m * (rho ((n / q) / m) (level q) : ℂ)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, if q ∣ n then B * (n.divisors.card : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hqn
      · have hNdiv : n / q ∣ n := by
          refine ⟨q, ?_⟩
          exact (Nat.div_mul_cancel hqn).symm
        have hcard : ((n / q).divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
          exact_mod_cast card_divisors_mono_of_dvd hNdiv hn.ne'
        calc
          ‖∑ m ∈ (n / q).divisors,
              α m * (rho ((n / q) / m) (level q) : ℂ)‖ ≤
              ∑ m ∈ (n / q).divisors,
                ‖α m * (rho ((n / q) / m) (level q) : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ _m ∈ (n / q).divisors, B := by
            apply Finset.sum_le_sum
            intro m hm
            rw [norm_mul]
            have hrho : ‖(rho ((n / q) / m) (level q) : ℂ)‖ ≤ 1 := by
              exact_mod_cast rho_le_one ((n / q) / m) (level q)
            simpa using (mul_le_mul (hα m) hrho (norm_nonneg _) hB)
          _ = B * ((n / q).divisors.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
          _ ≤ B * (n.divisors.card : ℝ) := mul_le_mul_of_nonneg_left hcard hB
      · simp
    _ = B * (n.divisors.card : ℝ) *
        (∑ q ∈ S, if q ∣ n then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> ring

/-- Both source endpoint families, with their signs forgotten only after the exact definition. -/
theorem norm_mtC2Coefficient_le
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      B * (n.divisors.card : ℝ) *
        (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by
  unfold mtC2Coefficient
  calc
    ‖mtC2BoundaryCoefficient α upperSpill level n -
        mtC2BoundaryCoefficient α lowerSpill level n‖ ≤
      ‖mtC2BoundaryCoefficient α upperSpill level n‖ +
        ‖mtC2BoundaryCoefficient α lowerSpill level n‖ := norm_sub_le _ _
    _ ≤ B * (n.divisors.card : ℝ) * primeDivisorCount upperSpill n +
        B * (n.divisors.card : ℝ) * primeDivisorCount lowerSpill n := by
      gcongr
      · exact norm_mtC2BoundaryCoefficient_le α upperSpill level hn hB hα
      · exact norm_mtC2BoundaryCoefficient_le α lowerSpill level hn hB hα
    _ = B * (n.divisors.card : ℝ) *
        (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by ring

/-- Pointwise source weight is controlled by the cube-weighted endpoint prime count. -/
theorem ternaryDivisorCount_mul_norm_mtC2Coefficient_le
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    (ternaryDivisorCount n : ℝ) *
        ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      B * ((n.divisors.card : ℝ) ^ 3) *
        (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hc := norm_mtC2Coefficient_le α lowerSpill upperSpill level hn hB hα
  have hcountLower : 0 ≤ primeDivisorCount lowerSpill n := by
    unfold primeDivisorCount
    positivity
  have hcountUpper : 0 ≤ primeDivisorCount upperSpill n := by
    unfold primeDivisorCount
    positivity
  have hd : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
  calc
    (ternaryDivisorCount n : ℝ) *
        ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      ((n.divisors.card : ℝ) ^ 2) *
        (B * (n.divisors.card : ℝ) *
          (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n)) := by
      exact mul_le_mul hd3 hc (norm_nonneg _) (by positivity)
    _ = B * ((n.divisors.card : ℝ) ^ 3) *
        (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by ring

/-- Weighted mean bound with both endpoint reciprocal masses explicit. -/
theorem sum_ternaryDivisorCount_mul_norm_mtC2Coefficient_le
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    (Y : ℕ) (hY : 1 ≤ Y)
    (hlowerPrime : ∀ q ∈ lowerSpill, q.Prime)
    (hupperPrime : ∀ q ∈ upperSpill, q.Prime)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      B * ((2 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          ((∑ q ∈ lowerSpill, 1 / (q : ℝ)) +
            ∑ q ∈ upperSpill, 1 / (q : ℝ))) := by
  have hlower := sum_weightedPrimeDivisorCount_le 3 Y hY lowerSpill hlowerPrime
  have hupper := sum_weightedPrimeDivisorCount_le 3 Y hY upperSpill hupperPrime
  have hB0 := hB
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      ∑ n ∈ Finset.Icc 1 Y,
        B * ((n.divisors.card : ℝ) ^ 3) *
          (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by
      apply Finset.sum_le_sum
      intro n hnMem
      exact ternaryDivisorCount_mul_norm_mtC2Coefficient_le
        α lowerSpill upperSpill level (by
          rw [Finset.mem_Icc] at hnMem
          omega) hB hα
    _ = B * (∑ n ∈ Finset.Icc 1 Y, weightedPrimeDivisorCount 3 lowerSpill n +
        ∑ n ∈ Finset.Icc 1 Y, weightedPrimeDivisorCount 3 upperSpill n) := by
      unfold weightedPrimeDivisorCount
      rw [← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ B * (((2 : ℝ) ^ 3 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
            ∑ q ∈ lowerSpill, 1 / (q : ℝ)) +
        ((2 : ℝ) ^ 3 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
            ∑ q ∈ upperSpill, 1 / (q : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hlower hupper) hB0
    _ = B * ((2 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          ((∑ q ∈ lowerSpill, 1 / (q : ℝ)) +
            ∑ q ∈ upperSpill, 1 / (q : ℝ))) := by ring

end

end RHTower.Sieve
