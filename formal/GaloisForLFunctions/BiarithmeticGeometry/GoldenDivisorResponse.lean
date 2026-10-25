import GaloisForLFunctions.BiarithmeticGeometry.GoldenArithmeticSource
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Divisors

/-!
# Exact ordinary divisor responses of the golden source

Only powers of five contribute to the inverse-zeta source. Its ordinary divisor
response therefore depends exactly on the five-adic valuation. The resulting
finite geometric profile decreases with both the valuation and the damping
parameter, and is bounded above by one.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The ordinary divisor response, with the natural convention at zero. -/
def goldenDivisorResponse (t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, goldenArithmeticSource t d

/-- The exact response at valuation `M`. The zeroth geometric difference vanishes. -/
def goldenDivisorProfile (t : ℝ) (M : ℕ) : ℝ :=
  1 - (1 / Real.sqrt 5) * ∑ r ∈ range (M + 1),
    ((goldenPrimaryRoot * t) ^ r - (goldenSecondaryRoot * t) ^ r)

private theorem fiveTower_divisor_sum (a : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, localFactorInverse 5 a d) =
      ∑ r ∈ range (padicValNat 5 n + 1), a ^ r := by
  let S := (range (padicValNat 5 n + 1)).image (fun r : ℕ => 5 ^ r)
  have hS : S ⊆ n.divisors := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨(Nat.pow_dvd_iff_le_padicValNat (by omega : 5 ≠ 1) hn).mpr
      (by have := mem_range.mp hr; omega), hn⟩
  have hsum : (∑ d ∈ n.divisors, localFactorInverse 5 a d) =
      ∑ d ∈ S, localFactorInverse 5 a d := by
    symm
    apply sum_subset hS
    intro d hd hdS
    apply localFactorInverse_eq_zero
    intro r hr
    have hdiv : 5 ^ r ∣ n := by rw [← hr]; exact (Nat.mem_divisors.mp hd).1
    have hrM := (Nat.pow_dvd_iff_le_padicValNat (by omega : 5 ≠ 1) hn).mp hdiv
    exact hdS (mem_image.mpr ⟨r, mem_range.mpr (by omega), hr.symm⟩)
  rw [hsum]
  dsimp only [S]
  rw [sum_image (fun r _ s _ h => Nat.pow_right_injective (by omega : 2 ≤ 5) h)]
  apply sum_congr rfl
  intro r _
  exact localFactorInverse_pow (by omega : 1 < 5) a r

/-- The source's actual divisor response depends exactly on its five-adic valuation. -/
theorem goldenDivisorResponse_eq_profile (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    goldenDivisorResponse t n = goldenDivisorProfile t (padicValNat 5 n) := by
  have hu : (∑ d ∈ n.divisors, unitKernel d) = (1 : ℝ) := by
    simp [unitKernel, hn]
  unfold goldenDivisorResponse goldenDivisorProfile
  simp_rw [goldenArithmeticSource_eq_towers]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hu,
    fiveTower_divisor_sum _ n hn, fiveTower_divisor_sum _ n hn, sum_sub_distrib]
  ring

/-- Every finite profile value occurs at an actual positive integer. -/
theorem goldenDivisorResponse_pow (t : ℝ) (M : ℕ) :
    goldenDivisorResponse t (5 ^ M) = goldenDivisorProfile t M := by
  unfold goldenDivisorResponse goldenDivisorProfile
  rw [Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 5)]
  simp_rw [goldenArithmeticSource_eq_towers,
    localFactorInverse_pow (by omega : 1 < 5)]
  have hu : (∑ r ∈ range (M + 1), unitKernel (5 ^ r)) = (1 : ℝ) := by
    have he (r : ℕ) : unitKernel (5 ^ r) = if r = 0 then 1 else 0 := by
      by_cases hr : r = 0
      · simp [hr, unitKernel]
      · simp [unitKernel, hr]
    simp_rw [he]
    simp
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hu, sum_sub_distrib]
  ring

private theorem golden_roots_order : goldenSecondaryRoot ≤ goldenPrimaryRoot := by
  have hs := Real.sqrt_nonneg (5 : ℝ)
  linarith only [golden_roots_sub, hs]

private theorem golden_power_difference_nonneg (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    0 ≤ (goldenPrimaryRoot * t) ^ r - (goldenSecondaryRoot * t) ^ r :=
  sub_nonneg.mpr (pow_le_pow_left₀ (mul_nonneg golden_root_bounds.2.2.1.le ht)
    (mul_le_mul_of_nonneg_right golden_roots_order ht) r)

theorem goldenDivisorProfile_zero (t : ℝ) : goldenDivisorProfile t 0 = 1 := by
  simp [goldenDivisorProfile]

/-- Each added five-power divisor subtracts a nonnegative coefficient. -/
theorem goldenDivisorProfile_antitone (t : ℝ) (ht : 0 ≤ t) :
    Antitone (goldenDivisorProfile t) := by
  apply antitone_nat_of_succ_le
  intro M
  rw [goldenDivisorProfile, goldenDivisorProfile, Finset.sum_range_succ]
  have h := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 5)
    (golden_power_difference_nonneg t ht (M + 1))
  linarith only [h]

/-- Increasing the damping parameter decreases every finite divisor profile. -/
theorem goldenDivisorProfile_parameter_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (M : ℕ) : goldenDivisorProfile t M ≤ goldenDivisorProfile s M := by
  apply sub_le_sub_left
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 5)
  apply sum_le_sum
  intro r _
  have hdiff : 0 ≤ goldenPrimaryRoot ^ r - goldenSecondaryRoot ^ r :=
    sub_nonneg.mpr (pow_le_pow_left₀ golden_root_bounds.2.2.1.le golden_roots_order r)
  have hpow := pow_le_pow_left₀ hs hst r
  simpa only [mul_pow, sub_mul] using mul_le_mul_of_nonneg_left hpow hdiff

/-- Every ordinary divisor response is at most one throughout the nonnegative parameter range. -/
theorem goldenDivisorResponse_le_one (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    goldenDivisorResponse t n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [goldenDivisorResponse]
  · rw [goldenDivisorResponse_eq_profile t n hn,
      ← goldenDivisorProfile_zero t]
    exact goldenDivisorProfile_antitone t ht (Nat.zero_le _)

end GaloisForLFunctions.BiarithmeticGeometry
