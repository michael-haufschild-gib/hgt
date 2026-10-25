import GaloisForLFunctions.BiarithmeticGeometry.WeightedBaseFiveDigits
import GaloisForLFunctions.ArithmeticOrientationTheory.LocalFactorsAreTheUnitsOfTheWienerMonoid

/-!
# The exact geometric-tower receiver

The inverse prime-five Euler factor has a geometric mean series. Its centered prefix obeys
the same Euclidean recursion as a weighted digit polynomial, giving equality at every horizon.
-/

noncomputable section
open Finset
open GaloisForLFunctions
open BezoutValuationIncidence TransHorizonIncidenceMechanics ArithmeticOrientationTheory

namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem fiveTower_off_support (a : ℝ) (n : ℕ)
    (hn : n ∉ Set.range (fun k : ℕ => 5 ^ k)) :
    localFactorInverse 5 a n / n = 0 := by
  rw [localFactorInverse_eq_zero a (fun k h => hn ⟨k, h.symm⟩), zero_div]

/-- The convergent mean of a prime-five geometric source. -/
theorem hasSum_fiveTower_div (a : ℝ) (ha : |a| < 5) :
    HasSum (fun n : ℕ => localFactorInverse 5 a n / n) (5 / (5 - a)) := by
  rw [← (Nat.pow_right_injective (by omega : 2 ≤ 5)).hasSum_iff
    (fun n hn => fiveTower_off_support a n hn)]
  have he : ((fun n : ℕ => localFactorInverse 5 a n / n) ∘ (fun k : ℕ => 5 ^ k)) =
      fun k : ℕ => (a / 5) ^ k := by
    funext k
    simp only [Function.comp_apply, localFactorInverse_pow (by omega : 1 < 5),
      Nat.cast_pow, Nat.cast_ofNat, div_pow]
  rw [he]
  have hr : |a / 5| < 1 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]; linarith
  have hden : 5 - a ≠ 0 := by have := le_abs_self a; linarith
  convert hasSum_geometric_of_abs_lt_one hr using 1
  field_simp [hden]

theorem summable_abs_fiveTower_div (a : ℝ) (ha : |a| < 5) :
    Summable (fun n : ℕ => |localFactorInverse 5 a n / n|) := by
  have h := (hasSum_fiveTower_div |a| (by rwa [abs_abs])).summable
  apply h.congr
  intro n
  by_cases hn : ∃ k, n = 5 ^ k
  · obtain ⟨k, rfl⟩ := hn
    rw [localFactorInverse_pow (by omega : 1 < 5),
      localFactorInverse_pow (by omega : 1 < 5), abs_div, abs_pow, Nat.abs_cast]
  · have hz : ∀ k, n ≠ 5 ^ k := fun k h => hn ⟨k, h⟩
    rw [localFactorInverse_eq_zero _ hz, localFactorInverse_eq_zero _ hz,
      zero_div, abs_zero]

private theorem fiveTower_local_factor (a : ℝ) :
    localFactorWeight (localFactorInverse 5 a) 5 a = unitKernel := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [localFactorWeight, localFactorInverse, unitKernel]
  · exact (dirichletConv_localFactorKernel (by norm_num : Nat.Prime 5) a _ hn).symm.trans
      (dirichletConv_localFactor_inverse (by norm_num : Nat.Prime 5) a hn)

private theorem unitKernel_centeredPrefix (n : ℕ) : weightCenteredPrefix unitKernel 1 n = 0 := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
  simp only [unitKernel, ite_mul, one_mul, zero_mul, sum_ite_eq', Nat.div_one]
  by_cases hn : 1 ≤ n
  · rw [if_pos (mem_Icc.mpr ⟨le_rfl, hn⟩), sub_self]
  · have hn0 : n = 0 := by omega
    subst n
    simp

/-- The explicit-mean centered prefix obeys the exact base-five digit recurrence. -/
theorem fiveTower_centeredPrefix_rec (a : ℝ) (ha : a ≠ 5) (n : ℕ) :
    weightCenteredPrefix (localFactorInverse 5 a) (5 / (5 - a)) n =
      a * weightCenteredPrefix (localFactorInverse 5 a) (5 / (5 - a)) (n / 5) -
        a / (5 - a) * (n % 5 : ℕ) := by
  have hm : (5 / (5 - a) : ℝ) - a * ((5 / (5 - a)) / 5) = 1 := by
    field_simp [sub_ne_zero.mpr (Ne.symm ha)]
  have h := weightCenteredPrefix_localFactorWeight (localFactorInverse 5 a)
    (5 / (5 - a)) (by omega : 1 ≤ 5) a n
  rw [fiveTower_local_factor] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hm, unitKernel_centeredPrefix] at h
  have hdiv : (n % 5 : ℕ) + (5 : ℝ) * (n / 5 : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n 5
  have hf : (n : ℝ) / 5 - (n / 5 : ℕ) = (n % 5 : ℕ) / 5 := by linarith only [hdiv]
  rw [hf] at h
  have he : a * (5 / (5 - a)) * ((n % 5 : ℕ) / 5) = a / (5 - a) * (n % 5 : ℕ) := by ring
  rw [he] at h
  linarith only [h]

/-- The geometric source receiver is exactly a weighted digit row. -/
theorem fiveTower_centeredPrefix_eq_digitRow (a : ℝ) (ha : a ≠ 5) (n : ℕ) :
    weightCenteredPrefix (localFactorInverse 5 a) (5 / (5 - a)) n =
      -(a / (5 - a)) * fiveDigitRow a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [weightCenteredPrefix_zero, fiveDigitRow_zero, mul_zero]
    · rw [fiveTower_centeredPrefix_rec a ha,
        ih (n / 5) (by omega), fiveDigitRow_rec a n]
      ring

/-- At every absolutely summable damping the explicit mean is the actual source mean. -/
theorem fiveTower_actualPrefix_eq_digitRow (a : ℝ) (ha : |a| < 5) (n : ℕ) :
    weightCenteredPrefix (localFactorInverse 5 a)
      (∑' d : ℕ, localFactorInverse 5 a d / d) n =
        -(a / (5 - a)) * fiveDigitRow a n := by
  rw [(hasSum_fiveTower_div a ha).tsum_eq]
  exact fiveTower_centeredPrefix_eq_digitRow a (by have := le_abs_self a; linarith) n

end GaloisForLFunctions.BiarithmeticGeometry
