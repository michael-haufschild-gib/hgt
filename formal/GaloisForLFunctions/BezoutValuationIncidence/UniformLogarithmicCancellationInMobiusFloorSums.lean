import GaloisForLFunctions.BezoutValuationIncidence.HyperbolaCancellationWithDivisorBoundedCoefficients
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicCancellationInTheVaughanConvolution
import GaloisForLFunctions.BezoutValuationIncidence.FixedVaughanPacketsHaveTwoExplicitObstructions
import GaloisForLFunctions.BezoutValuationIncidence.TheBalancedStatisticIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate

/-!
The truncated Möbius floor sum has its harmonic mean with every logarithmic
saving, uniformly over the cutoff. Rounding controls short cutoffs; Möbius
inversion expresses the omitted tail through signed partial sums.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The undamped floor transform of a truncated Möbius sequence. -/
def pmUndampedMobiusFloorPrefix (U n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 U, moebiusReal d * ((n / d : ℕ) : ℝ)

/-- Rounding every floor gives the finite-cutoff error bound. -/
theorem abs_pmUndampedMobiusFloorPrefix_sub_mean_le (U n : ℕ) :
    |pmUndampedMobiusFloorPrefix U n - (n : ℝ) * deningerHarmonicPartial U| ≤ U := by
  rw [pmUndampedMobiusFloorPrefix, deningerHarmonicPartial_eq_sum_Icc, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 U, |moebiusReal d| *
        |((n / d : ℕ) : ℝ) - (n : ℝ) / d| := by
      refine (abs_sum_le_sum_abs _ _).trans_eq ?_
      apply sum_congr rfl
      intro d _
      rw [← abs_mul]
      congr 1
      unfold moebiusReal
      ring
    _ ≤ ∑ _d ∈ Icc 1 U, (1 : ℝ) := sum_le_sum fun d hd => by
      calc
        _ ≤ 1 * 1 := mul_le_mul (abs_moebiusReal_le_one' d)
          (abs_natDiv_sub_div_le n d (mem_Icc.mp hd).1) (abs_nonneg _) zero_le_one
        _ = _ := mul_one _
    _ = _ := by simp

/-- Möbius inversion identifies the omitted floor tail at every cutoff. -/
theorem pmUndampedMobiusFloorPrefix_eq_one_sub_tail {n : ℕ} (hn : 1 ≤ n) (U : ℕ) :
    pmUndampedMobiusFloorPrefix U n = 1 -
      ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc U (n / k), moebiusReal d := by
  rw [← sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc]
  by_cases hUn : U ≤ n
  · have hIcc (N : ℕ) : Icc 1 N = Ioc 0 N := by
      ext d
      simp only [mem_Icc, mem_Ioc]
      omega
    have hsplit := sum_Ioc_consecutive
      (fun d => moebiusReal d * ((n / d : ℕ) : ℝ)) (Nat.zero_le U) hUn
    have hfull : (∑ d ∈ Icc 1 n, moebiusReal d * ((n / d : ℕ) : ℝ)) = 1 :=
      sum_moebius_natDiv_eq_one n n hn le_rfl
    rw [hIcc n] at hfull
    rw [pmUndampedMobiusFloorPrefix, hIcc U]
    linarith only [hsplit, hfull]
  · rw [Ioc_eq_empty (by omega), sum_empty, sub_zero]
    exact sum_moebius_natDiv_eq_one n U hn (by omega)

private theorem moebius_partial_sum_Ioc_eq {U x : ℕ} (hUx : U ≤ x) :
    (∑ d ∈ Ioc U x, moebiusReal d) =
      (∑ d ∈ Icc 1 x, moebiusReal d) - ∑ d ∈ Icc 1 U, moebiusReal d := by
  have hIcc (N : ℕ) : Icc 1 N = Ioc 0 N := by
    ext d
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hIcc x, hIcc U]
  have h := sum_Ioc_consecutive moebiusReal (Nat.zero_le U) hUx
  linarith only [h]

/-- The long floor tail loses one harmonic factor against a linear partial-sum modulus. -/
theorem abs_pmUndampedMobiusFloorPrefix_sub_one_le {D U n : ℕ} {L : ℝ}
    (hL : 0 ≤ L) (hDU : D ≤ U) (hn : 1 ≤ n)
    (hM : ∀ x : ℕ, D ≤ x → |∑ d ∈ Icc 1 x, moebiusReal d| ≤ L * x) :
    |pmUndampedMobiusFloorPrefix U n - 1| ≤
      2 * L * n * ∑ k ∈ Icc 1 n, 1 / (k : ℝ) := by
  rw [pmUndampedMobiusFloorPrefix_eq_one_sub_tail hn,
    show (1 : ℝ) - (∑ k ∈ Icc 1 n, ∑ d ∈ Ioc U (n / k), moebiusReal d) - 1 =
      -(∑ k ∈ Icc 1 n, ∑ d ∈ Ioc U (n / k), moebiusReal d) by ring, abs_neg, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
  by_cases hUk : U ≤ n / k
  · rw [moebius_partial_sum_Ioc_eq hUk]
    have hU := hM U hDU
    have hx := hM (n / k) (hDU.trans hUk)
    have hUcast : (U : ℝ) ≤ (n / k : ℕ) := by exact_mod_cast hUk
    have hfrac : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
    have hUx : L * U ≤ L * (n / k : ℕ) := mul_le_mul_of_nonneg_left hUcast hL
    calc
      _ ≤ |∑ d ∈ Icc 1 (n / k), moebiusReal d| + |∑ d ∈ Icc 1 U, moebiusReal d| := abs_sub _ _
      _ ≤ 2 * L * (n / k : ℕ) := by linarith only [hU, hx, hUx]
      _ ≤ 2 * L * ((n : ℝ) / k) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := by ring
  · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    positivity

/-- A common Mertens and harmonic modulus controls every cutoff, including the short ones. -/
theorem abs_pmUndampedMobiusFloorPrefix_sub_mean_le_uniform {D n : ℕ} {L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hn : 1 ≤ n)
    (hM : ∀ x : ℕ, D ≤ x → |∑ d ∈ Icc 1 x, moebiusReal d| ≤ L * x)
    (hH : ∀ x : ℕ, D ≤ x → |deningerHarmonicPartial x| ≤ K) (U : ℕ) :
    |pmUndampedMobiusFloorPrefix U n - (n : ℝ) * deningerHarmonicPartial U| ≤
      D + 1 + 2 * L * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) + K * n := by
  by_cases hDU : D ≤ U
  · have hfloor := abs_pmUndampedMobiusFloorPrefix_sub_one_le hL hDU hn hM
    have hHn : |(n : ℝ) * deningerHarmonicPartial U| ≤ K * n := by
      rw [abs_mul, Nat.abs_cast]
      exact (mul_le_mul_of_nonneg_left (hH U hDU) (Nat.cast_nonneg n)).trans_eq (mul_comm _ _)
    have htriangle : |pmUndampedMobiusFloorPrefix U n - (n : ℝ) * deningerHarmonicPartial U| ≤
        |pmUndampedMobiusFloorPrefix U n - 1| + 1 + |(n : ℝ) * deningerHarmonicPartial U| := by
      calc
        _ = |(pmUndampedMobiusFloorPrefix U n - 1) + 1 - (n : ℝ) * deningerHarmonicPartial U| := by congr 1; ring
        _ ≤ |(pmUndampedMobiusFloorPrefix U n - 1) + 1| + |(n : ℝ) * deningerHarmonicPartial U| := abs_sub _ _
        _ ≤ (|pmUndampedMobiusFloorPrefix U n - 1| + |(1 : ℝ)|) + |(n : ℝ) * deningerHarmonicPartial U| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_one]
    linarith only [hfloor, hHn, htriangle, (Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  · have hUD : (U : ℝ) ≤ D := by exact_mod_cast (lt_of_not_ge hDU).le
    have hrest : 0 ≤ 1 + 2 * L * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) + K * n := by positivity
    exact (abs_pmUndampedMobiusFloorPrefix_sub_mean_le U n).trans
      (by linarith only [hUD, hrest])

/-- Every logarithmic Mertens rate gives a common finite estimate for all undamped cutoffs. -/
theorem exists_uniform_pmUndampedMobiusFloorPrefix_log_bound (p : ℕ) (hp : 0 < p) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D n : ℕ, D₀ ≤ D → 1 ≤ n → ∀ U : ℕ,
        |pmUndampedMobiusFloorPrefix U n - (n : ℝ) * deningerHarmonicPartial U| ≤
          D + 1 + (2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) + C * n) /
            Real.log (D : ℝ) ^ p := by
  obtain ⟨B, hB, hM⟩ := Sieve.deningerMertensM_log_pow_rate p
  obtain ⟨C, hC, hH⟩ := Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow p hp
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hM
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hH
  refine ⟨B, C, hB, hC, max M₀ (max H₀ 2), (le_max_right H₀ 2).trans (le_max_right _ _),
    fun D n hD hn U => ?_⟩
  have hD2 : 2 ≤ D := ((le_max_right H₀ 2).trans (le_max_right M₀ _)).trans hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hD2)
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hM' (x : ℕ) (hx : D ≤ x) :
      |∑ d ∈ Icc 1 x, moebiusReal d| ≤ (B / Real.log (D : ℝ) ^ p) * x := by
    have hlog : Real.log (D : ℝ) ^ p ≤ Real.log (x : ℝ) ^ p :=
      pow_le_pow_left₀ hlogD.le (Real.log_le_log hD0 (by exact_mod_cast hx)) p
    rw [sum_Icc_moebiusReal_eq_mertensM]
    calc
      _ ≤ B * x / Real.log (x : ℝ) ^ p := hM₀ x (((le_max_left _ _).trans hD).trans hx)
      _ ≤ B * x / Real.log (D : ℝ) ^ p :=
        div_le_div_of_nonneg_left (mul_nonneg hB (Nat.cast_nonneg x)) (pow_pos hlogD p) hlog
      _ = _ := by ring
  have hH' (x : ℕ) (hx : D ≤ x) :
      |deningerHarmonicPartial x| ≤ C / Real.log (D : ℝ) ^ p := by
    have hlog : Real.log (D : ℝ) ^ p ≤ Real.log (x : ℝ) ^ p :=
      pow_le_pow_left₀ hlogD.le (Real.log_le_log hD0 (by exact_mod_cast hx)) p
    exact (hH₀ x ((((le_max_left H₀ 2).trans (le_max_right M₀ _)).trans hD).trans hx)).trans
      (div_le_div_of_nonneg_left hC (pow_pos hlogD p) hlog)
  have h := abs_pmUndampedMobiusFloorPrefix_sub_mean_le_uniform
    (div_nonneg hB (pow_nonneg hlogD.le _)) (div_nonneg hC (pow_nonneg hlogD.le _)) hn hM' hH' U
  refine h.trans_eq ?_
  ring

/-- The single Möbius floor sum is the convolution prefix with unit second cutoff. -/
theorem pmUndampedVaughanConvolutionPrefix_one_right (U n : ℕ) :
    pmUndampedVaughanConvolutionPrefix U 1 n = pmUndampedMobiusFloorPrefix U n := by
  rw [pmUndampedVaughanConvolutionPrefix_eq_rectangle]
  have hm : moebiusReal 1 = 1 := by simp [moebiusReal]
  simp only [Icc_self, sum_singleton, hm, one_mul, Nat.mul_one,
    pmUndampedMobiusFloorPrefix]

/-- The truncated Möbius floor sums have every logarithmic saving uniformly in their cutoff. -/
theorem exists_uniform_pmUndampedMobiusFloorPrefix_log_rate (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U : ℕ,
      |pmUndampedMobiusFloorPrefix U n - (n : ℝ) * deningerHarmonicPartial U| ≤
        C * (n : ℝ) / Real.log (n : ℝ) ^ q := by
  obtain ⟨C, hC, h⟩ := exists_uniform_pmUndampedVaughanConvolutionPrefix_log_rate q
  refine ⟨C, hC, h.mono fun n hn U => ?_⟩
  have hH : deningerHarmonicPartial 1 = 1 := by
    rw [deningerHarmonicPartial_eq_sum_Icc]
    simp
  simpa only [pmUndampedVaughanConvolutionPrefix_one_right, hH, mul_one] using hn U 1

#print axioms pmUndampedVaughanConvolutionPrefix_one_right
#print axioms exists_uniform_pmUndampedMobiusFloorPrefix_log_rate
#print axioms exists_uniform_pmUndampedMobiusFloorPrefix_log_bound

#print axioms abs_pmUndampedMobiusFloorPrefix_sub_mean_le
#print axioms pmUndampedMobiusFloorPrefix_eq_one_sub_tail
#print axioms abs_pmUndampedMobiusFloorPrefix_sub_one_le
#print axioms abs_pmUndampedMobiusFloorPrefix_sub_mean_le_uniform
end GaloisForLFunctions.BezoutValuationIncidence
