import GaloisForLFunctions.BezoutValuationIncidence.SawtoothBezoutSuccessorGradientAndRouteFZZPBridge
import GaloisForLFunctions.BezoutValuationIncidence.SixModeStabilityAndSharpQuarterDecorrelation
import GaloisForLFunctions.RHTower.EulerDeletionMobiusPeriodCovariance
import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization
import GaloisForLFunctions.BiScaleUncertainty.BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch

/-!
# Discrete primitive energy and sharp Jordan comparisons

The energy is the actual mean square of the zero-mean successor primitive on
the integer cycle of length `N!`. Existing discrete residue covariance identifies
its spectrum with `J₂/12`. Three sharp arithmetic comparisons select exactly
the pairs of modes {2,3}, {3,4}, and {4,6}; they determine the joint lower frontier
with Selberg variance and successor covariance.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.Sieve RHTower.DeletionPeriodCovariance
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The Jordan spectrum is the existing multiplicative gcd-power kernel at exponent two. -/
theorem jordanTotient2_eq_gcdPowKernel (n : ℕ) : jordanTotient2 n = gcdPowKernel 2 n := by
  rw [gcdPowKernel_apply]
  unfold jordanTotient2
  apply Finset.sum_congr rfl
  intro x hx
  rw [rpowArith_apply_of_ne_zero _ (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)]
  norm_cast

private theorem jordan_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) :
    jordanTotient2 (p ^ (k + 1)) = ((p : ℝ) ^ (k + 1)) ^ 2 - ((p : ℝ) ^ k) ^ 2 := by
  rw [jordanTotient2_eq_gcdPowKernel, gcdPowKernel_prime_pow 2 hp (by omega)]
  norm_cast

private theorem jordan_mul {a b : ℕ} (h : a.Coprime b) :
    jordanTotient2 (a * b) = jordanTotient2 a * jordanTotient2 b := by
  simp_rw [jordanTotient2_eq_gcdPowKernel]
  exact (isMultiplicative_gcdPowKernel 2).map_mul_of_coprime h

/-- A uniform arithmetic lower bound for the integration spectrum. -/
theorem jordanTotient2_ge_mul_totient (n : ℕ) :
    (n : ℝ) * (Nat.totient n : ℝ) ≤ jordanTotient2 n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp [jordanTotient2]
  | prime_pow p k hp =>
    rcases k with _ | k
    · simp
    · rw [jordan_prime_power hp, Nat.totient_prime_pow_succ hp]
      push_cast [Nat.cast_sub hp.one_le]
      rw [pow_succ]
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      nlinarith [mul_nonneg (sq_nonneg ((p : ℝ) ^ k)) (sub_nonneg.mpr hpR)]
  | coprime a b _ _ hab ha hb =>
    rw [jordan_mul hab, Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul]
    have ha0 : 0 ≤ (a : ℝ) * (Nat.totient a : ℝ) := by positivity
    have hb0 : 0 ≤ (b : ℝ) * (Nat.totient b : ℝ) := by positivity
    have h := mul_le_mul ha hb hb0 (ha0.trans ha)
    nlinarith

private theorem jordan_small_values :
    jordanTotient2 2 = 3 ∧ jordanTotient2 3 = 8 ∧ jordanTotient2 4 = 12 ∧
    jordanTotient2 5 = 24 ∧ jordanTotient2 6 = 24 ∧ jordanTotient2 7 = 48 ∧
    jordanTotient2 8 = 48 ∧ jordanTotient2 9 = 72 := by
  have h2 := jordan_prime_power Nat.prime_two 0
  have h3 := jordan_prime_power Nat.prime_three 0
  have h4 := jordan_prime_power Nat.prime_two 1
  have h5 := jordan_prime_power Nat.prime_five 0
  have h7 := jordan_prime_power Nat.prime_seven 0
  have h8 := jordan_prime_power Nat.prime_two 2
  have h9 := jordan_prime_power Nat.prime_three 1
  have h6 := jordan_mul (show Nat.Coprime 2 3 by norm_num)
  norm_num at h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h2, h3, h4, h5, by rw [h2, h3] at h6; norm_num at h6 ⊢; exact h6,
    h7, h8, h9⟩

private theorem jordan_three_facets {q : ℕ} (hq : 2 ≤ q) :
    (0 ≤ jordanTotient2 q - 5 * (Nat.totient q : ℝ) - 2 * moebiusReal q ∧
      (jordanTotient2 q - 5 * (Nat.totient q : ℝ) - 2 * moebiusReal q = 0 ↔
        q = 2 ∨ q = 3)) ∧
    (0 ≤ jordanTotient2 q - 6 * (Nat.totient q : ℝ) - 4 * moebiusReal q ∧
      (jordanTotient2 q - 6 * (Nat.totient q : ℝ) - 4 * moebiusReal q = 0 ↔
        q = 3 ∨ q = 4)) ∧
    (0 ≤ jordanTotient2 q - 6 * (Nat.totient q : ℝ) - 12 * moebiusReal q ∧
      (jordanTotient2 q - 6 * (Nat.totient q : ℝ) - 12 * moebiusReal q = 0 ↔
        q = 4 ∨ q = 6)) := by
  by_cases hlarge : 10 ≤ q
  · have ht : 4 ≤ Nat.totient q := by
      have hn : ¬Nat.totient q ≤ 2 := by
        intro h
        have hh := (GaloisForLFunctions.HTGeometry.totient_le_two_iff (by omega)).mp h
        omega
      obtain ⟨k, hk⟩ := Nat.totient_even (by omega : 2 < q)
      omega
    have htR : (4 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast ht
    have hqR : (10 : ℝ) ≤ q := by exact_mod_cast hlarge
    have hj := jordanTotient2_ge_mul_totient q
    have hm := (moebiusReal_le_one q).2
    have h1 : 0 < jordanTotient2 q - 5 * (Nat.totient q : ℝ) - 2 * moebiusReal q := by
      nlinarith
    have h2 : 0 < jordanTotient2 q - 6 * (Nat.totient q : ℝ) - 4 * moebiusReal q := by
      nlinarith
    have h3 : 0 < jordanTotient2 q - 6 * (Nat.totient q : ℝ) - 12 * moebiusReal q := by
      nlinarith
    exact ⟨⟨h1.le, by constructor <;> intro h <;> first | linarith | omega⟩,
      ⟨h2.le, by constructor <;> intro h <;> first | linarith | omega⟩,
      ⟨h3.le, by constructor <;> intro h <;> first | linarith | omega⟩⟩
  · obtain ⟨hj2, hj3, hj4, hj5, hj6, hj7, hj8, hj9⟩ := jordan_small_values
    have ht4 := wall11_totient_degeneracy_broken_by_bezout.1
    have ht6 := wall11_totient_degeneracy_broken_by_bezout.2.1
    have hm4 := wall11_totient_degeneracy_broken_by_bezout.2.2.1
    have hm6 := wall11_totient_degeneracy_broken_by_bezout.2.2.2
    rw [ht4] at hm4
    rw [ht6] at hm6
    have hm4' : moebiusReal 4 = 0 := by norm_num at hm4; linarith
    have hm6' : moebiusReal 6 = 1 := by norm_num at hm6; linarith
    change ((μ 4 : ℤ) : ℝ) = 0 at hm4'
    change ((μ 6 : ℤ) : ℝ) = 1 at hm6'
    have hm4Z : (μ 4 : ℤ) = 0 := by exact_mod_cast hm4'
    have hm6Z : (μ 6 : ℤ) = 1 := by exact_mod_cast hm6'
    have ht8 := Nat.totient_prime_pow_succ Nat.prime_two 2
    have ht9 := Nat.totient_prime_pow_succ Nat.prime_three 1
    have hm8 := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by decide : 3 ≠ 0)
    have hm9 := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_three (by decide : 2 ≠ 0)
    norm_num at ht8 ht9 hm8 hm9
    have hq9 : q ≤ 9 := by omega
    interval_cases q <;>
      norm_num [hj2, hj3, hj4, hj5, hj6, hj7, hj8, hj9, ht4, ht6, ht8, ht9,
        hm4Z, hm6Z, moebiusReal, hm8, hm9, Nat.totient_prime Nat.prime_three,
        Nat.totient_prime Nat.prime_five, Nat.totient_prime Nat.prime_seven,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three,
        ArithmeticFunction.moebius_apply_prime Nat.prime_five,
        ArithmeticFunction.moebius_apply_prime Nat.prime_seven]

/-- The three sharp Jordan facets, including every arithmetic equality case. -/
theorem jordanTotient2_sharp_successor_facets (n : ℕ) :
    let q := n + 2
    (5 * (Nat.totient q : ℝ) + 2 * moebiusReal q ≤ jordanTotient2 q ∧
      (jordanTotient2 q = 5 * (Nat.totient q : ℝ) + 2 * moebiusReal q ↔ q = 2 ∨ q = 3)) ∧
    (6 * (Nat.totient q : ℝ) + 4 * moebiusReal q ≤ jordanTotient2 q ∧
      (jordanTotient2 q = 6 * (Nat.totient q : ℝ) + 4 * moebiusReal q ↔ q = 3 ∨ q = 4)) ∧
    (6 * (Nat.totient q : ℝ) + 12 * moebiusReal q ≤ jordanTotient2 q ∧
      (jordanTotient2 q = 6 * (Nat.totient q : ℝ) + 12 * moebiusReal q ↔ q = 4 ∨ q = 6)) := by
  dsimp
  obtain ⟨⟨h1, he1⟩, ⟨h2, he2⟩, ⟨h3, he3⟩⟩ := jordan_three_facets (by omega : 2 ≤ n + 2)
  refine ⟨⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩⟩
  all_goals constructor
  · intro h; exact he1.mp (by linarith)
  · intro h; have := he1.mpr h; linarith
  · intro h; exact he2.mp (by linarith)
  · intro h; have := he2.mpr h; linarith
  · intro h; exact he3.mp (by linarith)
  · intro h; have := he3.mpr h; linarith

/-- Mean-square energy of the canonical successor primitive on its integer period. -/
def sievePrimitiveEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range N.factorial, (weightedCenteredSawtoothSum N c k)^2) /
    (N.factorial : ℝ)

/-- The canonical primitive is periodic on the integer factorial cycle. -/
theorem weightedCenteredSawtoothSum_factorial_periodic (N : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (weightedCenteredSawtoothSum N c) N.factorial := by
  intro k
  unfold weightedCenteredSawtoothSum
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdP := Nat.dvd_factorial hd0 (Finset.mem_Icc.mp hd).2
  rw [centeredDiscreteSawtooth_eq_mod_sub_half hd0,
    centeredDiscreteSawtooth_eq_mod_sub_half hd0, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd hdP, Nat.add_zero, Nat.mod_mod]

private theorem primitive_eq_centered_combination (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    weightedCenteredSawtoothSum N c k =
      -(residueCombination (Finset.Icc 1 N) c k - periodMean (Finset.Icc 1 N) c) := by
  unfold weightedCenteredSawtoothSum residueCombination periodMean
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  rw [centeredDiscreteSawtooth_eq_mod_sub_half hd0]
  ring

/-- The primitive has exactly zero mean on the factorial period, at every level. -/
theorem weightedCenteredSawtoothSum_period_sum (N : ℕ) (c : ℕ → ℝ) :
    ∑ k ∈ Finset.range N.factorial, weightedCenteredSawtoothSum N c k = 0 := by
  simp_rw [primitive_eq_centered_combination, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  rw [sum_residueCombination c (fun _ hd => (Finset.mem_Icc.mp hd).1)
    (fun _ hd => Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2)]
  simp

private theorem primitive_energy_eq_covariance (N : ℕ) (c : ℕ → ℝ) :
    sievePrimitiveEnergy N c = periodCovariance (Finset.Icc 1 N) c := by
  unfold sievePrimitiveEnergy
  simp_rw [primitive_eq_centered_combination, neg_sq]
  rw [sum_residueCombination_centered_sq c (fun _ hd => (Finset.mem_Icc.mp hd).1)
    (fun _ hd => Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2)]
  have hP : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  field_simp

private theorem covariance_eq_franel (N : ℕ) (c : ℕ → ℝ) :
    12 * periodCovariance (Finset.Icc 1 N) c =
      franelGcdQuadraticForm N c - (finiteHarmonicSum N c)^2 := by
  have hterm (m n : ℕ) (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) :
      c m * c n * (((Nat.gcd m n : ℝ)^2 - 1) / ((m : ℝ) * n)) =
      c m * c n * ((Nat.gcd m n : ℝ)^2 / ((m : ℝ) * n)) -
        (c m / (m : ℝ)) * (c n / (n : ℝ)) := by
    have hm0 : (m : ℝ) ≠ 0 := by
      have hp : 0 < m := (Finset.mem_Icc.mp hm).1
      exact_mod_cast hp.ne'
    have hn0 : (n : ℝ) ≠ 0 := by
      have hp : 0 < n := (Finset.mem_Icc.mp hn).1
      exact_mod_cast hp.ne'
    field_simp
  unfold periodCovariance franelGcdQuadraticForm finiteHarmonicSum
  rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
  simp_rw [← Finset.sum_sub_distrib]
  rw [← mul_assoc]
  norm_num
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  convert hterm m n hm hn using 1
  ring

/-- The discrete primitive has the Franel form with its constant-mode correction. -/
theorem twelve_mul_sievePrimitiveEnergy_eq_franel_sub_harmonic (N : ℕ) (c : ℕ → ℝ) :
    12 * sievePrimitiveEnergy N c =
      franelGcdQuadraticForm N c - (finiteHarmonicSum N c)^2 := by
  rw [primitive_energy_eq_covariance, covariance_eq_franel]

/-- Exact Jordan spectrum of the actual discrete-period integration energy. -/
theorem twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal (N : ℕ) (c : ℕ → ℝ) :
    12 * sievePrimitiveEnergy N c =
      ∑ q ∈ Finset.Icc 2 N, jordanTotient2 q * (selbergMultiplesCoord N c q)^2 := by
  rw [twelve_mul_sievePrimitiveEnergy_eq_franel_sub_harmonic,
    franelGcdQuadraticForm_eq_jordanTotient2_diagonal]
  rcases N with _ | N
  · simp [finiteHarmonicSum]
  · have hI : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_insert (by simp), jordanTotient2_one,
      selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    ring

/-- Zero period mean uniquely selects the primitive of the centered sieve response. -/
theorem sieve_zero_mean_primitive_iff (N : ℕ) (c F : ℕ → ℝ) :
    ((∀ k, F (k + 1) - F k = sieveSeq N c (k + 1) - finiteHarmonicSum N c) ∧
      (∑ k ∈ Finset.range N.factorial, F k) = 0) ↔
      F = weightedCenteredSawtoothSum N c := by
  constructor
  · rintro ⟨hgrad, hmean⟩
    have hconst (k : ℕ) : F k = weightedCenteredSawtoothSum N c k +
        (F 0 - weightedCenteredSawtoothSum N c 0) := by
      induction k with
      | zero => ring
      | succ k ih =>
        have h := weightedCenteredSawtoothSum_succ_sub_eq N c k
        rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum] at h
        have hg := hgrad k
        linarith
    have hsum : (∑ k ∈ Finset.range N.factorial, F k) =
        ∑ k ∈ Finset.range N.factorial,
          (weightedCenteredSawtoothSum N c k + (F 0 - weightedCenteredSawtoothSum N c 0)) :=
      Finset.sum_congr rfl fun k _ => hconst k
    rw [hsum, Finset.sum_add_distrib] at hmean
    rw [weightedCenteredSawtoothSum_period_sum] at hmean
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, zero_add] at hmean
    have hP : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
    have hz := (mul_eq_zero.mp hmean).resolve_left hP
    funext k
    rw [hconst, hz, add_zero]
  · rintro rfl
    refine ⟨?_, weightedCenteredSawtoothSum_period_sum N c⟩
    intro k
    simpa only [selbergMultiplesCoord_one_eq_finiteHarmonicSum] using
      weightedCenteredSawtoothSum_succ_sub_eq N c k

end
end GaloisForLFunctions.BezoutValuationIncidence
