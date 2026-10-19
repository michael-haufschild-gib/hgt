import GaloisForLFunctions.RHTower.Sieve.JointCongruenceClass
import Mathlib.Data.Nat.Squarefree
import GaloisForLFunctions.BezoutValuationIncidence.MobiusMagnitudePatternDensity

/-!
# Two prime-square exclusions in the first source band

The first-band magnitude is the squarefree indicator. Excluding the two
forbidden classes modulo four and nine bounds adjacent occupied pairs in
every interval by seven eighteenths of its length plus eight. Existing
shifted congruence estimates control each term of the indicator expansion;
no residue table is enumerated. Passing to the established pattern law
bounds its adjacent occupied mass by seven eighteenths.
-/

open Filter Topology Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private def divIndicator (q n : ℕ) : ℝ := if q ∣ n then 1 else 0

private theorem four_coprime_nine : Nat.Coprime 4 9 := by
  have h23 : Nat.Coprime 2 3 := Nat.coprime_two_left.mpr ⟨1, rfl⟩
  exact Nat.Coprime.pow 2 2 h23

private theorem adjacent_not_both_dvd (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    ¬ (q ∣ n ∧ q ∣ n + 1) := by
  rintro ⟨h0, h1⟩
  have hq1 : q ∣ 1 := (Nat.dvd_add_iff_left h0).mpr (by simpa [Nat.add_comm] using h1)
  have := Nat.le_of_dvd (by omega : 0 < (1 : ℕ)) hq1
  omega

private theorem squarefree_pair_indicator_le (n : ℕ) :
    (if Squarefree n ∧ Squarefree (n + 1) then (1 : ℝ) else 0) ≤
      1 - divIndicator 4 n - divIndicator 4 (n + 1) -
        divIndicator 9 n - divIndicator 9 (n + 1) +
        divIndicator 4 n * divIndicator 9 n +
        divIndicator 4 n * divIndicator 9 (n + 1) +
        divIndicator 9 n * divIndicator 4 (n + 1) +
        divIndicator 4 (n + 1) * divIndicator 9 (n + 1) := by
  by_cases hs : Squarefree n ∧ Squarefree (n + 1)
  · have h40 : ¬ 4 ∣ n := by
      simpa using Nat.squarefree_iff_prime_squarefree.mp hs.1 2 Nat.prime_two
    have h41 : ¬ 4 ∣ n + 1 := by
      simpa using Nat.squarefree_iff_prime_squarefree.mp hs.2 2 Nat.prime_two
    have h90 : ¬ 9 ∣ n := by
      simpa using Nat.squarefree_iff_prime_squarefree.mp hs.1 3 Nat.prime_three
    have h91 : ¬ 9 ∣ n + 1 := by
      simpa using Nat.squarefree_iff_prime_squarefree.mp hs.2 3 Nat.prime_three
    simp [hs, divIndicator, h40, h41, h90, h91]
  · rw [if_neg hs]
    have h4 : 0 ≤ 1 - divIndicator 4 n - divIndicator 4 (n + 1) := by
      have := adjacent_not_both_dvd 4 (by omega) n
      by_cases h0 : 4 ∣ n <;> by_cases h1 : 4 ∣ n + 1 <;>
        simp_all [divIndicator]
    have h9 : 0 ≤ 1 - divIndicator 9 n - divIndicator 9 (n + 1) := by
      have := adjacent_not_both_dvd 9 (by omega) n
      by_cases h0 : 9 ∣ n <;> by_cases h1 : 9 ∣ n + 1 <;>
        simp_all [divIndicator]
    nlinarith [mul_nonneg h4 h9]

private theorem divIndicator_four_mul_nine (n : ℕ) :
    divIndicator 4 n * divIndicator 9 n = divIndicator 36 n := by
  have hc := four_coprime_nine
  have he : (4 ∣ n ∧ 9 ∣ n) ↔ 36 ∣ n := by
    constructor
    · rintro ⟨h4, h9⟩
      exact hc.mul_dvd_of_dvd_of_dvd h4 h9
    · intro h
      exact ⟨dvd_trans (by norm_num) h, dvd_trans (by norm_num) h⟩
  by_cases h4 : 4 ∣ n <;> by_cases h9 : 9 ∣ n <;>
    simp_all [divIndicator]

private theorem sum_divIndicator_error (q s t L : ℕ) (hq : 0 < q) :
    |(∑ n ∈ Ioc t (t + L), divIndicator q (n + s)) - (L : ℝ) / q| < 1 := by
  simpa only [divIndicator, Finset.sum_boole] using
    RHTower.Sieve.abs_card_filter_dvd_add_shift_sub_lt q s t L hq

private theorem sum_pairIndicator_error (a b t L : ℕ)
    (hc : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    |(∑ n ∈ Ioc t (t + L), divIndicator a n * divIndicator b (n + 1)) -
      (L : ℝ) / ((a : ℝ) * b)| < 1 := by
  obtain ⟨n₀, h0a, h0b⟩ := RHTower.Sieve.exists_joint_solution hb hc 1
  have h := RHTower.Sieve.abs_card_joint_sub_lt hc (Nat.mul_pos ha hb) h0a h0b t L
  have he (n : ℕ) : divIndicator a n * divIndicator b (n + 1) =
      if a ∣ n ∧ b ∣ n + 1 then (1 : ℝ) else 0 := by
    by_cases h1 : a ∣ n <;> by_cases h2 : b ∣ n + 1 <;>
      simp [divIndicator, h1, h2]
  simpa only [he, Finset.sum_boole] using h

/-- Two prime-square exclusions bound consecutive squarefree pairs in every interval. -/
private theorem squarefreeSuccessorCount_twoPrime_le (t L : ℕ) :
    (#{n ∈ Ioc t (t + L) | Squarefree n ∧ Squarefree (n + 1)} : ℝ) ≤
      (7 / 18 : ℝ) * L + 8 := by
  have h := Finset.sum_le_sum (s := Ioc t (t + L))
    (fun n _ => squarefree_pair_indicator_le n)
  simp only [Finset.sum_boole, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    divIndicator_four_mul_nine, Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
    nsmul_eq_mul, mul_one] at h
  have h40 := sum_divIndicator_error 4 0 t L (by omega)
  have h41 := sum_divIndicator_error 4 1 t L (by omega)
  have h90 := sum_divIndicator_error 9 0 t L (by omega)
  have h91 := sum_divIndicator_error 9 1 t L (by omega)
  have h360 := sum_divIndicator_error 36 0 t L (by omega)
  have h361 := sum_divIndicator_error 36 1 t L (by omega)
  have h49 := sum_pairIndicator_error 4 9 t L four_coprime_nine (by omega) (by omega)
  have h94 := sum_pairIndicator_error 9 4 t L four_coprime_nine.symm (by omega) (by omega)
  simp only [Nat.add_zero] at h40 h90 h360
  norm_num at h40 h41 h90 h91 h360 h361 h49 h94
  linarith only [h, (abs_lt.mp h40).1, (abs_lt.mp h41).1,
    (abs_lt.mp h90).1, (abs_lt.mp h91).1, (abs_lt.mp h360).2,
    (abs_lt.mp h361).2, (abs_lt.mp h49).2, (abs_lt.mp h94).2]

/-- Occupied first-band magnitudes are exactly the squarefree integers. -/
theorem moebiusFirstBandMagnitude_one_iff_squarefree (n : ℕ) :
    moebiusBandMagnitude 1 n = 1 ↔ Squarefree n := by
  have habs : |moebiusReal n| = if Squarefree n then (1 : ℝ) else 0 := by
    unfold moebiusReal
    exact_mod_cast (ArithmeticFunction.abs_moebius (n := n))
  have he : moebiusBandMagnitude 1 n = |moebiusReal n| := by
    simp [moebiusBandMagnitude]
  rw [he, habs]
  split_ifs <;> simp_all

/-- A finite two-prime sieve bounds adjacent occupied first-band source magnitudes. -/
theorem moebiusFirstBandAdjacentOneCount_le (t L : ℕ) :
    (#{n ∈ Ioc t (t + L) | moebiusBandMagnitude 1 n = 1 ∧
      moebiusBandMagnitude 1 (n + 1) = 1} : ℝ) ≤ (7 / 18 : ℝ) * L + 8 := by
  simpa only [moebiusFirstBandMagnitude_one_iff_squarefree] using squarefreeSuccessorCount_twoPrime_le t L

/-- The unconditional first-band joint law has adjacent occupied mass at most seven eighteenths. -/
theorem moebiusFirstBandAdjacentOneDensity_le :
    moebiusBandPatternDensity 1 (fun i : Fin 2 => i.val) (fun _ => 1) ≤ (7 / 18 : ℝ) := by
  have hp (n : ℕ) :
      (∀ i : Fin 2, moebiusBandMagnitude 1 (n + i.val) = 1) ↔
        Squarefree n ∧ Squarefree (n + 1) := by
    constructor
    · intro h
      exact ⟨(moebiusFirstBandMagnitude_one_iff_squarefree n).mp (by simpa using h 0),
        (moebiusFirstBandMagnitude_one_iff_squarefree (n + 1)).mp (by simpa using h 1)⟩
    · intro h i
      fin_cases i
      · simpa using (moebiusFirstBandMagnitude_one_iff_squarefree n).mpr h.1
      · simpa using (moebiusFirstBandMagnitude_one_iff_squarefree (n + 1)).mpr h.2
  have hcount (N : ℕ) :
      moebiusBandPatternCount 1 N (fun i : Fin 2 => i.val) (fun _ => 1) =
        #{n ∈ Ioc 0 N | Squarefree n ∧ Squarefree (n + 1)} := by
    unfold moebiusBandPatternCount
    apply congrArg Finset.card
    ext n
    constructor
    · intro hn
      obtain ⟨hn, hpat⟩ := mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hhi⟩, (hp n).mp hpat⟩
    · intro hn
      obtain ⟨hn, hsf⟩ := mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hn
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hhi⟩, (hp n).mpr hsf⟩
  have hright : Tendsto (fun N : ℕ => (7 / 18 : ℝ) + 8 / N) atTop (𝓝 (7 / 18 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).const_add (7 / 18)
  apply le_of_tendsto_of_tendsto
    (tendsto_moebiusBandPatternFrequency 1 (fun i : Fin 2 => i.val) (fun _ => 1)) hright
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hcount]
  calc
    _ ≤ ((7 / 18 : ℝ) * N + 8) / N := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      simpa only [Nat.zero_add] using squarefreeSuccessorCount_twoPrime_le 0 N
    _ = _ := by field_simp [hNr.ne']

end
end GaloisForLFunctions.BezoutValuationIncidence
