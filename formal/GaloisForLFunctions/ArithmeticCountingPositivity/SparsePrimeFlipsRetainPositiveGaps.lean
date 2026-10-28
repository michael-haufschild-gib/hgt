import GaloisForLFunctions.ArithmeticCountingPositivity.HarmonicCorrelationPaysThePrimeGap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingReadsTheDensityOfTheGauge

/-!
# Sparse prime flips retain positive gaps

The harmonic mass of multiples of `p` is exactly `H_{⌊N/p⌋}/p`. A sign gauge
flipping only `p` can therefore lose at most `2/p` of its normalized pole
correlation. For `p ≥ 3` the squared-angle estimate pays the positive gap
`(2 log 2)(1 - 2/p)²`. These completely multiplicative twins have the same
polar matching coefficient as the untwisted source. Positive gaps and polar
matching together consequently do not select that source.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The count of multiples retains its exact harmonic weight. -/
theorem harmonicMass_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (p ∣ ·), (1 : ℝ) / n =
      gaugeHarmonicSum (fun _ => 1) (N / p) / p := by
  rw [filter_dvd_Icc_eq_image hp,
    sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  simp only [gaugeHarmonicSum, sum_div]
  exact sum_congr rfl fun n _ => by push_cast; ring

/-- A single prime flip is a sign at every coordinate, including zero. -/
theorem singleFlip_mul_self (p n : ℕ) : finiteFlip {p} n * finiteFlip {p} n = 1 := by
  simp only [finiteFlip, prod_singleton]
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Counting the possible negative coordinates gives a horizon-uniform correlation floor. -/
theorem singleFlip_harmonicCorrelation_ge {p N : ℕ} (hp : 0 < p) (hN : 1 ≤ N) :
    1 - 2 / (p : ℝ) ≤ harmonicCorrelation (finiteFlip {p}) N := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  let H := gaugeHarmonicSum (fun _ => 1) N
  let S := gaugeHarmonicSum (finiteFlip {p}) N
  have hH : 0 < H := gaugeHarmonicSum_one_pos hN
  have hcount : H - S ≤ 2 * (gaugeHarmonicSum (fun _ => 1) (N / p) / p) := by
    rw [← harmonicMass_multiples hp N, mul_sum, sum_filter]
    change (∑ n ∈ Icc 1 N, (1 : ℝ) / n) -
      (∑ n ∈ Icc 1 N, finiteFlip {p} n / n) ≤ _
    rw [← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    by_cases hd : p ∣ n
    · rw [if_pos hd]
      have hsign : -1 ≤ finiteFlip {p} n := by
        have hsq := singleFlip_mul_self p n
        nlinarith only [hsq, sq_nonneg (finiteFlip {p} n + 1)]
      have h := div_le_div_of_nonneg_right (show 1 - finiteFlip {p} n ≤ 2 by
        linarith only [hsign]) hn0.le
      simpa only [sub_div, mul_one_div] using h
    · rw [if_neg hd, finiteFlip_eq_one_of_coprime (by simpa using hd), sub_self]
  have hHle : gaugeHarmonicSum (fun _ => 1) (N / p) ≤ H := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.div_le_self N p)⟩
    · intro n _ _
      positivity
  have hd := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hHle hp0.le)
    (by norm_num : (0 : ℝ) ≤ 2)
  change 1 - 2 / (p : ℝ) ≤ S / H
  rw [le_div_iff₀ hH]
  have he : (1 - 2 / (p : ℝ)) * H = H - 2 * (H / p) := by ring
  rw [he]
  linarith only [hcount, hd]

/-- Every single prime flip above two retains an explicit positive hyperplane gap. -/
theorem singleFlip_hasHyperplaneGap {p : ℕ} (hp : 3 ≤ p) :
    HasHyperplaneGap (finiteFlip {p}) (2 * Real.log 2 * (1 - 2 / (p : ℝ)) ^ 2) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_prime_gap_ge_squared_correlation hε
  refine ⟨max 1 N₀, fun N hN x hx => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hbound := hN₀ N ((le_max_right _ _).trans hN) (finiteFlip {p})
    (singleFlip_mul_self p) x hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hr : 0 ≤ 1 - 2 / (p : ℝ) := by
    have := (div_lt_one hp0).mpr hp2
    linarith only [this]
  have hc := singleFlip_harmonicCorrelation_ge (show 0 < p by omega) hN1
  have hs := pow_le_pow_left₀ hr hc 2
  have hg : 0 ≤ 2 * Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg one_le_two)
  have hm : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hgap := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hg) hm
  linarith only [hbound, hgap]

/-- A concrete multiplicative twin has a positive gap and the untwisted polar matching. -/
theorem a_nontrivial_multiplicative_twin_has_a_positive_gap :
    ∃ ω : ℕ → ℝ, IsSignGauge ω ∧ ω 3 = -1 ∧
      HasHyperplaneGap ω (2 * Real.log 2 / 9) ∧
      ∀ y : ℕ, 1 ≤ y →
        |gaugeMertensSum ω y - Real.log y| ≤ Real.log 4 + 4 + Real.log 3 := by
  refine ⟨finiteFlip {3}, finiteFlip_isSignGauge {3}, ?_, ?_, ?_⟩
  · simp only [finiteFlip, prod_singleton, Nat.prime_three.factorization_self, pow_one]
  · convert singleFlip_hasHyperplaneGap (p := 3) le_rfl using 1 <;> norm_num <;> ring
  · have h := (finiteFlip_matching (F := {3}) (by
      intro p hp
      rcases mem_singleton.mp hp with rfl
      exact Nat.prime_three)).2
    intro y hy
    have h' := h y hy
    simpa only [one_mul, sum_singleton, Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num,
      mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h'

/-- No gap threshold below `2 log 2`, even with multiplicativity and polar matching,
selects the untwisted source: arbitrarily sparse prime flips pass that threshold. -/
theorem every_submaximal_gap_has_a_nontrivial_multiplicative_twin {a : ℝ}
    (ha : a < 2 * Real.log 2) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ finiteFlip {p} p = -1 ∧
      IsSignGauge (finiteFlip {p}) ∧ HasHyperplaneGap (finiteFlip {p}) a ∧
      ∀ y : ℕ, 1 ≤ y →
        |gaugeMertensSum (finiteFlip {p}) y - Real.log y| ≤
          Real.log 4 + 4 + 2 * Real.log p / ((p : ℝ) - 1) := by
  let g := 2 * Real.log 2
  have hg : 0 < g := mul_pos (by norm_num) (Real.log_pos one_lt_two)
  have hga : 0 < g - a := sub_pos.mpr ha
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * g / (g - a))
  obtain ⟨p, hkp, hp⟩ := Nat.exists_infinite_primes (max 3 k)
  have hp3 : 3 ≤ p := (le_max_left _ _).trans hkp
  have hkp' : k ≤ p := (le_max_right _ _).trans hkp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlarge : 4 * g / (g - a) < p := hk.trans_le (by exact_mod_cast hkp')
  have hsmall : 4 * g / (p : ℝ) < g - a := by
    rw [div_lt_iff₀ hga] at hlarge
    rw [div_lt_iff₀ hp0]
    nlinarith only [hlarge]
  have hgap : a < g * (1 - 2 / (p : ℝ)) ^ 2 := by
    have he : g * (1 - 2 / (p : ℝ)) ^ 2 =
        g - 4 * g / p + g * (2 / (p : ℝ)) ^ 2 := by ring
    rw [he]
    linarith only [hsmall, mul_nonneg hg.le (sq_nonneg (2 / (p : ℝ)))]
  refine ⟨p, hp, hp3, ?_, finiteFlip_isSignGauge {p}, ?_, ?_⟩
  · simp only [finiteFlip, prod_singleton, hp.factorization_self, pow_one]
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := singleFlip_hasHyperplaneGap hp3 ε hε
    refine ⟨N₀, fun N hN x hx => (hN₀ N hN x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · linarith only [hgap]
    · exact sum_nonneg fun _ _ => sq_nonneg _
  · have hF : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by
      intro q hq
      rcases mem_singleton.mp hq with rfl
      exact hp
    intro y hy
    simpa only [one_mul, sum_singleton, mul_div_assoc] using (finiteFlip_matching hF).2 y hy

end GaloisForLFunctions.ArithmeticCountingPositivity
