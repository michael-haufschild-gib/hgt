import GaloisForLFunctions.ArithmeticCountingPositivity.SparsePrimeFlipsRetainPositiveGaps

/-!
# Prime parity pairing

For `ω(n) = (-1)^v_p(n)`, every negative coordinate is `p` times a positive
coordinate. Counting these fibres with weight `1/n` gives
`p(H_N - S_N) = H_{⌊N/p⌋} + S_{⌊N/p⌋}`. It forces the correlation floor
`(p-1)/(p+1)` and identifies its excess as a positive boundary count. The
squared-angle estimate converts this count into a positive prime gap, even
for the prime-two flip.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The two nonnegative parity counts, with twice the usual harmonic weight. -/
def parityMass (positive : Bool) (p N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (1 + (if positive then 1 else -1) * finiteFlip {p} n) / n

theorem parityMass_nonneg (positive : Bool) (p N : ℕ) : 0 ≤ parityMass positive p N := by
  refine sum_nonneg fun n _ => div_nonneg ?_ (Nat.cast_nonneg n)
  have hs := singleFlip_mul_self p n
  cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  · nlinarith only [hs, sq_nonneg (finiteFlip {p} n - 1)]
  · nlinarith only [hs, sq_nonneg (finiteFlip {p} n + 1)]

theorem parityMass_mono (positive : Bool) (p : ℕ) : Monotone (parityMass positive p) := by
  intro M N hMN
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
  · intro n _ _
    apply div_nonneg _ (Nat.cast_nonneg n)
    have hs := singleFlip_mul_self p n
    cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
    · nlinarith only [hs, sq_nonneg (finiteFlip {p} n - 1)]
    · nlinarith only [hs, sq_nonneg (finiteFlip {p} n + 1)]

theorem parityMass_true (p N : ℕ) : parityMass true p N =
    gaugeHarmonicSum (fun _ => 1) N + gaugeHarmonicSum (finiteFlip {p}) N := by
  simp only [parityMass, ↓reduceIte, one_mul, add_div, sum_add_distrib,
    gaugeHarmonicSum]

theorem parityMass_false (p N : ℕ) : parityMass false p N =
    gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (finiteFlip {p}) N := by
  simp only [parityMass, Bool.false_eq_true, ↓reduceIte, neg_one_mul, ← sub_eq_add_neg,
    sub_div, sum_sub_distrib, gaugeHarmonicSum]

/-- Multiplication by `p` bijects positive parity fibres with negative parity fibres. -/
theorem prime_parity_pairing {p : ℕ} (hp : p.Prime) (N : ℕ) :
    parityMass false p N = parityMass true p (N / p) / p := by
  have hflip : finiteFlip {p} p = -1 := by
    simp only [finiteFlip, prod_singleton, hp.factorization_self, pow_one]
  have hmul {n : ℕ} (hn : 0 < n) : finiteFlip {p} (p * n) = -finiteFlip {p} n := by
    rw [(finiteFlip_isSignGauge {p}).mul hp.ne_zero hn.ne', hflip, neg_one_mul]
  have hsupport : parityMass false p N =
      ∑ n ∈ (Icc 1 N).filter (p ∣ ·), (1 - finiteFlip {p} n) / n := by
    rw [parityMass, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul, ← sub_eq_add_neg]
    by_cases hd : p ∣ n
    · rw [if_pos hd]
    · rw [if_neg hd, finiteFlip_eq_one_of_coprime (by simpa using hd), sub_self, zero_div]
  rw [hsupport, filter_dvd_Icc_eq_image hp.pos,
    sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), parityMass, sum_div]
  refine sum_congr rfl fun n hn => ?_
  rw [hmul (mem_Icc.mp hn).1, Nat.cast_mul]
  simp only [↓reduceIte, one_mul]
  ring

/-- The excess over the limiting ratio is exactly the positive boundary count. -/
theorem prime_parity_boundary_identity {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ((p : ℝ) + 1) * gaugeHarmonicSum (finiteFlip {p}) N -
        ((p : ℝ) - 1) * gaugeHarmonicSum (fun _ => 1) N =
      parityMass true p N - parityMass true p (N / p) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := prime_parity_pairing hp N
  rw [parityMass_false, eq_div_iff hp0] at h
  rw [parityMass_true p N]
  linear_combination -h

/-- The boundary count is nonnegative and uniformly bounded in the horizon. -/
theorem prime_parity_boundary_bounds {p : ℕ} (hp : p.Prime) (N : ℕ) :
    0 ≤ ((p : ℝ) + 1) * gaugeHarmonicSum (finiteFlip {p}) N -
        ((p : ℝ) - 1) * gaugeHarmonicSum (fun _ => 1) N ∧
    ((p : ℝ) + 1) * gaugeHarmonicSum (finiteFlip {p}) N -
        ((p : ℝ) - 1) * gaugeHarmonicSum (fun _ => 1) N ≤
      2 * (1 + Real.log p) := by
  rw [prime_parity_boundary_identity hp]
  have hplus := parityMass_mono true p (Nat.div_le_self N p)
  have hminus := parityMass_mono false p (Nat.div_le_self N p)
  have htail := roughHarmonic_sub_div_le 0 N hp.one_le
  simp only [roughHarmonic, roughInterval_zero] at htail
  change gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (fun _ => 1) (N / p) ≤
    1 + Real.log p at htail
  refine ⟨sub_nonneg.mpr hplus, ?_⟩
  rw [parityMass_false, parityMass_false] at hminus
  rw [parityMass_true, parityMass_true]
  linarith only [hminus, htail]

/-- Pairing parity fibres gives the sharp harmonic correlation floor. -/
theorem primeFlip_harmonicCorrelation_ge {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) :
    ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤ harmonicCorrelation (finiteFlip {p}) N := by
  have h := (prime_parity_boundary_bounds hp N).1
  have hH := gaugeHarmonicSum_one_pos hN
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  rw [harmonicCorrelation, le_div_iff₀ hH, div_mul_eq_mul_div, div_le_iff₀ hp1]
  nlinarith only [h]

/-- The correlation approaches its exact limiting value with an explicit harmonic error. -/
theorem primeFlip_harmonicCorrelation_error {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) :
    |harmonicCorrelation (finiteFlip {p}) N - ((p : ℝ) - 1) / ((p : ℝ) + 1)| ≤
      2 * (1 + Real.log p) /
        (((p : ℝ) + 1) * gaugeHarmonicSum (fun _ => 1) N) := by
  have hH := gaugeHarmonicSum_one_pos hN
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  have he : harmonicCorrelation (finiteFlip {p}) N - ((p : ℝ) - 1) / ((p : ℝ) + 1) =
      (((p : ℝ) + 1) * gaugeHarmonicSum (finiteFlip {p}) N -
        ((p : ℝ) - 1) * gaugeHarmonicSum (fun _ => 1) N) /
        (((p : ℝ) + 1) * gaugeHarmonicSum (fun _ => 1) N) := by
    unfold harmonicCorrelation
    field_simp [hp1.ne', hH.ne']
  rw [he, abs_of_nonneg (div_nonneg (prime_parity_boundary_bounds hp N).1
    (mul_nonneg hp1.le hH.le))]
  exact div_le_div_of_nonneg_right (prime_parity_boundary_bounds hp N).2
    (mul_nonneg hp1.le hH.le)

/-- The parity pairing determines the exact harmonic density of a prime flip. -/
theorem primeFlip_harmonicCorrelation_tendsto {p : ℕ} (hp : p.Prime) :
    Tendsto (harmonicCorrelation (finiteFlip {p})) atTop
      (𝓝 (((p : ℝ) - 1) / ((p : ℝ) + 1))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C := 2 * (1 + Real.log p) / ((p : ℝ) + 1)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop (C / ε))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hH := gaugeHarmonicSum_one_pos hN1
  have hlarge : C / ε < gaugeHarmonicSum (fun _ => 1) N :=
    (hN₀ N ((le_max_right _ _).trans hN)).trans_le (log_le_gaugeHarmonicSum_one hN1)
  have hsmall : C / gaugeHarmonicSum (fun _ => 1) N < ε := by
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hH]
    nlinarith only [hlarge]
  rw [Real.dist_eq]
  refine (primeFlip_harmonicCorrelation_error hp hN1).trans_lt ?_
  have he : 2 * (1 + Real.log p) /
      (((p : ℝ) + 1) * gaugeHarmonicSum (fun _ => 1) N) =
      C / gaugeHarmonicSum (fun _ => 1) N := by
    dsimp only [C]
    rw [div_div]
  rwa [he]

/-- Every single prime flip retains the gap paid by its parity count. -/
theorem primeFlip_hasHyperplaneGap {p : ℕ} (hp : p.Prime) :
    HasHyperplaneGap (finiteFlip {p})
      (2 * Real.log 2 * (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_prime_gap_ge_squared_correlation hε
  refine ⟨max 1 N₀, fun N hN x hx => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hbound := hN₀ N ((le_max_right _ _).trans hN) (finiteFlip {p})
    (singleFlip_mul_self p) x hx
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hr : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := by positivity
  have hs := pow_le_pow_left₀ hr (primeFlip_harmonicCorrelation_ge hp hN1) 2
  have hg : 0 ≤ 2 * Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg one_le_two)
  have hm : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hgap := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hg) hm
  linarith only [hbound, hgap]

/-- Flipping prime two retains a positive gap; flipping every prime does not. -/
theorem two_adic_parity_has_gap_but_liouville_does_not :
    HasHyperplaneGap (finiteFlip {2}) (2 * Real.log 2 / 9) ∧
      ¬ HasHyperplaneGap liouvilleSign (2 * Real.log 2 / 9) := by
  constructor
  · convert primeFlip_hasHyperplaneGap Nat.prime_two using 1
    norm_num
    ring
  · apply not_liouville_hasHyperplaneGap
    exact div_pos (mul_pos (by norm_num) (Real.log_pos one_lt_two)) (by norm_num)

end GaloisForLFunctions.ArithmeticCountingPositivity
