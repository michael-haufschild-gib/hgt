import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeExhaustionLosesUniformGaps
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveMarginIsTwoLogTwo

/-!
# Cofinite prime flips and harmonic exhaustion

Removing finitely many prime signs from Liouville preserves bounded harmonic
sums. An exact divisibility recurrence gives the bound `2/c_F`, where `c_F`
is the finite-flip density. Every such cofinite flip has greatest prime gap
zero. Finite prime cutoffs converge pointwise to Liouville, but their harmonic
squared distance from it tends to two at every fixed cutoff.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- The sign which flips every prime outside the finite set `F`. -/
def cofiniteFlip (F : Finset ℕ) (n : ℕ) : ℝ :=
  liouvilleSign n * finiteFlip F n

private theorem finiteFlip_square (F : Finset ℕ) (n : ℕ) :
    finiteFlip F n * finiteFlip F n = 1 := by
  by_cases hn : n = 0
  · subst n
    simp [finiteFlip]
  · exact (finiteFlip_isSignGauge F).mul_self hn

theorem cofiniteFlip_mul_self (F : Finset ℕ) (n : ℕ) :
    cofiniteFlip F n * cofiniteFlip F n = 1 := by
  calc
    _ = (liouvilleSign n * liouvilleSign n) * (finiteFlip F n * finiteFlip F n) := by
      dsimp only [cofiniteFlip]
      ring
    _ = 1 := by rw [liouvilleSign_mul_self, finiteFlip_square, mul_one]

theorem cofiniteFlip_isSignGauge (F : Finset ℕ) : IsSignGauge (cofiniteFlip F) where
  mul := by
    intro m n hm hn
    simp only [cofiniteFlip, liouvilleSign_mul hm hn, (finiteFlip_isSignGauge F).mul hm hn]
    ring
  mul_self := fun {_} _ => cofiniteFlip_mul_self F _

private theorem cofiniteFlip_insert {F : Finset ℕ} {p : ℕ} (hpF : p ∉ F) (n : ℕ) :
    cofiniteFlip (insert p F) n = (-1 : ℝ) ^ n.factorization p * cofiniteFlip F n := by
  simp only [cofiniteFlip, finiteFlip, prod_insert hpF]
  ring

private theorem cofiniteFlip_unflipped_prime {F : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpF : p ∉ F) : cofiniteFlip F p = -1 := by
  have hFp : finiteFlip F p = 1 := by
    apply prod_eq_one
    intro q hq
    rw [hp.factorization, Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hq hpF), pow_zero]
  have hlambda : liouvilleSign p = -1 := by
    simpa only [pow_one] using (liouvilleSign_prime_pow (k := 1) hp)
  rw [cofiniteFlip, hFp, mul_one, hlambda]

/-- Removing one prime sign reverses the finite-flip divisibility recurrence. -/
theorem cofiniteFlip_harmonic_recurrence {F : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpF : p ∉ F) (N : ℕ) :
    (p : ℝ) * gaugeHarmonicSum (cofiniteFlip (insert p F)) N -
        gaugeHarmonicSum (cofiniteFlip (insert p F)) (N / p) =
      (p : ℝ) * gaugeHarmonicSum (cofiniteFlip F) N +
        gaugeHarmonicSum (cofiniteFlip F) (N / p) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hFp := cofiniteFlip_unflipped_prime hp hpF
  have hGp : cofiniteFlip (insert p F) p = 1 := by
    rw [cofiniteFlip_insert hpF, hp.factorization_self, pow_one, hFp]
    norm_num
  have hsame {n : ℕ} (hn : ¬ p ∣ n) :
      cofiniteFlip (insert p F) n = cofiniteFlip F n := by
    rw [cofiniteFlip_insert hpF, Nat.factorization_eq_zero_of_not_dvd hn, pow_zero, one_mul]
  have hdiff : gaugeHarmonicSum (cofiniteFlip F) N -
      gaugeHarmonicSum (cofiniteFlip (insert p F)) N =
      (∑ n ∈ (Icc 1 N).filter (p ∣ ·), cofiniteFlip F n / n) -
        ∑ n ∈ (Icc 1 N).filter (p ∣ ·), cofiniteFlip (insert p F) n / n := by
    rw [gaugeHarmonicSum, gaugeHarmonicSum, ← sum_sub_distrib,
      ← sum_sub_distrib, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : p ∣ n
    · rw [if_pos hn]
    · rw [if_neg hn, hsame hn, sub_self]
  rw [gaugeHarmonicSum_multiples _ (cofiniteFlip_isSignGauge F) hp.pos,
    gaugeHarmonicSum_multiples _ (cofiniteFlip_isSignGauge (insert p F)) hp.pos,
    hFp, hGp] at hdiff
  field_simp [hp0] at hdiff
  linarith only [hdiff]

/-- The harmonic sum of a cofinite flip is bounded by the reciprocal finite density. -/
theorem cofiniteFlip_harmonicSum_abs_le {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime)
    (N : ℕ) :
    |gaugeHarmonicSum (cofiniteFlip F) N| ≤ 2 / finiteFlipHarmonicDensity F := by
  revert N hF
  induction F using Finset.induction_on with
  | empty =>
      intro _ N
      simpa only [gaugeHarmonicSum, cofiniteFlip, finiteFlip, finiteFlipHarmonicDensity,
        prod_empty, mul_one, div_one] using abs_sum_liouvilleSign_div_le N
  | @insert p F hpF ih =>
      intro hF N
      have hp := hF p (mem_insert_self p F)
      have hF' : ∀ q ∈ F, q.Prime := fun q hq => hF q (mem_insert_of_mem hq)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
        have hp1' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        linarith only [hp1']
      have hc := finiteFlipHarmonicDensity_pos hF'
      have hC := finiteFlipHarmonicDensity_pos hF
      have hcinsert : finiteFlipHarmonicDensity (insert p F) =
          ((p : ℝ) - 1) / ((p : ℝ) + 1) * finiteFlipHarmonicDensity F := prod_insert hpF
      have hbalance : (p : ℝ) * (2 / finiteFlipHarmonicDensity (insert p F)) =
          ((p : ℝ) + 1) * (2 / finiteFlipHarmonicDensity F) +
            2 / finiteFlipHarmonicDensity (insert p F) := by
        rw [hcinsert]
        field_simp [hp1.ne', hc.ne']
        ring
      induction N using Nat.strong_induction_on with
      | h N ihN =>
          by_cases hN : N = 0
          · subst N
            simp only [gaugeHarmonicSum, Icc_eq_empty_of_lt (by omega : 0 < 1),
              sum_empty, abs_zero]
            positivity
          have hsmall := ihN (N / p) (Nat.div_lt_self (Nat.pos_of_ne_zero hN) hp.one_lt)
          have hrec := cofiniteFlip_harmonic_recurrence hp hpF N
          have he : (p : ℝ) * gaugeHarmonicSum (cofiniteFlip (insert p F)) N =
              (p : ℝ) * gaugeHarmonicSum (cofiniteFlip F) N +
                gaugeHarmonicSum (cofiniteFlip F) (N / p) +
                  gaugeHarmonicSum (cofiniteFlip (insert p F)) (N / p) := by
            linarith only [hrec]
          have hb : (p : ℝ) * |gaugeHarmonicSum (cofiniteFlip (insert p F)) N| ≤
              ((p : ℝ) + 1) * (2 / finiteFlipHarmonicDensity F) +
                2 / finiteFlipHarmonicDensity (insert p F) := by
            calc
              _ = |(p : ℝ) * gaugeHarmonicSum (cofiniteFlip (insert p F)) N| := by
                rw [abs_mul, abs_of_pos hp0]
              _ = _ := congrArg abs he
              _ ≤ |(p : ℝ) * gaugeHarmonicSum (cofiniteFlip F) N| +
                  |gaugeHarmonicSum (cofiniteFlip F) (N / p)| +
                    |gaugeHarmonicSum (cofiniteFlip (insert p F)) (N / p)| :=
                (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
              _ ≤ (p : ℝ) * (2 / finiteFlipHarmonicDensity F) +
                  2 / finiteFlipHarmonicDensity F +
                    2 / finiteFlipHarmonicDensity (insert p F) := by
                apply add_le_add (add_le_add ?_ (ih hF' (N / p))) hsmall
                rw [abs_mul, abs_of_pos hp0]
                exact mul_le_mul_of_nonneg_left (ih hF' N) hp0.le
              _ = _ := by ring
          rw [← hbalance] at hb
          exact le_of_mul_le_mul_left hb hp0

/-- Every cofinite prime flip has greatest hyperplane gap exactly zero. -/
theorem isGreatest_cofiniteFlip_hyperplaneGap {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) : IsGreatest {g | HasHyperplaneGap (cofiniteFlip F) g} 0 := by
  refine ⟨hasHyperplaneGap_zero_of_mul_self_eq_one (cofiniteFlip_mul_self F), fun g hg => ?_⟩
  by_contra h
  exact not_hasHyperplaneGap_of_abs_harmonicSum_le (cofiniteFlip_mul_self F)
    (cofiniteFlip_harmonicSum_abs_le hF) (not_le.mp h) hg

/-- Cofinite flips have zero harmonic correlation with the untwisted pole. -/
theorem cofiniteFlip_harmonicCorrelation_tendsto {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (harmonicCorrelation (cofiniteFlip F)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hlog.eventually_gt_atTop ((2 / finiteFlipHarmonicDensity F) / ε))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hH := gaugeHarmonicSum_one_pos hN1
  have hlarge : (2 / finiteFlipHarmonicDensity F) / ε < gaugeHarmonicSum (fun _ => 1) N :=
    (hN₀ N ((le_max_right _ _).trans hN)).trans_le (log_le_gaugeHarmonicSum_one hN1)
  have hsmall : (2 / finiteFlipHarmonicDensity F) / gaugeHarmonicSum (fun _ => 1) N < ε := by
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hH]
    nlinarith only [hlarge]
  rw [Real.dist_eq, sub_zero, harmonicCorrelation, abs_div, abs_of_pos hH]
  exact (div_le_div_of_nonneg_right (cofiniteFlip_harmonicSum_abs_le hF N) hH.le).trans_lt hsmall

/-- Harmonic squared distance from a finite prime flip to Liouville. -/
def finiteFlipLiouvilleDistanceSq (F : Finset ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, (finiteFlip F n - liouvilleSign n) ^ 2 / n) /
    gaugeHarmonicSum (fun _ => 1) N

/-- The distance is twice the missing cofinite harmonic correlation. -/
theorem finiteFlipLiouvilleDistanceSq_eq (F : Finset ℕ) {N : ℕ} (hN : 1 ≤ N) :
    finiteFlipLiouvilleDistanceSq F N = 2 - 2 * harmonicCorrelation (cofiniteFlip F) N := by
  have hH := (gaugeHarmonicSum_one_pos hN).ne'
  have he (n : ℕ) : (finiteFlip F n - liouvilleSign n) ^ 2 / (n : ℝ) =
      2 * (1 / (n : ℝ)) - 2 * (cofiniteFlip F n / n) := by
    have hs : (finiteFlip F n - liouvilleSign n) ^ 2 = 2 - 2 * cofiniteFlip F n := by
      dsimp only [cofiniteFlip]
      nlinarith only [finiteFlip_square F n, liouvilleSign_mul_self n]
    rw [hs]
    ring
  rw [finiteFlipLiouvilleDistanceSq, sum_congr rfl (fun n _ => he n),
    sum_sub_distrib, ← mul_sum, ← mul_sum]
  change (2 * gaugeHarmonicSum (fun _ => 1) N - 2 * gaugeHarmonicSum (cofiniteFlip F) N) /
      gaugeHarmonicSum (fun _ => 1) N = _
  rw [harmonicCorrelation]
  field_simp [hH]

/-- The harmonic distance approaches two with an explicit error at every positive horizon. -/
theorem finiteFlipLiouvilleDistanceSq_error_le {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    |finiteFlipLiouvilleDistanceSq F N - 2| ≤
      4 / (finiteFlipHarmonicDensity F * gaugeHarmonicSum (fun _ => 1) N) := by
  have hH := gaugeHarmonicSum_one_pos hN
  rw [finiteFlipLiouvilleDistanceSq_eq F hN,
    show 2 - 2 * harmonicCorrelation (cofiniteFlip F) N - 2 =
      -(2 * harmonicCorrelation (cofiniteFlip F) N) by ring,
    abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    harmonicCorrelation, abs_div, abs_of_pos hH]
  calc
    _ ≤ 2 * ((2 / finiteFlipHarmonicDensity F) / gaugeHarmonicSum (fun _ => 1) N) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (cofiniteFlip_harmonicSum_abs_le hF N) hH.le) (by norm_num)
    _ = _ := by ring

/-- Every fixed finite prime flip has limiting harmonic squared distance two from Liouville. -/
theorem tendsto_finiteFlipLiouvilleDistanceSq {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (finiteFlipLiouvilleDistanceSq F) atTop (𝓝 2) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub
    ((cofiniteFlip_harmonicCorrelation_tendsto hF).const_mul 2)
  have hlim : Tendsto (fun N => 2 - 2 * harmonicCorrelation (cofiniteFlip F) N) atTop (𝓝 2) := by
    simpa only [mul_zero, sub_zero] using h
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (finiteFlipLiouvilleDistanceSq_eq F hN).symm

/-- At any fixed horizon, sufficiently large prime cutoffs give distance exactly zero. -/
theorem finitePrimeExhaustion_distance_eventually_zero (N : ℕ) :
    ∀ᶠ Q : ℕ in atTop, finiteFlipLiouvilleDistanceSq (Nat.primesBelow Q) N = 0 := by
  filter_upwards [eventually_gt_atTop N] with Q hQ
  rw [finiteFlipLiouvilleDistanceSq]
  have hz : ∑ n ∈ Icc 1 N,
      (finiteFlip (Nat.primesBelow Q) n - liouvilleSign n) ^ 2 / (n : ℝ) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [finiteFlip_primesBelow_eq_liouville ((mem_Icc.mp hn).2.trans_lt hQ), sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
  rw [hz, zero_div]

/-- The horizon-first and prime-cutoff-first harmonic limits are two and zero. -/
theorem finitePrimeExhaustion_two_harmonic_limits :
    (∀ Q : ℕ, Tendsto (finiteFlipLiouvilleDistanceSq (Nat.primesBelow Q)) atTop (𝓝 2)) ∧
      ∀ N : ℕ, Tendsto (fun Q => finiteFlipLiouvilleDistanceSq (Nat.primesBelow Q) N)
        atTop (𝓝 0) := by
  constructor
  · intro Q
    exact tendsto_finiteFlipLiouvilleDistanceSq fun p hp => (Nat.mem_primesBelow.mp hp).2
  · intro N
    apply tendsto_const_nhds.congr'
    filter_upwards [finitePrimeExhaustion_distance_eventually_zero N] with Q hQ
    exact hQ.symm

/-- Zero-gap cofinite flips nevertheless stabilize pointwise to the untwisted sign. -/
theorem cofinitePrimeExhaustion_eventually_eq_one (n : ℕ) :
    ∀ᶠ Q : ℕ in atTop, cofiniteFlip (Nat.primesBelow Q) n = 1 := by
  filter_upwards [finitePrimeExhaustion_eventually_eq_liouville n] with Q hQ
  rw [cofiniteFlip, hQ, liouvilleSign_mul_self]

end GaloisForLFunctions.ArithmeticCountingPositivity
