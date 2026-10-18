import GaloisForLFunctions.TransHorizonIncidenceMechanics.IntegerJumpEnergyAndBeyondEnvelopeDefect
import Mathlib.NumberTheory.Bertrand

/-!
# Strict Möbius margin and damping stability on infinite radical fibers

Classical baseline: Bertrand's postulate, integer total variation, discrete
polarization, finite-sum continuity, and radical invariance. The observation and
shifted-correlation baselines are [TH10] https://arxiv.org/abs/1009.5281 and
[CMS16] https://arxiv.org/abs/1612.03136. The truncated divisor sum is exactly
D(n;a) in Helfgott–Thompson, Proposition 3.2, https://doi.org/10.1007/s40993-022-00408-8.

Equivalent classical formulation: write s_N(k)=Σ_{d∣k,d≤N}μ(d). For N≥2,
choose a prime N<p≤2N. The values at 1,2,p,2p are 1,0,1,0. Their integer
jump energy pays at least 3+|s_N(M+1)| whenever M+1≥4N. Together with the
known small-endpoint envelope, this upgrades |s_N(M+1)|≤2 to D_N(M)≤−1
for every N≥2 and M≥1.

Finite continuous dependence on ε gives one δ_N>0 for all base checkpoints
2≤k<6(N+1). Radical and equal-response energy monotonicity transfer the same
interval |ε|<δ_N to infinitely many endpoints: for N≥2,M≥1 and
R_N(M+1)<6(N+1), D_N(M;c_ε)<−1/2. Empty prefixes and N≤1 have zero defect.
Every positive power of every certified base shares the interval, independently
of exponent. The response-two prime family has a positive damping interval on
which its response stays above one while all its power defects stay negative.

Continuity also shows that excluding ε=0 does not improve a unit envelope
required uniformly for every ε>0: the real ratio remains C≤5 and the real
additive buffer remains b<5. No classification for each fixed positive ε, no
explicit δ_N, and no all-ε defect theorem are asserted.

Classification: New formulation, with known constituents labeled; no external
novelty or priority claim. All results are proved over general parameters.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- [Known] Integer path displacement is controlled on any finite interval. -/
theorem integer_path_abs_sub_le_sum_Icc (f : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b + 1) :
    |(f (b + 1) : ℝ) - f a| ≤
      ∑ j ∈ Icc a b, ((f (j + 1) : ℝ) - f j) ^ (2 : ℕ) := by
  have h := integer_path_abs_sub_le_sum_sq f a (b + 1 - a)
  have he : a + (b + 1 - a) = b + 1 := by omega
  rw [he] at h
  have hi : Icc a b = Ico a (b + 1) := by
    ext j
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hi, Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

private theorem sum_Icc_split (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c + 1) (hb : 1 ≤ b) :
    (∑ j ∈ Icc a c, f j) = (∑ j ∈ Icc a (b - 1), f j) + ∑ j ∈ Icc b c, f j := by
  have hs : Icc a c = Icc a (b - 1) ∪ Icc b c := by
    ext j
    simp only [mem_Icc, mem_union]
    omega
  rw [hs, sum_union]
  rw [disjoint_left]
  intro j hj hk
  simp only [mem_Icc] at hj hk
  omega

/-- [Known] A completed zero-one-zero excursion adds two units of energy. -/
theorem integer_prefix_energy_of_zero_one_zero (f : ℕ → ℤ)
    (h1 : f 1 = 1) (h2 : f 2 = 0) {p q M : ℕ}
    (hp : 2 ≤ p) (hpq : p ≤ q) (hqM : q ≤ M + 1)
    (hfp : f p = 1) (hfq : f q = 0) :
    3 + |(f (M + 1) : ℝ)| ≤
      ∑ j ∈ Icc 1 M, ((f (j + 1) : ℝ) - f j) ^ (2 : ℕ) := by
  have hA := integer_prefix_energy_of_first_zero f h1 h2 (M := p - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p), hfp] at hA
  have hB := integer_path_abs_sub_le_sum_Icc f (a := p) (b := q - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q), hfp, hfq] at hB
  have hC := integer_path_abs_sub_le_sum_Icc f hqM
  rw [hfq] at hC
  rw [sum_Icc_split _ (b := p) (by omega) (by omega) (by omega),
    sum_Icc_split _ (a := p) (b := q) (by omega) hqM (by omega)]
  norm_num at hA hB hC
  linarith

/-- [New formulation] A rough prime and its double force an extra Möbius energy excursion. -/
theorem moebius_prefix_energy_ge_three_add_abs {N M : ℕ}
    (hN : 2 ≤ N) (hM : 4 * N ≤ M + 1) :
    3 + |sieveSeq N moebiusReal (M + 1)| ≤
      ∑ j ∈ Icc 1 M, (sieveSeq N moebiusReal (j + 1) -
        sieveSeq N moebiusReal j) ^ (2 : ℕ) := by
  obtain ⟨p, hp, hNp, hpN⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hr := isTransHorizonRough_of_prime_gt hp hNp
  let f : ℕ → ℤ := fun k => ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ k), μ d
  have hf (k : ℕ) : (f k : ℝ) = sieveSeq N moebiusReal k :=
    (sieveSeq_moebiusReal_eq_intCast N k).symm
  have h1 : (f 1 : ℝ) = 1 := by
    rw [hf, sieveSeq_moebiusReal_eq_ite_of_le (by omega) (by omega), if_pos rfl]
  have h2 : (f 2 : ℝ) = 0 := by
    rw [hf, sieveSeq_moebiusReal_eq_ite_of_le (by omega) hN, if_neg (by omega)]
  have hfp : (f p : ℝ) = 1 := by
    rw [hf, sieveSeq_of_isTransHorizonRough hr, ← hf, h1]
  have hfq : (f (2 * p) : ℝ) = 0 := by
    rw [hf, sieveSeq_moebiusReal_mul_eq_zero_of_isTransHorizonRough (le_refl 2) hN hr]
  simpa only [hf] using integer_prefix_energy_of_zero_one_zero f
    (by exact_mod_cast h1) (by exact_mod_cast h2) (p := p) (q := 2 * p)
    (by omega) (by omega) (by omega) (by exact_mod_cast hfp) (by exact_mod_cast hfq)

/-- [New formulation] Every nonempty magnitude-two Möbius checkpoint has a strict unit defect margin. -/
theorem moebius_prefix_defect_le_neg_one_of_abs_le_two {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hb : |sieveSeq N moebiusReal (M + 1)| ≤ 2) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ -1 := by
  by_cases hsmall : M + 1 ≤ 4 * N
  · apply moebius_prefix_defect_le_neg_one_of_abs_le_one hN hM
    have h := abs_sieveSeq_moebiusReal_le_one_of_le_five_mul (N := N) (by omega) (by omega : M + 1 ≤ 5 * N)
    exact h
  · have hE := moebius_prefix_energy_ge_three_add_abs hN (M := M) (by omega)
    have hp := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM moebiusReal
    rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega : 1 ≤ 1) (by omega : 1 ≤ N), if_pos rfl,
      one_pow] at hp
    have ht := mul_nonneg (abs_nonneg (sieveSeq N moebiusReal (M + 1))) (sub_nonneg.mpr hb)
    nlinarith [sq_abs (sieveSeq N moebiusReal (M + 1))]


/-- [Corollary] All nonempty six-horizon Möbius prefixes have the strict margin. -/
theorem moebius_prefix_defect_le_neg_one_of_lt_six_succ {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hhi : M + 1 < 6 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ -1 :=
  moebius_prefix_defect_le_neg_one_of_abs_le_two hN hM
    (abs_sieveSeq_moebiusReal_le_two_of_lt_six_succ (by omega) hhi)

/-- [Known] Each damped coefficient is continuous, including the identically zero index-zero coefficient. -/
theorem continuous_pmPowerDampedRealWeight (d : ℕ) :
    Continuous (fun ε : ℝ => pmPowerDampedRealWeight ε d) := by
  by_cases hd : d = 0
  · subst d
    simp [pmPowerDampedRealWeight, moebiusReal]
    exact continuous_const
  · unfold pmPowerDampedRealWeight
    exact continuous_const.mul ((Real.continuous_const_rpow (by exact_mod_cast hd)).comp continuous_neg)

/-- [Known] Every finite-horizon response depends continuously on damping. -/
theorem continuous_sieveSeq_pmPowerDampedRealWeight (N k : ℕ) :
    Continuous (fun ε : ℝ => sieveSeq N (pmPowerDampedRealWeight ε) k) := by
  unfold sieveSeq
  exact continuous_finsetSum _ fun d _ => continuous_pmPowerDampedRealWeight d

/-- [Known] Every finite prefix defect depends continuously on damping. -/
theorem continuous_sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight (N M : ℕ) :
    Continuous (fun ε : ℝ => sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε)) := by
  simp_rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_sieveSeq_pmPowerDampedRealWeight N k).mul
      ((continuous_sieveSeq_pmPowerDampedRealWeight N (k + 1)).sub
        (continuous_sieveSeq_pmPowerDampedRealWeight N k))

private theorem zero_damping_weight : pmPowerDampedRealWeight 0 = moebiusReal := by
  funext d
  simp [pmPowerDampedRealWeight]

/-- [New formulation] All certified finite checkpoints share one bilateral damping interval. -/
theorem exists_uniform_damping_radius_finite_checkpoints {N : ℕ} (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ k : ℕ, 2 ≤ k → k < 6 * (N + 1) →
      sieveRenormalizedPrefixDefect N (k - 1) (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ) := by
  have he : ∀ᶠ ε : ℝ in nhds 0, ∀ k ∈ Icc 2 (6 * (N + 1) - 1),
      sieveRenormalizedPrefixDefect N (k - 1) (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ) := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hk' := mem_Icc.mp hk
    have h0 : sieveRenormalizedPrefixDefect N (k - 1) (pmPowerDampedRealWeight 0) < -(1 / 2 : ℝ) := by
      rw [zero_damping_weight]
      have hm := moebius_prefix_defect_le_neg_one_of_lt_six_succ hN
        (M := k - 1) (by omega) (by omega)
      linarith
    exact (continuous_sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight N (k - 1)).continuousAt.eventually
      (eventually_lt_nhds h0)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε k hk hkN
  exact hd (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε) k
    (mem_Icc.mpr ⟨hk, by omega⟩)

/-- [Corollary] The same interval controls every endpoint in the nontrivial certified radical fibers. -/
theorem exists_uniform_damping_radius_radical_margin {N : ℕ} (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ k : ℕ, 1 ≤ k →
      2 ≤ horizonRadicalState N k → horizonRadicalState N k < 6 * (N + 1) →
      sieveRenormalizedPrefixDefect N (k - 1) (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hc⟩ := exists_uniform_damping_radius_finite_checkpoints hN
  refine ⟨δ, hδ, ?_⟩
  intro ε hε k hk hr hrN
  exact (sieveRenormalizedPrefixDefect_le_horizonRadicalState N hk
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)).trans_lt
      (hc ε hε _ hr hrN)


/-- [New formulation] Rough-prime comparison extends the strict margin to all certified nonempty prefixes. -/
theorem exists_uniform_damping_radius_all_certified_margin {N : ℕ} (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ M : ℕ, 1 ≤ M →
      horizonRadicalState N (M + 1) < 6 * (N + 1) →
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hc⟩ := exists_uniform_damping_radius_finite_checkpoints hN
  refine ⟨δ, hδ, ?_⟩
  intro ε hε M hM hrN
  by_cases hk : M + 1 < 6 * (N + 1)
  · simpa only [Nat.add_sub_cancel] using hc ε hε (M + 1) (by omega) hk
  have hr := horizonRadicalState_pos N (M + 1)
  by_cases hr1 : horizonRadicalState N (M + 1) = 1
  · obtain ⟨p, hp, hNp, hpN⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
    have heq : sieveSeq N (pmPowerDampedRealWeight ε) (M + 1) =
        sieveSeq N (pmPowerDampedRealWeight ε) p := by
      rw [← sieveSeq_horizonRadicalState N (M + 1)
        (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε), hr1,
        sieveSeq_prime_of_gt hp hNp]
    have hd := sieveRenormalizedPrefixDefect_le_of_sieveSeq_eq N (pmPowerDampedRealWeight ε)
      (by omega : 2 ≤ p) (by omega : p ≤ M + 1) heq
    simp only [Nat.add_sub_cancel] at hd
    exact hd.trans_lt (hc ε hε p (by omega) (by omega))
  · have hd := sieveRenormalizedPrefixDefect_le_horizonRadicalState N
      (by omega : 1 ≤ M + 1) (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)
    simp only [Nat.add_sub_cancel] at hd
    exact hd.trans_lt (hc ε hε _ (by omega) hrN)

/-- [Corollary] Every horizon has a damping interval uniform over all certified prefixes. -/
theorem exists_uniform_damping_radius_all_certified_prefixes (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ M : ℕ,
      horizonRadicalState N (M + 1) < 6 * (N + 1) →
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  by_cases hN : 2 ≤ N
  · obtain ⟨δ, hδ, hc⟩ := exists_uniform_damping_radius_all_certified_margin hN
    refine ⟨δ, hδ, ?_⟩
    intro ε hε M hrN
    by_cases hM : M = 0
    · subst M
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
    · have hd := hc ε hε M (by omega) hrN
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro ε _ M _
    have hs : N = 0 ∨ N = 1 := by omega
    rcases hs with rfl | rfl <;>
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff, sieveSeq, sum_filter,
        pmPowerDampedRealWeight, moebiusReal]

/-- [New formulation] A single interval certifies every positive power, independently of exponent. -/
theorem exists_uniform_damping_radius_power_margin {N : ℕ} (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ k m : ℕ,
      2 ≤ k → k < 6 * (N + 1) → 1 ≤ m →
      sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hc⟩ := exists_uniform_damping_radius_finite_checkpoints hN
  refine ⟨δ, hδ, ?_⟩
  intro ε hε k m hk hkN hm
  have hpow := sieveRenormalizedPrefixDefect_pow_antitone N
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε) hk (le_refl 1) hm
  simp only [pow_one] at hpow
  exact hpow.trans_lt (hc ε hε k hk hkN)


/-- [New formulation] Positive damping preserves envelope failure together with strict defect negativity. -/
theorem exists_damping_radius_counterfamily_power_separation {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ m : ℕ, 1 ≤ m →
      1 < sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) ((30 * p) ^ m) ∧
      sieveRenormalizedPrefixDefect (6 * p - 1) ((30 * p) ^ m - 1)
        (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hc⟩ := exists_uniform_damping_radius_power_margin (by omega : 2 ≤ 6 * p - 1)
  have h0 : 1 < sieveSeq (6 * p - 1) (pmPowerDampedRealWeight 0) (30 * p) := by
    rw [zero_damping_weight, sieveSeq_moebiusReal_five_horizon_counterfamily hp h5]
    norm_num
  have he : ∀ᶠ ε : ℝ in nhds 0,
      1 < sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) (30 * p) :=
    (continuous_sieveSeq_pmPowerDampedRealWeight (6 * p - 1) (30 * p)).continuousAt.eventually
      (eventually_gt_nhds h0)
  obtain ⟨η, hη, hηc⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro ε hε m hm
  have hε' := lt_min_iff.mp hε
  constructor
  · rw [sieveSeq_pmPowerDampedRealWeight_pow ε (6 * p - 1) (30 * p) hm]
    exact hηc (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε'.2)
  · exact hc ε hε'.1 (30 * p) m (by omega) (by omega) hm


/-- [Known] Uniform strictly positive damping bounds pass to the undamped response by continuity. -/
theorem sieveSeq_moebiusReal_abs_le_of_positive_damping (N k : ℕ) (B : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ B) :
    |sieveSeq N moebiusReal k| ≤ B := by
  by_contra hn
  have h0 : B < |sieveSeq N (pmPowerDampedRealWeight 0) k| := by
    rw [zero_damping_weight]
    exact lt_of_not_ge hn
  have he : ∀ᶠ ε : ℝ in nhds 0,
      B < |sieveSeq N (pmPowerDampedRealWeight ε) k| :=
    (continuous_sieveSeq_pmPowerDampedRealWeight N k).abs.continuousAt.eventually
      (eventually_gt_nhds h0)
  obtain ⟨δ, hδ, hc⟩ := Metric.mem_nhds_iff.mp he
  have hpos : 0 < δ / 2 := by linarith
  have hdist : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith
  exact (not_lt_of_ge (h (δ / 2) hpos)) (hc hdist)

/-- [New formulation] The sharp universal ratio remains five when damping must be strictly positive. -/
theorem forall_positive_pmPowerDamped_unit_envelope_iff_ratio_le_five (C : ℝ) :
    (∀ (ε : ℝ) (N k : ℕ), 0 < ε → 2 ≤ k → (k : ℝ) ≤ C * N →
      |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ C ≤ 5 := by
  constructor
  · intro h
    apply (forall_moebiusReal_unit_envelope_iff_ratio_le_five C).mp
    intro N k hk hhi
    exact sieveSeq_moebiusReal_abs_le_of_positive_damping N k 1
      (fun ε hε => h ε N k hε hk hhi)
  · intro hC ε N k hε hk hhi
    exact (forall_pmPowerDamped_unit_envelope_iff_ratio_le_five C).mpr hC
      ε N k hε.le hk hhi

/-- [New formulation] The sharp universal additive buffer is unchanged after excluding zero damping. -/
theorem forall_positive_pmPowerDamped_unit_envelope_iff_additive_lt_five (b : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∀ N k : ℕ, 2 ≤ k → (k : ℝ) ≤ 5 * N + b →
      |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ b < 5 := by
  constructor
  · intro h
    apply (forall_moebiusReal_unit_envelope_iff_additive_lt_five b).mp
    intro N k hk hhi
    exact sieveSeq_moebiusReal_abs_le_of_positive_damping N k 1
      (fun ε hε => h ε hε N k hk hhi)
  · intro hb ε hε N k hk hhi
    exact (forall_pmPowerDamped_unit_envelope_iff_additive_lt_five b).mpr hb
      ε hε.le N k hk hhi

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
