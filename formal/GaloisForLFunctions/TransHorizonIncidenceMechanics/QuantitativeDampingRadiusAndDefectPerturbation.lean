import GaloisForLFunctions.TransHorizonIncidenceMechanics.StrictMobiusMarginAndUniformDampingStability

/-!
# Quantitative damping radius on infinite radical fibers

Classical baseline: the exponential tangent inequality, finite coefficient ℓ¹
bounds, product perturbation algebra, and radical invariance of squarefree
truncated divisor sums. Observation baseline [TH10]: https://arxiv.org/abs/1009.5281;
shifted-correlation baseline [CMS16]: https://arxiv.org/abs/1612.03136.
The sum s_N(k)=Σ_{d∣k,d≤N}μ(d) is exactly D(n;a) in Helfgott–Thompson,
Proposition 3.2, https://doi.org/10.1007/s40993-022-00408-8.

Equivalent classical formulation: with c_ε(d)=μ(d)d^(−ε), ε≥0,
Σ_{d≤N}|c_ε(d)−μ(d)|≤ε N log N. For two bounded response paths of magnitude
at most B, uniform response error A changes an M-edge defect by at most 4MBA.
The six-horizon magnitude-two envelope therefore gives
|D_N(M;c_ε)−D_N(M;μ)|≤8MεNlog N whenever M+1<6(N+1).

The strict Möbius margin D_N(M;μ)≤−1 then yields the explicit radius
δ_N=1/(96N(N+1)log N)>0 for N≥2. Throughout 0≤ε≤δ_N, every nonempty prefix
with R_N(M+1)<6(N+1) has D_N(M;c_ε)≤−1/2. Reduction to finite radical
representatives and rough-prime comparison remove dependence on endpoint
height. All positive powers of a certified base share the same radius.

For prime p>5, N=6p−1, k=30p, the same interval ensures response at every
positive power k^m is at least 3/2 while its defect is at most −1/2. The base k
remains the first unit-envelope failure. This is a quantified separation of
endpoint amplitude from accumulated defect energy.

Classification: New formulation with known constituents individually labeled.
No optimality of the constant or radius order, no fixed-positive-ε asymptotic
claim, and no all-ε≥0 six-horizon defect theorem are asserted.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false


/-- [Known] Finite coefficient ℓ¹ distance bounds every divisor response difference. -/
theorem abs_sieveSeq_sub_le_coefficient_distance (N k : ℕ) (c b : ℕ → ℝ) :
    |sieveSeq N c k - sieveSeq N b k| ≤ ∑ d ∈ Icc 1 N, |c d - b d| := by
  unfold sieveSeq
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _))

/-- [Known] A bounded path's edge correlation defect has a uniform perturbation estimate. -/
theorem abs_edge_defect_sub_le {x y u v A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hu : |u| ≤ B) (hdx : |x - u| ≤ A) (hdy : |y - v| ≤ A) :
    |x * (y - x) - u * (v - u)| ≤ 4 * B * A := by
  have hxy : |y - x| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by linarith)
  have hd : |(y - v) - (x - u)| ≤ 2 * A :=
    (abs_sub _ _).trans (by linarith)
  calc
    |x * (y - x) - u * (v - u)| =
        |(x - u) * (y - x) + u * ((y - v) - (x - u))| := by congr 1; ring
    _ ≤ |(x - u) * (y - x)| + |u * ((y - v) - (x - u))| := abs_add_le _ _
    _ = |x - u| * |y - x| + |u| * |(y - v) - (x - u)| := by rw [abs_mul, abs_mul]
    _ ≤ A * (2 * B) + B * (2 * A) := by
      exact add_le_add (mul_le_mul hdx hxy (abs_nonneg _) hA)
        (mul_le_mul hu hd (abs_nonneg _) hB)
    _ = 4 * B * A := by ring

/-- [Known] Finite prefix defects are Lipschitz on bounded response paths. -/
theorem abs_prefix_defect_sub_le_of_response_bounds (N M : ℕ) (c b : ℕ → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N c j| ≤ B)
    (hb : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N b j| ≤ B)
    (hd : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N c j - sieveSeq N b j| ≤ A) :
    |sieveRenormalizedPrefixDefect N M c - sieveRenormalizedPrefixDefect N M b| ≤
      4 * M * B * A := by
  simp_rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Icc 1 M, |sieveSeq N c j * (sieveSeq N c (j + 1) - sieveSeq N c j) -
        sieveSeq N b j * (sieveSeq N b (j + 1) - sieveSeq N b j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Icc 1 M, 4 * B * A := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_Icc.mp hj
      have h0 : j ∈ Icc 1 (M + 1) := mem_Icc.mpr ⟨hj'.1, by omega⟩
      have h1 : j + 1 ∈ Icc 1 (M + 1) := mem_Icc.mpr ⟨by omega, by omega⟩
      exact abs_edge_defect_sub_le hA hB (hc j h0) (hc _ h1) (hb j h0) (hd j h0) (hd _ h1)
    _ = 4 * M * B * A := by simp; ring

/-- [Known] The exponential tangent bound controls a single damped coefficient. -/
theorem abs_pmPowerDamped_sub_moebius_le_log {ε : ℝ} (hε : 0 ≤ ε)
    {d : ℕ} (hd : 1 ≤ d) :
    |pmPowerDampedRealWeight ε d - moebiusReal d| ≤ ε * Real.log d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hl : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have he : Real.exp (Real.log d * -ε) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hl (neg_nonpos.mpr hε))
  have ht := Real.add_one_le_exp (Real.log d * -ε)
  have hm : |moebiusReal d| ≤ 1 := by
    simpa [pmPowerDampedRealWeight] using abs_pmPowerDampedRealWeight_le_one (le_refl (0 : ℝ)) d
  calc
    |pmPowerDampedRealWeight ε d - moebiusReal d| =
        |moebiusReal d| * (1 - Real.exp (Real.log d * -ε)) := by
      unfold pmPowerDampedRealWeight
      rw [Real.rpow_def_of_pos hd0]
      rw [← mul_sub_one, abs_mul, abs_of_nonpos (sub_nonpos.mpr he)]
      ring
    _ ≤ 1 - Real.exp (Real.log d * -ε) := by
      exact (mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr he)).trans_eq (one_mul _)
    _ ≤ ε * Real.log d := by nlinarith

/-- [Corollary] Total coefficient perturbation has an explicit horizon logarithmic bound. -/
theorem sum_abs_pmPowerDamped_sub_moebius_le {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    (∑ d ∈ Icc 1 N, |pmPowerDampedRealWeight ε d - moebiusReal d|) ≤
      ε * N * Real.log N := by
  calc
    _ ≤ ∑ _d ∈ Icc 1 N, ε * Real.log N := by
      apply sum_le_sum
      intro d hd
      have hd' := mem_Icc.mp hd
      exact (abs_pmPowerDamped_sub_moebius_le_log hε hd'.1).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log
          (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hd'.2)) hε)
    _ = ε * N * Real.log N := by simp; ring

/-- [Corollary] Damping perturbs every endpoint response by at most ε N log N. -/
theorem abs_sieveSeq_pmPowerDamped_sub_moebius_le {ε : ℝ} (hε : 0 ≤ ε) (N k : ℕ) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k - sieveSeq N moebiusReal k| ≤
      ε * N * Real.log N :=
  (abs_sieveSeq_sub_le_coefficient_distance N k _ _).trans
    (sum_abs_pmPowerDamped_sub_moebius_le hε N)

/-- [Known] Including the initial point preserves the six-horizon magnitude-two bound. -/
theorem abs_sieveSeq_pmPowerDamped_le_two_on_prefix {ε : ℝ} (hε : 0 ≤ ε)
    {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hhi : k < 6 * (N + 1)) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k| ≤ 2 := by
  by_cases hk2 : 2 ≤ k
  · exact abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_lt_six_succ hε hk2 hhi
  · have he : k = 1 := by omega
    subst k
    simp [sieveSeq, sum_filter, Nat.dvd_one, hN, pmPowerDampedRealWeight, moebiusReal]

/-- [New formulation] Six-horizon defect perturbation grows linearly in ε and the finite prefix length. -/
theorem abs_prefix_defect_pmPowerDamped_sub_moebius_le {ε : ℝ} (hε : 0 ≤ ε)
    {N M : ℕ} (hN : 1 ≤ N) (hhi : M + 1 < 6 * (N + 1)) :
    |sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) -
      sieveRenormalizedPrefixDefect N M moebiusReal| ≤ 8 * M * ε * N * Real.log N := by
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hb (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (hj : j ∈ Icc 1 (M + 1)) :
      |sieveSeq N (pmPowerDampedRealWeight η) j| ≤ 2 :=
    abs_sieveSeq_pmPowerDamped_le_two_on_prefix hη hN (mem_Icc.mp hj).1
      (lt_of_le_of_lt (mem_Icc.mp hj).2 hhi)
  have hzero : pmPowerDampedRealWeight 0 = moebiusReal := by
    funext d
    simp [pmPowerDampedRealWeight]
  have h := abs_prefix_defect_sub_le_of_response_bounds N M
    (pmPowerDampedRealWeight ε) moebiusReal
    (A := ε * N * Real.log N) (B := 2) (by positivity) (by norm_num)
    (hb ε hε) (by simpa only [hzero] using hb 0 (le_refl 0))
    (fun j _ => abs_sieveSeq_pmPowerDamped_sub_moebius_le hε N j)
  convert h using 1; ring

/-- [New formulation] An explicit horizon-dependent damping radius. -/
def sixHorizonDampingRadius (N : ℕ) : ℝ :=
  1 / (96 * N * ((N : ℝ) + 1) * Real.log N)

/-- [Corollary] The explicit radius is positive at every nontrivial horizon. -/
theorem sixHorizonDampingRadius_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < sixHorizonDampingRadius N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hl := Real.log_pos hNr
  unfold sixHorizonDampingRadius
  positivity

/-- [Corollary] Damping in the explicit interval obeys a finite coefficient-error budget. -/
theorem damping_radius_log_budget {N : ℕ} (hN : 2 ≤ N) {ε : ℝ}
    (hε : ε ≤ sixHorizonDampingRadius N) :
    96 * ((N : ℝ) + 1) * (ε * N * Real.log N) ≤ 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hl := Real.log_pos hNr
  have hp : 0 < 96 * (N : ℝ) * ((N : ℝ) + 1) * Real.log N := by positivity
  have h := (le_div_iff₀ hp).mp hε
  nlinarith

/-- [New formulation] The explicit damping interval certifies every finite six-horizon checkpoint. -/
theorem prefix_defect_pmPowerDamped_le_neg_half_of_explicit_radius
    {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M) (hhi : M + 1 < 6 * (N + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ sixHorizonDampingRadius N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have he := abs_prefix_defect_pmPowerDamped_sub_moebius_le hε (by omega : 1 ≤ N) hhi
  have h0 := moebius_prefix_defect_le_neg_one_of_lt_six_succ hN hM hhi
  have hbudget := damping_radius_log_budget hN hεhi
  have hMr : (M : ℝ) ≤ 6 * ((N : ℝ) + 1) := by
    exact_mod_cast (by omega : M ≤ 6 * (N + 1))
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hm := mul_le_mul_of_nonneg_right hMr (by positivity : 0 ≤ ε * N * Real.log N)
  have hd := (abs_le.mp he).2
  nlinarith

/-- [New formulation] The explicit interval controls all certified radical fibers, including rough endpoints. -/
theorem radical_defect_pmPowerDamped_le_neg_half_of_explicit_radius
    {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ sixHorizonDampingRadius N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have hc (k : ℕ) (hk : 2 ≤ k) (hkN : k < 6 * (N + 1)) :
      sieveRenormalizedPrefixDefect N (k - 1) (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) :=
    prefix_defect_pmPowerDamped_le_neg_half_of_explicit_radius hN
      (by omega) (by omega) hε hεhi
  by_cases hk : M + 1 < 6 * (N + 1)
  · exact prefix_defect_pmPowerDamped_le_neg_half_of_explicit_radius hN hM hk hε hεhi
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
    exact hd.trans (hc p (by omega) (by omega))
  · have hd := sieveRenormalizedPrefixDefect_le_horizonRadicalState N
      (by omega : 1 ≤ M + 1) (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)
    simp only [Nat.add_sub_cancel] at hd
    exact hd.trans (hc _ (by omega) hrN)

/-- [Corollary] Every positive power of a certified base shares the explicit damping interval. -/
theorem power_defect_pmPowerDamped_le_neg_half_of_explicit_radius
    {N k m : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k < 6 * (N + 1)) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ sixHorizonDampingRadius N) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have hpow := sieveRenormalizedPrefixDefect_pow_antitone N
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε) hk (le_refl 1) hm
  simp only [pow_one] at hpow
  exact hpow.trans (prefix_defect_pmPowerDamped_le_neg_half_of_explicit_radius hN
    (by omega) (by omega) hε hεhi)

/-- [Corollary] The explicit defect radius also controls every response, with no endpoint restriction. -/
theorem response_error_le_of_explicit_damping_radius {N : ℕ} (hN : 2 ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ sixHorizonDampingRadius N) (k : ℕ) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k - sieveSeq N moebiusReal k| ≤
      1 / (96 * ((N : ℝ) + 1)) := by
  apply (abs_sieveSeq_pmPowerDamped_sub_moebius_le hε N k).trans
  apply (le_div_iff₀ (by positivity : 0 < 96 * ((N : ℝ) + 1))).mpr
  nlinarith [damping_radius_log_budget hN hεhi]

/-- [New formulation] An explicit damping interval separates unit-envelope failure from negative defect. -/
theorem explicit_damping_counterfamily_power_separation {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) {ε : ℝ} (hε : 0 ≤ ε)
    (hεhi : ε ≤ sixHorizonDampingRadius (6 * p - 1)) {m : ℕ} (hm : 1 ≤ m) :
    (3 / 2 : ℝ) ≤ sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) ((30 * p) ^ m) ∧
      sieveRenormalizedPrefixDefect (6 * p - 1) ((30 * p) ^ m - 1)
        (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have hN : 2 ≤ 6 * p - 1 := by omega
  constructor
  · rw [sieveSeq_pmPowerDampedRealWeight_pow ε (6 * p - 1) (30 * p) hm]
    have he := response_error_le_of_explicit_damping_radius hN hε hεhi (30 * p)
    rw [sieveSeq_moebiusReal_five_horizon_counterfamily hp h5] at he
    have hb : 1 / (96 * (((6 * p - 1 : ℕ) : ℝ) + 1)) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 96 * (((6 * p - 1 : ℕ) : ℝ) + 1))).mpr
      have hn : (0 : ℝ) ≤ ((6 * p - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hlo := (abs_le.mp he).1
    linarith
  · exact power_defect_pmPowerDamped_le_neg_half_of_explicit_radius hN
      (by omega) (by omega) hm hε hεhi

/-- [Corollary] Positive damping in the explicit interval retains the family's first unit-envelope failure. -/
theorem explicit_damping_counterfamily_first_failure {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) {ε : ℝ} (hε : 0 ≤ ε)
    (hεhi : ε ≤ sixHorizonDampingRadius (6 * p - 1)) :
    (∀ j : ℕ, 2 ≤ j → j < 30 * p →
      |sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) j| ≤ 1) ∧
      1 < sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) (30 * p) := by
  constructor
  · intro j hj hjhi
    exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hj (by omega)
  · have h := (explicit_damping_counterfamily_power_separation hp h5 hε hεhi (le_refl 1)).1
    simp only [pow_one] at h
    linarith

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
