import GaloisForLFunctions.TransHorizonIncidenceMechanics.QuantitativeDampingRadiusAndDefectPerturbation
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Divisor-incidence perturbation and logarithmic damping stability

Classical baseline: finite-sum triangle inequalities, exact divisor-incidence
floor reciprocity, product perturbation, and the harmonic bound H_N≤1+log N.
The observation baseline is [TH10] https://arxiv.org/abs/1009.5281 and the
shifted-correlation baseline is [CMS16] https://arxiv.org/abs/1612.03136.

Equivalent classical formulation: write s_c(j)=Σ_{d∣j,d≤N}c(d) and
D_c(M)=Σ_{j=1}^M s_c(j)(s_c(j+1)−s_c(j)). If |s_c|,|s_b|≤B on the prefix,
then |D_c(M)−D_b(M)|≤4B Σ_{d≤N}|c(d)−b(d)| floor((M+1)/d).
Thus perturbations are charged at their actual divisor incidences, without
requiring periodic averaging or squarefree support.

For c_ε(d)=μ(d)d^(−ε), ε≥0, the unit coefficient is unchanged. Removing it
before applying the harmonic bound gives Σ_{d≤N}log(d)/d≤(log N)². Combined
with the six-horizon magnitude-two envelope, this yields
|D_ε(M)−D_0(M)|≤8ε(M+1)(log N)² when M+1<6(N+1).

For N≥2, the explicit radius δ_N=1/(96(N+1)(log N)²)>0 gives D_ε(M)≤−1/2
for every nonempty prefix whose endpoint radical R_N(M+1)<6(N+1), throughout
0≤ε≤δ_N. A general finite-certificate transfer law handles infinite radical
fibers and rough endpoints. The radius strictly enlarges 1/(96N(N+1)log N).
All positive powers of a finite certified base share the same interval.

For prime p>5, N=6p−1 and k=30p, every positive power k^m has response at
least 31/16 and defect at most −1/2 on the larger interval. The base k remains
the first unit-envelope failure. Classification: New formulation with known
constituents labeled; no external priority claim, no optimality assertion,
and no all-ε≥0 defect theorem.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false


/-- [Known] A response difference is bounded by the response of absolute coefficient differences. -/
theorem abs_sieveSeq_sub_le_sieveSeq_abs_sub (N k : ℕ) (c b : ℕ → ℝ) :
    |sieveSeq N c k - sieveSeq N b k| ≤ sieveSeq N (fun d => |c d - b d|) k := by
  unfold sieveSeq
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

/-- [Known] Summed response error is charged only at actual divisor incidences. -/
theorem sum_abs_sieveSeq_sub_le_divisor_incidence (N K : ℕ) (c b : ℕ → ℝ) :
    (∑ j ∈ Icc 1 K, |sieveSeq N c j - sieveSeq N b j|) ≤
      ∑ d ∈ Icc 1 N, |c d - b d| * ((K / d : ℕ) : ℝ) := by
  rw [sum_mul_nat_div_eq_sum_sieveSeq]
  exact sum_le_sum (fun j _ => abs_sieveSeq_sub_le_sieveSeq_abs_sub N j c b)

/-- [Known] Edge perturbation admits separate charges for its two endpoint errors. -/
theorem abs_edge_defect_sub_le_endpoint_errors {x y u v B : ℝ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) (hu : |u| ≤ B) :
    |x * (y - x) - u * (v - u)| ≤ B * (3 * |x - u| + |y - v|) := by
  have hxy : |y - x| ≤ 2 * B := (abs_sub _ _).trans (by linarith)
  have hd : |(y - v) - (x - u)| ≤ |y - v| + |x - u| := abs_sub _ _
  calc
    _ = |(x - u) * (y - x) + u * ((y - v) - (x - u))| := by congr 1; ring
    _ ≤ |(x - u) * (y - x)| + |u * ((y - v) - (x - u))| := abs_add_le _ _
    _ = |x - u| * |y - x| + |u| * |(y - v) - (x - u)| := by rw [abs_mul, abs_mul]
    _ ≤ |x - u| * (2 * B) + B * (|y - v| + |x - u|) :=
      add_le_add (mul_le_mul_of_nonneg_left hxy (abs_nonneg _))
        (mul_le_mul hu hd (abs_nonneg _) hB)
    _ = B * (3 * |x - u| + |y - v|) := by ring

private theorem sum_shift_le_sum_succ (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (M : ℕ) :
    (∑ j ∈ Icc 1 M, a (j + 1)) ≤ ∑ j ∈ Icc 1 (M + 1), a j := by
  induction M with
  | zero => simpa using ha 1
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ M + 1),
      sum_Icc_succ_top (by omega : 1 ≤ M + 1 + 1)]
    exact add_le_add ih (le_refl _)

/-- [New formulation] Prefix defect stability is controlled by aggregate response error. -/
theorem abs_prefix_defect_sub_le_sum_response_errors (N M : ℕ) (c b : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N c j| ≤ B)
    (hb : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N b j| ≤ B) :
    |sieveRenormalizedPrefixDefect N M c - sieveRenormalizedPrefixDefect N M b| ≤
      4 * B * ∑ j ∈ Icc 1 (M + 1), |sieveSeq N c j - sieveSeq N b j| := by
  let a : ℕ → ℝ := fun j => |sieveSeq N c j - sieveSeq N b j|
  have ha (j : ℕ) : 0 ≤ a j := abs_nonneg _
  have h0 : (∑ j ∈ Icc 1 M, a j) ≤ ∑ j ∈ Icc 1 (M + 1), a j :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (by omega)) (fun j _ _ => ha j)
  have h1 := sum_shift_le_sum_succ a ha M
  simp_rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Icc 1 M, |sieveSeq N c j * (sieveSeq N c (j + 1) - sieveSeq N c j) -
        sieveSeq N b j * (sieveSeq N b (j + 1) - sieveSeq N b j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Icc 1 M, B * (3 * a j + a (j + 1)) := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_Icc.mp hj
      have h0 : j ∈ Icc 1 (M + 1) := mem_Icc.mpr ⟨hj'.1, by omega⟩
      have h1 : j + 1 ∈ Icc 1 (M + 1) := mem_Icc.mpr ⟨by omega, by omega⟩
      exact abs_edge_defect_sub_le_endpoint_errors hB (hc j h0) (hc _ h1) (hb j h0)
    _ = B * (3 * (∑ j ∈ Icc 1 M, a j) + ∑ j ∈ Icc 1 M, a (j + 1)) := by
      rw [← mul_sum, sum_add_distrib, ← mul_sum]
    _ ≤ 4 * B * ∑ j ∈ Icc 1 (M + 1), a j := by
      have h := mul_le_mul_of_nonneg_left (show 3 * (∑ j ∈ Icc 1 M, a j) +
        (∑ j ∈ Icc 1 M, a (j + 1)) ≤ 4 * ∑ j ∈ Icc 1 (M + 1), a j by linarith) hB
      nlinarith

/-- [New formulation] A finite divisor-incidence norm controls every bounded prefix defect. -/
theorem abs_prefix_defect_sub_le_divisor_incidence (N M : ℕ) (c b : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N c j| ≤ B)
    (hb : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N b j| ≤ B) :
    |sieveRenormalizedPrefixDefect N M c - sieveRenormalizedPrefixDefect N M b| ≤
      4 * B * ∑ d ∈ Icc 1 N, |c d - b d| * (((M + 1) / d : ℕ) : ℝ) :=
  (abs_prefix_defect_sub_le_sum_response_errors N M c b hB hc hb).trans
    (mul_le_mul_of_nonneg_left (sum_abs_sieveSeq_sub_le_divisor_incidence N (M + 1) c b)
      (by positivity))

/-- [Known] Removing the unit divisor sharpens the logarithmic harmonic budget. -/
theorem sum_log_div_le_log_sq {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Icc 1 N, Real.log d / d) ≤ (Real.log N) ^ (2 : ℕ) := by
  have hmem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hH : (∑ d ∈ Icc 1 N, (d : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log N
  rw [← sum_erase_add (Icc 1 N) (fun d : ℕ => (d : ℝ)⁻¹) hmem] at hH
  norm_num only [Nat.cast_one, inv_one] at hH
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [← sum_erase_add (Icc 1 N) (fun d : ℕ => Real.log d / d) hmem]
  norm_num only [Nat.cast_one, Real.log_one, zero_div, add_zero]
  calc
    _ ≤ ∑ d ∈ (Icc 1 N).erase 1, Real.log N * (d : ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      have hd' := mem_Icc.mp (mem_erase.mp hd).2
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hd'.2))
        (inv_nonneg.mpr (Nat.cast_nonneg d))
    _ = Real.log N * ∑ d ∈ (Icc 1 N).erase 1, (d : ℝ)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ (Real.log N) ^ (2 : ℕ) := by
      have h := mul_le_mul_of_nonneg_left (show (∑ d ∈ (Icc 1 N).erase 1, (d : ℝ)⁻¹) ≤ Real.log N by linarith) hl
      nlinarith

/-- [Corollary] Floor-weighted damping error has a logarithmic-square budget. -/
theorem sum_damping_error_mul_div_le {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    (∑ d ∈ Icc 1 N, |pmPowerDampedRealWeight ε d - moebiusReal d| * ((K / d : ℕ) : ℝ)) ≤
      ε * K * (Real.log N) ^ (2 : ℕ) := by
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ε * Real.log d * ((K : ℝ) / d) := by
      apply sum_le_sum
      intro d hd
      have hd' := mem_Icc.mp hd
      have hl : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd'.1)
      exact mul_le_mul (abs_pmPowerDamped_sub_moebius_le_log hε hd'.1)
        Nat.cast_div_le (Nat.cast_nonneg _) (mul_nonneg hε hl)
    _ = ε * K * ∑ d ∈ Icc 1 N, Real.log d / d := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ε * K * (Real.log N) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left (sum_log_div_le_log_sq hN) (by positivity)

/-- [Corollary] Aggregate damped response error is bounded independently of the coefficient count. -/
theorem sum_abs_sieveSeq_damping_sub_le_log_sq {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    (∑ j ∈ Icc 1 K, |sieveSeq N (pmPowerDampedRealWeight ε) j - sieveSeq N moebiusReal j|) ≤
      ε * K * (Real.log N) ^ (2 : ℕ) :=
  (sum_abs_sieveSeq_sub_le_divisor_incidence N K _ _).trans
    (sum_damping_error_mul_div_le hε hN K)

/-- [New formulation] Six-horizon defect stability depends on logarithmic-square incidence mass. -/
theorem abs_prefix_defect_damping_sub_le_log_sq {ε : ℝ} (hε : 0 ≤ ε)
    {N M : ℕ} (hN : 1 ≤ N) (hhi : M + 1 < 6 * (N + 1)) :
    |sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) -
      sieveRenormalizedPrefixDefect N M moebiusReal| ≤
        8 * ε * ((M : ℝ) + 1) * (Real.log N) ^ (2 : ℕ) := by
  have hb (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (hj : j ∈ Icc 1 (M + 1)) :
      |sieveSeq N (pmPowerDampedRealWeight η) j| ≤ 2 :=
    abs_sieveSeq_pmPowerDamped_le_two_on_prefix hη hN (mem_Icc.mp hj).1
      (lt_of_le_of_lt (mem_Icc.mp hj).2 hhi)
  have hzero : pmPowerDampedRealWeight 0 = moebiusReal := by
    funext d
    simp [pmPowerDampedRealWeight]
  have h := (abs_prefix_defect_sub_le_sum_response_errors N M
    (pmPowerDampedRealWeight ε) moebiusReal (B := 2) (by norm_num)
    (hb ε hε) (by simpa only [hzero] using hb 0 (le_refl 0))).trans
    (mul_le_mul_of_nonneg_left (sum_abs_sieveSeq_damping_sub_le_log_sq hε hN (M + 1))
      (by norm_num : (0 : ℝ) ≤ 4 * 2))
  calc
    _ ≤ 4 * 2 * (ε * ((M + 1 : ℕ) : ℝ) * (Real.log N) ^ (2 : ℕ)) := h
    _ = 8 * ε * ((M : ℝ) + 1) * (Real.log N) ^ (2 : ℕ) := by push_cast; ring

/-- [New formulation] The incidence-sensitive damping radius has only logarithmic-square coefficient cost. -/
def incidenceDampingRadius (N : ℕ) : ℝ :=
  1 / (96 * ((N : ℝ) + 1) * (Real.log N) ^ (2 : ℕ))

/-- [Corollary] Every nontrivial horizon has a positive incidence-sensitive radius. -/
theorem incidenceDampingRadius_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < incidenceDampingRadius N := by
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  unfold incidenceDampingRadius
  positivity

/-- [Corollary] The incidence radius strictly enlarges the uniform coefficient-count radius. -/
theorem sixHorizonDampingRadius_lt_incidenceDampingRadius {N : ℕ} (hN : 2 ≤ N) :
    sixHorizonDampingRadius N < incidenceDampingRadius N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hl : 0 < Real.log N := Real.log_pos hNr
  have hlog : Real.log N < N := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    linarith
  unfold sixHorizonDampingRadius incidenceDampingRadius
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_lt_mul_of_pos_left hlog
    (by positivity : 0 < 96 * ((N : ℝ) + 1) * Real.log N)
  nlinarith

/-- [Corollary] The explicit incidence radius pays the logarithmic-square perturbation budget. -/
theorem incidence_damping_radius_budget {N : ℕ} (hN : 2 ≤ N) {ε : ℝ}
    (hεhi : ε ≤ incidenceDampingRadius N) :
    96 * ((N : ℝ) + 1) * (ε * (Real.log N) ^ (2 : ℕ)) ≤ 1 := by
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp : 0 < 96 * ((N : ℝ) + 1) * (Real.log N) ^ (2 : ℕ) := by positivity
  have h := (le_div_iff₀ hp).mp hεhi
  nlinarith

/-- [New formulation] Incidence counting certifies the strict finite-checkpoint margin on a larger interval. -/
theorem prefix_defect_le_neg_half_of_incidence_radius {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hhi : M + 1 < 6 * (N + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ incidenceDampingRadius N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have he := abs_prefix_defect_damping_sub_le_log_sq hε (by omega : 1 ≤ N) hhi
  have h0 := moebius_prefix_defect_le_neg_one_of_lt_six_succ hN hM hhi
  have hb := incidence_damping_radius_budget hN hεhi
  have hMr : (M : ℝ) + 1 ≤ 6 * ((N : ℝ) + 1) := by exact_mod_cast hhi.le
  have hm := mul_le_mul_of_nonneg_right hMr
    (by positivity : 0 ≤ ε * (Real.log N) ^ (2 : ℕ))
  have hd := (abs_le.mp he).2
  nlinarith

/-- [New formulation] Any finite six-horizon certificate transfers to all its squarefree radical fibers. -/
theorem prefix_defect_le_of_finite_radical_certificate {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) {c : ℕ → ℝ}
    (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0) {C : ℝ}
    (hc : ∀ k : ℕ, 2 ≤ k → k < 6 * (N + 1) → sieveRenormalizedPrefixDefect N (k - 1) c ≤ C)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M c ≤ C := by
  by_cases hk : M + 1 < 6 * (N + 1)
  · simpa only [Nat.add_sub_cancel] using hc (M + 1) (by omega) hk
  have hr := horizonRadicalState_pos N (M + 1)
  by_cases hr1 : horizonRadicalState N (M + 1) = 1
  · obtain ⟨p, hp, hNp, hpN⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
    have heq : sieveSeq N c (M + 1) = sieveSeq N c p := by
      rw [← sieveSeq_horizonRadicalState N (M + 1) hsf, hr1, sieveSeq_prime_of_gt hp hNp]
    have hd := sieveRenormalizedPrefixDefect_le_of_sieveSeq_eq N c
      (by omega : 2 ≤ p) (by omega : p ≤ M + 1) heq
    simp only [Nat.add_sub_cancel] at hd
    exact hd.trans (hc p (by omega) (by omega))
  · have hd := sieveRenormalizedPrefixDefect_le_horizonRadicalState N (by omega : 1 ≤ M + 1) hsf
    simp only [Nat.add_sub_cancel] at hd
    exact hd.trans (hc _ (by omega) hrN)

/-- [New formulation] The enlarged interval controls infinitely many endpoints through their radical states. -/
theorem radical_defect_le_neg_half_of_incidence_radius {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ incidenceDampingRadius N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) :=
  prefix_defect_le_of_finite_radical_certificate hN hM
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)
    (fun k hk hkN => prefix_defect_le_neg_half_of_incidence_radius hN
      (by omega) (by omega) hε hεhi) hrN

/-- [Corollary] Every positive power of a certified base shares the enlarged interval. -/
theorem power_defect_le_neg_half_of_incidence_radius {N k m : ℕ}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k < 6 * (N + 1)) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ incidenceDampingRadius N) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have hpow := sieveRenormalizedPrefixDefect_pow_antitone N
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε) hk (le_refl 1) hm
  simp only [pow_one] at hpow
  exact hpow.trans (prefix_defect_le_neg_half_of_incidence_radius hN
    (by omega) (by omega) hε hεhi)

/-- [Corollary] The same radius controls each finite-checkpoint response through the aggregate incidence budget. -/
theorem response_error_le_sixteenth_of_incidence_radius {N k : ℕ}
    (hN : 2 ≤ N) (hk : 1 ≤ k) (hkN : k < 6 * (N + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hεhi : ε ≤ incidenceDampingRadius N) :
    |sieveSeq N (pmPowerDampedRealWeight ε) k - sieveSeq N moebiusReal k| ≤ (1 / 16 : ℝ) := by
  have hs := (single_le_sum (fun j _ => abs_nonneg
    (sieveSeq N (pmPowerDampedRealWeight ε) j - sieveSeq N moebiusReal j))
    (mem_Icc.mpr ⟨hk, le_refl k⟩)).trans
      (sum_abs_sieveSeq_damping_sub_le_log_sq hε (by omega : 1 ≤ N) k)
  have hb := incidence_damping_radius_budget hN hεhi
  have hkr : (k : ℝ) ≤ 6 * ((N : ℝ) + 1) := by exact_mod_cast hkN.le
  have hm := mul_le_mul_of_nonneg_right hkr
    (by positivity : 0 ≤ ε * (Real.log N) ^ (2 : ℕ))
  nlinarith

/-- [New formulation] The enlarged interval preserves strong envelope failure and strict negative power defects. -/
theorem incidence_damping_counterfamily_power_separation {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) {ε : ℝ} (hε : 0 ≤ ε)
    (hεhi : ε ≤ incidenceDampingRadius (6 * p - 1)) {m : ℕ} (hm : 1 ≤ m) :
    (31 / 16 : ℝ) ≤ sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) ((30 * p) ^ m) ∧
      sieveRenormalizedPrefixDefect (6 * p - 1) ((30 * p) ^ m - 1)
        (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ) := by
  have hN : 2 ≤ 6 * p - 1 := by omega
  constructor
  · rw [sieveSeq_pmPowerDampedRealWeight_pow ε (6 * p - 1) (30 * p) hm]
    have he := response_error_le_sixteenth_of_incidence_radius hN
      (by omega : 1 ≤ 30 * p) (by omega) hε hεhi
    rw [sieveSeq_moebiusReal_five_horizon_counterfamily hp h5] at he
    have hlo := (abs_le.mp he).1
    linarith
  · exact power_defect_le_neg_half_of_incidence_radius hN (by omega) (by omega) hm hε hεhi

/-- [Corollary] The prime family's first failure persists throughout the larger explicit interval. -/
theorem incidence_damping_counterfamily_first_failure {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) {ε : ℝ} (hε : 0 ≤ ε)
    (hεhi : ε ≤ incidenceDampingRadius (6 * p - 1)) :
    (∀ j : ℕ, 2 ≤ j → j < 30 * p →
      |sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) j| ≤ 1) ∧
      1 < sieveSeq (6 * p - 1) (pmPowerDampedRealWeight ε) (30 * p) := by
  constructor
  · intro j hj hjhi
    exact abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε hj (by omega)
  · have h := (incidence_damping_counterfamily_power_separation hp h5 hε hεhi (le_refl 1)).1
    simp only [pow_one] at h
    linarith

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
