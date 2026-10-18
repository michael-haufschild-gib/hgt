import GaloisForLFunctions.BezoutValuationIncidence.PredictableMartingaleDecompositionAndCovarianceCancellationBridge
import GaloisForLFunctions.BezoutValuationIncidence.ChineseRemainderBezoutPeriodicityAndSawtoothDefect
import GaloisForLFunctions.RHTower.PMAdjacentDivisorCorrelation

/-!
# Asymmetric adjacent-divisor truncation

The existing bounded divisor field, exact divisor-average identity, adjacent
mean limit, and unit CRT defect yield a quantitative estimate with independent
coefficient cutoffs. Passing the finite truncation estimate through the existing
limit controls the limiting density without another double-series tail proof.
Reciprocal summability at half damping supplies a power tail for every positive
damping. These estimates prepare a uniform harmonic remainder; they do not by
themselves give strict interior contraction.
-/

open Finset RHTower Filter Topology
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem nonneg_divisor_mean_le {a : ℕ → ℝ}
    (ha : ∀ d, 0 ≤ a d) (hs : Summable (fun d => a d / (d : ℝ)))
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, a d) / (N : ℝ) ≤
      ∑' d : ℕ, a d / (d : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he := pm_divisor_average_eq_tsum a hNR
  simp only [Nat.floor_natCast] at he
  rw [he]
  have hpoint (d : ℕ) :
      a d * ((⌊(N : ℝ) / d⌋₊ : ℝ) / N) ≤ a d / (d : ℝ) := by
    calc
      _ ≤ a d * (((N : ℝ) / d) / N) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (Nat.floor_le (div_nonneg hNR.le (Nat.cast_nonneg d))) hNR.le) (ha d)
      _ = _ := by rw [div_right_comm, div_self hNR.ne']; ring
  exact (Summable.of_nonneg_of_le
    (fun d => mul_nonneg (ha d) (div_nonneg (Nat.cast_nonneg _) hNR.le))
      hpoint hs).tsum_le_tsum hpoint hs

private theorem abs_divisor_sub_sieved_le (c : ℕ → ℝ) (D n : ℕ) :
    |(∑ d ∈ n.divisors, c d) - sievedDivisorSum D c n| ≤
      ∑ d ∈ n.divisors, if D < d then |c d| else 0 := by
  classical
  unfold sievedDivisorSum
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  by_cases hDd : D < d
  · simp [truncatedSieveWeight, mem_Icc, hDd, Nat.not_le.mpr hDd]
  · simp [truncatedSieveWeight, mem_Icc, hd1, hDd, Nat.le_of_not_gt hDd]

private theorem mean_abs_divisor_sub_sieved_le {c : ℕ → ℝ}
    (hc : Summable (fun d => |c d| / (d : ℝ))) (D : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, |(∑ d ∈ n.divisors, c d) - sievedDivisorSum D c n|) /
        (N : ℝ) ≤
      ∑' d : ℕ, (if D < d then |c d| else 0) / (d : ℝ) := by
  have ha (d : ℕ) : 0 ≤ if D < d then |c d| else 0 := by split_ifs <;> positivity
  have hle (d : ℕ) : (if D < d then |c d| else 0) / (d : ℝ) ≤
      |c d| / (d : ℝ) := by
    split_ifs
    · exact le_rfl
    · simpa only [zero_div] using div_nonneg (abs_nonneg (c d)) (Nat.cast_nonneg d)
  have hs := Summable.of_nonneg_of_le
    (fun d => div_nonneg (ha d) (Nat.cast_nonneg d)) hle hc
  exact (div_le_div_of_nonneg_right
    (sum_le_sum fun n _ => abs_divisor_sub_sieved_le c D n) (Nat.cast_nonneg N)).trans
    (nonneg_divisor_mean_le ha hs hN)

private theorem shifted_mean_abs_divisor_sub_sieved_le {c : ℕ → ℝ}
    (hc : Summable (fun d => |c d| / (d : ℝ))) (D : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N,
        |(∑ d ∈ (n + 1).divisors, c d) - sievedDivisorSum D c (n + 1)|) /
        (N : ℝ) ≤
      2 * ∑' d : ℕ, (if D < d then |c d| else 0) / (d : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    |(∑ d ∈ n.divisors, c d) - sievedDivisorSum D c n|
  let B : ℝ := ∑' d : ℕ, (if D < d then |c d| else 0) / (d : ℝ)
  have hB : 0 ≤ B := tsum_nonneg fun d => by split_ifs <;> positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnext : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have htotal : (∑ n ∈ Icc 1 (N + 1), f n) ≤ B * (N + 1 : ℕ) :=
    (div_le_iff₀ hnext).mp (mean_abs_divisor_sub_sieved_le hc D (by omega))
  have hshift : (∑ n ∈ Icc 1 N, f (n + 1)) ≤
      ∑ n ∈ Icc 1 (N + 1), f n := by
    rw [sum_Icc_one_split_head_and_shift f (by omega : 1 ≤ N + 1)]
    simp only [Nat.add_sub_cancel]
    have hfirst : 0 ≤ f 1 := abs_nonneg _
    linarith
  apply (div_le_iff₀ hNR).mpr
  change (∑ n ∈ Icc 1 N, f (n + 1)) ≤ 2 * B * N
  calc
    _ ≤ B * (N + 1 : ℕ) := hshift.trans htotal
    _ ≤ _ := by push_cast; nlinarith

private theorem abs_sievedDivisorSum_le_head_mass (c : ℕ → ℝ) (D : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    |sievedDivisorSum D c n| ≤ ∑ d ∈ Icc 1 D, |c d| := by
  rw [← sieveSeq_eq_sievedDivisorSum D c hn, sieveSeq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)

private theorem abs_adjacent_mean_sub_truncated_le {c b : ℕ → ℝ}
    (hc : Summable (fun d => |c d| / (d : ℝ)))
    (hb : Summable (fun a => |b a| / (a : ℝ)))
    (hfield : ∀ n : ℕ, 1 ≤ n → |∑ a ∈ n.divisors, b a| ≤ 1)
    (D A : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N,
        (∑ d ∈ n.divisors, c d) * (∑ a ∈ (n + 1).divisors, b a)) / (N : ℝ) -
      (∑ n ∈ Icc 1 N, sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)) /
        (N : ℝ)| ≤
      (∑' d : ℕ, (if D < d then |c d| else 0) / (d : ℝ)) +
        2 * (∑ d ∈ Icc 1 D, |c d|) *
          ∑' a : ℕ, (if A < a then |b a| else 0) / (a : ℝ) := by
  let K : ℝ := ∑ d ∈ Icc 1 D, |c d|
  have hK : 0 ≤ K := sum_nonneg fun _ _ => abs_nonneg _
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      |(∑ d ∈ n.divisors, c d) * (∑ a ∈ (n + 1).divisors, b a) -
          sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)| ≤
        |(∑ d ∈ n.divisors, c d) - sievedDivisorSum D c n| +
          K * |(∑ a ∈ (n + 1).divisors, b a) - sievedDivisorSum A b (n + 1)| := by
    let F : ℝ := ∑ a ∈ (n + 1).divisors, b a
    let G : ℝ := ∑ d ∈ n.divisors, c d
    let S : ℝ := sievedDivisorSum A b (n + 1)
    let U : ℝ := sievedDivisorSum D c n
    change |G * F - U * S| ≤ |G - U| + K * |F - S|
    have hF : |F| ≤ 1 := hfield (n + 1) (by omega)
    have hU : |U| ≤ K := abs_sievedDivisorSum_le_head_mass c D (mem_Icc.mp hn).1
    calc
      _ = |F * (G - U) + (F - S) * U| := by congr 1; ring
      _ ≤ |F * (G - U)| + |(F - S) * U| := abs_add_le _ _
      _ = |F| * |G - U| + |F - S| * |U| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |G - U| + |F - S| * K :=
        add_le_add (mul_le_mul_of_nonneg_right hF (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hU (abs_nonneg _))
      _ = _ := by ring
  have hNabs : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
  rw [← sub_div, ← sum_sub_distrib, abs_div, hNabs]
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpoint)
  have hh := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  rw [sum_add_distrib, ← mul_sum, add_div, mul_div_assoc] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (∑' d : ℕ, (if D < d then |c d| else 0) / (d : ℝ)) +
        K * (2 * ∑' a : ℕ, (if A < a then |b a| else 0) / (a : ℝ)) :=
      add_le_add (mean_abs_divisor_sub_sieved_le hc D hN)
        (mul_le_mul_of_nonneg_left (shifted_mean_abs_divisor_sub_sieved_le hb A hN) hK)
    _ = _ := by ring

private theorem sum_sieveSeq_mul_succ_bilinear (D A N : ℕ) (c b : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, sieveSeq D c n * sieveSeq A b (n + 1)) =
      ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
        c d * b a * (bezoutIncidenceCount N d a : ℝ) := by
  classical
  have hpt (n : ℕ) :
      sieveSeq D c n * sieveSeq A b (n + 1) =
        ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
          if d ∣ n ∧ a ∣ (n + 1) then c d * b a else 0 := by
    unfold sieveSeq
    rw [sum_filter, sum_filter, sum_mul]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases hd : d ∣ n <;> by_cases ha : a ∣ (n + 1) <;> simp [hd, ha]
  simp_rw [hpt]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  unfold bezoutIncidenceCount bezoutIncidenceSet
  rw [card_filter, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases h : d ∣ n ∧ a ∣ (n + 1) <;> simp [h]

private theorem abs_bilinear_adjacent_head_defect_le (D A N : ℕ) (c b : ℕ → ℝ) :
    |(∑ n ∈ Icc 1 N, sieveSeq D c n * sieveSeq A b (n + 1)) -
      (N : ℝ) * ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
        c d * b a * (if d.Coprime a then 1 / ((d : ℝ) * a) else 0)| ≤
      (∑ d ∈ Icc 1 D, |c d|) * (∑ a ∈ Icc 1 A, |b a|) := by
  classical
  have heq :
      (∑ n ∈ Icc 1 N, sieveSeq D c n * sieveSeq A b (n + 1)) -
          (N : ℝ) * ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
            c d * b a * (if d.Coprime a then 1 / ((d : ℝ) * a) else 0) =
        ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
          c d * b a * bezoutSawtoothDefect N d a := by
    rw [sum_sieveSeq_mul_succ_bilinear, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    unfold bezoutSawtoothDefect
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
        |c d * b a * bezoutSawtoothDefect N d a| :=
      (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun d _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A, |c d| * |b a| := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro a ha
      rw [abs_mul, abs_mul]
      have hh := (abs_bezoutSawtoothDefect_le_one N
        (mem_Icc.mp hd).1 (mem_Icc.mp ha).1).2.2
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hh (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by simp_rw [← mul_sum]; rw [sum_mul]

private theorem abs_truncated_adjacent_mean_sub_density_le
    (D A : ℕ) (c b : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N, sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)) /
        (N : ℝ) -
      ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
        c d * b a * (if d.Coprime a then 1 / ((d : ℝ) * a) else 0)| ≤
      ((∑ d ∈ Icc 1 D, |c d|) * (∑ a ∈ Icc 1 A, |b a|)) / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he (S L : ℝ) : S / (N : ℝ) - L = (S - (N : ℝ) * L) / N := by
    field_simp
  have hsum :
      (∑ n ∈ Icc 1 N, sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)) =
        ∑ n ∈ Icc 1 N, sieveSeq D c n * sieveSeq A b (n + 1) := by
    refine sum_congr rfl fun n hn => ?_
    rw [sieveSeq_eq_sievedDivisorSum D c (mem_Icc.mp hn).1,
      sieveSeq_eq_sievedDivisorSum A b (by omega : 1 ≤ n + 1)]
  rw [he, hsum, abs_div, abs_of_pos hNR]
  exact div_le_div_of_nonneg_right (abs_bilinear_adjacent_head_defect_le D A N c b) hNR.le

private theorem tendsto_truncated_adjacent_mean (D A : ℕ) (c b : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)) /
        (N : ℝ)) atTop
      (𝓝 (∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
        c d * b a * (if d.Coprime a then 1 / ((d : ℝ) * a) else 0))) := by
  let L : ℝ := ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
    c d * b a * (if d.Coprime a then 1 / ((d : ℝ) * a) else 0)
  have herr : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)) /
        (N : ℝ) - L) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      (tendsto_const_div_atTop_nhds_zero_nat
        ((∑ d ∈ Icc 1 D, |c d|) * (∑ a ∈ Icc 1 A, |b a|)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact abs_truncated_adjacent_mean_sub_density_le D A c b hN
  simpa only [sub_add_cancel, zero_add] using herr.add_const L

private theorem summable_abs_real_weight_reciprocal {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => |pmPowerDampedRealWeight ε d| / (d : ℝ)) := by
  simpa [pmPowerDampedRealWeight, moebiusReal, norm_div,
    Real.norm_eq_abs] using
      (pm_summable_real_mobius_reciprocal hε).norm

/-- Absolute reciprocal mass omitted by the coefficient cutoff. -/
def pmPowerDampedReciprocalTail (ε : ℝ) (D : ℕ) : ℝ :=
  ∑' d : ℕ, (if D < d then |pmPowerDampedRealWeight ε d| else 0) / (d : ℝ)

/-- Two independent coefficient cutoffs quantify the existing adjacent mean
limit. The bounded full field pays the first tail; the retained outer mass
pays the shifted tail. The existing unit CRT defect pays the finite head. -/
theorem abs_pm_adjacent_divisor_mean_sub_density_le_two_cutoffs
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (D A : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N,
        pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n) /
          (N : ℝ) - pmAdjacentDivisorDensity ε η| ≤
      2 * pmPowerDampedReciprocalTail η D +
        4 * (∑ d ∈ Icc 1 D, |pmPowerDampedRealWeight η d|) *
          pmPowerDampedReciprocalTail ε A +
        ((∑ d ∈ Icc 1 D, |pmPowerDampedRealWeight η d|) *
          (∑ a ∈ Icc 1 A, |pmPowerDampedRealWeight ε a|)) / (N : ℝ) := by
  let c := pmPowerDampedRealWeight η
  let b := pmPowerDampedRealWeight ε
  let Q : ℕ → ℝ := fun N =>
    (∑ n ∈ Icc 1 N,
      pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n) / (N : ℝ)
  let R : ℕ → ℝ := fun N =>
    (∑ n ∈ Icc 1 N, sievedDivisorSum D c n * sievedDivisorSum A b (n + 1)) /
      (N : ℝ)
  let L : ℝ := ∑ d ∈ Icc 1 D, ∑ a ∈ Icc 1 A,
    c d * b a * (if d.Coprime a then 1 / ((d : ℝ) * a) else 0)
  let B : ℝ := pmPowerDampedReciprocalTail η D +
    2 * (∑ d ∈ Icc 1 D, |c d|) * pmPowerDampedReciprocalTail ε A
  let H : ℝ := (∑ d ∈ Icc 1 D, |c d|) * (∑ a ∈ Icc 1 A, |b a|)
  have hfield (n : ℕ) (_ : 1 ≤ n) : |∑ a ∈ n.divisors, b a| ≤ 1 := by
    change |pmPowerDampedDivisorCoeff ε n| ≤ 1
    rw [abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε.le n)]
    exact pmPowerDampedDivisorCoeff_le_one hε.le n
  have htrunc (M : ℕ) (hM : 1 ≤ M) : |Q M - R M| ≤ B := by
    simpa only [Q, R, B, c, b, pmPowerDampedReciprocalTail,
      pmPowerDampedDivisorCoeff, pmPowerDampedRealWeight, moebiusReal, mul_comm] using
      abs_adjacent_mean_sub_truncated_le
        (summable_abs_real_weight_reciprocal hη)
        (summable_abs_real_weight_reciprocal hε) hfield D A hM
  have hlim : Tendsto (fun M => |Q M - R M|) atTop
      (𝓝 |pmAdjacentDivisorDensity ε η - L|) :=
    ((tendsto_pm_adjacent_divisor_mean hε hη).sub
      (tendsto_truncated_adjacent_mean D A c b)).abs
  have hdensity : |pmAdjacentDivisorDensity ε η - L| ≤ B := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact htrunc M hM
  have hhead : |R N - L| ≤ H / (N : ℝ) :=
    abs_truncated_adjacent_mean_sub_density_le D A c b hN
  change |Q N - pmAdjacentDivisorDensity ε η| ≤ _
  calc
    _ = |(Q N - R N) + (R N - L) + (L - pmAdjacentDivisorDensity ε η)| := by
      congr 1
      ring
    _ ≤ |Q N - R N| + |R N - L| + |L - pmAdjacentDivisorDensity ε η| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ B + H / (N : ℝ) + B :=
      add_le_add (add_le_add (htrunc N hN) hhead)
        (by simpa only [abs_sub_comm] using hdensity)
    _ = _ := by dsimp only [B, H, c, b]; ring

private theorem real_weight_head_mass_le {ε : ℝ} (hε : 0 ≤ ε) (D : ℕ) :
    (∑ d ∈ Icc 1 D, |pmPowerDampedRealWeight ε d|) ≤ D := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 D) : |pmPowerDampedRealWeight ε d| ≤ 1 := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    unfold pmPowerDampedRealWeight moebiusReal
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) (-ε))]
    exact (mul_le_mul hmu
      (Real.rpow_le_one_of_one_le_of_nonpos hd1 (neg_nonpos.mpr hε))
        (Real.rpow_nonneg (Nat.cast_nonneg d) (-ε)) (by norm_num)).trans_eq (by ring)
  simpa using sum_le_sum hpoint

/-- The two-cutoff bound with elementary cutoff-size costs. -/
theorem abs_pm_adjacent_divisor_mean_sub_density_le_cutoff_sizes
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (D A : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N,
        pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n) /
          (N : ℝ) - pmAdjacentDivisorDensity ε η| ≤
      2 * pmPowerDampedReciprocalTail η D +
        4 * (D : ℝ) * pmPowerDampedReciprocalTail ε A +
        ((D : ℝ) * A) / (N : ℝ) := by
  have htail : 0 ≤ pmPowerDampedReciprocalTail ε A := by
    unfold pmPowerDampedReciprocalTail
    exact tsum_nonneg fun d => by split_ifs <;> positivity
  have hD := real_weight_head_mass_le hη.le D
  have hA := real_weight_head_mass_le hε.le A
  apply (abs_pm_adjacent_divisor_mean_sub_density_le_two_cutoffs hε hη D A hN).trans
  apply add_le_add
  · apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hD (by norm_num)) htail
  · exact div_le_div_of_nonneg_right
      (mul_le_mul hD hA (sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg D))
      (Nat.cast_nonneg N)

/-- Existing reciprocal summability at half damping supplies an explicit
power tail for every positive damping. -/
theorem pmPowerDampedReciprocalTail_le_half_exponent_moment
    {ε : ℝ} (hε : 0 < ε) {A : ℕ} (hA : 1 ≤ A) :
    pmPowerDampedReciprocalTail ε A ≤
      (A : ℝ) ^ (-ε / 2) *
        ∑' d : ℕ, |pmPowerDampedRealWeight (ε / 2) d| / (d : ℝ) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hs := (summable_abs_real_weight_reciprocal (show 0 < ε / 2 by linarith)).mul_left
    ((A : ℝ) ^ (-ε / 2))
  have hnonneg (d : ℕ) : 0 ≤ (if A < d then |pmPowerDampedRealWeight ε d| else 0) /
      (d : ℝ) := by split_ifs <;> positivity
  have hpoint (d : ℕ) :
      (if A < d then |pmPowerDampedRealWeight ε d| else 0) / (d : ℝ) ≤
        (A : ℝ) ^ (-ε / 2) * (|pmPowerDampedRealWeight (ε / 2) d| / (d : ℝ)) := by
    by_cases hd : A < d
    · rw [if_pos hd]
      have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hAd : (A : ℝ) ≤ d := by exact_mod_cast hd.le
      have hp : (d : ℝ) ^ (-ε / 2) ≤ (A : ℝ) ^ (-ε / 2) :=
        Real.rpow_le_rpow_of_nonpos hAR hAd (by linarith)
      have he : |pmPowerDampedRealWeight ε d| / (d : ℝ) =
          (d : ℝ) ^ (-ε / 2) *
            (|pmPowerDampedRealWeight (ε / 2) d| / (d : ℝ)) := by
        unfold pmPowerDampedRealWeight
        rw [abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hdR.le (-ε)),
          abs_of_nonneg (Real.rpow_nonneg hdR.le (-(ε / 2)))]
        have hr : (d : ℝ) ^ (-ε) = (d : ℝ) ^ (-ε / 2) * (d : ℝ) ^ (-(ε / 2)) := by
          rw [← Real.rpow_add hdR]
          congr 1
          ring
        rw [hr]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hp (div_nonneg (abs_nonneg _) hdR.le)
    · rw [if_neg hd, zero_div]
      positivity
  have hb := (Summable.of_nonneg_of_le hnonneg hpoint hs).tsum_le_tsum hpoint hs
  simpa only [pmPowerDampedReciprocalTail, tsum_mul_left] using hb

end GaloisForLFunctions.BezoutValuationIncidence
