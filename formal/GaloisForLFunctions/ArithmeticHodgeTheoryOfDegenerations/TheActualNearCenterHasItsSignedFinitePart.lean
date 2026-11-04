import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearCenterRetainsItsHarmonicFinitePart
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLinearMomentRemovesTheOverlapLogarithm

/-!
# The actual near center has its signed finite part

The logarithmic window gives an exact triangular cutoff in the integer
gap. Its difference kernel retains the harmonic Ramanujan finite part;
the sum kernel vanishes after normalization by the horizon.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)

/-- The difference kernel restricted to an exact logarithmic window. -/
def nearDifferencePair (t : ℝ) (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    if n ≠ j ∧ |Real.log j - Real.log n| ≤ t then
      u n * v j / |(n : ℝ) - j| else 0

private theorem nearDifferencePair_eq_gaps (t : ℝ) (N : ℕ) (u v : ℕ → ℝ) :
    nearDifferencePair t N u v =
      ∑ h ∈ Icc 1 N, (1 / (h : ℝ)) * ∑ n ∈ Icc 1 (N - h),
        if |Real.log ((n + h : ℕ) : ℝ) - Real.log n| ≤ t then
          u n * v (n + h) + u (n + h) * v n else 0 := by
  let A : ℕ → ℕ → ℝ := fun n j =>
    if |Real.log j - Real.log n| ≤ t then u n * v j / ((j : ℝ) - n) else 0
  let B : ℕ → ℕ → ℝ := fun n j =>
    if |Real.log j - Real.log n| ≤ t then u j * v n / ((j : ℝ) - n) else 0
  have hpt : ∀ n j : ℕ,
      (if n ≠ j ∧ |Real.log j - Real.log n| ≤ t then
        u n * v j / |(n : ℝ) - j| else 0) =
      (if n < j then A n j else 0) + (if j < n then B j n else 0) := by
    intro n j
    dsimp only [A, B]
    rcases lt_trichotomy n j with h | h | h
    · have hR : (n : ℝ) < j := by exact_mod_cast h
      simp only [ne_eq, h.ne, not_false_eq_true, true_and, if_pos h, if_neg (by omega : ¬j < n), add_zero,
        abs_of_neg (sub_neg.mpr hR), neg_sub]
    · subst j
      simp
    · have hR : (j : ℝ) < n := by exact_mod_cast h
      simp only [ne_eq, h.ne', not_false_eq_true, true_and, if_neg (by omega : ¬n < j), if_pos h, zero_add,
        abs_of_pos (sub_pos.mpr hR), abs_sub_comm (Real.log n)]
  unfold nearDifferencePair
  simp_rw [hpt]
  simp only [sum_add_distrib]
  rw [sum_comm (f := fun n j => if j < n then B j n else 0),
    sum_sum_ite_lt A N, sum_sum_ite_lt B N, ← sum_add_distrib]
  apply sum_congr rfl
  intro h hh
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro n hn
  dsimp only [A, B]
  simp only [Nat.cast_add, add_sub_cancel_left]
  split_ifs <;> ring

private theorem near_log_gap_iff_ceil_le {t : ℝ} (ht : 0 < t) {n h : ℕ}
    (hn : 1 ≤ n) (hh : 1 ≤ h) :
    (|Real.log ((n + h : ℕ) : ℝ) - Real.log n| ≤ t) ↔
      ⌈(h : ℝ) / (Real.exp t - 1)⌉₊ ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hd : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  rw [log_add_sub_log hn, abs_of_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity))),
    Real.log_le_iff_le_exp (by positivity), Nat.ceil_le, div_le_iff₀ hd]
  constructor
  · intro hlog
    have hb : (h : ℝ) / n ≤ Real.exp t - 1 := by linarith only [hlog]
    exact (div_le_iff₀ hn0).mp hb |>.trans_eq (mul_comm _ _)
  · intro hgap
    have hb : (h : ℝ) / n ≤ Real.exp t - 1 :=
      (div_le_iff₀ hn0).mpr (hgap.trans_eq (mul_comm _ _))
    linarith only [hb]

private theorem ceil_gap_interval_empty {d : ℝ} (hd : 0 < d) {h N : ℕ}
    (hhN : h ≤ N) (hH : nearCenterGapCutoff d N < h) :
    Icc ⌈(h : ℝ) / d⌉₊ (N - h) = ∅ := by
  apply Icc_eq_empty_of_lt
  apply Nat.lt_of_not_ge
  intro hle
  have hb : (h : ℝ) / d ≤ ((N - h : ℕ) : ℝ) :=
    (Nat.le_ceil ((h : ℝ) / d)).trans (by exact_mod_cast hle)
  rw [Nat.cast_sub hhN, div_le_iff₀ hd] at hb
  have he : (h : ℝ) ≤ nearCenterGapCutoff d N := by
    unfold nearCenterGapCutoff
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hb]
  exact (not_le_of_gt hH) he

/-- Exact logarithmic near pairs have the triangular linear-gap cutoff. -/
theorem nearDifferencePair_ramanujan_eq_truncated {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : 1 ≤ N) (m l : ℕ) :
    nearDifferencePair t N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) =
      truncatedCenterDifference m l (Real.exp t - 1) N := by
  let d : ℝ := Real.exp t - 1
  let H : ℝ := nearCenterGapCutoff d N
  let Q : ℕ := ⌊H⌋₊
  have hd : 0 < d := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hH0 : 0 ≤ H := by dsimp only [H, nearCenterGapCutoff]; positivity
  have hHN : H ≤ N := by
    dsimp only [H, nearCenterGapCutoff]
    rw [div_le_iff₀ (by positivity)]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith only [hN0]
  have hQN : Q ≤ N := by exact_mod_cast (Nat.floor_le hH0).trans hHN
  rw [nearDifferencePair_eq_gaps]
  have hrow : ∀ h ∈ Icc 1 N,
      (∑ n ∈ Icc 1 (N - h),
        if |Real.log ((n + h : ℕ) : ℝ) - Real.log n| ≤ t then
          ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
            ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n else 0) =
      (∑ n ∈ Icc ⌈(h : ℝ) / d⌉₊ (N - h),
        (ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
          ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)) := by
    intro h hh
    have hceil : 1 ≤ ⌈(h : ℝ) / d⌉₊ := by
      apply Nat.one_le_ceil_iff.mpr
      exact div_pos (by exact_mod_cast (mem_Icc.mp hh).1) hd
    have hfilter : (Icc 1 (N - h)).filter (fun n => ⌈(h : ℝ) / d⌉₊ ≤ n) =
        Icc ⌈(h : ℝ) / d⌉₊ (N - h) := by
      ext n
      simp only [mem_filter, mem_Icc]
      omega
    rw [← hfilter, sum_filter]
    apply sum_congr rfl
    intro n hn
    simp only [d, near_log_gap_iff_ceil_le ht (mem_Icc.mp hn).1 (mem_Icc.mp hh).1]
  rw [sum_congr (s₁ := Icc 1 N) rfl
    (fun (h : ℕ) hh => congrArg (fun x : ℝ => (1 / (h : ℝ)) * x) (hrow h hh))]
  unfold truncatedCenterDifference
  change (∑ h ∈ Icc 1 N, _) = ∑ h ∈ Icc 1 Q, _
  symm
  apply sum_subset
  · intro h hh
    exact mem_Icc.mpr ⟨(mem_Icc.mp hh).1, (mem_Icc.mp hh).2.trans hQN⟩
  · intro h hh hnQ
    have hQh : Q < h := by
      have hh1 := (mem_Icc.mp hh).1
      simp only [mem_Icc, not_and] at hnQ
      exact Nat.lt_of_not_ge (hnQ hh1)
    have hHh : H < h := (Nat.lt_floor_add_one H).trans_le
      (by exact_mod_cast (show Q + 1 ≤ h by omega))
    rw [ceil_gap_interval_empty hd (mem_Icc.mp hh).2 hHh, sum_empty, mul_zero]

/-- The sum kernel restricted to near arithmetic pairs. -/
def nearSumPair (c : ℝ) (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, u n * v j / ((n : ℝ) + j)

/-- The near center pairing in pole gauge. -/
def nearCenterPair (c : ℝ) (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
    u n * v j * archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)

/-- The near center splits exactly into its difference and sum kernels. -/
theorem nearCenterPair_eq (c : ℝ) (N : ℕ) (u v : ℕ → ℝ) :
    nearCenterPair c N u v =
      (1 / 2 : ℝ) * (nearDifferencePair (2 * c / N) N u v + nearSumPair c N u v) := by
  have hd : nearDifferencePair (2 * c / N) N u v =
      ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, u n * v j / |(n : ℝ) - j| := by
    simp only [nearDifferencePair, nearRowIndices, sum_filter, ne_comm]
  rw [hd]
  unfold nearCenterPair nearSumPair
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjN := (mem_filter.mp hj).1
  have hne := (mem_filter.mp hj).2.1
  have he := archimedeanCenterKernel_div_sqrt_mul (mem_Icc.mp hn).1
    (mem_Icc.mp hjN).1 hne.symm
  calc
    _ = u n * v j * (archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)) := by ring
    _ = _ := by rw [he]; ring

/-- The near sum kernel costs only the overlap, uniformly over the horizon. -/
theorem abs_nearSumPair_le {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hw : c / N ≤ 1) {u v : ℕ → ℝ} {B : ℝ}
    (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B) :
    |nearSumPair c N u v| ≤ 4 * Real.exp 2 * B ^ 2 * c := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : ∀ n ∈ Icc 1 N,
      |∑ j ∈ nearRowIndices c N n, u n * v j / ((n : ℝ) + j)| ≤
        2 * B ^ 2 * linearNearRowRadius c / N := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    calc
      _ ≤ ∑ j ∈ nearRowIndices c N n, B ^ 2 / n := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        rw [abs_div, abs_mul, abs_of_pos (add_pos_of_pos_of_nonneg hn0 hj0)]
        have hab : |u n| * |v j| ≤ B ^ 2 := by
          rw [pow_two]
          exact mul_le_mul (hu n) (hv j) (abs_nonneg _) hB
        exact (div_le_div_of_nonneg_right hab (by positivity)).trans
          (div_le_div_of_nonneg_left (sq_nonneg B) hn0 (le_add_of_nonneg_right hj0))
      _ ≤ (2 * linearNearRowRadius c * ((n : ℝ) / N)) * (B ^ 2 / n) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_nearRowIndices_le_relative_radius hc hn hw)
          (by positivity)
      _ = _ := by field_simp [hn0.ne', hN0.ne']
  calc
    _ ≤ ∑ n ∈ Icc 1 N, 2 * B ^ 2 * linearNearRowRadius c / N :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => hr n hn)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
        linearNearRowRadius]
      field_simp [hN0.ne']
      ring

/-- The sum kernel disappears after division by the horizon along a vanishing-width clock. -/
theorem tendsto_nearSumPair_div_horizon {u v : ℕ → ℝ} {B : ℝ}
    (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearSumPair (c N) N u v / (2 * N)) atTop (𝓝 0) := by
  have hlim := hcN.const_mul (2 * Real.exp 2 * B ^ 2)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
  exact (div_le_div_of_nonneg_right (abs_nearSumPair_le (hc N) hN hw.le hu hv)
    (by positivity)).trans_eq (by ring)

/-- The exact near difference pairing retains its signed triangular harmonic finite part. -/
theorem tendsto_nearDifferencePair_finite_part {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      nearDifferencePair (2 * c N / N) N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) /
        (2 * N) - (if m = 1 ∧ l = 1 then Real.log (c N) else 0)) atTop
      (𝓝 (if m = l then
        (if m = 1 then Real.log 2 + Real.eulerMascheroniConstant - 1 else -vonMangoldt m) else 0)) := by
  let H : ℕ → ℝ := fun N => nearCenterGapCutoff (Real.exp (2 * c N / N) - 1) N
  let T : ℕ → ℝ := fun N => lagHarmonic m ⌊H N⌋₊ - lagSum m ⌊H N⌋₊ / H N
  let K : ℝ := 4 * (l * m : ℕ) *
    (2 * (∑ t ∈ l.divisors, (t : ℝ)) * ∑ t ∈ m.divisors, (t : ℝ)) +
      2 * ∑ t ∈ m.divisors, (t : ℝ)
  have hzero : Tendsto (fun N : ℕ =>
      nearDifferencePair (2 * c N / N) N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) /
        (2 * N) - (if m = l then T N else 0)) atTop (𝓝 0) := by
    have hlim := tendsto_harmonic_div_self.const_mul (K / 2)
    simp only [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have ht : 0 < 2 * c N / N := div_pos (mul_pos zero_lt_two (hc N)) hN0
    have hd : 0 < Real.exp (2 * c N / N) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
    rw [Real.norm_eq_abs, nearDifferencePair_ramanujan_eq_truncated ht hN m l]
    exact (abs_truncatedCenterDifference_sub_le hm hl hd hN).trans_eq (by dsimp only [K]; ring)
  by_cases hml : m = l
  · subst l
    simp only [if_true] at hzero ⊢
    have hmain := tendsto_triangular_lagHarmonic_at_overlap hm hc hcinf hcN
    have h := hzero.add hmain
    simp only [zero_add, and_self] at h ⊢
    exact h.congr fun N => by dsimp only [T, H]; ring
  · have hnot : ¬(m = 1 ∧ l = 1) := by rintro ⟨rfl, rfl⟩; exact hml rfl
    simpa only [if_neg hml, if_neg hnot, sub_zero] using hzero

/-- The actual near center has a conductor-sensitive signed finite part. -/
theorem tendsto_nearCenterPair_finite_part {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      nearCenterPair (c N) N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) / N -
        (if m = 1 ∧ l = 1 then Real.log (c N) else 0)) atTop
      (𝓝 (if m = l then
        (if m = 1 then Real.log 2 + Real.eulerMascheroniConstant - 1 else -vonMangoldt m) else 0)) := by
  let B : ℝ := (∑ d ∈ m.divisors, (d : ℝ)) + ∑ d ∈ l.divisors, (d : ℝ)
  have hu : ∀ n, |ramanujanLagCoefficient l n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le l n).trans (le_add_of_nonneg_left (by positivity))
  have hv : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_right (by positivity))
  have h := (tendsto_nearDifferencePair_finite_part hm hl hc hcinf hcN).add
    (tendsto_nearSumPair_div_horizon hu hv hc hcN)
  simp only [add_zero] at h
  exact h.congr fun N => by rw [nearCenterPair_eq]; ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.nearDifferencePair_ramanujan_eq_truncated
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearCenterPair_finite_part
