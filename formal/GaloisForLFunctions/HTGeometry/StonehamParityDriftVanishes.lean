import GaloisForLFunctions.HTGeometry.ThreeAdicOrbitPhaseSums

/-!
# The parity drift of the Stoneham constant vanishes

For `α = Σ_{j ≥ 1} 3^{−j} 2^{−3^j}` the parity drift satisfies `D_α(N) = o(N)`:

* inside the `k`-th window the drift weight is a combination of three threshold indicators of the
  class coordinates `uₓ` of the orbit `2Aₖ 4ˣ mod 3ᵏ`;
* the threshold discrepancy of that orbit is `O(k² 3^{2k/3})` (`abs_card_threshold_sub_le`), so
  every prefix of a window carries drift `O(k² 3^{2k/3})`;
* adding the complete windows before it gives `|D_α(N)| = O(log² N · N^{2/3})`.

Consequently `¬ ParityDriftHypothesis α` (`not_parityDriftHypothesis_stoneham`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamParityDrift

open BinaryParityDrift

/-! ### The drift weight as threshold indicators -/

/-- The thresholds `⌈(d 3ᵏ − 8)/12⌉` of the class coordinate for the base-4 digit levels. -/
def cellThreshold (k d : ℕ) : ℕ := (d * 3 ^ k + 3) / 12

theorem cellDigit_eq_div (k r : ℕ) : cellDigit k r = ((4 * r / 3 ^ k : ℕ) : ℤ) := by
  unfold cellDigit
  rw [← Int.natCast_floor_eq_floor (by positivity)]
  congr 1
  have := Nat.floor_div_eq_div (K := ℝ) (4 * r) (3 ^ k)
  push_cast at this
  exact this

theorem cellWeight_three_mul_add_two {k u : ℕ} (hu : 3 * u + 2 < 3 ^ k) :
    cellWeight k (3 * u + 2) =
      -(if cellThreshold k 1 ≤ u then 1 else 0) + 2 * (if cellThreshold k 2 ≤ u then 1 else 0) -
        (if cellThreshold k 3 ≤ u then 1 else 0) := by
  unfold cellWeight digitWeight cellThreshold
  rw [cellDigit_eq_div]
  have hq : 0 < 3 ^ k := by positivity
  have h1 : 1 ≤ 4 * (3 * u + 2) / 3 ^ k ↔ 1 * 3 ^ k ≤ 4 * (3 * u + 2) := Nat.le_div_iff_mul_le hq
  have h2 : 2 ≤ 4 * (3 * u + 2) / 3 ^ k ↔ 2 * 3 ^ k ≤ 4 * (3 * u + 2) := Nat.le_div_iff_mul_le hq
  have h3 : 3 ≤ 4 * (3 * u + 2) / 3 ^ k ↔ 3 * 3 ^ k ≤ 4 * (3 * u + 2) := Nat.le_div_iff_mul_le hq
  have h4 : 4 * (3 * u + 2) / 3 ^ k < 4 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
  split_ifs <;> omega

/-- The bound `(1 + log τ)((2 + log τ) √(τ 3ʲ) + 3^{k−1−j})` of the threshold discrepancy. -/
noncomputable def orbitDiscrepancyBound (k j : ℕ) : ℝ :=
  (1 + Real.log (3 ^ (k - 1))) * ((2 + Real.log (3 ^ (k - 1))) *
    Real.sqrt (3 ^ (k - 1) * 3 ^ j) + 3 ^ (k - 1 - j))

/-- **Incomplete windows of cell weights.** -/
theorem abs_sum_cellWeight_orbit_le {k b j m : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2)
    (hjk : j + 1 ≤ k) (hm : m ≤ 3 ^ (k - 1)) :
    |((∑ x ∈ range m, cellWeight k (orbitPt k b x) : ℤ) : ℝ)| ≤
      1 + 4 * orbitDiscrepancyBound k j := by
  have hq := three_pow_eq_three_mul hk
  have hterm : ∀ x, cellWeight k (orbitPt k b x) =
      -(if cellThreshold k 1 ≤ orbitCoord k b x then 1 else 0) +
        2 * (if cellThreshold k 2 ≤ orbitCoord k b x then 1 else 0) -
          (if cellThreshold k 3 ≤ orbitCoord k b x then 1 else 0) := by
    intro x
    rw [orbitPt_eq hk hb x]
    apply cellWeight_three_mul_add_two
    rw [← orbitPt_eq hk hb]
    exact Nat.mod_lt _ (by positivity)
  have hthr : ∀ d ≤ 3, cellThreshold k d ≤ 3 ^ (k - 1) := by
    intro d hd; unfold cellThreshold; interval_cases d <;> omega
  have hN : ∀ d ≤ 3, |(#{x ∈ range m | cellThreshold k d ≤ orbitCoord k b x} : ℝ) -
      m * (3 ^ (k - 1) - cellThreshold k d) / 3 ^ (k - 1)| ≤ orbitDiscrepancyBound k j :=
    fun d hd => abs_card_threshold_sub_le hk hb hjk (hthr d hd) hm
  have hcomb : |((cellThreshold k 1 : ℤ) - 2 * cellThreshold k 2 + cellThreshold k 3 : ℤ)| ≤ 1 := by
    unfold cellThreshold; rw [abs_le]; constructor <;> omega
  have hcombR : |((cellThreshold k 1 : ℝ) - 2 * cellThreshold k 2 + cellThreshold k 3)| ≤ 1 := by
    exact_mod_cast hcomb
  rw [sum_congr rfl fun x _ => hterm x, sum_sub_distrib, sum_add_distrib, sum_neg_distrib,
    ← mul_sum]
  simp only [sum_boole]
  push_cast
  have h1 := hN 1 (by norm_num)
  have h2 := hN 2 (by norm_num)
  have h3 := hN 3 (by norm_num)
  set E := orbitDiscrepancyBound k j with hE
  have hτ : (0 : ℝ) < 3 ^ (k - 1) := by positivity
  have hmτ : (m : ℝ) / 3 ^ (k - 1) ≤ 1 := by
    rw [div_le_one hτ]; exact_mod_cast hm
  have hmain : |(m : ℝ) * (3 ^ (k - 1) - cellThreshold k 1) / 3 ^ (k - 1) * (-1) +
      2 * ((m : ℝ) * (3 ^ (k - 1) - cellThreshold k 2) / 3 ^ (k - 1)) -
      (m : ℝ) * (3 ^ (k - 1) - cellThreshold k 3) / 3 ^ (k - 1)| ≤ 1 := by
    rw [show (m : ℝ) * (3 ^ (k - 1) - cellThreshold k 1) / 3 ^ (k - 1) * (-1) +
        2 * ((m : ℝ) * (3 ^ (k - 1) - cellThreshold k 2) / 3 ^ (k - 1)) -
        (m : ℝ) * (3 ^ (k - 1) - cellThreshold k 3) / 3 ^ (k - 1) =
        (m : ℝ) / 3 ^ (k - 1) * ((cellThreshold k 1 : ℝ) - 2 * cellThreshold k 2 +
          cellThreshold k 3) by field_simp; ring, abs_mul]
    have : |(m : ℝ) / 3 ^ (k - 1)| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; exact hmτ
    calc _ ≤ 1 * 1 := mul_le_mul this hcombR (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [abs_le] at h1 h2 h3 hmain ⊢
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hN 1 (by norm_num))
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hmain.1, hmain.2]

/-- Sums along the orbit over at most `a + 1` periods. -/
theorem abs_sum_orbit_periods_le {k b : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ) {B : ℝ}
    (hB : ∀ m ≤ 3 ^ (k - 1), |((∑ x ∈ range m, f (orbitPt k b x) : ℤ) : ℝ)| ≤ B) (a : ℕ) {r : ℕ}
    (hr : r ≤ 3 ^ (k - 1)) :
    |((∑ x ∈ range (3 ^ (k - 1) * a + r), f (orbitPt k b x) : ℤ) : ℝ)| ≤ (a + 1) * B := by
  induction a with
  | zero => simpa using hB r hr
  | succ a ih =>
    rw [show 3 ^ (k - 1) * (a + 1) + r = 3 ^ (k - 1) + (3 ^ (k - 1) * a + r) by ring,
      sum_range_add]
    have hper : ∀ x, orbitPt k b (3 ^ (k - 1) + x) = orbitPt k b x := fun x => by
      rw [add_comm, ← mul_one (3 ^ (k - 1)), orbitPt_add_mul_period hk]
    simp_rw [hper]
    push_cast
    have h0 := hB (3 ^ (k - 1)) le_rfl
    push_cast at h0 ih
    calc _ ≤ |(∑ x ∈ range (3 ^ (k - 1)), (f (orbitPt k b x) : ℝ))| +
          |∑ x ∈ range (3 ^ (k - 1) * a + r), (f (orbitPt k b x) : ℝ)| := abs_add_le _ _
      _ ≤ B + (a + 1) * B := add_le_add h0 ih
      _ = _ := by ring

/-- **Window prefixes.**  The first `m ≤ 3ᵏ` digit weights of the `k`-th window sum to at most
`28 + 16 E`. -/
theorem abs_sum_window_prefix_le {k j m : ℕ} (hk : 1 ≤ k) (hjk : j + 1 ≤ k) (hm : m ≤ 3 ^ k) :
    |((∑ i ∈ range m, digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) : ℤ) : ℝ)| ≤
      28 + 16 * orbitDiscrepancyBound k j := by
  have hbmod : (2 * stonehamA k) % 3 = 2 := by rw [Nat.mul_mod, stonehamA_mod_three hk]
  have hq := three_pow_eq_three_mul hk
  -- cell weights along the orbit over `m ≤ 3τ`
  have hcell : |((∑ i ∈ range m, cellWeight k (orbitPt k (2 * stonehamA k) i) : ℤ) : ℝ)| ≤
      4 * (1 + 4 * orbitDiscrepancyBound k j) := by
    have hB := fun m' (hm' : m' ≤ 3 ^ (k - 1)) => abs_sum_cellWeight_orbit_le hk hbmod hjk hm'
    have hdecomp : m = 3 ^ (k - 1) * (m / 3 ^ (k - 1)) + m % 3 ^ (k - 1) :=
      (Nat.div_add_mod m _).symm
    have ha : m / 3 ^ (k - 1) ≤ 3 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]; omega
    have hr : m % 3 ^ (k - 1) ≤ 3 ^ (k - 1) := (Nat.mod_lt _ (by positivity)).le
    have := abs_sum_orbit_periods_le hk (cellWeight k) hB (m / 3 ^ (k - 1)) hr
    rw [← hdecomp] at this
    have hE0 : 0 ≤ 1 + 4 * orbitDiscrepancyBound k j := le_trans (abs_nonneg _) (hB 0 (by simp))
    refine this.trans ?_
    have : ((m / 3 ^ (k - 1) : ℕ) : ℝ) + 1 ≤ 4 := by
      have : ((m / 3 ^ (k - 1) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast ha
      linarith
    nlinarith
  -- digit weights against cell weights
  have h2 : ∑ i ∈ range (3 ^ k), digitChange k (orbitPt k (2 * stonehamA k) i) ≤ 12 :=
    sum_window_digitChange_le hk
  have hdig : |∑ i ∈ range m, (digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
      cellWeight k (orbitPt k (2 * stonehamA k) i))| ≤ 24 :=
    calc _ ≤ ∑ i ∈ range m, |digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
          cellWeight k (orbitPt k (2 * stonehamA k) i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range m, 2 * digitChange k (orbitPt k (2 * stonehamA k) i) :=
          sum_le_sum fun i hi =>
            abs_digitWeight_window_sub_le hk (lt_of_lt_of_le (mem_range.mp hi) hm)
      _ ≤ ∑ i ∈ range (3 ^ k), 2 * digitChange k (orbitPt k (2 * stonehamA k) i) :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hm) fun i _ _ =>
            mul_nonneg zero_le_two (digitChange_nonneg _ _)
      _ = 2 * ∑ i ∈ range (3 ^ k), digitChange k (orbitPt k (2 * stonehamA k) i) :=
          (mul_sum _ _ _).symm
      _ ≤ 24 := by linarith
  have hdigR : |((∑ i ∈ range m, (digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
      cellWeight k (orbitPt k (2 * stonehamA k) i)) : ℤ) : ℝ)| ≤ 24 := by exact_mod_cast hdig
  have hsplit : (∑ i ∈ range m, digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) : ℤ) =
      ∑ i ∈ range m, (digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
        cellWeight k (orbitPt k (2 * stonehamA k) i)) +
      ∑ i ∈ range m, cellWeight k (orbitPt k (2 * stonehamA k) i) := by
    rw [← sum_add_distrib]; simp
  rw [hsplit, Int.cast_add]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 24 + 4 * (1 + 4 * orbitDiscrepancyBound k j) := add_le_add hdigR hcell
    _ = 28 + 16 * orbitDiscrepancyBound k j := by ring

/-- **Drift bound inside the windows.** -/
theorem abs_drift_windowEnd_add_le {k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ 3 ^ (k + 1)) :
    |(drift stoneham (windowEnd k + m) : ℝ)| ≤
      30 + 33 * k + 16 * orbitDiscrepancyBound (k + 1) (k / 3) := by
  have hsplit : drift stoneham (windowEnd k + m) = drift stoneham (windowEnd k) +
      ∑ i ∈ range m, digitWeight (quatDigit stoneham ((3 ^ (k + 1) + 1) / 2 + i + 1)) := by
    rw [drift_eq_sum_digitWeight, drift_eq_sum_digitWeight, sum_range_add]
    rfl
  have h1 : |(drift stoneham (windowEnd k) : ℝ)| ≤ 2 + 33 * k := by
    exact_mod_cast abs_drift_windowEnd_le k
  have h2 := abs_sum_window_prefix_le (k := k + 1) (j := k / 3) (by omega) (by omega) hm
  rw [hsplit]
  push_cast at h2 ⊢
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 + 33 * k + (28 + 16 * orbitDiscrepancyBound (k + 1) (k / 3)) := add_le_add h1 h2
    _ = _ := by ring

/-! ### The drift rate -/

theorem sqrt_three_pow (j : ℕ) : Real.sqrt (3 ^ j) = Real.sqrt 3 ^ j := by
  rw [show (3 : ℝ) ^ j = (Real.sqrt 3 ^ j) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

/-- `E_{k+1} ≤ 4(k + 1)² 3ᵏ/(√3)^{⌊k/3⌋}`. -/
theorem orbitDiscrepancyBound_le (k : ℕ) :
    orbitDiscrepancyBound (k + 1) (k / 3) ≤ 4 * (k + 1) ^ 2 * (3 ^ k / Real.sqrt 3 ^ (k / 3)) := by
  unfold orbitDiscrepancyBound
  simp only [Nat.add_sub_cancel]
  set j := k / 3 with hj
  have hjk : 2 * j ≤ k := by omega
  set s := Real.sqrt 3 ^ j with hs
  have hs0 : 0 < s := by positivity
  have hs2 : Real.sqrt (3 ^ j) = s := sqrt_three_pow j
  set T : ℝ := 3 ^ k / s with hT
  have hT0 : 0 ≤ T := by positivity
  -- the logarithm is at most `2k`
  have hL0 : 0 ≤ Real.log ((3 : ℝ) ^ k) := Real.log_nonneg (one_le_pow₀ (by norm_num))
  have hL : Real.log ((3 : ℝ) ^ k) ≤ 2 * k := by
    rw [Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  -- the two summands are at most `T`
  have hX : Real.sqrt (3 ^ k * 3 ^ j) ≤ T := by
    rw [hT, le_div_iff₀ hs0, ← hs2, ← Real.sqrt_mul (by positivity)]
    calc Real.sqrt (3 ^ k * 3 ^ j * 3 ^ j) ≤ Real.sqrt (3 ^ k * 3 ^ k) := by
          apply Real.sqrt_le_sqrt
          rw [mul_assoc]
          gcongr
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 3 ^ k := Real.sqrt_mul_self (by positivity)
  have hY : (3 : ℝ) ^ (k - j) ≤ T := by
    rw [hT, le_div_iff₀ hs0]
    have hs3 : s ≤ 3 ^ j := by
      rw [hs]
      gcongr
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    calc (3 : ℝ) ^ (k - j) * s ≤ 3 ^ (k - j) * 3 ^ j := by gcongr
      _ = 3 ^ k := by rw [← pow_add]; congr 1; omega
  have hX0 : 0 ≤ Real.sqrt (3 ^ k * 3 ^ j) := Real.sqrt_nonneg _
  calc (1 + Real.log (3 ^ k)) * ((2 + Real.log (3 ^ k)) * Real.sqrt (3 ^ k * 3 ^ j) +
        3 ^ (k - j))
      ≤ (1 + 2 * k) * ((2 + 2 * k) * T + T) := by
        refine mul_le_mul ?_ (add_le_add (mul_le_mul ?_ hX hX0 ?_) hY) ?_ ?_
        · linarith
        · linarith
        · positivity
        · positivity
        · positivity
    _ = (1 + 2 * k) * (3 + 2 * k) * T := by ring
    _ ≤ 4 * (k + 1) ^ 2 * T :=
        mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) hT0
    _ = 4 * (k + 1) ^ 2 * (3 ^ k / Real.sqrt 3 ^ j) := rfl

/-- The rate `(30 + 33k)/3ᵏ + 576 (⌊k/3⌋ + 1)²/(√3)^{⌊k/3⌋}`. -/
noncomputable def stonehamDriftRate (k : ℕ) : ℝ :=
  (30 + 33 * k) / 3 ^ k + 576 * (((k / 3 : ℕ) : ℝ) + 1) ^ 2 / Real.sqrt 3 ^ (k / 3)

theorem abs_drift_div_le_rate {k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ 3 ^ (k + 1)) :
    |(drift stoneham (windowEnd k + m) : ℝ) / (windowEnd k + m : ℕ)| ≤ stonehamDriftRate k := by
  have hD := abs_drift_windowEnd_add_le hk hm
  have hE := orbitDiscrepancyBound_le k
  have hN : (3 : ℝ) ^ k ≤ (windowEnd k + m : ℕ) := by
    have := three_pow_le_windowEnd k
    exact_mod_cast le_trans this (Nat.le_add_right _ _)
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hs : (0 : ℝ) < Real.sqrt 3 ^ (k / 3) := by positivity
  have hk3 : ((k : ℝ) + 1) ^ 2 ≤ 9 * (((k / 3 : ℕ) : ℝ) + 1) ^ 2 := by
    have : (k : ℝ) + 1 ≤ 3 * (((k / 3 : ℕ) : ℝ) + 1) := by
      have : k + 1 ≤ 3 * (k / 3 + 1) := by omega
      exact_mod_cast this
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  rw [abs_div, Nat.abs_cast]
  calc |(drift stoneham (windowEnd k + m) : ℝ)| / (windowEnd k + m : ℕ)
      ≤ (30 + 33 * k + 16 * (4 * (k + 1) ^ 2 * (3 ^ k / Real.sqrt 3 ^ (k / 3)))) / 3 ^ k := by
        apply div_le_div₀ (by positivity) (hD.trans (by linarith)) h3 hN
    _ = (30 + 33 * k) / 3 ^ k + 64 * ((k : ℝ) + 1) ^ 2 / Real.sqrt 3 ^ (k / 3) := by
        field_simp
        ring
    _ ≤ stonehamDriftRate k := by
        unfold stonehamDriftRate
        gcongr (30 + 33 * (k : ℝ)) / 3 ^ k + ?_ / _
        linarith

theorem tendsto_stonehamDriftRate : Tendsto stonehamDriftRate atTop (𝓝 0) := by
  have ha : Tendsto (fun k : ℕ => (30 + 33 * (k : ℝ)) / 3 ^ k) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 3)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 3)
    have := (h0.const_mul 30).add (h1.const_mul 33)
    simp only [pow_one, pow_zero, mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    ring
  have hr : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hg : Tendsto (fun j : ℕ => 576 * ((j : ℝ) + 1) ^ 2 / Real.sqrt 3 ^ j) atTop (𝓝 0) := by
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 hr
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
    have := ((h2.add (h1.const_mul 2)).add h0).const_mul 576
    simp only [pow_one, pow_zero, mul_zero, add_zero] at this
    refine this.congr fun j => ?_
    ring
  have := ha.add (hg.comp (Nat.tendsto_div_const_atTop (by norm_num : (3 : ℕ) ≠ 0)))
  rw [add_zero] at this
  exact this.congr fun k => rfl

/-- The last window end not exceeding `N`. -/
def lastWindow (N : ℕ) : ℕ := Nat.findGreatest (fun k => windowEnd k ≤ N) N

theorem le_lastWindow {K N : ℕ} (h : windowEnd K ≤ N) : K ≤ lastWindow N := by
  have hK : K ≤ N := le_trans (Nat.lt_pow_self (by norm_num : 1 < 3)).le
    (le_trans (three_pow_le_windowEnd K) h)
  exact Nat.le_findGreatest hK h

theorem windowEnd_lastWindow_le {N : ℕ} (h : windowEnd 0 ≤ N) : windowEnd (lastWindow N) ≤ N :=
  Nat.findGreatest_spec (P := fun k => windowEnd k ≤ N) (Nat.zero_le N) h

theorem lt_windowEnd_lastWindow_succ (N : ℕ) : N < windowEnd (lastWindow N + 1) := by
  by_cases h : lastWindow N + 1 ≤ N
  · have := Nat.findGreatest_is_greatest (P := fun k => windowEnd k ≤ N) (Nat.lt_succ_self _) h
    exact not_le.mp this
  · have h1 := three_pow_le_windowEnd (lastWindow N + 1)
    have h2 := Nat.lt_pow_self (by norm_num : 1 < 3) (n := lastWindow N + 1)
    omega

/-- **The parity drift of the Stoneham constant vanishes.** -/
theorem tendsto_drift_stoneham :
    Tendsto (fun N : ℕ => (drift stoneham N : ℝ) / N) atTop (𝓝 0) := by
  have hκ : Tendsto lastWindow atTop atTop := by
    rw [tendsto_atTop]
    intro K
    rw [eventually_atTop]
    exact ⟨windowEnd K, fun N hN => le_lastWindow hN⟩
  have hbound : ∀ᶠ N : ℕ in atTop,
      |(drift stoneham N : ℝ) / N| ≤ stonehamDriftRate (lastWindow N) := by
    rw [eventually_atTop]
    refine ⟨windowEnd 1, fun N hN => ?_⟩
    set k := lastWindow N with hk
    have hk1 : 1 ≤ k := le_lastWindow hN
    have h0 : windowEnd 0 ≤ N := le_trans (by decide) hN
    have hlo := windowEnd_lastWindow_le h0
    have hhi := lt_windowEnd_lastWindow_succ N
    rw [← hk] at hlo hhi
    rw [windowEnd_succ] at hhi
    have hN' : N = windowEnd k + (N - windowEnd k) := by omega
    have hm : N - windowEnd k ≤ 3 ^ (k + 1) := by omega
    have := abs_drift_div_le_rate hk1 hm
    rw [← hN'] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_stonehamDriftRate.comp hκ)
  filter_upwards [hbound] with N hN
  rw [Real.norm_eq_abs]
  exact hN

/-- **The Parity-Drift Hypothesis fails for the Stoneham constant.** -/
theorem not_parityDriftHypothesis_stoneham : ¬ ParityDriftHypothesis stoneham :=
  fun h => h tendsto_drift_stoneham

end GaloisForLFunctions.HTGeometry.StonehamParityDrift
