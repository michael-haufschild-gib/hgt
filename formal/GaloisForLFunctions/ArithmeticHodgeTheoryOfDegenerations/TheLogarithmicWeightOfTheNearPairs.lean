import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum
import GaloisForLFunctions.HTGeometry.SharpHardySchur

/-!
# The logarithmic weight of the near pairs

A near pair sum weighted by the logarithm of its smaller index at the width `w = c/N`,

`Σ_{0 < |log(j/n)| ≤ 2w} log(w min(n, j)) u(n) v(j) K(|log(j/n)|/w)/√(nj)`,

has the leading term `2ūv̄ (∫_0^2 K) c (log c − 1)`, with error
`O((1 + log c)² + c²(1 + log c + log N)/N)` (`abs_logNearPairSum_sub_le`).

* **Arbitrary weights** (`abs_nearPairSum_sub_le_weighted`): the row estimate of the near pair
  sum holds row by row, so a weight `ρ` enters only through `Σ_m |ρ(m)| · err(m)`, the row error
  `nearRowError` being `O(w)` on the short rows `m < 1/(βw)` (they meet no partner), `O(1/m)` on
  the full rows and `O(w)` on the `O(wN)` rows reaching the horizon.
* **The logarithm** is unbounded, `|log(wm)| ≤ log N`, but only on the short rows, where
  `Σ |log(wm)| ≤ 4/w` (`sum_abs_log_short_rows_le`); on the other rows `|log(wm)| ≤ log 4 + log c`.
* **The main term** is Stirling's `Σ_{m ≤ N} log(wm) = N(log c − 1) + O(log N)`
  (`abs_sum_log_mul_sub_le`), the periodic weights entering through summation by parts.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory

/-! ### Arbitrary weights -/

/-- The row error of a near pair sum: short rows, full rows, and rows reaching the horizon. -/
def nearRowError (A B C β w : ℝ) (N m : ℕ) : ℝ :=
  (if (m : ℝ) < 1 / (β * w) then 2 * B * A * β * w else 0) +
    (if 1 / (2 * β * w) ≤ (m : ℝ) then C * (1 / m) else 0) +
    (if N * Real.exp (-(β * w)) < (m : ℝ) then 4 * B * A * β * w else 0)

/-- **The row estimate.** Each row of a near pair sum is its mean times the row integral, up to
the row error. -/
theorem abs_rowWindow_sub_mean_le_nearRowError {K : ℝ → ℝ} {α β A L w : ℝ} (hα : 0 ≤ α)
    (hαβ : α ≤ β) (hβ : 0 < β) (hw : 0 < w) (hβw : β * w ≤ 1) (hA : ∀ ℓ ∈ Icc α β, |K ℓ| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|) (hL0 : 0 ≤ L)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hper : ∀ n, p (n + q) = p n) {B : ℝ}
    (hp : ∀ n, |p n| ≤ B) {N m : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    |rowWindow K α β w N m p - periodicMean p q * ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))| ≤
      nearRowError A B ((2 * q + 1) * B * (4 * A + 2 * β * L)) β w N m := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hp 0)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hβw0 : 0 < β * w := mul_pos hβ hw
  have hIb : |∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))| ≤ 2 * A * β * w :=
    abs_integral_kernel_le hα hαβ hw hβw hA
  have hC0 : 0 ≤ (2 * q + 1) * B * (4 * A + 2 * β * L) := by positivity
  have hmeanB : |periodicMean p q| ≤ B := by
    rw [periodicMean, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ range q, |p r| ≤ ∑ _r ∈ range q, B := Finset.sum_le_sum fun r _ => hp r
      _ = B * q := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hexp1 : β * w ≤ Real.exp (β * w) - 1 := by linarith [Real.add_one_le_exp (β * w)]
  have hexp2 : Real.exp (β * w) - 1 ≤ 2 * (β * w) := by
    have h := Real.abs_exp_sub_one_le (x := β * w) (by rw [abs_of_pos hβw0]; exact hβw)
    rw [abs_of_pos hβw0] at h
    linarith [le_abs_self (Real.exp (β * w) - 1)]
  have hpI : |periodicMean p q * ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))| ≤
      2 * B * A * β * w := by
    rw [abs_mul]
    calc _ ≤ B * (2 * A * β * w) := mul_le_mul hmeanB hIb (abs_nonneg _) hB0
      _ = 2 * B * A * β * w := by ring
  have hnn1 : 0 ≤ (if (m : ℝ) < 1 / (β * w) then 2 * B * A * β * w else 0) := by
    split_ifs <;> positivity
  have hnn2 : 0 ≤ (if 1 / (2 * β * w) ≤ (m : ℝ) then
      (2 * q + 1) * B * (4 * A + 2 * β * L) * (1 / m) else 0) := by split_ifs <;> positivity
  have hnn3 : 0 ≤ (if N * Real.exp (-(β * w)) < (m : ℝ) then 4 * B * A * β * w else 0) := by
    split_ifs <;> positivity
  unfold nearRowError
  by_cases h1 : (m : ℝ) * (Real.exp (β * w) - 1) < 1
  · rw [rowWindow_eq_zero_of_lt hm1 h1, zero_sub, abs_neg]
    have hmX : (m : ℝ) < 1 / (β * w) := by
      rw [lt_div_iff₀ hβw0]
      nlinarith
    rw [if_pos hmX]
    linarith
  · push Not at h1
    have hmY : 1 / (2 * β * w) ≤ (m : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    by_cases htop : (m : ℝ) * (Real.exp (β * w) - 1) ≤ (N - m : ℕ)
    · have h := abs_rowWindow_sub_le hα hαβ hw hβw hA hL hL0 hq hper hp hm1 htop
      rw [if_pos hmY]
      calc _ ≤ (2 * q + 1) * B * (4 * A + 2 * β * L) / m := h
        _ = (2 * q + 1) * B * (4 * A + 2 * β * L) * (1 / m) := by ring
        _ ≤ _ := by linarith
    · push Not at htop
      have hmZ : N * Real.exp (-(β * w)) < (m : ℝ) := by
        rw [Nat.cast_sub hmN] at htop
        have h2 : (N : ℝ) < m * Real.exp (β * w) := by linarith
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
        exact h2
      have hRW := abs_rowWindow_le hw hα hαβ hA hp hm1 (N := N)
      rw [if_pos hmZ]
      have hRW' : |rowWindow K α β w N m p| ≤ 2 * B * A * β * w := by
        refine hRW.trans ?_
        calc B * A * (Real.exp (β * w) - 1) ≤ B * A * (2 * (β * w)) :=
              mul_le_mul_of_nonneg_left hexp2 (by positivity)
          _ = 2 * B * A * β * w := by ring
      calc _ ≤ |rowWindow K α β w N m p| +
            |periodicMean p q * ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))| := abs_sub _ _
        _ ≤ 4 * B * A * β * w := by linarith
        _ ≤ _ := by linarith

/-- **The weighted near pair sum.** With an arbitrary weight `ρ` of the smaller index,
`|Σ_{pairs} ρ u v K − I Σ_m ρ(m)(u(m)v̄ + v(m)ū)| ≤ 2B Σ_m |ρ(m)| err(m)`. -/
theorem abs_nearPairSum_sub_le_weighted {K : ℝ → ℝ} {α β A L w : ℝ} (hα : 0 ≤ α)
    (hαβ : α ≤ β) (hβ : 0 < β) (hw : 0 < w) (hβw : β * w ≤ 1) (hA : ∀ ℓ ∈ Icc α β, |K ℓ| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|) (hL0 : 0 ≤ L)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B) (ρ : ℕ → ℝ) (N : ℕ) :
    |nearPairSum K α β w N u v ρ - (∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))) *
        ∑ m ∈ Finset.Icc 1 N, ρ m * (u m * periodicMean v q + v m * periodicMean u q)| ≤
      2 * B * ∑ m ∈ Finset.Icc 1 N,
        |ρ m| * nearRowError A B ((2 * q + 1) * B * (4 * A + 2 * β * L)) β w N m := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  rw [nearPairSum_eq_rows K hα hw N u v ρ, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hv' := abs_rowWindow_sub_mean_le_nearRowError hα hαβ hβ hw hβw hA hL hL0 hq hv hvB hm
  have hu' := abs_rowWindow_sub_mean_le_nearRowError hα hαβ hβ hw hβw hA hL hL0 hq hu huB hm
  set I := ∫ ℓ in α..β, K ℓ * (w * Real.exp (w * ℓ / 2))
  set F := nearRowError A B ((2 * q + 1) * B * (4 * A + 2 * β * L)) β w N m
  have e : ρ m * (u m * rowWindow K α β w N m v + v m * rowWindow K α β w N m u) -
      I * (ρ m * (u m * periodicMean v q + v m * periodicMean u q)) =
      ρ m * (u m * (rowWindow K α β w N m v - periodicMean v q * I) +
        v m * (rowWindow K α β w N m u - periodicMean u q * I)) := by ring
  rw [e, abs_mul]
  have h1 : |u m * (rowWindow K α β w N m v - periodicMean v q * I)| ≤ B * F := by
    rw [abs_mul]; exact mul_le_mul (huB m) hv' (abs_nonneg _) hB0
  have h2 : |v m * (rowWindow K α β w N m u - periodicMean u q * I)| ≤ B * F := by
    rw [abs_mul]; exact mul_le_mul (hvB m) hu' (abs_nonneg _) hB0
  calc _ ≤ |ρ m| * (B * F + B * F) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
    _ = 2 * B * (|ρ m| * F) := by ring

theorem sum_mul_ite_eq (s : Finset ℕ) (f : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] (k : ℝ) :
    ∑ m ∈ s, f m * (if P m then k else 0) = k * ∑ m ∈ s.filter P, f m := by
  rw [Finset.sum_filter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring

/-! ### The logarithm on the rows -/

/-- `Σ_{m < 1/(2w)} |log(wm)| ≤ 4/w`: on the short rows `|log(wm)| ≤ 2/√(wm)`. -/
theorem sum_abs_log_short_rows_le {w : ℝ} (hw : 0 < w) (N : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < 1 / (2 * w)), |Real.log (w * m)| ≤
      4 / w := by
  set X := 1 / (2 * w) with hX
  have hX0 : 0 < X := by positivity
  have hsw0 : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < X) ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1.1, Nat.le_floor hm.2.le⟩
  have hpt : ∀ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < X),
      |Real.log (w * m)| ≤ 2 / Real.sqrt w * (1 / Real.sqrt m) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1.1
    have hwm : 0 < w * m := mul_pos hw hm0
    have hwm1 : w * m < 1 := by
      have h := hm.2
      rw [hX, lt_div_iff₀ (by positivity)] at h
      nlinarith
    rw [abs_of_neg (Real.log_neg hwm hwm1)]
    have hlog : -Real.log (w * m) = 2 * Real.log (1 / Real.sqrt (w * m)) := by
      rw [one_div, Real.log_inv, Real.log_sqrt hwm.le]; ring
    have hle : Real.log (1 / Real.sqrt (w * m)) ≤ 1 / Real.sqrt (w * m) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have e : 1 / Real.sqrt (w * m) = 1 / Real.sqrt w * (1 / Real.sqrt m) := by
      rw [Real.sqrt_mul hw.le, one_div_mul_one_div]
    have e2 : 2 / Real.sqrt w * (1 / Real.sqrt m) = 2 * (1 / Real.sqrt w * (1 / Real.sqrt m)) := by
      ring
    rw [hlog, e2, ← e]
    linarith
  have hsqrt : ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, 1 / Real.sqrt m ≤ 2 * Real.sqrt ⌊X⌋₊ := by
    have h := sum_inv_sqrt_succ_le ⌊X⌋₊
    rw [← sum_range_succ_eq_sum_Icc]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) h
    push_cast; ring_nf
  have hfl : Real.sqrt ⌊X⌋₊ ≤ 1 / Real.sqrt w := by
    rw [le_div_iff₀ hsw0, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    have hXw : (⌊X⌋₊ : ℝ) * w ≤ 1 := by
      have := Nat.floor_le hX0.le
      have e : X * w = 1 / 2 := by rw [hX]; field_simp
      nlinarith
    calc Real.sqrt (⌊X⌋₊ * w) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hXw
      _ = 1 := Real.sqrt_one
  calc _ ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < X),
        2 / Real.sqrt w * (1 / Real.sqrt m) := Finset.sum_le_sum hpt
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, 2 / Real.sqrt w * (1 / Real.sqrt m) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = 2 / Real.sqrt w * ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, 1 / Real.sqrt m := by rw [Finset.mul_sum]
    _ ≤ 2 / Real.sqrt w * (2 * (1 / Real.sqrt w)) :=
        mul_le_mul_of_nonneg_left (hsqrt.trans (by linarith)) (by positivity)
    _ = 4 / w := by
        have hsw : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw.le
        field_simp
        linarith

/-- On the rows `1/(4w) ≤ m ≤ N`, `|log(wm)| ≤ log 4 + log c`. -/
theorem abs_log_mul_le_of_row {c w : ℝ} (hc : 1 ≤ c) (hw : 0 < w) {N m : ℕ} (hwN : w * N = c)
    (hm : 1 / (2 * 2 * w) ≤ (m : ℝ)) (hmN : m ≤ N) :
    |Real.log (w * m)| ≤ Real.log 4 + Real.log c := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hwm : 0 < w * m := mul_pos hw hm0
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlo : 1 / 4 ≤ w * m := by
    rw [div_le_iff₀ (by positivity)] at hm
    linarith
  have hhi : w * m ≤ c := by
    rw [← hwN]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hw.le
  have h1 : Real.log (w * m) ≤ Real.log c := Real.log_le_log hwm hhi
  have h2 : Real.log (1 / 4) ≤ Real.log (w * m) := Real.log_le_log (by norm_num) hlo
  rw [one_div, Real.log_inv] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Stirling: `|log N! − (N log N − N)| ≤ 1 + log N`. -/
theorem abs_log_factorial_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (N.factorial : ℝ) - (N * Real.log N - N)| ≤ 1 + Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf := Stirling.log_stirlingSeq_formula N
  have hlo : Real.log (Real.sqrt Real.pi) ≤ Real.log (Stirling.stirlingSeq N) :=
    Real.log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hhi : Real.log (Stirling.stirlingSeq N) ≤ Real.log (Stirling.stirlingSeq 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    exact Real.log_le_log (lt_of_lt_of_le (by positivity) (Stirling.sqrt_pi_le_stirlingSeq
      (by omega))) (Stirling.stirlingSeq'_antitone (Nat.zero_le m))
  rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at hhi
  have hpi : 0 < Real.log (Real.sqrt Real.pi) := Real.log_pos (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.pi_gt_three]))
  have hlog : Real.log (N / Real.exp 1) = Real.log N - 1 := by
    rw [Real.log_div hN0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have h2n : Real.log (2 * N) = Real.log 2 + Real.log N := Real.log_mul (by norm_num) hN0.ne'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rw [hlog, h2n] at hf
  have hlN := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
  rw [abs_le]
  constructor <;> nlinarith

/-- `Σ_{m ≤ N} log(wm) = N(log(wN) − 1) + O(1 + log N)`. -/
theorem abs_sum_log_mul_sub_le {w : ℝ} (hw : 0 < w) {N : ℕ} (hN : 1 ≤ N) :
    |∑ m ∈ Finset.Icc 1 N, Real.log (w * m) - N * (Real.log (w * N) - 1)| ≤ 1 + Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) =
      N * Real.log w + Real.log (N.factorial : ℝ) := by
    have h1 : ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) =
        ∑ m ∈ Finset.Icc 1 N, (Real.log w + Real.log m) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : (m : ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hm).1; positivity
      rw [Real.log_mul hw.ne' hm0]
    have h2 : ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) = Real.log (N.factorial : ℝ) := by
      rw [← sum_range_succ_eq_sum_Icc (fun m : ℕ => Real.log (m : ℝ)) N,
        ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
        Real.log_prod (fun i _ => by positivity)]
    rw [h1, Finset.sum_add_distrib, h2, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul]
  rw [hsum, Real.log_mul hw.ne' hN0.ne']
  have h := abs_log_factorial_sub_le hN
  have e : N * Real.log w + Real.log (N.factorial : ℝ) - N * (Real.log w + Real.log N - 1) =
      Real.log (N.factorial : ℝ) - (N * Real.log N - N) := by ring
  rw [e]; exact h

/-! ### The main term -/

/-- **The logarithmic main term.** With `I = ∫_0^2 K w e^{wℓ/2}` and `w = c/N`,
`I Σ_m log(wm)(u(m)v̄ + v(m)ū) = 2ūv̄ (∫_0^2 K) c(log c − 1) + O(c²(1 + log c + log N)/N)`. -/
theorem abs_logMain_sub_le {K : ℝ → ℝ} {A L : ℝ} (hA : ∀ ℓ ∈ Icc (0 : ℝ) 2, |K ℓ| ≤ A)
    (hL : ∀ x ∈ Icc (0 : ℝ) 2, ∀ y ∈ Icc (0 : ℝ) 2, |K x - K y| ≤ L * |x - y|)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    (hubar : |periodicMean u q| ≤ 1) (hvbar : |periodicMean v q| ≤ 1)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : 8 * c ≤ N) :
    |(∫ ℓ in (0 : ℝ)..2, K ℓ * (c / N * Real.exp (c / N * ℓ / 2))) *
        ∑ m ∈ Finset.Icc 1 N, Real.log (c / N * m) *
          (u m * periodicMean v q + v m * periodicMean u q) -
      2 * (periodicMean u q * periodicMean v q) * (∫ ℓ in (0 : ℝ)..2, K ℓ) *
        (c * (Real.log c - 1))| ≤
      (12 * A + 16 * A * q * B) * (c ^ 2 * (1 + Real.log c + Real.log N) / N) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 ⟨le_rfl, by norm_num⟩)
  have hB : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hc0 : 0 < c := by linarith
  obtain ⟨w, hwdef⟩ : ∃ w, w = c / N := ⟨_, rfl⟩
  rw [← hwdef]
  have hw : 0 < w := by rw [hwdef]; exact div_pos hc0 hN0
  have hwN : w * N = c := by rw [hwdef]; field_simp
  have hw8 : w ≤ 1 / 8 := by rw [hwdef, div_le_iff₀ hN0]; linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hKc : ContinuousOn K (Set.Icc 0 2) := continuousOn_of_abs_sub_le hL
  set ubar := periodicMean u q
  set vbar := periodicMean v q
  set I := ∫ ℓ in (0 : ℝ)..2, K ℓ * (w * Real.exp (w * ℓ / 2)) with hIdef
  set I₀ := ∫ ℓ in (0 : ℝ)..2, K ℓ with hI₀def
  have hI₀ : |I₀| ≤ 2 * A := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2) (f := K)
      (C := A) (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        rw [Real.norm_eq_abs]; exact hA x ⟨hx.1.le, hx.2⟩)
    rw [Real.norm_eq_abs, ← hI₀def] at h
    norm_num at h
    linarith
  have hI : |I| ≤ 4 * A * w := by
    have h := abs_integral_kernel_le (α := 0) (β := 2) le_rfl (by norm_num) hw (by linarith) hA
    rw [← hIdef] at h
    linarith
  have hII : |I - w * I₀| ≤ 4 * A * w ^ 2 := by
    have hint1 : IntervalIntegrable (fun ℓ => K ℓ * (w * Real.exp (w * ℓ / 2))) volume 0 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num)]
      have hE : Continuous fun ℓ : ℝ => w * Real.exp (w * ℓ / 2) := by fun_prop
      exact hKc.mul hE.continuousOn
    have hint2 : IntervalIntegrable K volume 0 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num)]; exact hKc
    have e : I - w * I₀ = ∫ ℓ in (0 : ℝ)..2, (K ℓ * (w * Real.exp (w * ℓ / 2)) - w * K ℓ) := by
      rw [intervalIntegral.integral_sub hint1 (hint2.const_mul w),
        intervalIntegral.integral_const_mul]
    rw [e]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2)
      (f := fun ℓ => K ℓ * (w * Real.exp (w * ℓ / 2)) - w * K ℓ) (C := A * w * (2 * w))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        have hx0 : 0 < x := hx.1
        have hwx : 0 < w * x / 2 := by have := mul_pos hw hx0; linarith
        have he : |Real.exp (w * x / 2) - 1| ≤ 2 * w := by
          have h0 : |w * x / 2| ≤ 1 := by
            rw [abs_of_pos hwx]; nlinarith [hx.2]
          refine (Real.abs_exp_sub_one_le h0).trans ?_
          rw [abs_of_pos hwx]; nlinarith [hx.2]
        rw [Real.norm_eq_abs]
        have e2 : K x * (w * Real.exp (w * x / 2)) - w * K x =
            w * K x * (Real.exp (w * x / 2) - 1) := by ring
        rw [e2, abs_mul, abs_mul, abs_of_pos hw]
        calc w * |K x| * |Real.exp (w * x / 2) - 1| ≤ w * A * (2 * w) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hA x ⟨hx0.le, hx.2⟩) hw.le) he
                (abs_nonneg _) (mul_nonneg hw.le hA0)
          _ = A * w * (2 * w) := by ring)
    rw [Real.norm_eq_abs] at h
    norm_num at h
    linarith
  -- the logarithms
  have hlogpt : ∀ m ∈ Finset.Icc 1 N, |Real.log (w * m)| ≤ Real.log c + Real.log N := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmN := (Finset.mem_Icc.mp hm).2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hwm : 0 < w * m := mul_pos hw hm0
    have hhi : w * m ≤ c := by
      rw [← hwN]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hw.le
    have hlo : w ≤ w * m := le_mul_of_one_le_right hw.le (by exact_mod_cast hm1)
    have h1 : Real.log (w * m) ≤ Real.log c := Real.log_le_log hwm hhi
    have h2 : Real.log w ≤ Real.log (w * m) := Real.log_le_log hw hlo
    have h3 : Real.log w = Real.log c - Real.log N := by
      rw [hwdef, Real.log_div hc0.ne' hN0.ne']
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  set SL := ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) with hSLdef
  have hSL : |SL - N * (Real.log c - 1)| ≤ 1 + Real.log N := by
    have h := abs_sum_log_mul_sub_le hw hN
    rwa [hwN] at h
  have hSLb : |SL| ≤ N * (Real.log c + Real.log N) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Finset.Icc 1 N, |Real.log (w * m)| ≤
          ∑ _m ∈ Finset.Icc 1 N, (Real.log c + Real.log N) := Finset.sum_le_sum hlogpt
      _ = _ := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- summation by parts against the periodic weights
  have habel : ∀ {p : ℕ → ℝ}, (∀ n, p (n + q) = p n) → (∀ n, |p n| ≤ B) →
      |∑ m ∈ Finset.Icc 1 N, Real.log (w * m) * p m - periodicMean p q * SL| ≤
        2 * q * B * (Real.log c + Real.log N) := by
    intro p hp hpB
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h := abs_sum_range_mul_shift_sub_mean_le hq hp hpB 1
      (fun i => Real.log (w * ((i : ℝ) + 1))) M
    have e1 : ∑ i ∈ range (M + 1), Real.log (w * ((i : ℝ) + 1)) * p (1 + i) =
        ∑ m ∈ Finset.Icc 1 (M + 1), Real.log (w * m) * p m := by
      rw [← sum_range_succ_eq_sum_Icc]
      exact Finset.sum_congr rfl fun i _ => by push_cast; rw [add_comm 1 i]
    have e2 : ∑ i ∈ range (M + 1), Real.log (w * ((i : ℝ) + 1)) = SL := by
      rw [hSLdef, ← sum_range_succ_eq_sum_Icc]
      exact Finset.sum_congr rfl fun i _ => by push_cast; rfl
    have e3 : |Real.log (w * ((M : ℝ) + 1))| = Real.log c := by
      have : w * ((M : ℝ) + 1) = c := by rw [← hwN]; push_cast; ring
      rw [this, abs_of_nonneg hlogc]
    have e4 : ∑ i ∈ range M, |Real.log (w * (((i + 1 : ℕ) : ℝ) + 1)) -
        Real.log (w * ((i : ℝ) + 1))| = Real.log (M + 1 : ℕ) := by
      have hmono : ∀ i : ℕ, Real.log (w * ((i : ℝ) + 1)) ≤ Real.log (w * (((i + 1 : ℕ) : ℝ) + 1)) :=
        fun i => Real.log_le_log (by positivity) (by push_cast; nlinarith)
      rw [Finset.sum_congr rfl fun i _ => abs_of_nonneg (sub_nonneg.mpr (hmono i))]
      rw [Finset.sum_range_sub (fun i : ℕ => Real.log (w * ((i : ℝ) + 1))) M]
      push_cast
      rw [Real.log_mul hw.ne' (by positivity), Real.log_mul hw.ne' (by norm_num)]
      simp
    rw [e1, e2, e3, e4] at h
    calc _ ≤ 2 * q * B * (Real.log c + Real.log (M + 1 : ℕ)) := h
      _ = _ := by push_cast; ring
  have hRu := habel hu huB
  have hRv := habel hv hvB
  -- assembling
  have hub : |ubar| ≤ 1 := hubar
  have hvb : |vbar| ≤ 1 := hvbar
  have h1 : ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) * (u m * vbar + v m * ubar) =
      vbar * ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) * u m +
        ubar * ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) * v m := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h1]
  set Su := ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) * u m
  set Sv := ∑ m ∈ Finset.Icc 1 N, Real.log (w * m) * v m
  have e : I * (vbar * Su + ubar * Sv) - 2 * (ubar * vbar) * I₀ * (c * (Real.log c - 1)) =
      2 * (ubar * vbar) * ((I - w * I₀) * SL) +
        2 * (ubar * vbar) * (w * I₀ * (SL - N * (Real.log c - 1))) +
          I * (vbar * (Su - ubar * SL) + ubar * (Sv - vbar * SL)) := by
    rw [← hwN]; ring
  rw [e]
  set Qd := c ^ 2 * (1 + Real.log c + Real.log N) / N with hQd
  have hw2N : w ^ 2 * N = c ^ 2 / N := by rw [hwdef]; field_simp
  have hwle : w ≤ c ^ 2 / N := by
    rw [hwdef]; exact div_le_div_of_nonneg_right (by nlinarith) hN0.le
  have hQd' : Qd = c ^ 2 / N * (1 + Real.log c + Real.log N) := by rw [hQd]; ring
  have hc2N : 0 ≤ c ^ 2 / N := by positivity
  have q1 : w ^ 2 * N * (Real.log c + Real.log N) ≤ Qd := by
    rw [hw2N, hQd']; exact mul_le_mul_of_nonneg_left (by linarith) hc2N
  have q2 : w * (1 + Real.log N) ≤ Qd := by
    rw [hQd']; exact mul_le_mul hwle (by linarith) (by positivity) hc2N
  have q3 : w * (Real.log c + Real.log N) ≤ Qd := by
    rw [hQd']; exact mul_le_mul hwle (by linarith) (by positivity) hc2N
  have b1 : |2 * (ubar * vbar) * ((I - w * I₀) * SL)| ≤ 8 * A * Qd := by
    simp only [abs_mul, abs_two]
    calc 2 * (|ubar| * |vbar|) * (|I - w * I₀| * |SL|) ≤
          2 * (1 * 1) * ((4 * A * w ^ 2) * (N * (Real.log c + Real.log N))) := by gcongr
      _ = 8 * A * (w ^ 2 * N * (Real.log c + Real.log N)) := by ring
      _ ≤ 8 * A * Qd := mul_le_mul_of_nonneg_left q1 (by positivity)
  have b2 : |2 * (ubar * vbar) * (w * I₀ * (SL - N * (Real.log c - 1)))| ≤ 4 * A * Qd := by
    simp only [abs_mul, abs_two, abs_of_pos hw]
    calc 2 * (|ubar| * |vbar|) * (w * |I₀| * |SL - N * (Real.log c - 1)|) ≤
          2 * (1 * 1) * (w * (2 * A) * (1 + Real.log N)) := by gcongr
      _ = 4 * A * (w * (1 + Real.log N)) := by ring
      _ ≤ 4 * A * Qd := mul_le_mul_of_nonneg_left q2 (by positivity)
  have b3 : |I * (vbar * (Su - ubar * SL) + ubar * (Sv - vbar * SL))| ≤ 16 * A * q * B * Qd := by
    have hin : |vbar * (Su - ubar * SL) + ubar * (Sv - vbar * SL)| ≤
        4 * q * B * (Real.log c + Real.log N) := by
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul]
      calc |vbar| * |Su - ubar * SL| + |ubar| * |Sv - vbar * SL| ≤
            1 * (2 * q * B * (Real.log c + Real.log N)) +
              1 * (2 * q * B * (Real.log c + Real.log N)) := by gcongr
        _ = _ := by ring
    rw [abs_mul]
    calc |I| * |vbar * (Su - ubar * SL) + ubar * (Sv - vbar * SL)| ≤
          (4 * A * w) * (4 * q * B * (Real.log c + Real.log N)) :=
          mul_le_mul hI hin (abs_nonneg _) (by positivity)
      _ = 16 * A * q * B * (w * (Real.log c + Real.log N)) := by ring
      _ ≤ 16 * A * q * B * Qd := mul_le_mul_of_nonneg_left q3 (by positivity)
  have t1 := abs_add_le (2 * (ubar * vbar) * ((I - w * I₀) * SL) +
    2 * (ubar * vbar) * (w * I₀ * (SL - N * (Real.log c - 1))))
    (I * (vbar * (Su - ubar * SL) + ubar * (Sv - vbar * SL)))
  have t2 := abs_add_le (2 * (ubar * vbar) * ((I - w * I₀) * SL))
    (2 * (ubar * vbar) * (w * I₀ * (SL - N * (Real.log c - 1))))
  linarith

theorem sum_mul_ite_eq' (s : Finset ℕ) (f g : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ m ∈ s, f m * (if P m then g m else 0) = ∑ m ∈ s.filter P, f m * g m := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring

/-- The row errors against the logarithmic weight:
`2B Σ_m |log(wm)| err(m) = O((1 + log c)² + c²(1 + log c + log N)/N)`. -/
theorem sum_abs_log_mul_nearRowError_le {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : 8 * c ≤ N) :
    2 * B * ∑ m ∈ Finset.Icc 1 N, |Real.log (c / N * m)| * nearRowError A B C 2 (c / N) N m ≤
      2 * B * (16 * B * A + 6 * C) * (1 + Real.log c) ^ 2 +
        96 * B ^ 2 * A * (c ^ 2 * (1 + Real.log c + Real.log N) / N) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hc0 : 0 < c := by linarith
  obtain ⟨w, hwdef⟩ : ∃ w, w = c / N := ⟨_, rfl⟩
  rw [← hwdef]
  have hw : 0 < w := by rw [hwdef]; exact div_pos hc0 hN0
  have hwN : w * N = c := by rw [hwdef]; field_simp
  have hw8 : w ≤ 1 / 8 := by rw [hwdef, div_le_iff₀ hN0]; linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- the three parts of the row error
  unfold nearRowError
  simp only [mul_add, Finset.sum_add_distrib]
  have h2B : (0 : ℝ) ≤ 2 * B := by positivity
  -- short rows
  have s1 : 2 * B * A * 2 * w * ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => (m : ℝ) < 1 / (2 * w)),
      |Real.log (w * m)| ≤ 16 * B * A := by
    have h := sum_abs_log_short_rows_le hw N
    calc _ ≤ 2 * B * A * 2 * w * (4 / w) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 16 * B * A := by field_simp; ring
  -- full rows
  have hY0 : 0 < 1 / (2 * 2 * w) := by positivity
  have hYN : 1 / (2 * 2 * w) ≤ N := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have s2 : ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 / (2 * 2 * w) ≤ (m : ℝ)),
      |Real.log (w * m)| * (C * (1 / (m : ℝ))) ≤ 6 * C * (1 + Real.log c) ^ 2 := by
    have hpt : ∀ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 / (2 * 2 * w) ≤ (m : ℝ)),
        |Real.log (w * m)| * (C * (1 / (m : ℝ))) ≤ C * (Real.log 4 + Real.log c) * (1 / (m : ℝ)) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      have h := abs_log_mul_le_of_row hc hw hwN hm.2 hm.1.2
      have hm0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
      calc _ = C * |Real.log (w * m)| * (1 / (m : ℝ)) := by ring
        _ ≤ C * (Real.log 4 + Real.log c) * (1 / (m : ℝ)) := by gcongr
    have hinv := sum_filter_le_inv_le hN hY0 hYN
    have e4 : (N : ℝ) / (1 / (2 * 2 * w)) = 4 * c := by rw [← hwN]; field_simp; ring
    rw [e4] at hinv
    have hlog4c : Real.log (4 * c) = Real.log 4 + Real.log c :=
      Real.log_mul (by norm_num) hc0.ne'
    calc _ ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 / (2 * 2 * w) ≤ (m : ℝ)),
          C * (Real.log 4 + Real.log c) * (1 / (m : ℝ)) := Finset.sum_le_sum hpt
      _ = C * (Real.log 4 + Real.log c) * ∑ m ∈ (Finset.Icc 1 N).filter
          (fun m : ℕ => 1 / (2 * 2 * w) ≤ (m : ℝ)), (1 / (m : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ C * (Real.log 4 + Real.log c) * (1 + Real.log (4 * c)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ C * (2 * (1 + Real.log c)) * (3 * (1 + Real.log c)) := by
          rw [hlog4c]; gcongr <;> linarith
      _ = 6 * C * (1 + Real.log c) ^ 2 := by ring
  -- rows reaching the horizon
  have hZ0 : 0 ≤ N * Real.exp (-(2 * w)) := by positivity
  have hZN : N * Real.exp (-(2 * w)) ≤ N :=
    mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hexp : 1 - 2 * w ≤ Real.exp (-(2 * w)) := by linarith [Real.add_one_le_exp (-(2 * w))]
  have s3 : 4 * B * A * 2 * w * ∑ m ∈ (Finset.Icc 1 N).filter
      (fun m : ℕ => N * Real.exp (-(2 * w)) < (m : ℝ)), |Real.log (w * m)| ≤
      48 * B * A * (c ^ 2 * (1 + Real.log c + Real.log N) / N) := by
    have hpt : ∀ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => N * Real.exp (-(2 * w)) < (m : ℝ)),
        |Real.log (w * m)| ≤ Real.log 4 + Real.log c := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      refine abs_log_mul_le_of_row hc hw hwN ?_ hm.1.2
      have hY : 1 / (2 * 2 * w) ≤ N * Real.exp (-(2 * w)) := by
        rw [div_le_iff₀ (by positivity)]
        have : (N : ℝ) * (1 - 2 * w) ≤ N * Real.exp (-(2 * w)) :=
          mul_le_mul_of_nonneg_left hexp hN0.le
        nlinarith
      linarith [hm.2]
    have hcard := card_filter_gt_le N hZ0 hZN
    have hcnt : (N : ℝ) - N * Real.exp (-(2 * w)) + 1 ≤ 3 * c := by nlinarith
    calc _ ≤ 4 * B * A * 2 * w * ∑ _m ∈ (Finset.Icc 1 N).filter
          (fun m : ℕ => N * Real.exp (-(2 * w)) < (m : ℝ)), (Real.log 4 + Real.log c) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
      _ = 4 * B * A * 2 * w * (((Finset.Icc 1 N).filter
          (fun m : ℕ => N * Real.exp (-(2 * w)) < (m : ℝ))).card * (Real.log 4 + Real.log c)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * B * A * 2 * w * ((3 * c) * (2 * (1 + Real.log c))) := by
          gcongr
          · exact hcard.trans hcnt
          · linarith
      _ = 48 * B * A * (w * c * (1 + Real.log c)) := by ring
      _ ≤ 48 * B * A * (c ^ 2 * (1 + Real.log c + Real.log N) / N) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have e : w * c = c ^ 2 / N := by rw [hwdef]; ring
          rw [e, div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg c))
            hN0.le
  have hP1 : 1 ≤ (1 + Real.log c) ^ 2 := by nlinarith
  have hs1 : 16 * B * A ≤ 16 * B * A * (1 + Real.log c) ^ 2 :=
    le_mul_of_one_le_right (by positivity) hP1
  calc _ ≤ 2 * B * (16 * B * A * (1 + Real.log c) ^ 2) + 2 * B * (6 * C * (1 + Real.log c) ^ 2) +
        2 * B * (48 * B * A * (c ^ 2 * (1 + Real.log c + Real.log N) / N)) := by
        gcongr
        · rw [sum_mul_ite_eq]; exact s1.trans hs1
        · rw [sum_mul_ite_eq' _ _ (fun m : ℕ => C * (1 / (m : ℝ)))]; exact s2
        · rw [sum_mul_ite_eq]; exact s3
    _ = _ := by ring

/-- The constant of the logarithmic near pair estimate. -/
def logNearConstant (A L : ℝ) (q : ℕ) (B : ℝ) : ℝ :=
  2 * B * (16 * B * A + 6 * ((2 * q + 1) * B * (4 * A + 2 * 2 * L))) + 96 * B ^ 2 * A +
    (12 * A + 16 * A * q * B)

/-- **The logarithmic near pair sum.** For `1 ≤ c ≤ N/8`, `w = c/N`:
`Σ_{0 < |log(j/n)| ≤ 2w} log(w min(n, j)) u(n)v(j)K(|log(j/n)|/w)/√(nj)
  = 2ūv̄ (∫_0^2 K) c(log c − 1) + O((1 + log c)² + c²(1 + log c + log N)/N)`. -/
theorem abs_logNearPairSum_sub_le {K : ℝ → ℝ} {A L : ℝ} (hA : ∀ ℓ ∈ Icc (0 : ℝ) 2, |K ℓ| ≤ A)
    (hL : ∀ x ∈ Icc (0 : ℝ) 2, ∀ y ∈ Icc (0 : ℝ) 2, |K x - K y| ≤ L * |x - y|) (hL0 : 0 ≤ L)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    (hubar : |periodicMean u q| ≤ 1) (hvbar : |periodicMean v q| ≤ 1)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : 8 * c ≤ N) :
    |nearPairSum K 0 2 (c / N) N u v (fun m => Real.log (c / N * m)) -
        2 * (periodicMean u q * periodicMean v q) * (∫ ℓ in (0 : ℝ)..2, K ℓ) *
          (c * (Real.log c - 1))| ≤
      logNearConstant A L q B * ((1 + Real.log c) ^ 2 + c ^ 2 * (1 + Real.log c + Real.log N) / N) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 ⟨le_rfl, by norm_num⟩)
  have hB : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  have hN0 : (0 : ℝ) < N := by linarith
  have hc0 : 0 < c := by linarith
  have hw : 0 < c / N := div_pos hc0 hN0
  have hw2 : 2 * (c / N) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hN0]; linarith
  have hW := abs_nearPairSum_sub_le_weighted (α := 0) (β := 2) le_rfl (by norm_num) two_pos hw hw2
    hA hL hL0 hq hu hv huB hvB (fun m => Real.log (c / N * m)) N
  have hR := sum_abs_log_mul_nearRowError_le hA0 hB
    (show 0 ≤ (2 * q + 1) * B * (4 * A + 2 * 2 * L) by positivity) hc hcN
  have hM := abs_logMain_sub_le hA hL hq hu hv huB hvB hubar hvbar hc hcN
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hP : 0 ≤ (1 + Real.log c) ^ 2 := sq_nonneg _
  have hQ : 0 ≤ c ^ 2 * (1 + Real.log c + Real.log N) / N := by positivity
  have e : logNearConstant A L q B * ((1 + Real.log c) ^ 2 +
      c ^ 2 * (1 + Real.log c + Real.log N) / N) =
      2 * B * (16 * B * A + 6 * ((2 * q + 1) * B * (4 * A + 2 * 2 * L))) * (1 + Real.log c) ^ 2 +
        96 * B ^ 2 * A * (c ^ 2 * (1 + Real.log c + Real.log N) / N) +
        (12 * A + 16 * A * q * B) * (c ^ 2 * (1 + Real.log c + Real.log N) / N) +
        ((96 * B ^ 2 * A + (12 * A + 16 * A * q * B)) * (1 + Real.log c) ^ 2 +
          2 * B * (16 * B * A + 6 * ((2 * q + 1) * B * (4 * A + 2 * 2 * L))) *
            (c ^ 2 * (1 + Real.log c + Real.log N) / N)) := by
    unfold logNearConstant; ring
  have hextra : 0 ≤ (96 * B ^ 2 * A + (12 * A + 16 * A * q * B)) * (1 + Real.log c) ^ 2 +
      2 * B * (16 * B * A + 6 * ((2 * q + 1) * B * (4 * A + 2 * 2 * L))) *
        (c ^ 2 * (1 + Real.log c + Real.log N) / N) := by positivity
  rw [e]
  have htri := abs_sub_le (nearPairSum K 0 2 (c / N) N u v (fun m => Real.log (c / N * m)))
    ((∫ ℓ in (0 : ℝ)..2, K ℓ * (c / N * Real.exp (c / N * ℓ / 2))) *
      ∑ m ∈ Finset.Icc 1 N, Real.log (c / N * m) *
        (u m * periodicMean v q + v m * periodicMean u q))
    (2 * (periodicMean u q * periodicMean v q) * (∫ ℓ in (0 : ℝ)..2, K ℓ) * (c * (Real.log c - 1)))
  linarith [hW.trans hR]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
