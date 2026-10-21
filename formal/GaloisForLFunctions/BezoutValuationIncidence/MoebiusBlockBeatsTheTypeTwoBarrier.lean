import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowMeanSquareCarriesTheCrossScaleLoss
import GaloisForLFunctions.BezoutValuationIncidence.MoebiusCancelsInAlmostAllLinearShortWindows
import GaloisForLFunctions.BezoutValuationIncidence.SingleModulusCancellationOfTheMoebiusBlock

/-!
# The Möbius block beats the Type-II barrier

Take the actual Möbius block `c' = μ·𝟙_{(Q, 2Q]}`, `x(n) = c'(n)/n²`, and average it over windows of
length `H = log₂ Q`. On windows inside `(Q, 2Q]`, Abel summation against `1/m²` gives
`|Σ_{t<m≤t+H} x(m)| ≤ |Σ_{t<m≤t+H} μ(m)|/Q² + 4H²/Q³`, and the at most `2H` windows across the ends
are bounded trivially, so

`Σ_n x̄(n)² ≤ (2/(H²Q⁴)) Σ_{Q≤t<2Q} (Σ_{t<m≤t+H} μ(m))² + 32H²/Q⁵ + 2H/Q⁴ = o(Q⁻³)`

by Matomäki–Radziwiłł in linear windows. Fed into the short-window transfer law, for every `ε > 0`
and all large `Q`, every row `c` on primes `p ≤ Q₀` with `8 log₂ Q ≤ ε² p` satisfies

`|B(c, c') + m(c) R(c') + β(c) H(c')| ≤ ε √(Σ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2}
  + |Σ_{Q<n≤2Q} μ(n)/n²| Σ_p |c(p)|/(6p) + ¾ Σ_p |c(p)| p² Σ_n |c'(n)|/n³`.

The first term is `ε` times the size `√(Σ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2}` of the large-sieve bound for
the block. The large-sieve bound is attained, up to a constant, by coherent large-scale rows (the
Type-II barrier), so the Möbius block is not Type-II extremal: in the whole balanced regime, at every
small-scale coefficient vector supported above `8 log₂ Q/ε²`, its cross-scale remainder is `o` of
that barrier, and the block-mass term is `o(1/Q)` by the prime number theorem. The saving is
Matomäki–Radziwiłł strength, a factor `o(1)`; a power saving would need power cancellation of `μ`
in almost all windows of length `≍ P`.
-/

open Finset Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The window length `log₂ Q` -/

theorem tendsto_natLog_two_atTop : Tendsto (Nat.log 2) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨2 ^ b, fun Q hQ =>
    (Nat.le_log_of_pow_le (by norm_num) hQ)⟩

theorem natLog_two_two_mul_le (k : ℕ) : Nat.log 2 (2 * k) ≤ Nat.log 2 k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [mul_comm, Nat.log_mul_base (by norm_num) hk.ne']

theorem sq_le_four_mul_two_pow (k : ℕ) : k ^ 2 ≤ 4 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> norm_num
    · rw [pow_succ 2 k]
      nlinarith

/-- `(log₂ Q)² ≤ 4Q`. -/
theorem natLog_two_sq_le (Q : ℕ) : (Nat.log 2 Q) ^ 2 ≤ 4 * Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  · exact (sq_le_four_mul_two_pow _).trans (Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 hQ.ne'))

/-! ## §2. The averaged Möbius block is small in `ℓ²` -/

/-- A sum over the `H` last points is a window sum. -/
theorem sum_range_sub_eq_sum_Ioc (g : ℕ → ℝ) {n H : ℕ} (hHn : H ≤ n) :
    ∑ i ∈ range H, g (n - i) = ∑ m ∈ Ioc (n - H) n, g m := by
  refine sum_nbij' (fun i => n - i) (fun m => n - m) (fun i hi => ?_) (fun m hm => ?_)
    (fun i hi => ?_) (fun m hm => ?_) (fun i _ => rfl)
  · simp only [mem_range, mem_Ioc] at hi ⊢; omega
  · simp only [mem_range, mem_Ioc] at hm ⊢; omega
  · simp only [mem_range] at hi; omega
  · simp only [mem_Ioc] at hm; omega

/-- On a window inside `(Q, 2Q]`, the weighted Möbius sum is the plain one over `(t+1)²` up to
`4H²/Q³`. -/
theorem abs_sum_Ioc_moebiusWindowRow_div_le {Q t H : ℕ} (hQ : 1 ≤ Q) (htQ : Q ≤ t)
    (htH : t + H ≤ 2 * Q) :
    |∑ m ∈ Ioc t (t + H), moebiusWindowRow Q m / (m : ℝ) ^ 2| ≤
      |∑ m ∈ Ioc t (t + H), moebiusReal m| / (Q : ℝ) ^ 2 + 4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3 := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  set w : ℝ := 1 / ((t : ℝ) + 1) ^ 2
  have hsplit : ∑ m ∈ Ioc t (t + H), moebiusWindowRow Q m / (m : ℝ) ^ 2 =
      w * ∑ m ∈ Ioc t (t + H), moebiusReal m +
        ∑ m ∈ Ioc t (t + H), moebiusReal m * (1 / (m : ℝ) ^ 2 - w) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hm' := mem_Ioc.mp hm
    rw [moebiusWindowRow, if_pos ⟨by omega, by omega⟩]
    ring
  have htR : (Q : ℝ) ≤ t := by exact_mod_cast htQ
  have hw : w ≤ 1 / (Q : ℝ) ^ 2 := by
    simp only [w]; gcongr; linarith
  have hterm : ∀ m ∈ Ioc t (t + H), |moebiusReal m * (1 / (m : ℝ) ^ 2 - w)| ≤
      4 * H / (Q : ℝ) ^ 3 := by
    intro m hm
    have hm' := mem_Ioc.mp hm
    have hmR : (t : ℝ) + 1 ≤ m := by exact_mod_cast (show t + 1 ≤ m by omega)
    have hmH : (m : ℝ) ≤ t + H := by exact_mod_cast hm'.2
    have hm2 : (m : ℝ) ≤ 2 * Q := by
      have : m ≤ 2 * Q := by omega
      exact_mod_cast this
    have hdiff : 0 ≤ w - 1 / (m : ℝ) ^ 2 := by
      simp only [w]; rw [sub_nonneg]; gcongr
    have hwm : w - 1 / (m : ℝ) ^ 2 ≤ 4 * H / (Q : ℝ) ^ 3 := by
      have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
      have hm0 : (0 : ℝ) < m := by linarith
      simp only [w]
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      have hnum : (m : ℝ) ^ 2 - ((t : ℝ) + 1) ^ 2 ≤ H * (4 * Q) := by nlinarith
      have hden : (Q : ℝ) ^ 4 ≤ ((t : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2 := by
        have h1 : (Q : ℝ) ^ 2 ≤ ((t : ℝ) + 1) ^ 2 := by gcongr; linarith
        have h2 : (Q : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by gcongr; linarith
        nlinarith
      have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
      have h1 : ((m : ℝ) ^ 2 - ((t : ℝ) + 1) ^ 2) * (Q : ℝ) ^ 3 ≤ H * (4 * Q) * (Q : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      have h3 : 4 * (H : ℝ) * (Q : ℝ) ^ 4 ≤ 4 * H * (((t : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      have h2 : (H : ℝ) * (4 * Q) * (Q : ℝ) ^ 3 = 4 * H * (Q : ℝ) ^ 4 := by ring
      simp only [one_mul, mul_one]
      linarith
    rw [abs_mul, abs_sub_comm, abs_of_nonneg hdiff]
    calc |moebiusReal m| * (w - 1 / (m : ℝ) ^ 2) ≤ 1 * (4 * H / (Q : ℝ) ^ 3) :=
          mul_le_mul (abs_moebiusReal_le_one' m) hwm hdiff (by norm_num)
      _ = 4 * H / (Q : ℝ) ^ 3 := one_mul _
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by positivity), div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  · refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans (le_of_eq ?_))
    rw [sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
    ring

/-- Every point of the weighted block is at most `1/Q²`. -/
theorem abs_moebiusWindowRow_div_le {Q : ℕ} (hQ : 1 ≤ Q) (m : ℕ) :
    |moebiusWindowRow Q m / (m : ℝ) ^ 2| ≤ 1 / (Q : ℝ) ^ 2 := by
  unfold moebiusWindowRow
  split_ifs with h
  · have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hm : (Q : ℝ) ≤ m := by exact_mod_cast h.1.le
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
    calc |moebiusReal m| / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (abs_moebiusReal_le_one' m) (by positivity)
      _ ≤ 1 / (Q : ℝ) ^ 2 := by gcongr
  · simp only [zero_div, abs_zero]; positivity

/-- **The averaged Möbius block.** For `1 ≤ H ≤ Q`,
`Σ_n x̄(n)² ≤ (2/(H²Q⁴)) Σ_{Q≤t<2Q} (Σ_{t<m≤t+H} μ(m))² + 32H²/Q⁵ + 2H/Q⁴`. -/
theorem sum_sq_shortWindowAverage_moebiusWindowRow_le {Q H : ℕ} (hH : 1 ≤ H) (hHQ : H ≤ Q) :
    ∑ n ∈ Icc (Q + 1) (Q + Q + H),
        shortWindowAverage H (fun n => moebiusWindowRow Q n / (n : ℝ) ^ 2) n ^ 2 ≤
      2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) *
          ∑ t ∈ Ico Q (2 * Q), (∑ m ∈ Ioc t (t + H), moebiusReal m) ^ 2 +
        32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 5 + 2 * H / (Q : ℝ) ^ 4 := by
  classical
  have hQ : 1 ≤ Q := hH.trans hHQ
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set x : ℕ → ℝ := fun n => moebiusWindowRow Q n / (n : ℝ) ^ 2
  set A : ℕ → ℝ := fun t => ∑ m ∈ Ioc t (t + H), moebiusReal m
  set good : ℕ → Prop := fun t => Q ≤ t ∧ t + H ≤ 2 * Q
  set G : ℕ → ℝ := fun t => if good t then 2 * A t ^ 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) +
    32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 6 else 1 / (Q : ℝ) ^ 4
  -- the pointwise bound through the window ending at `n`
  have hpt : ∀ n ∈ Icc (Q + 1) (Q + Q + H), shortWindowAverage H x n ^ 2 ≤ G (n - H) := by
    intro n hn
    have hn' := mem_Icc.mp hn
    have hwin : shortWindowAverage H x n = (∑ m ∈ Ioc (n - H) (n - H + H), x m) / H := by
      rw [shortWindowAverage, sum_range_sub_eq_sum_Ioc x (by omega), Nat.sub_add_cancel (by omega)]
    rw [hwin, div_pow]
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    simp only [G]
    split_ifs with hg
    · have hb := abs_sum_Ioc_moebiusWindowRow_div_le hQ hg.1 hg.2
      have hsq : (∑ m ∈ Ioc (n - H) (n - H + H), x m) ^ 2 ≤
          2 * (A (n - H) ^ 2 / (Q : ℝ) ^ 4) + 2 * (4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3) ^ 2 := by
        have h0 : 0 ≤ |A (n - H)| / (Q : ℝ) ^ 2 := by positivity
        have h1 : 0 ≤ 4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3 := by positivity
        rw [← sq_abs]
        calc |∑ m ∈ Ioc (n - H) (n - H + H), x m| ^ 2
            ≤ (|A (n - H)| / (Q : ℝ) ^ 2 + 4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hb 2
          _ ≤ 2 * (|A (n - H)| / (Q : ℝ) ^ 2) ^ 2 + 2 * (4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3) ^ 2 := by
              nlinarith [sq_nonneg (|A (n - H)| / (Q : ℝ) ^ 2 - 4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3)]
          _ = _ := by rw [div_pow, sq_abs, ← pow_mul]
      rw [div_le_iff₀ hH2]
      calc _ ≤ 2 * (A (n - H) ^ 2 / (Q : ℝ) ^ 4) + 2 * (4 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 3) ^ 2 := hsq
        _ = (2 * A (n - H) ^ 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) + 32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 6) *
            (H : ℝ) ^ 2 := by field_simp; ring
    · have hb : |∑ m ∈ Ioc (n - H) (n - H + H), x m| ≤ H * (1 / (Q : ℝ) ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        refine (sum_le_sum fun m _ => abs_moebiusWindowRow_div_le hQ m).trans (le_of_eq ?_)
        rw [sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
      rw [div_le_iff₀ hH2, ← sq_abs]
      calc |∑ m ∈ Ioc (n - H) (n - H + H), x m| ^ 2 ≤ (H * (1 / (Q : ℝ) ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = 1 / (Q : ℝ) ^ 4 * (H : ℝ) ^ 2 := by ring
  -- shift to the starts and split good and bad starts
  have hshift : ∑ n ∈ Icc (Q + 1) (Q + Q + H), G (n - H) = ∑ t ∈ Icc (Q + 1 - H) (Q + Q), G t := by
    refine sum_nbij' (fun n => n - H) (fun t => t + H) (fun n hn => ?_) (fun t ht => ?_)
      (fun n hn => ?_) (fun t ht => ?_) (fun n _ => rfl)
    · simp only [mem_Icc] at hn ⊢; omega
    · simp only [mem_Icc] at ht ⊢; omega
    · simp only [mem_Icc] at hn; omega
    · simp only [mem_Icc] at ht; omega
  have hgood : ∑ t ∈ (Icc (Q + 1 - H) (Q + Q)).filter good,
      (2 * A t ^ 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) + 32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 6) ≤
      2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) * ∑ t ∈ Ico Q (2 * Q), A t ^ 2 +
        32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 5 := by
    have hsub : (Icc (Q + 1 - H) (Q + Q)).filter good ⊆ Ico Q (2 * Q) := by
      intro t ht
      obtain ⟨-, h1, h2⟩ := (mem_filter.mp ht)
      exact mem_Ico.mpr ⟨h1, by omega⟩
    calc _ ≤ ∑ t ∈ Ico Q (2 * Q),
          (2 * A t ^ 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) + 32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 6) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) * ∑ t ∈ Ico Q (2 * Q), A t ^ 2 +
          32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 5 := by
          rw [sum_add_distrib, sum_const, Nat.card_Ico, mul_sum, nsmul_eq_mul,
            show 2 * Q - Q = Q by omega]
          congr 1
          · exact sum_congr rfl fun t _ => by ring
          · field_simp
  have hbad : ∑ _t ∈ (Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t), 1 / (Q : ℝ) ^ 4 ≤
      2 * H / (Q : ℝ) ^ 4 := by
    have hsub : (Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t) ⊆
        Ico (Q + 1 - H) Q ∪ Ioc (2 * Q - H) (2 * Q) := by
      intro t ht
      obtain ⟨h1, h2⟩ := mem_filter.mp ht
      have h1' := mem_Icc.mp h1
      simp only [good, not_and_or, not_le] at h2
      rcases h2 with h | h
      · exact mem_union_left _ (mem_Ico.mpr ⟨h1'.1, h⟩)
      · exact mem_union_right _ (mem_Ioc.mpr ⟨by omega, by omega⟩)
    have hcard : ((Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t)).card ≤ 2 * H := by
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      rw [Nat.card_Ico, Nat.card_Ioc]
      omega
    rw [sum_const, nsmul_eq_mul, mul_one_div]
    have : (((Icc (Q + 1 - H) (Q + Q)).filter (fun t => ¬ good t)).card : ℝ) ≤ 2 * H := by
      exact_mod_cast hcard
    gcongr
  calc _ ≤ ∑ n ∈ Icc (Q + 1) (Q + Q + H), G (n - H) := sum_le_sum hpt
    _ = ∑ t ∈ Icc (Q + 1 - H) (Q + Q), G t := hshift
    _ = _ := by simp only [G]; rw [sum_ite]
    _ ≤ _ := add_le_add hgood hbad

/-- **Matomäki–Radziwiłł for the averaged block.** At `H = log₂ Q`, `Σ_n x̄(n)² = o(Q⁻³)`. -/
theorem eventually_sum_sq_shortWindowAverage_moebiusWindowRow_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ Q : ℕ in atTop, ∑ n ∈ Icc (Q + 1) (Q + Q + Nat.log 2 Q),
        shortWindowAverage (Nat.log 2 Q) (fun n => moebiusWindowRow Q n / (n : ℝ) ^ 2) n ^ 2 ≤
      η / (Q : ℝ) ^ 3 := by
  have hMR := tendsto_sum_sq_moebius_window_div tendsto_natLog_two_atTop
    (fun _ _ h => Nat.log_mono_right h) natLog_two_two_mul_le (fun k => Nat.log_le_self 2 k)
  have hev := hMR.eventually (eventually_le_nhds (by positivity : 0 < η / 4))
  filter_upwards [hev, tendsto_natLog_two_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop ⌈512 / η⌉₊, eventually_ge_atTop ⌈256 / η ^ 2⌉₊] with Q hQ1 hH1 hQ2 hQ3
  set H := Nat.log 2 Q
  have hHQ : H ≤ Q := Nat.log_le_self 2 Q
  have hQ : 1 ≤ Q := hH1.trans hHQ
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hpos : (0 : ℝ) < (H : ℝ) ^ 2 * Q := by positivity
  have hA : ∑ t ∈ Ico Q (2 * Q), (∑ m ∈ Ioc t (t + H), moebiusReal m) ^ 2 ≤
      η / 4 * ((H : ℝ) ^ 2 * Q) := (div_le_iff₀ hpos).mp hQ1
  have hb := sum_sq_shortWindowAverage_moebiusWindowRow_le hH1 hHQ
  have hsqH : ((H : ℝ)) ^ 2 ≤ 4 * Q := by exact_mod_cast natLog_two_sq_le Q
  have hηQ : 512 ≤ η * Q := by
    have h := (Nat.le_ceil (512 / η)).trans (by exact_mod_cast hQ2 : (⌈512 / η⌉₊ : ℝ) ≤ Q)
    rw [div_le_iff₀ hη] at h; linarith
  have hηQ2 : 256 ≤ η ^ 2 * Q := by
    have h := (Nat.le_ceil (256 / η ^ 2)).trans
      (by exact_mod_cast hQ3 : (⌈256 / η ^ 2⌉₊ : ℝ) ≤ Q)
    rw [div_le_iff₀ (by positivity)] at h; linarith
  have hQ3pos : (0 : ℝ) < (Q : ℝ) ^ 3 := by positivity
  have t1 : 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) *
      ∑ t ∈ Ico Q (2 * Q), (∑ m ∈ Ioc t (t + H), moebiusReal m) ^ 2 ≤ η / 2 / (Q : ℝ) ^ 3 := by
    calc _ ≤ 2 / ((H : ℝ) ^ 2 * (Q : ℝ) ^ 4) * (η / 4 * ((H : ℝ) ^ 2 * Q)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = η / 2 / (Q : ℝ) ^ 3 := by field_simp; ring
  have t2 : 32 * (H : ℝ) ^ 2 / (Q : ℝ) ^ 5 ≤ η / 4 / (Q : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hQ3pos]
    have : 128 * (H : ℝ) ^ 2 ≤ η * (Q : ℝ) ^ 2 := by nlinarith
    have hQ3 : (0 : ℝ) ≤ (Q : ℝ) ^ 3 := hQ3pos.le
    nlinarith
  have t3 : 2 * (H : ℝ) / (Q : ℝ) ^ 4 ≤ η / 4 / (Q : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hQ3pos]
    have h8 : 8 * (H : ℝ) ≤ η * Q := by
      by_contra hc
      push Not at hc
      have : (η * Q) ^ 2 < (8 * (H : ℝ)) ^ 2 := by
        have : 0 ≤ η * Q := by positivity
        nlinarith
      nlinarith
    have hQ3 : (0 : ℝ) ≤ (Q : ℝ) ^ 3 := hQ3pos.le
    nlinarith
  calc _ ≤ _ := hb
    _ ≤ η / 2 / (Q : ℝ) ^ 3 + η / 4 / (Q : ℝ) ^ 3 + η / 4 / (Q : ℝ) ^ 3 := by linarith
    _ = η / (Q : ℝ) ^ 3 := by ring

/-! ## §3. The cross-scale remainder of the Möbius block -/

theorem moebiusWindowRow_supp {Q n : ℕ} (h : moebiusWindowRow Q n ≠ 0) : n ∈ Icc (Q + 1) (Q + Q) := by
  unfold moebiusWindowRow at h
  split_ifs at h with hn
  · exact mem_Icc.mpr ⟨hn.1, by omega⟩
  · exact absurd rfl h

theorem sum_Icc_moebiusWindowRow_div_eq_blockMass (Q : ℕ) :
    ∑ n ∈ Icc (Q + 1) (Q + Q), moebiusWindowRow Q n / (n : ℝ) ^ 2 = moebiusBlockMass Q := by
  rw [moebiusBlockMass, show Icc (Q + 1) (Q + Q) = Ioc Q (2 * Q) by ext n; simp; omega]
  refine sum_congr rfl fun n hn => ?_
  have := mem_Ioc.mp hn
  rw [moebiusWindowRow, if_pos this]

theorem sum_Icc_moebiusWindowRow_sq_div_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ n ∈ Icc (Q + 1) (Q + Q), moebiusWindowRow Q n ^ 2 / (n : ℝ) ^ 4 ≤ 1 / (Q : ℝ) ^ 3 := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  calc _ ≤ ∑ _n ∈ Icc (Q + 1) (Q + Q), 1 / (Q : ℝ) ^ 4 := by
        refine sum_le_sum fun n _ => ?_
        have h2 := pow_le_pow_left₀ (abs_nonneg _) (abs_moebiusWindowRow_div_le hQ n) 2
        rw [sq_abs] at h2
        calc moebiusWindowRow Q n ^ 2 / (n : ℝ) ^ 4 = (moebiusWindowRow Q n / (n : ℝ) ^ 2) ^ 2 := by
              ring
          _ ≤ (1 / (Q : ℝ) ^ 2) ^ 2 := h2
          _ = 1 / (Q : ℝ) ^ 4 := by ring
    _ = 1 / (Q : ℝ) ^ 3 := by
        rw [sum_const, Nat.card_Icc, show Q + Q + 1 - (Q + 1) = Q by omega, nsmul_eq_mul]
        field_simp

/-- **The Möbius block beats the Type-II barrier.** For every `ε > 0` and all large `Q`, every row `c`
on primes `p ≤ Q₀` with `8 log₂ Q ≤ ε² p` has, against the Möbius block `c' = μ·𝟙_{(Q, 2Q]}`,
`|B + m R' + β H'| ≤ ε √(Σ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2} + |Σ_{Q<n≤2Q} μ(n)/n²| Σ_p |c(p)|/(6p)
  + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`. -/
theorem eventually_abs_rowBilinear_moebiusWindowRow_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, 2 ≤ Q₀ →
      Q + Q + Nat.log 2 Q ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (Nat.log 2 Q : ℝ) ≤ ε ^ 2 * p) → (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (moebiusWindowRow Q) +
          rowMean N c * vonMangoldtReadout N (moebiusWindowRow Q) +
          rowBeta N c * finiteHarmonicSum N (moebiusWindowRow Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
            Real.sqrt (1 / (Q : ℝ) ^ 3) +
          |moebiusBlockMass Q| / 6 * ∑ p ∈ S, |c p| / p +
          3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 := by
  filter_upwards [eventually_sum_sq_shortWindowAverage_moebiusWindowRow_le
    (by positivity : 0 < ε ^ 2), tendsto_natLog_two_atTop.eventually_ge_atTop 1] with Q hQ hH1
  intro N Q₀ S c hQ₀ hN hS hSP hsupp
  set H := Nat.log 2 Q
  have hHQ : H ≤ Q := Nat.log_le_self 2 Q
  have hQ1 : 1 ≤ Q := hH1.trans hHQ
  have ht := abs_rowBilinear_add_mean_add_beta_le_shortWindow (A := Q) (L := Q) hQ₀ hS hsupp
    (fun n hn => moebiusWindowRow_supp hn) hH1 hN
  rw [sum_Icc_moebiusWindowRow_div_eq_blockMass] at ht
  set S₂ := ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2
  set V := Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2)
  set R := Real.sqrt (1 / (Q : ℝ) ^ 3)
  have hS₂ : 0 ≤ Real.sqrt S₂ := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  -- the averaged term
  have hT1 : Real.pi ^ 2 / 48 * Real.sqrt S₂ * Real.sqrt ((Q : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) *
      Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q + H),
        shortWindowAverage H (fun n => moebiusWindowRow Q n / (n : ℝ) ^ 2) n ^ 2) ≤
      ε / 2 * Real.sqrt S₂ * V * R := by
    have h1 : Real.sqrt ((Q : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) ≤ Real.sqrt 2 * V := by
      rw [← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      have : (H : ℝ) ≤ Q := by exact_mod_cast hHQ
      nlinarith
    have h2 : Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q + H),
        shortWindowAverage H (fun n => moebiusWindowRow Q n / (n : ℝ) ^ 2) n ^ 2) ≤ ε * R := by
      rw [show ε * R = Real.sqrt (ε ^ 2 / (Q : ℝ) ^ 3) by
        rw [div_eq_mul_one_div, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]]
      exact Real.sqrt_le_sqrt hQ
    have hc : Real.pi ^ 2 / 48 * Real.sqrt 2 ≤ 1 / 2 := by
      have hpi := Real.pi_lt_d2
      have hs : Real.sqrt 2 ≤ 3 / 2 := by
        rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
      nlinarith [Real.sqrt_nonneg 2]
    calc _ ≤ Real.pi ^ 2 / 48 * Real.sqrt S₂ * (Real.sqrt 2 * V) * (ε * R) := by gcongr
      _ = (Real.pi ^ 2 / 48 * Real.sqrt 2) * ε * (Real.sqrt S₂ * V * R) := by ring
      _ ≤ 1 / 2 * ε * (Real.sqrt S₂ * V * R) := by gcongr
      _ = ε / 2 * Real.sqrt S₂ * V * R := by ring
  -- the smoothed-away term
  have hT2 : Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) *
      Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
      Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q), moebiusWindowRow Q n ^ 2 / (n : ℝ) ^ 4) ≤
      ε / 2 * Real.sqrt S₂ * V * R := by
    have h1 : Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) ≤ ε / 2 * Real.sqrt S₂ := by
      rw [← Real.sqrt_mul (by positivity), show ε / 2 * Real.sqrt S₂ =
        Real.sqrt ((ε / 2) ^ 2 * S₂) by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ?_
      rw [mul_sum, mul_sum]
      refine sum_le_sum fun p hp => ?_
      have h8 := hSP p hp
      have hc2 : 0 ≤ c p ^ 2 * p := by positivity
      nlinarith
    have h2 : Real.sqrt (∑ n ∈ Icc (Q + 1) (Q + Q), moebiusWindowRow Q n ^ 2 / (n : ℝ) ^ 4) ≤ R :=
      Real.sqrt_le_sqrt (sum_Icc_moebiusWindowRow_sq_div_le hQ1)
    exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hV) h2 (Real.sqrt_nonneg _) (by positivity)
  calc _ ≤ _ := ht
    _ ≤ (ε / 2 * Real.sqrt S₂ * V * R) + (ε / 2 * Real.sqrt S₂ * V * R) +
        |moebiusBlockMass Q| / 6 * ∑ p ∈ S, |c p| / p +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 := by
        gcongr
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
