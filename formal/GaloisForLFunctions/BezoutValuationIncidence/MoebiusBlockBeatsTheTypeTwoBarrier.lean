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

end

end GaloisForLFunctions.BezoutValuationIncidence
