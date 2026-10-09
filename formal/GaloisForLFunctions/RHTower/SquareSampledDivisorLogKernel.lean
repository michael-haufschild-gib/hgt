import GaloisForLFunctions.RHTower.DivisorRemainderLogAbelBound

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

/-- A nonnegative increasing weight costs at most twice its terminal bound. -/
theorem abs_sum_mul_monotone_le_of_prefix_bound
    (a w : ℕ → ℝ) (B W : ℝ) (N : ℕ) (hW : 0 ≤ W)
    (hw : ∀ n < N, 0 ≤ w n) (hmono : Monotone w)
    (hwW : ∀ n < N, w n ≤ W)
    (hA : ∀ n ≤ N, |∑ k ∈ range n, a k| ≤ B) :
    |∑ n ∈ range N, a n * w n| ≤ 2 * B * W := by
  have hB : 0 ≤ B := by simpa using hA 0 (Nat.zero_le _)
  cases N with
  | zero => simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB) hW
  | succ N =>
    have hprefix (n : ℕ) (hn : n ≤ N) : |deningerPartialSum a n| ≤ B :=
      hA (n + 1) (by omega)
    have hdiff (n : ℕ) : 0 ≤ w (n + 1) - w n :=
      sub_nonneg.mpr (hmono (Nat.le_succ n))
    have habs (n : ℕ) : |w n - w (n + 1)| = w (n + 1) - w n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono (Nat.le_succ n)))]
      ring
    calc
      |∑ n ∈ range (N + 1), a n * w n|
          = |deningerPartialSum a N * w N +
              ∑ n ∈ range N, deningerPartialSum a n * (w n - w (n + 1))| :=
            congrArg abs (deningerAbelSummation a w N)
      _ ≤ |deningerPartialSum a N * w N| +
              ∑ n ∈ range N, |deningerPartialSum a n * (w n - w (n + 1))| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
      _ ≤ B * w N + ∑ n ∈ range N, B * (w (n + 1) - w n) := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hw N (by omega))]
          exact mul_le_mul_of_nonneg_right (hprefix N le_rfl) (hw N (by omega))
        · apply sum_le_sum
          intro n hn
          rw [abs_mul, habs]
          exact mul_le_mul_of_nonneg_right (hprefix n (by have := mem_range.mp hn; omega)) (hdiff n)
      _ = B * (2 * w N - w 0) := by
        rw [← mul_sum, sum_range_sub]
        ring
      _ ≤ 2 * B * W := by
        have := hw 0 (by omega)
        have := hwW N (by omega)
        nlinarith [mul_nonneg hB (sub_nonneg.mpr this), mul_nonneg hB (hw 0 (by omega))]

/-- Explicit signed square-sampled divisor-error prefix envelope. -/
noncomputable def squareSampledDivisorRemainderBound (N q : ℕ) : ℝ :=
  (N : ℝ) * (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) +
    16 * ((N : ℝ) + (q * squareSampledHyperbolaCutoff N q : ℕ)) *
      Real.sqrt (squareSampledHyperbolaCutoff N q) *
        (1 + Real.log (q * squareSampledHyperbolaCutoff N q : ℕ)) ^ 4

private theorem log_nat_mono {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast h)

theorem squareSampledDivisorRemainderBound_nonneg (N q : ℕ) :
    0 ≤ squareSampledDivisorRemainderBound N q := by
  have hl : 0 ≤ Real.log ((N : ℝ) ^ 2 + 1) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (N : ℝ)])
  unfold squareSampledDivisorRemainderBound
  positivity

theorem squareSampledDivisorRemainderBound_mono (q : ℕ) :
    Monotone (fun N => squareSampledDivisorRemainderBound N q) := by
  intro M N hMN
  have hD : squareSampledHyperbolaCutoff M q ≤ squareSampledHyperbolaCutoff N q := by
    unfold squareSampledHyperbolaCutoff
    apply Nat.sqrt_le_sqrt
    apply Nat.div_le_div_right
    have hpred := Nat.sub_le_sub_right hMN 1
    nlinarith
  have hR : q * squareSampledHyperbolaCutoff M q ≤ q * squareSampledHyperbolaCutoff N q :=
    Nat.mul_le_mul_left q hD
  have hlog := log_nat_mono hR
  have hlog0 := Real.log_natCast_nonneg (q * squareSampledHyperbolaCutoff M q)
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hpoly : Real.log ((M : ℝ) ^ 2 + 1) ≤ Real.log ((N : ℝ) ^ 2 + 1) :=
    Real.log_le_log (by positivity)
      (by nlinarith [show (0 : ℝ) ≤ M by positivity, show (0 : ℝ) ≤ N by positivity])
  have hpoly0 : 0 ≤ Real.log ((M : ℝ) ^ 2 + 1) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (M : ℝ)])
  have hsum : (M : ℝ) + (q * squareSampledHyperbolaCutoff M q : ℕ) ≤
      (N : ℝ) + (q * squareSampledHyperbolaCutoff N q : ℕ) :=
    add_le_add hMN' (by exact_mod_cast hR)
  have hsqrt : Real.sqrt (squareSampledHyperbolaCutoff M q) ≤
      Real.sqrt (squareSampledHyperbolaCutoff N q) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hD)
  have hpow : (1 + Real.log (q * squareSampledHyperbolaCutoff M q : ℕ)) ^ 4 ≤
      (1 + Real.log (q * squareSampledHyperbolaCutoff N q : ℕ)) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  unfold squareSampledDivisorRemainderBound
  apply add_le_add
  · exact mul_le_mul hMN' (by linarith) (by linarith) (by positivity)
  · have h16 := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 16)
    have hprod := mul_le_mul h16 hsqrt (Real.sqrt_nonneg _) (by positivity)
    exact mul_le_mul hprod hpow (by positivity) (by positivity)

/-- The increasing logarithmic boundary weight preserves the square-prefix saving. -/
theorem abs_sum_mobiusSquareDivisorRemainder_square_log_weight_le
    (N : ℕ) {q : ℕ} (hq : 0 < q) :
    |∑ s ∈ range N, (Real.log (q : ℝ) + Real.log (s ^ 2 / q : ℕ) / 2) *
        mobiusSquareDivisorRemainder (s ^ 2 / q)| ≤
      2 * squareSampledDivisorRemainderBound N q *
        (Real.log (q : ℝ) + Real.log ((N : ℝ) ^ 2 + 1) / 2) := by
  let w : ℕ → ℝ := fun s => Real.log (q : ℝ) + Real.log (s ^ 2 / q : ℕ) / 2
  have hw0 (s : ℕ) : 0 ≤ w s := by
    dsimp [w]
    have := Real.log_natCast_nonneg q
    have := Real.log_natCast_nonneg (s ^ 2 / q)
    positivity
  have hmono : Monotone w := by
    intro s t hst
    have hsq : s ^ 2 / q ≤ t ^ 2 / q := Nat.div_le_div_right (by nlinarith)
    have hl := log_nat_mono hsq
    dsimp [w]
    linarith
  have hupper (s : ℕ) (hs : s < N) :
      w s ≤ Real.log (q : ℝ) + Real.log ((N : ℝ) ^ 2 + 1) / 2 := by
    have hx : s ^ 2 / q ≤ N ^ 2 + 1 := (Nat.div_le_self _ _).trans (by nlinarith)
    have hl := log_nat_mono hx
    push_cast at hl
    dsimp [w]
    linarith
  have hW : 0 ≤ Real.log (q : ℝ) + Real.log ((N : ℝ) ^ 2 + 1) / 2 := by
    have := Real.log_natCast_nonneg q
    have := Real.log_nonneg (by nlinarith [sq_nonneg (N : ℝ)] : 1 ≤ (N : ℝ) ^ 2 + 1)
    linarith
  have hA (M : ℕ) (hM : M ≤ N) :
      |∑ s ∈ range M, mobiusSquareDivisorRemainder (s ^ 2 / q)| ≤
        squareSampledDivisorRemainderBound N q :=
    (abs_sum_mobiusSquareDivisorRemainder_square_quotient_le M hq).trans
      (squareSampledDivisorRemainderBound_mono q hM)
  simpa only [w, mul_comm] using
    abs_sum_mul_monotone_le_of_prefix_bound
      (fun s => mobiusSquareDivisorRemainder (s ^ 2 / q)) w
      (squareSampledDivisorRemainderBound N q)
      (Real.log (q : ℝ) + Real.log ((N : ℝ) ^ 2 + 1) / 2) N hW
      (fun s _ => hw0 s) hmono hupper hA

/-- Uniform explicit control of both logarithmic terms in the divisor remainder kernel. -/
theorem abs_mobiusSquareDivisorRemainderKernel_le (N : ℕ) {q : ℕ} (hq : 0 < q) :
    |mobiusSquareDivisorRemainderKernel N q| ≤
      2 * squareSampledDivisorRemainderBound N q *
        (Real.log (q : ℝ) + Real.log ((N : ℝ) ^ 2 + 1) / 2) +
      (N : ℝ) / 2 * (8 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) *
        Real.log ((N : ℝ) ^ 2 + 1) := by
  let L : ℝ := Real.log ((N : ℝ) ^ 2 + 1)
  let inner : ℕ → ℝ := fun s => ∑ n ∈ range (s ^ 2 / q),
    mobiusSquareDivisorRemainder n * (Real.log (n : ℝ) - Real.log (n + 1 : ℕ))
  have hinner (s : ℕ) (hs : s ∈ range N) : |inner s| ≤ (8 + 2 * L) * L := by
    have hsN := mem_range.mp hs
    have hx : s ^ 2 / q ≤ N ^ 2 + 1 := (Nat.div_le_self _ _).trans (by nlinarith)
    have hl := log_nat_mono hx
    push_cast at hl
    have hl0 := Real.log_natCast_nonneg (s ^ 2 / q)
    have hL0 : 0 ≤ L := hl0.trans hl
    apply (abs_mobiusSquareDivisorRemainder_log_difference_le (s ^ 2 / q)).trans
    change (8 + 2 * Real.log (s ^ 2 / q : ℕ)) * Real.log (s ^ 2 / q : ℕ) ≤ _
    gcongr
  have hsumInner : |∑ s ∈ range N, inner s| ≤ (N : ℝ) * ((8 + 2 * L) * L) := by
    calc
      _ ≤ ∑ s ∈ range N, |inner s| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ range N, (8 + 2 * L) * L := sum_le_sum hinner
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]
  have hkernel : mobiusSquareDivisorRemainderKernel N q =
      (∑ s ∈ range N, (Real.log (q : ℝ) + Real.log (s ^ 2 / q : ℕ) / 2) *
        mobiusSquareDivisorRemainder (s ^ 2 / q)) +
      (1 / 2 : ℝ) * ∑ s ∈ range N, inner s := by
    simp only [mobiusSquareDivisorRemainderKernel, mobiusSquareDivisorLogAbel,
      sum_add_distrib, mul_sum, inner]
  rw [hkernel]
  have htriangle := abs_add_le
    (∑ s ∈ range N, (Real.log (q : ℝ) + Real.log (s ^ 2 / q : ℕ) / 2) *
      mobiusSquareDivisorRemainder (s ^ 2 / q))
    ((1 / 2 : ℝ) * ∑ s ∈ range N, inner s)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at htriangle
  have hboundary := abs_sum_mobiusSquareDivisorRemainder_square_log_weight_le N hq
  dsimp [L] at hsumInner
  nlinarith

end RHTower
