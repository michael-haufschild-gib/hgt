import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTouchingCrossMatrixHasAUniformErrorBudget
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap

/-!
# The arithmetic boundary at touching

At width `1/N`, two unequal positive integers, one at most `N`, can have
logarithmic distance at most that width only at the pair `N,N+1`.
Thus the first non-ratio prime interactions form a single boundary star.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticEffectivityTheory
open _root_.RHTower (vonMangoldtAtom)

/-- An integer log window at touching contains exactly one possible unequal boundary pair. -/
theorem small_integer_log_gap_forces_boundary {N a b : ℕ} (hN : 2 ≤ N)
    (ha : a ∈ Icc 1 N) (hb : 1 ≤ b) (hne : a ≠ b)
    (hgap : |Real.log b - Real.log a| ≤ 1 / (N : ℝ)) :
    a = N ∧ b = N + 1 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbN : N < b := by
    by_contra h
    exact (not_lt_of_ge hgap) (inv_horizon_lt_integer_log_gap ha (mem_Icc.mpr ⟨hb, by omega⟩) hne)
  have haN : a = N := by
    by_contra h
    have hsucc : a + 1 ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp ha).2; omega⟩
    have hlo := inv_horizon_lt_integer_log_gap ha hsucc (by omega)
    have hlog0 : Real.log a ≤ Real.log (a + 1 : ℕ) :=
      Real.log_le_log ha0 (by exact_mod_cast Nat.le_succ a)
    have hlogb : Real.log (a + 1 : ℕ) ≤ Real.log b :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show a + 1 ≤ b by have := (mem_Icc.mp ha).2; omega))
    rw [abs_of_nonneg (sub_nonneg.mpr hlog0)] at hlo
    exact (not_lt_of_ge hgap) (hlo.trans_le
      ((sub_le_sub_right hlogb _).trans (le_abs_self _)))
  subst a
  refine ⟨rfl, ?_⟩
  by_contra h
  have hNb : N + 2 ≤ b := by omega
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hratio : (N : ℝ) / (N + 2) < 1 := (div_lt_one hN2).mpr (by linarith)
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hN0 hN2) (ne_of_lt hratio)
  rw [Real.log_div hN0.ne' hN2.ne'] at hlog
  have hlower : 2 / ((N : ℝ) + 2) < Real.log ((N : ℝ) + 2) - Real.log N := by
    have he : 2 / ((N : ℝ) + 2) = 1 - (N : ℝ) / (N + 2) := by
      field_simp [hN2.ne']
      ring
    rw [he]
    linarith only [hlog]
  have hfrac : 1 / (N : ℝ) ≤ 2 / ((N : ℝ) + 2) := by
    apply (div_le_div_iff₀ hN0 hN2).mpr
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hN']
  have hmon : Real.log ((N : ℝ) + 2) ≤ Real.log b :=
    Real.log_le_log hN2 (by exact_mod_cast hNb)
  exact (not_lt_of_ge hgap) ((hfrac.trans_lt hlower).trans_le
    ((sub_le_sub_right hmon _).trans (le_abs_self _)))

/-- The upward non-ratio term at touching can only meet the last atom. -/
theorem nonRatio_up_term_eq_boundary {g : ℝ → ℝ} {N k m n : ℕ} (hN : 2 ≤ N)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (1 / (N : ℝ)) → g u = 0)
    (hk : 2 ≤ k) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))) =
      if n = N ∧ k * m = N + 1 then bumpCorr g (Real.log (N + 1 : ℕ) - Real.log N) else 0 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hkm : 1 ≤ k * m := Nat.mul_pos (by omega) (mem_Icc.mp hm).1
  have hlog : Real.log k - (Real.log n - Real.log m) = Real.log (k * m : ℕ) - Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hk0.ne' hm0.ne']
    ring
  by_cases heq : n = k * m
  · rw [if_pos heq, if_neg (by intro h; omega)]
  rw [if_neg heq, hlog]
  by_cases hb : n = N ∧ k * m = N + 1
  · rw [if_pos hb, hb.1, hb.2]
  · rw [if_neg hb]
    apply bumpCorr_eq_zero hsupp
    by_contra h
    exact hb (small_integer_log_gap_forces_boundary hN hn hkm heq (not_lt.mp h))

/-- The full non-ratio lag at touching is one boundary star and its transpose. -/
theorem nonRatioLag_eq_boundary_star {g : ℝ → ℝ} {N k : ℕ} (hN : 2 ≤ N)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (1 / (N : ℝ)) → g u = 0)
    (hk : 2 ≤ k) (x : ℕ → ℝ) :
    nonRatioLag g N k x =
      2 * bumpCorr g (Real.log (N + 1 : ℕ) - Real.log N) * x N *
        ∑ m ∈ Icc 1 N, (if k * m = N + 1 then x m else 0) := by
  classical
  let d : ℝ := bumpCorr g (Real.log (N + 1 : ℕ) - Real.log N)
  have hNmem : N ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hterm (m n : ℕ) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
      x m * x n *
          ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
          (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
        (if m = N then d * x N * (if k * n = N + 1 then x n else 0) else 0) +
          (if n = N then d * x N * (if k * m = N + 1 then x m else 0) else 0) := by
    rw [nonRatio_down_eq, bumpCorr_neg,
      nonRatio_up_term_eq_boundary hN hsupp hk hn hm,
      nonRatio_up_term_eq_boundary hN hsupp hk hm hn]
    dsimp only [d]
    by_cases hmN : m = N <;> by_cases hnN : n = N <;>
      simp only [hmN, hnN, false_and, true_and, ite_true, ite_false,
        add_zero, zero_add, mul_zero] <;> split_ifs <;> ring
  unfold nonRatioLag
  have he : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
      ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
      (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))))) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        ((if m = N then d * x N * (if k * n = N + 1 then x n else 0) else 0) +
          (if n = N then d * x N * (if k * m = N + 1 then x m else 0) else 0)) :=
    sum_congr rfl fun m hm => sum_congr rfl fun n hn => hterm m n hm hn
  rw [he]
  simp only [sum_add_distrib]
  have hfirst : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      if m = N then d * x N * (if k * n = N + 1 then x n else 0) else 0) =
      d * x N * ∑ n ∈ Icc 1 N, if k * n = N + 1 then x n else 0 := by
    simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', hNmem, ite_true, ← mul_sum]
  have hsecond : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      if n = N then d * x N * (if k * m = N + 1 then x m else 0) else 0) =
      d * x N * ∑ m ∈ Icc 1 N, if k * m = N + 1 then x m else 0 := by
    simp only [sum_ite_eq', hNmem, ite_true, ← mul_sum]
  rw [hfirst, hsecond]
  dsimp only [d]
  ring

/-- The actual prime correction is a finite weighted boundary star. -/
theorem nonRatioForm_eq_boundary_star {g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (1 / (N : ℝ)) → g u = 0) (x : ℕ → ℝ) :
    nonRatioForm g N x =
      2 * bumpCorr g (Real.log (N + 1 : ℕ) - Real.log N) *
        ∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
          (if k * m = N + 1 then vonMangoldtAtom k * (x N * x m) else 0) := by
  classical
  have hzero : ∀ k, k ∉ Icc 2 (N + 1) → vonMangoldtAtom k * nonRatioLag g N k x = 0 := by
    intro k hk
    by_cases hk2 : k < 2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
    have hklarge : N + 1 < k := by
      simp only [mem_Icc, not_and_or, not_le] at hk
      omega
    rw [nonRatioLag_eq_boundary_star hN hsupp (by omega)]
    have hmzero : (∑ m ∈ Icc 1 N, if k * m = N + 1 then x m else 0) = 0 := by
      apply sum_eq_zero
      intro m hm
      have hkm : k ≤ k * m := by
        simpa only [mul_one] using Nat.mul_le_mul_left k (mem_Icc.mp hm).1
      rw [if_neg (by omega)]
    rw [hmzero, mul_zero, mul_zero]
  unfold nonRatioForm
  rw [tsum_eq_sum hzero, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [nonRatioLag_eq_boundary_star hN hsupp (mem_Icc.mp hk).1, mul_sum, mul_sum, mul_sum]
  apply sum_congr rfl
  intro m hm
  split_ifs <;> ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.small_integer_log_gap_forces_boundary

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.nonRatioLag_eq_boundary_star

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.nonRatioForm_eq_boundary_star
