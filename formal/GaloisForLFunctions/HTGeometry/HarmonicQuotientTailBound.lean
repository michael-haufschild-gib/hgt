import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Quantitative harmonic quotient tails

The reciprocal mass of rows with complementary quotient below `T` is
at most `1 + log (2T)`. A two-range row estimate consequently gives an
explicit squared-norm bound even for a moving quotient cutoff.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry

private theorem sum_Ioc_one_div_eq_sub_harmonic {M N : ℕ} (hMN : M ≤ N) :
    (∑ n ∈ Ioc M N, 1 / (n : ℝ)) = (harmonic N : ℝ) - harmonic M := by
  have hset : Ioc M N = Icc 1 N \ Icc 1 M := by
    ext n
    simp only [mem_Ioc, mem_sdiff, mem_Icc]
    omega
  have hsub : Icc 1 M ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
  rw [hset]
  have h := sum_sdiff (f := fun n : ℕ => 1 / (n : ℝ)) hsub
  rw [_root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic,
    _root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic] at h
  exact eq_sub_iff_add_eq.mpr h

/-- The harmonic mass below a complementary-quotient cutoff has only logarithmic cost. -/
theorem harmonic_quotient_tail_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T), 1 / (n : ℝ)) ≤
      1 + Real.log (2 * T) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  let M : ℕ := ⌊(N : ℝ) / T⌋₊
  have hMle : M ≤ N := by
    have h : (M : ℝ) ≤ N :=
      (Nat.floor_le (div_nonneg hN0.le hT0.le)).trans (div_le_self hN0.le hT)
    exact_mod_cast h
  have hsub : (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T) ⊆ Ioc M N := by
    intro n hn
    obtain ⟨hn, hquot⟩ := mem_filter.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hx : (N : ℝ) / T < n := by
      apply (div_lt_iff₀ hT0).mpr
      have h := (div_lt_iff₀ hn0).mp hquot
      nlinarith only [h]
    have hMn : (M : ℝ) < n := (Nat.floor_le (div_nonneg hN0.le hT0.le)).trans_lt hx
    exact mem_Ioc.mpr ⟨by exact_mod_cast hMn, (mem_Icc.mp hn).2⟩
  have hbound : (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T), 1 / (n : ℝ)) ≤
      (harmonic N : ℝ) - harmonic M := by
    rw [← sum_Ioc_one_div_eq_sub_harmonic hMle]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
  have hupper := harmonic_le_one_add_log N
  by_cases hx : (N : ℝ) / T < 1
  · have hM0 : M = 0 := Nat.floor_eq_zero.mpr hx
    rw [hM0, harmonic_zero, Rat.cast_zero, sub_zero] at hbound
    have hNT : (N : ℝ) < T := (div_lt_one hT0).mp hx
    have hlog : Real.log N ≤ Real.log (2 * T) :=
      Real.log_le_log hN0 (by linarith only [hNT, hT0])
    linarith only [hbound, hupper, hlog]
  · have hx1 : 1 ≤ (N : ℝ) / T := le_of_not_gt hx
    have hM1 : 1 ≤ M := (Nat.one_le_floor_iff _).mpr hx1
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM1R
    have hfloor : (N : ℝ) / T < M + 1 := Nat.lt_floor_add_one _
    have hdouble : (N : ℝ) / T < 2 * M := by linarith only [hfloor, hM1R]
    have hratio : (N : ℝ) / M ≤ 2 * T := by
      apply (div_le_iff₀ hM0).mpr
      have h := (div_lt_iff₀ hT0).mp hdouble
      nlinarith only [h]
    have hlog : Real.log N - Real.log M ≤ Real.log (2 * T) := by
      rw [← Real.log_div hN0.ne' hM0.ne']
      exact Real.log_le_log (div_pos hN0 hM0) hratio
    have hlower : Real.log M ≤ (harmonic M : ℝ) := by
      have h := log_add_one_le_harmonic M
      have hm : Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
        Real.log_le_log hM0 (by exact_mod_cast Nat.le_succ M)
      linarith only [h, hm]
    linarith only [hbound, hupper, hlower, hlog]

/-- A good quotient range and a global row bound give a quantitative square-error estimate. -/
theorem sum_sq_le_harmonic_quotient_tail {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T)
    {A B : ℝ} (R : ℕ → ℝ)
    (hglobal : ∀ n ∈ Icc 1 N, |R n| ≤ B / Real.sqrt n)
    (hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n → |R n| ≤ A / Real.sqrt n) :
    (∑ n ∈ Icc 1 N, R n ^ 2) ≤
      A ^ 2 * (1 + Real.log N) + B ^ 2 * (1 + Real.log (2 * T)) := by
  have hsquare (n : ℕ) (C : ℝ) (hc : |R n| ≤ C / Real.sqrt n) :
      R n ^ 2 ≤ C ^ 2 / n := by
    calc
      _ = |R n| * |R n| := by rw [← sq, sq_abs]
      _ ≤ (C / Real.sqrt n) * (C / Real.sqrt n) :=
        mul_le_mul hc hc (abs_nonneg _) ((abs_nonneg _).trans hc)
      _ = _ := by rw [← sq, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      R n ^ 2 ≤ A ^ 2 / n + if (N : ℝ) / n < T then B ^ 2 / n else 0 := by
    by_cases hq : (N : ℝ) / n < T
    · rw [if_pos hq]
      exact (hsquare n B (hglobal n hn)).trans
        (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))
    · rw [if_neg hq, add_zero]
      exact hsquare n A (hgood n hn (le_of_not_gt hq))
  have hsum : (∑ n ∈ Icc 1 N, R n ^ 2) ≤
      A ^ 2 * (harmonic N : ℝ) + B ^ 2 *
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T), 1 / (n : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (A ^ 2 / n + if (N : ℝ) / n < T then B ^ 2 / n else 0) :=
        sum_le_sum hpoint
      _ = _ := by
        rw [sum_add_distrib, ← sum_filter, ← _root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic,
          mul_sum, mul_sum]
        apply congrArg₂ (fun x y : ℝ => x + y)
        · exact sum_congr rfl fun n _ => by ring
        · exact sum_congr rfl fun n _ => by ring
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (sq_nonneg _))
    (mul_le_mul_of_nonneg_left (harmonic_quotient_tail_le hN hT) (sq_nonneg _)))

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.harmonic_quotient_tail_le
#print axioms GaloisForLFunctions.HTGeometry.sum_sq_le_harmonic_quotient_tail
