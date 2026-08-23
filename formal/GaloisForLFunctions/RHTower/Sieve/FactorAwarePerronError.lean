import GaloisForLFunctions.RHTower.Sieve.GhsLatticeCutoff
import GaloisForLFunctions.RHTower.Sieve.PerronCutoffComparisons

/-!
# The factor-aware truncated Perron error

The truncated Perron weight `min(1, 1/(T|log(x/m)|))` attached to a modulus `m = d·n` is summed
over `n` after splitting at `1/2 ≤ x/m ≤ 2`.  Near the cutoff the logarithm is replaced by the
displacement and the lattice estimate applies; far from it the logarithm is bounded below by
`log 2` and only the harmonic sum remains.  Both halves keep the divisor `d` explicit, which is
what allows the error to be summed against the arithmetic weights of the two prime factors
instead of against a single collapsed coefficient sequence.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The truncated Perron weight, with its true value `1` at the cutoff itself. -/
def truncPerronWeight (T y : ℝ) : ℝ :=
  if Real.log y = 0 then 1 else min 1 (1 / (T * |Real.log y|))

theorem truncPerronWeight_nonneg {T : ℝ} (hT : 0 ≤ T) (y : ℝ) : 0 ≤ truncPerronWeight T y := by
  rw [truncPerronWeight]
  split_ifs with h
  · norm_num
  · exact le_min zero_le_one (by positivity)

theorem truncPerronWeight_le_one (T y : ℝ) : truncPerronWeight T y ≤ 1 := by
  rw [truncPerronWeight]
  split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

/-- **The near-cutoff Perron weight.**  Inside the dyadic window the reciprocal logarithm is
dominated by the reciprocal displacement. -/
theorem perron_weight_near_le {x n T : ℝ} (hx : 0 < x) (hn : 0 < n) (hT : 0 < T)
    (h1 : x / 2 ≤ n) (h2 : n ≤ 2 * x) (hne : n ≠ x) :
    1 / (T * |Real.log (x / n)|) ≤ 4 * x / (T * |x - n|) := by
  have hy1 : (1 : ℝ) / 2 ≤ x / n := by rw [le_div_iff₀ hn]; linarith
  have hy2 : x / n ≤ 2 := by rw [div_le_iff₀ hn]; linarith
  have hkey := abs_sub_one_le_two_mul_abs_log hy1 hy2
  have hdisp : |x / n - 1| = |x - n| / n := by
    rw [show x / n - 1 = (x - n) / n by field_simp, abs_div, abs_of_pos hn]
  rw [hdisp, div_le_iff₀ hn] at hkey
  have hxn : (0 : ℝ) < |x - n| := by
    rw [abs_pos]; intro hc; exact hne (by linarith [sub_eq_zero.mp hc])
  have hlog0 : (0 : ℝ) < |Real.log (x / n)| := by nlinarith [hkey, hxn, hn]
  have hmul : |x - n| ≤ 4 * x * |Real.log (x / n)| := by nlinarith [hkey, h2, abs_nonneg (x - n)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hmul hT.le]

/-- **The far-cutoff Perron weight.** -/
theorem perron_weight_far_le {x n T : ℝ} (hx : 0 < x) (hn : 0 < n) (hT : 0 < T)
    (h : n < x / 2 ∨ 2 * x < n) :
    1 / (T * |Real.log (x / n)|) ≤ 1 / (T * Real.log 2) := by
  have hcase : x / n ≤ 1 / 2 ∨ 2 ≤ x / n := by
    rcases h with h | h
    · right; rw [le_div_iff₀ hn]; linarith
    · left; rw [div_le_div_iff₀ hn (by norm_num)]; linarith
  have hkey := log_two_le_abs_log (by positivity) hcase
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hkey hT.le)

/-- At most one multiple of a positive `d` hits `x`. -/
theorem card_filter_mul_eq_le_one {x d : ℝ} (hd : 0 < d) (M : ℕ) :
    (((Finset.Icc 1 M).filter (fun n : ℕ => d * (n : ℝ) = x)).card) ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [Finset.mem_filter] at ha hb
  have h : d * (a : ℝ) = d * (b : ℝ) := by rw [ha.2, hb.2]
  have hab : (a : ℝ) = (b : ℝ) := mul_left_cancel₀ hd.ne' h
  exact_mod_cast hab

/-- **(E5): the near half of the factor-aware Perron error.**  For a modulus `d`, summing the
Perron weight over the multiples `d·n` lying in the dyadic window `[x/2, 2x]` costs only the
lattice estimate, with the divisor `d` retained in the main term. -/
theorem perron_near_pair_le {x T d : ℝ} (hx : 0 < x) (hT : 0 < T) (hd : 0 < d) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M,
        (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then
            (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))) else 0)
      ≤ 2 * (3 + (16 * x / (T * d)) * (1 + Real.log M)) + 2 := by
  classical
  have hpoint : ∀ n ∈ Finset.Icc 1 M,
      (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then
          (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))) else 0)
        ≤ 2 * min 1 (x / ((T / 4) * |x - d * (n : ℝ)|))
            + (if d * (n : ℝ) = x then 2 else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hdn : (0 : ℝ) < d * (n : ℝ) := by positivity
    have hfac0 : (0 : ℝ) < x / (d * (n : ℝ)) := by positivity
    have hmin : (0 : ℝ) ≤ min 1 (x / ((T / 4) * |x - d * (n : ℝ)|)) :=
      le_min zero_le_one (by positivity)
    rcases eq_or_ne (d * (n : ℝ)) x with heq | hne
    · rw [if_pos heq]
      have hterm : (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then
          (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))) else 0) ≤ 2 := by
        split_ifs with hnear
        · rw [heq, div_self hx.ne']
          have := truncPerronWeight_le_one T (1 : ℝ)
          linarith
        · norm_num
      linarith
    · rw [if_neg hne]
      have hlogne : Real.log (x / (d * (n : ℝ))) ≠ 0 := by
        intro hc
        have hy : x / (d * (n : ℝ)) = 1 := by
          have h := Real.exp_log hfac0
          rw [hc, Real.exp_zero] at h
          exact h.symm
        rw [div_eq_one_iff_eq hdn.ne'] at hy
        exact hne hy.symm
      split_ifs with hnear
      · have hfac : x / (d * (n : ℝ)) ≤ 2 := by
          rw [div_le_iff₀ hdn]; linarith [hnear.1]
        rw [truncPerronWeight, if_neg hlogne]
        have hmin0 : (0 : ℝ) ≤ min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|)) :=
          le_min zero_le_one (by positivity)
        have hcmp := perron_weight_near_le hx hdn hT hnear.1 hnear.2 hne
        have hcmp' : min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|))
            ≤ min 1 (x / ((T / 4) * |x - d * (n : ℝ)|)) := by
          refine min_le_min le_rfl (hcmp.trans (le_of_eq ?_))
          field_simp
        have hstep : (x / (d * (n : ℝ))) * min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|))
            ≤ 2 * min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|)) :=
          mul_le_mul_of_nonneg_right hfac hmin0
        linarith
      · linarith
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [Finset.sum_add_distrib]
  have hlat : ∑ n ∈ Finset.Icc 1 M, 2 * min 1 (x / ((T / 4) * |x - d * (n : ℝ)|))
      ≤ 2 * (3 + (16 * x / (T * d)) * (1 + Real.log M)) := by
    rw [← Finset.mul_sum]
    have h := lattice_min_sum_le hx hd (show (0:ℝ) < T / 4 by positivity) M
    have hrw : 4 * x / (T / 4 * d) = 16 * x / (T * d) := by field_simp; ring
    rw [hrw] at h
    linarith
  have hexc : ∑ n ∈ Finset.Icc 1 M, (if d * (n : ℝ) = x then (2:ℝ) else 0) ≤ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := card_filter_mul_eq_le_one (x := x) hd M
    have hc : (((Finset.Icc 1 M).filter (fun n : ℕ => d * (n : ℝ) = x)).card : ℝ) ≤ 1 := by
      exact_mod_cast this
    linarith
  linarith

/-- **(E6): the far half of the factor-aware Perron error.**  Outside the dyadic window the
logarithm is bounded below by `log 2`, so only the harmonic sum survives. -/
theorem perron_far_pair_le {x T d : ℝ} (hx : 0 < x) (hT : 0 < T) (hd : 0 < d) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M,
        (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then 0
          else (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))))
      ≤ (x / (T * Real.log 2 * d)) * (1 + Real.log M) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpoint : ∀ n ∈ Finset.Icc 1 M,
      (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then 0
        else (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))))
        ≤ (x / (T * Real.log 2 * d)) * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hdn : (0 : ℝ) < d * (n : ℝ) := by positivity
    split_ifs with hnear
    · positivity
    · have hfar : d * (n : ℝ) < x / 2 ∨ 2 * x < d * (n : ℝ) := by
        by_contra hc
        push Not at hc
        exact hnear hc
      have hne : d * (n : ℝ) ≠ x := by
        rcases hfar with h | h <;> intro hc <;> rw [hc] at h <;> linarith
      have hlogne : Real.log (x / (d * (n : ℝ))) ≠ 0 := by
        intro hc
        have hfac0 : (0 : ℝ) < x / (d * (n : ℝ)) := by positivity
        have hy : x / (d * (n : ℝ)) = 1 := by
          have h := Real.exp_log hfac0
          rw [hc, Real.exp_zero] at h
          exact h.symm
        rw [div_eq_one_iff_eq hdn.ne'] at hy
        exact hne hy.symm
      rw [truncPerronWeight, if_neg hlogne]
      have hw := perron_weight_far_le hx hdn hT hfar
      have hwm : min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|)) ≤ 1 / (T * Real.log 2) :=
        (min_le_right _ _).trans hw
      have hmin0 : (0 : ℝ) ≤ min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|)) :=
        le_min zero_le_one (by positivity)
      calc (x / (d * (n : ℝ))) * min 1 (1 / (T * |Real.log (x / (d * (n : ℝ)))|))
          ≤ (x / (d * (n : ℝ))) * (1 / (T * Real.log 2)) :=
            mul_le_mul_of_nonneg_left hwm (by positivity)
        _ = (x / (T * Real.log 2 * d)) * (1 / (n : ℝ)) := by
            field_simp
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log M :=
    sum_Icc_one_div_le_one_add_log M
  have hpos : (0 : ℝ) ≤ x / (T * Real.log 2 * d) := by positivity
  exact mul_le_mul_of_nonneg_left hharm hpos

end

end RHTower.Sieve
