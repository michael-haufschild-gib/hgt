import GaloisForLFunctions.RHTower.Sieve.FibreSmoothDecomp

/-!
# A majorant of the smooth model's increments, uniform in the shift

Summation by parts with the shift-sum inside needs a bound on `sup_k |w(k,j+1) − w(k,j)|`, not just
on the variation at each shift.  The three pieces of `fibreSmooth_decomp` each supply one, because
each depends on the shift monotonically:

* `c/(m+1) − c/m` is nondecreasing in `m`, so `kernelDiff`'s increment is nondecreasing in `k` and
  therefore lies between its values at `k = 1` and `k = K`;
* `m ↦ (c/m − D)⁺` is convex, so its one-step drop is largest at the smallest argument, i.e. at
  `k = 1`;
* the shortfall `(√x − x/i)⁺` does not involve the shift at all.

Hence `sup_k |Δ w| ≤ |Δ kernelDiff₁| + |Δ kernelDiff_K| + Δ⁻(overshoot at 1) + Δ⁺(shortfall)`, whose
sum over the support telescopes to `O(h)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- One-step drops of `c/m` shrink as `m` grows. -/
theorem div_succ_sub_div_antitone {c m m' : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hmm : m ≤ m') :
    c / (m + 1) - c / m ≤ c / (m' + 1) - c / m' := by
  have hm' : 0 < m' := lt_of_lt_of_le hm hmm
  have e1 : c / (m + 1) - c / m = -(c / (m * (m + 1))) := by
    field_simp
    ring
  have e2 : c / (m' + 1) - c / m' = -(c / (m' * (m' + 1))) := by
    field_simp
    ring
  rw [e1, e2, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hc (by positivity) (by nlinarith)

/-- Truncation at zero of `c/m − D` is convex: its one-step drop is largest at small `m`. -/
theorem trunc_div_diff_antitone {c D m m' : ℝ} (hc : 0 ≤ c) (hm : 0 < m)
    (hmm : m = m' ∨ m + 1 ≤ m') :
    max (c / m' - D) 0 - max (c / (m' + 1) - D) 0
      ≤ max (c / m - D) 0 - max (c / (m + 1) - D) 0 := by
  rcases hmm with heq | hstep
  · rw [heq]
  have hm' : 0 < m' := by linarith
  -- the right-hand side is nonnegative
  have hmono : c / (m + 1) ≤ c / m :=
    div_le_div_of_nonneg_left hc hm (by linarith)
  have hPnn : 0 ≤ max (c / m - D) 0 - max (c / (m + 1) - D) 0 := by
    have : max (c / (m + 1) - D) 0 ≤ max (c / m - D) 0 :=
      max_le_max (by linarith) le_rfl
    linarith
  rcases le_or_gt (c / m' - D) 0 with hneg | hpos
  · have h2 : c / (m' + 1) - D ≤ 0 := by
      have : c / (m' + 1) ≤ c / m' := div_le_div_of_nonneg_left hc hm' (by linarith)
      linarith
    rw [max_eq_right hneg, max_eq_right h2]
    linarith
  · -- the shift is still inside the positive region at `m + 1`
    have hstep' : c / m' ≤ c / (m + 1) :=
      div_le_div_of_nonneg_left hc (by linarith) hstep
    have hposm : 0 < c / (m + 1) - D := by linarith
    have hposm0 : 0 < c / m - D := by linarith
    rw [max_eq_left hposm.le, max_eq_left hposm0.le, max_eq_left hpos.le]
    have hupper : max (c / (m' + 1) - D) 0 ≥ c / (m' + 1) - D := le_max_left _ _
    have hkey : c / (m' + 1) - c / m' ≤ c / (m + 1) - c / m :=
      div_succ_sub_div_antitone hc hm (by linarith)
    linarith

/-- The overshoot decreases in the inner variable. -/
theorem fibreOver_antitone {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (k i : ℕ) :
    fibreOver x h k (i + 1) ≤ fibreOver x h k i := by
  have hc : (0 : ℝ) ≤ x + h * Real.sqrt x := by
    have : (0 : ℝ) ≤ h * Real.sqrt x := mul_nonneg hh (Real.sqrt_nonneg x)
    linarith
  rw [fibreOver, fibreOver]
  refine max_le_max ?_ le_rfl
  have hden : (0 : ℝ) < (i : ℝ) + (k : ℝ) + 1 := by positivity
  have : (x + h * Real.sqrt x) / (((i + 1 : ℕ) : ℝ) + (k : ℝ))
      ≤ (x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ) + 1) := by
    push_cast
    apply le_of_eq
    ring_nf
  refine le_trans (by linarith [this]) ?_
  have hmono : (x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ) + 1)
      ≤ (x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ)) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hi; subst hk
        norm_num
      · refine div_le_div_of_nonneg_left hc ?_ (by linarith)
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith [Nat.cast_nonneg (α := ℝ) i]
    · refine div_le_div_of_nonneg_left hc ?_ (by linarith)
      have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
      linarith [Nat.cast_nonneg (α := ℝ) k]
  linarith

/-- The shortfall increases in the inner variable. -/
theorem fibreUnder_monotone {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    fibreUnder x i ≤ fibreUnder x (i + 1) := by
  rw [fibreUnder, fibreUnder]
  refine max_le_max ?_ le_rfl
  have hmono : x / (((i + 1 : ℕ) : ℝ)) ≤ x / (i : ℝ) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp
      positivity
    · have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      refine div_le_div_of_nonneg_left hx hi0 ?_
      push_cast
      linarith
  linarith

/-- The shift-uniform majorant of the smooth model's increments. -/
def fibreIncrRaw (x h : ℝ) (K j : ℕ) : ℝ :=
  |kernelDiff x h 1 (j + 2) - kernelDiff x h 1 (j + 1)|
    + |kernelDiff x h K (j + 2) - kernelDiff x h K (j + 1)|
    + (fibreOver x h 1 (j + 1) - fibreOver x h 1 (j + 2))
    + (fibreUnder x (j + 2) - fibreUnder x (j + 1))

theorem fibreIncrRaw_nonneg {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (K j : ℕ) :
    0 ≤ fibreIncrRaw x h K j := by
  have h1 := fibreOver_antitone hx hh 1 (j + 1)
  have h2 := fibreUnder_monotone hx (j + 1)
  have h3 : (0 : ℝ) ≤ |kernelDiff x h 1 (j + 2) - kernelDiff x h 1 (j + 1)| := abs_nonneg _
  have h4 : (0 : ℝ) ≤ |kernelDiff x h K (j + 2) - kernelDiff x h K (j + 1)| := abs_nonneg _
  rw [fibreIncrRaw]
  linarith

/-- The `kernelDiff` increment is nondecreasing in the shift. -/
theorem kernelDiff_increment_mono_shift {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k k' : ℕ}
    (hk : 1 ≤ k) (hkk : k ≤ k') (n : ℕ) :
    kernelDiff x h k (n + 1) - kernelDiff x h k n
      ≤ kernelDiff x h k' (n + 1) - kernelDiff x h k' n := by
  have hc : (0 : ℝ) ≤ x + h * Real.sqrt x := by
    have : (0 : ℝ) ≤ h * Real.sqrt x := mul_nonneg hh (Real.sqrt_nonneg x)
    linarith
  have hm : (0 : ℝ) < (n : ℝ) + (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmm : (n : ℝ) + (k : ℝ) ≤ (n : ℝ) + (k' : ℝ) := by
    have : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk
    linarith
  have hbase := div_succ_sub_div_antitone (c := x + h * Real.sqrt x) hc hm hmm
  rw [kernelDiff, kernelDiff, kernelDiff, kernelDiff]
  push_cast
  have e1 : (n : ℝ) + 1 + (k : ℝ) = ((n : ℝ) + (k : ℝ)) + 1 := by ring
  have e2 : (n : ℝ) + 1 + (k' : ℝ) = ((n : ℝ) + (k' : ℝ)) + 1 := by ring
  rw [e1, e2]
  linarith

end RHTower.Sieve

end
