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
    have hkey : c / (m + 1) - c / m ≤ c / (m' + 1) - c / m' :=
      div_succ_sub_div_antitone hc hm (by linarith)
    linarith

/-- The overshoot decreases in the inner variable. -/
theorem fibreOver_antitone {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    fibreOver x h k (i + 1) ≤ fibreOver x h k i := by
  have hc : (0 : ℝ) ≤ x + h * Real.sqrt x := by
    have : (0 : ℝ) ≤ h * Real.sqrt x := mul_nonneg hh (Real.sqrt_nonneg x)
    linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hm : (0 : ℝ) < (i : ℝ) + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) i]
  rw [fibreOver, fibreOver]
  refine max_le_max ?_ le_rfl
  have hcast : ((i + 1 : ℕ) : ℝ) + (k : ℝ) = ((i : ℝ) + (k : ℝ)) + 1 := by push_cast; ring
  rw [hcast]
  have hmono := div_le_div_of_nonneg_left hc hm
    (by linarith : (i : ℝ) + (k : ℝ) ≤ (i : ℝ) + (k : ℝ) + 1)
  linarith

/-- The shortfall increases in the inner variable. -/
theorem fibreUnder_monotone {x : ℝ} (hx : 0 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    fibreUnder x i ≤ fibreUnder x (i + 1) := by
  have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  rw [fibreUnder, fibreUnder]
  refine max_le_max ?_ le_rfl
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hmono := div_le_div_of_nonneg_left hx hi0 (by linarith : (i : ℝ) ≤ (i : ℝ) + 1)
  linarith

/-- The shift-uniform majorant of the smooth model's increments. -/
def fibreIncrRaw (x h : ℝ) (K j : ℕ) : ℝ :=
  |kernelDiff x h 1 (j + 2) - kernelDiff x h 1 (j + 1)|
    + |kernelDiff x h K (j + 2) - kernelDiff x h K (j + 1)|
    + (fibreOver x h 1 (j + 1) - fibreOver x h 1 (j + 2))
    + (fibreUnder x (j + 2) - fibreUnder x (j + 1))

theorem fibreIncrRaw_nonneg {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (K j : ℕ) :
    0 ≤ fibreIncrRaw x h K j := by
  have h1 := fibreOver_antitone hx hh (le_refl 1) (j + 1)
  have h2 := fibreUnder_monotone hx (Nat.le_add_left 1 j)
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

/-- A quantity trapped between two others is bounded by the sum of their sizes. -/
theorem abs_le_add_abs_of_between {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    |b| ≤ |a| + |c| := by
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le a
    have h2 := abs_nonneg c
    linarith
  · have h1 := le_abs_self c
    have h2 := abs_nonneg a
    linarith

/-- **The smooth model's increments, majorised uniformly in the shift.** -/
theorem abs_fibreSmooth_increment_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k K : ℕ}
    (hk : 1 ≤ k) (hkK : k ≤ K) (j : ℕ) :
    |fibreSmooth x h k (j + 2) - fibreSmooth x h k (j + 1)| ≤ fibreIncrRaw x h K j := by
  have hc : (0 : ℝ) ≤ x + h * Real.sqrt x := by
    have : (0 : ℝ) ≤ h * Real.sqrt x := mul_nonneg hh (Real.sqrt_nonneg x)
    linarith
  -- the `kernelDiff` part is trapped between the shifts `1` and `K`
  have hK1 : kernelDiff x h 1 (j + 2) - kernelDiff x h 1 (j + 1)
      ≤ kernelDiff x h k (j + 2) - kernelDiff x h k (j + 1) :=
    kernelDiff_increment_mono_shift hx hh (le_refl 1) hk (j + 1)
  have hK2 : kernelDiff x h k (j + 2) - kernelDiff x h k (j + 1)
      ≤ kernelDiff x h K (j + 2) - kernelDiff x h K (j + 1) :=
    kernelDiff_increment_mono_shift hx hh hk hkK (j + 1)
  have hKpart : |kernelDiff x h k (j + 2) - kernelDiff x h k (j + 1)|
      ≤ |kernelDiff x h 1 (j + 2) - kernelDiff x h 1 (j + 1)|
        + |kernelDiff x h K (j + 2) - kernelDiff x h K (j + 1)| :=
    abs_le_add_abs_of_between hK1 hK2
  -- the overshoot part is largest at shift `1`
  have c1 : (((j + 1 : ℕ)) : ℝ) + (k : ℝ) = (j : ℝ) + 1 + (k : ℝ) := by push_cast; ring
  have c2 : (((j + 2 : ℕ)) : ℝ) + (k : ℝ) = (j : ℝ) + 1 + (k : ℝ) + 1 := by push_cast; ring
  have c3 : (((j + 1 : ℕ)) : ℝ) + ((1 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  have c4 : (((j + 2 : ℕ)) : ℝ) + ((1 : ℕ) : ℝ) = (j : ℝ) + 2 + 1 := by push_cast; ring
  have e1 : fibreOver x h k (j + 1)
      = max ((x + h * Real.sqrt x) / ((j : ℝ) + 1 + (k : ℝ)) - 2 * Real.sqrt x) 0 := by
    rw [fibreOver, c1]
  have e2 : fibreOver x h k (j + 2)
      = max ((x + h * Real.sqrt x) / ((j : ℝ) + 1 + (k : ℝ) + 1) - 2 * Real.sqrt x) 0 := by
    rw [fibreOver, c2]
  have e3 : fibreOver x h 1 (j + 1)
      = max ((x + h * Real.sqrt x) / ((j : ℝ) + 2) - 2 * Real.sqrt x) 0 := by
    rw [fibreOver, c3]
  have e4 : fibreOver x h 1 (j + 2)
      = max ((x + h * Real.sqrt x) / ((j : ℝ) + 2 + 1) - 2 * Real.sqrt x) 0 := by
    rw [fibreOver, c4]
  have hgap : ((j : ℝ) + 2 = (j : ℝ) + 1 + (k : ℝ)) ∨ ((j : ℝ) + 2 + 1 ≤ (j : ℝ) + 1 + (k : ℝ)) := by
    rcases eq_or_lt_of_le hk with hone | htwo
    · left
      have : (k : ℝ) = 1 := by exact_mod_cast hone.symm
      rw [this]
      ring
    · right
      have h2 : 2 ≤ k := htwo
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
      linarith
  have hOkey := trunc_div_diff_antitone (c := x + h * Real.sqrt x) (D := 2 * Real.sqrt x)
    (m := (j : ℝ) + 2) (m' := (j : ℝ) + 1 + (k : ℝ)) hc (by positivity) hgap
  have hOanti := fibreOver_antitone hx hh hk (j + 1)
  have hOpart : |fibreOver x h k (j + 2) - fibreOver x h k (j + 1)|
      ≤ fibreOver x h 1 (j + 1) - fibreOver x h 1 (j + 2) := by
    rw [abs_of_nonpos (by linarith), e1, e2, e3, e4]
    rw [e1, e2] at hOanti
    linarith [hOkey]
  -- the shortfall part is shift-free
  have hUmono := fibreUnder_monotone hx (Nat.le_add_left 1 j)
  have hUpart : |fibreUnder x (j + 2) - fibreUnder x (j + 1)|
      = fibreUnder x (j + 2) - fibreUnder x (j + 1) := abs_of_nonneg (by linarith)
  -- assemble
  rw [fibreSmooth_decomp x h k (j + 2), fibreSmooth_decomp x h k (j + 1)]
  refine le_trans (abs_max_zero_sub_le _ _) ?_
  have hsplit : (kernelDiff x h k (j + 2) - fibreOver x h k (j + 2) - fibreUnder x (j + 2) + 1)
      - (kernelDiff x h k (j + 1) - fibreOver x h k (j + 1) - fibreUnder x (j + 1) + 1)
      = (kernelDiff x h k (j + 2) - kernelDiff x h k (j + 1))
        - (fibreOver x h k (j + 2) - fibreOver x h k (j + 1))
        - (fibreUnder x (j + 2) - fibreUnder x (j + 1)) := by ring
  rw [hsplit, fibreIncrRaw]
  refine le_trans (abs_sub _ _) ?_
  refine le_trans (add_le_add (abs_sub _ _) le_rfl) ?_
  linarith [hKpart, hOpart, hUpart.le, hUpart.ge]

end RHTower.Sieve

end
