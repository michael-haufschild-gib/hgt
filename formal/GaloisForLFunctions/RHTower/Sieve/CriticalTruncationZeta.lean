import GaloisForLFunctions.PNTPlus.ZetaBounds

/-!
# The truncated zeta series on the critical line, compared with `ζ`

Jutila's large-values estimate pays the off-diagonal Gram entries `∑_{n ∼ N} n^{iτ}` by the fourth
moment of `ζ`.  The passage from the exponential sum to `ζ` is Euler–Maclaurin, which the corpus
already owns in the sharp form `Zeta0EqZeta` (PNT+): with

```text
ζ₀ N s = ∑_{n ≤ N} n^{-s} + (−N^{1−s})/(1−s) + (−N^{-s})/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{-s-1} dx
```

one has `ζ₀ N s = ζ s` on `Re s > 0`, and `ZetaBnd_aux1` bounds the integral term.  Specialising to
the critical line gives the bridge below, whose only non-elementary ingredient is `ζ` itself.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- The critical-line point `1/2 + it`. -/
def criticalPt (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℝ) * Complex.I

theorem criticalPt_re (t : ℝ) : (criticalPt t).re = 1 / 2 := by
  simp [criticalPt]

theorem criticalPt_im (t : ℝ) : (criticalPt t).im = t := by
  simp [criticalPt]

theorem criticalPt_ne_one {t : ℝ} (ht : t ≠ 0) : criticalPt t ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [criticalPt_im] at this
  simp at this
  exact ht this

/-- **The truncated critical-line series against `ζ`.**  For `|t| ≥ 2` and `N ≥ 1`,
the partial sum of `∑ n^{-1/2-it}` differs from `ζ(1/2+it)` by an explicit elementary amount. -/
theorem norm_sum_range_criticalPt_le {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖∑ n ∈ Finset.range (N + 1), (1 : ℂ) / (n : ℂ) ^ (criticalPt t)‖
      ≤ ‖riemannZeta (criticalPt t)‖
        + (N : ℝ) ^ ((1 : ℝ) / 2) / |t| + (N : ℝ) ^ (-(1 : ℝ) / 2) / 2
          + 4 * |t| * (N : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hN0 : 0 < N := hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  have hs : criticalPt t = ((1 / 2 : ℝ) : ℂ) + (t : ℝ) * Complex.I := rfl
  have hre : 0 < (criticalPt t).re := by rw [criticalPt_re]; norm_num
  have hzeta : riemannZeta0 N (criticalPt t) = riemannZeta (criticalPt t) :=
    Zeta0EqZeta hN0 hre (criticalPt_ne_one ht0)
  -- unfold the Euler–Maclaurin representation
  have hsum : (∑ n ∈ Finset.range (N + 1), (1 : ℂ) / (n : ℂ) ^ (criticalPt t))
      = riemannZeta (criticalPt t)
        - ((- (N : ℂ) ^ (1 - criticalPt t)) / (1 - criticalPt t)
            + (- (N : ℂ) ^ (-(criticalPt t))) / 2
            + criticalPt t * ∫ x in Set.Ioi (N : ℝ),
                ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (criticalPt t + 1)) := by
    rw [← hzeta, riemannZeta0]
    ring
  rw [hsum]
  have hcpow1 : ‖(- (N : ℂ) ^ (1 - criticalPt t))‖ = (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos hN0]
    congr 1
    simp [criticalPt_re]
    norm_num
  have hcpow2 : ‖(- (N : ℂ) ^ (-(criticalPt t)))‖ = (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos hN0]
    congr 1
    simp [criticalPt_re]
    norm_num
  have hden : |t| ≤ ‖1 - criticalPt t‖ := by
    have : (1 - criticalPt t).im = -t := by
      simp [criticalPt_im]
    calc |t| = |(1 - criticalPt t).im| := by rw [this]; simp
      _ ≤ ‖1 - criticalPt t‖ := Complex.abs_im_le_norm _
  have hfirst : ‖(- (N : ℂ) ^ (1 - criticalPt t)) / (1 - criticalPt t)‖
      ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / |t| := by
    rw [norm_div, hcpow1]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hsecond : ‖(- (N : ℂ) ^ (-(criticalPt t))) / 2‖ = (N : ℝ) ^ (-(1 : ℝ) / 2) / 2 := by
    rw [norm_div, hcpow2]
    simp
  have hthird : ‖criticalPt t * ∫ x in Set.Ioi (N : ℝ),
      ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (criticalPt t + 1)‖
      ≤ 4 * |t| * (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    have hb := ZetaBnd_aux1 N hN (σ := (1 / 2 : ℝ)) (t := t) (by constructor <;> norm_num) ht
    rw [← hs] at hb
    refine le_trans hb (le_of_eq ?_)
    rw [show (-(1 / 2 : ℝ)) = -(1 : ℝ) / 2 by ring]
    field_simp
    ring
  have hE : ‖((- (N : ℂ) ^ (1 - criticalPt t)) / (1 - criticalPt t)
        + (- (N : ℂ) ^ (-(criticalPt t))) / 2
        + criticalPt t * ∫ x in Set.Ioi (N : ℝ),
            ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (criticalPt t + 1))‖
      ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / |t| + (N : ℝ) ^ (-(1 : ℝ) / 2) / 2
          + 4 * |t| * (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    refine le_trans norm_add₃_le ?_
    linarith [hfirst, hsecond.le, hsecond.ge, hthird]
  have hsplit := norm_sub_le (riemannZeta (criticalPt t))
    ((- (N : ℂ) ^ (1 - criticalPt t)) / (1 - criticalPt t)
        + (- (N : ℂ) ^ (-(criticalPt t))) / 2
        + criticalPt t * ∫ x in Set.Ioi (N : ℝ),
            ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (criticalPt t + 1))
  linarith [hsplit, hE]

end

end RHTower.Sieve
