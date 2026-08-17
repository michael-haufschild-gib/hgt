import GaloisForLFunctions.PNTPlus.ZetaBounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A crude polynomial bound for `ζ` on the right half of the critical strip

The Euler–Maclaurin truncation at `N = 1` already bounds `ζ` polynomially wherever the abscissa is
positive: the finite sum contributes `1`, the two boundary terms contribute at most `1/2` each once
the ordinate is at least `2`, and the remaining integral is bounded by `2|t|/σ`.  Hence

`‖ζ(σ + it)‖ ≤ 2 + 2|t|/σ`   for `0 < σ ≤ 2`, `|t| ≥ 2`.

This is far from sharp, but it is exactly what a Jensen zero-count on a disc of bounded radius
needs: only the logarithm of the bound enters there.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- **The crude polynomial bound.**  On the right half of the strip `ζ` is bounded by
`2 + 2|t|/σ`. -/
theorem norm_riemannZeta_le_of_re_pos {σ t : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2 + 2 * |t| / σ := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hrepos : 0 < s.re := by rw [hre]; exact hσ0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hrepos
    simp at hrepos
  have hne1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [him] at this
    rw [this] at ht
    norm_num at ht
  rw [← Zeta0EqZeta (N := 1) (by norm_num) hrepos hne1, riemannZeta0]
  have hsum : (∑ n ∈ Finset.range 2, 1 / ((n : ℂ)) ^ s) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [Nat.cast_zero, Nat.cast_one, Complex.zero_cpow hs0, Complex.one_cpow]
    norm_num
  have hone : (((1 : ℕ) : ℂ)) = 1 := by norm_num
  have hb1 : ‖(-(((1 : ℕ) : ℂ)) ^ (1 - s)) / (1 - s)‖ ≤ 1 / 2 := by
    rw [hone, Complex.one_cpow, norm_div, norm_neg, norm_one]
    have hlow : (2 : ℝ) ≤ ‖1 - s‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm (1 - s))
      have : (1 - s).im = -t := by simp [him]
      rw [this, abs_neg]
      exact ht
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hb2 : ‖(-(((1 : ℕ) : ℂ)) ^ (-s)) / 2‖ = 1 / 2 := by
    rw [hone, Complex.one_cpow, norm_div, norm_neg, norm_one]
    norm_num
  have hb3 : ‖s * ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ 2 * |t| / σ := by
    have h := ZetaBnd_aux1 1 (le_refl 1) (σ := σ) (t := t) ⟨hσ0, hσ2⟩ ht
    rw [← hs] at h
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_one, Real.one_rpow]
    ring
  calc ‖(∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ)) ^ s)
        + (-(((1 : ℕ) : ℂ)) ^ (1 - s)) / (1 - s) + (-(((1 : ℕ) : ℂ)) ^ (-s)) / 2
        + s * ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ‖(∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ)) ^ s)‖
        + ‖(-(((1 : ℕ) : ℂ)) ^ (1 - s)) / (1 - s)‖ + ‖(-(((1 : ℕ) : ℂ)) ^ (-s)) / 2‖
        + ‖s * ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
        exact norm_add₄_le
    _ ≤ 1 + 1 / 2 + 1 / 2 + 2 * |t| / σ := by
        have : (1 + 1) = 2 := by norm_num
        rw [this, hsum, norm_one]
        exact add_le_add (add_le_add (add_le_add (le_refl 1) hb1) (le_of_eq hb2)) hb3
    _ = 2 + 2 * |t| / σ := by ring

/-- For abscissa at least `2` the Dirichlet series bounds `ζ` by `ζ(2)`. -/
theorem norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have h1 : (1 : ℝ) < s.re := by linarith
  have hz := zeta_eq_tsum_one_div_nat_cpow h1
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := summable_one_div_nat_cpow.mpr h1
  have hbaselsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    HasSum.summable _root_.hasSum_zeta_two
  have hnorm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hs0 : s ≠ 0 := by
        intro hh
        rw [hh] at hs
        simp at hs
        linarith
      simp [Complex.zero_cpow hs0]
    · have hpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      rw [norm_div, norm_one, norm_natCast_cpow_of_pos h s]
      rw [show ((n : ℝ)) ^ (2 : ℕ) = (n : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      push_cast
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact Real.rpow_le_rpow_of_exponent_le hpos hs
  rw [hz]
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hbaselsum
  · refine le_trans (Summable.tsum_mono
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hbaselsum) hbaselsum hnorm) ?_
    rw [HasSum.tsum_eq _root_.hasSum_zeta_two]

/-- **The uniform crude bound.**  Right of abscissa `1/4` and above ordinate `2`, `ζ` is bounded by
`2 + 8|t|`. -/
theorem norm_riemannZeta_le_quarter {s : ℂ} (hσ : 1 / 4 ≤ s.re) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 2 + 8 * |s.im| := by
  rcases le_or_gt s.re 2 with h | h
  · have hs : s = ((s.re : ℂ) + (s.im : ℂ) * I) := by
      apply Complex.ext <;> simp
    have hbound : ‖riemannZeta ((s.re : ℂ) + (s.im : ℂ) * I)‖ ≤ 2 + 2 * |s.im| / s.re :=
      norm_riemannZeta_le_of_re_pos (by linarith) h ht
    rw [← hs] at hbound
    have hq : (0 : ℝ) < s.re := by linarith
    have hdiv : 2 * |s.im| / s.re ≤ 8 * |s.im| := by
      rw [div_le_iff₀ hq]
      nlinarith [abs_nonneg s.im, hσ]
    linarith
  · refine le_trans (norm_riemannZeta_le_of_two_le_re h.le) ?_
    nlinarith [Real.pi_lt_d2, Real.pi_gt_three, abs_nonneg s.im]

end RHTower
