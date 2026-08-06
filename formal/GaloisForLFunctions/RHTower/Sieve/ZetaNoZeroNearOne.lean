import GaloisForLFunctions.RHTower.Sieve.ZetaZeroCount

/-!
# The narrow disc about `9/8 + iγ` contains no zero at all

A point within `1/8` of `9/8 + iγ` has real part at least `1`, where `ζ` does not vanish.  So the
family of zeros retained by Landau's lemma at radius `1/4` around that centre is **empty**, and the
counting bound `exists_zero_count_bound` derived from it, while true, says nothing.

The counting statement that does carry content is `exists_wide_zero_count`, whose disc has radius
`21/40` and therefore reaches `Re ρ ≥ 9/8 - 21/40 = 3/5`.
-/

namespace RHTower.Sieve

open Complex

/-- Points of the narrow disc have real part at least `1`. -/
theorem one_le_re_of_near_nine_eighths {γ : ℝ} {w : ℂ}
    (hw : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 1 / 8) :
    1 ≤ w.re := by
  have h1 : |(w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re|
      ≤ ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _
  have h2 : (w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re = w.re - 9 / 8 := by
    rw [Complex.sub_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h2] at h1
  have h3 := abs_le.mp (le_trans h1 hw)
  linarith [h3.1]

/-- **The narrow disc is zero-free.**  Hence the family retained by Landau's lemma at radius `1/4`
about `9/8 + iγ` is empty. -/
theorem zeta_ne_zero_near_nine_eighths {γ : ℝ} {w : ℂ}
    (hw : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 1 / 8) :
    riemannZeta w ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (one_le_re_of_near_nine_eighths hw)

/-- **The narrow retained family is empty.** -/
theorem zeta_narrow_retained_empty {γ : ℝ} {Z : Finset ℂ}
    (hdist : ∀ ρ ∈ Z, ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 1 / 8)
    (hzero : ∀ ρ ∈ Z, riemannZeta ρ = 0) : Z = ∅ := by
  ext ρ
  simp only [Finset.notMem_empty, iff_false]
  intro hρ
  exact zeta_ne_zero_near_nine_eighths (hdist ρ hρ) (hzero ρ hρ)

/-- Points of the wide disc have real part at least `3/5`. -/
theorem three_fifths_le_re_of_wide {γ : ℝ} {w : ℂ}
    (hw : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40) :
    3 / 5 ≤ w.re := by
  have h1 : |(w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re|
      ≤ ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _
  have h2 : (w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re = w.re - 9 / 8 := by
    rw [Complex.sub_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h2] at h1
  have h3 := abs_le.mp (le_trans h1 hw)
  linarith [h3.1]

end RHTower.Sieve
