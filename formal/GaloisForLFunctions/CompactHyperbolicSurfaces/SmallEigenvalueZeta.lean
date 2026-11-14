import GaloisForLFunctions.CompactHyperbolicSurfaces.SelbergZeta

/-!
# Zeros of the Selberg zeta function off the critical line

On `0 < Re s < 1`, `Re s ≠ ½`, the zeros of `Z` are exactly the points `½ ± √(¼ − λ_j)` with
`0 < λ_j < ¼` (`offLine_zeros_eq`): from `λ_j + s(s − 1) = 0`, writing `s = ½ + w`,
`w² = ¼ − λ_j` is real, so `w` is real or purely imaginary, and `Re s ≠ ½`, `0 < Re s < 1` force
`w = ±√(¼ − λ_j)`, `0 < λ_j < ¼`.
-/

open MeasureTheory Set Real
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

namespace CompactQuotient

variable (X : CompactQuotient)

/-- **The zeros off the critical line.**  In `0 < Re s < 1`, `Re s ≠ ½`, the zeros of `Z` are the
points `½ ± √(¼ − λ_j)` with `0 < λ_j < ¼`. -/
theorem offLine_zeros_eq (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {a : ℝ} (ha : 1 < a) :
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta ha s = 0} =
      {s | ∃ j : X.SpecIndex ha, 0 < X.spectralParam ha j ∧ X.spectralParam ha j < 1 / 4 ∧
        (s = ((1 / 2 + √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) ∨
          s = ((1 / 2 - √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ))} := by
  ext s
  simp only [Set.mem_setOf_eq]
  rw [selbergZeta_eq_zero_iff hhyp ha]
  constructor
  · rintro ⟨h0, h1, hne, j, hj⟩
    have hre := congrArg Complex.re hj
    have him := congrArg Complex.im hj
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im] at hre him
    have hy : s.im = 0 := by
      have h2 : s.im * (2 * s.re - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (by linarith : s.re = 1 / 2) hne
    rw [hy] at hre
    have hσ2 : (s.re - 1 / 2) ^ 2 = 1 / 4 - X.spectralParam ha j := by linear_combination hre
    have hσ0 : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
    have hpos2 : 0 < (s.re - 1 / 2) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hσ0))
    have hlt2 : (s.re - 1 / 2) ^ 2 < 1 / 4 := by nlinarith [mul_pos h0 (sub_pos.mpr h1)]
    have hsqrt : √(1 / 4 - X.spectralParam ha j) = |s.re - 1 / 2| := by
      rw [← hσ2, Real.sqrt_sq_eq_abs]
    refine ⟨j, by linarith, by linarith, ?_⟩
    have hs : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hy])
    rcases abs_cases (s.re - 1 / 2) with ⟨habs, -⟩ | ⟨habs, -⟩
    · left
      rw [hs, hsqrt, habs]
      congr 1
      ring
    · right
      rw [hs, hsqrt, habs]
      congr 1
      ring
  · rintro ⟨j, hj0, hj1, hs⟩
    have hσ : 0 < √(1 / 4 - X.spectralParam ha j) := Real.sqrt_pos.mpr (by linarith)
    have hσ' : √(1 / 4 - X.spectralParam ha j) < 1 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    have hsq : √(1 / 4 - X.spectralParam ha j) ^ 2 = 1 / 4 - X.spectralParam ha j :=
      Real.sq_sqrt (by linarith)
    rcases hs with rfl | rfl
    · refine ⟨by rw [Complex.ofReal_re]; linarith, by rw [Complex.ofReal_re]; linarith,
        by rw [Complex.ofReal_re]; exact ne_of_gt (by linarith), j, ?_⟩
      have e : ((X.spectralParam ha j : ℝ) : ℂ) +
          ((1 / 2 + √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) *
            (((1 / 2 + √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) - 1) =
          ((X.spectralParam ha j + (1 / 2 + √(1 / 4 - X.spectralParam ha j)) *
            (1 / 2 + √(1 / 4 - X.spectralParam ha j) - 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.ofReal_eq_zero]
      linear_combination hsq
    · refine ⟨by rw [Complex.ofReal_re]; linarith, by rw [Complex.ofReal_re]; linarith,
        by rw [Complex.ofReal_re]; exact ne_of_lt (by linarith), j, ?_⟩
      have e : ((X.spectralParam ha j : ℝ) : ℂ) +
          ((1 / 2 - √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) *
            (((1 / 2 - √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) - 1) =
          ((X.spectralParam ha j + (1 / 2 - √(1 / 4 - X.spectralParam ha j)) *
            (1 / 2 - √(1 / 4 - X.spectralParam ha j) - 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.ofReal_eq_zero]
      linear_combination hsq

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
