import GaloisForLFunctions.RHTower.XiSliceCoeffNearDoublePositivity
import GaloisForLFunctions.RHTower.XiSliceDetectionOrderBound

/-!
# Shadowed off-line zeros make `ξ` small on the critical line

Let `ρ` be a zero of `ξ` with displacement `δ = |Re ρ − ½|` and ordinate `γ`.  Suppose its ordinate
is *shadowed to depth `j`*: some set `C₀` of `m ≥ j` critical zero copies lies within `D` of `γ`,
and the exposed off-line zeros at `γ` satisfy `3j D² Σ (Im z)²/|z − γ|⁴ ≤ m − j + 1`.  The cone and
near-double law then make the slice coefficients `c_n(γ)` nonnegative for `n ≤ 2j`.  The
detection bound (`exists_re_xiSliceCoeff_neg_of_tail_lt`) forbids this unless the tail at
`x = δ` is large.

**Theorem** (`re_xiSliceCoeff_zero_le_of_shadowed`).  Under shadowing to depth `j`, for every
`R > δ` with `|g_γ| ≤ M` on `|x| = R`:

  `|ξ(½ + iγ)|² = c_0(γ) ≤ M (δ/R)^{2j+1} / (1 − δ/R)`.

So a deeply shadowed off-line zero forces `ξ` to be exponentially small, in the shadowing depth, at
the critical point of its own ordinate.  With `R = 2δ`: `|ξ(½+iγ)|² ≤ 2^{−2j} M(2δ)`.
Unconditionally, shadowing depth and the size of `ξ` on the line trade off against each other.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- **Shadowing depth forces smallness of `ξ` on the critical line.** -/
theorem re_xiSliceCoeff_zero_le_of_shadowed {ρ : ℂ} (hρ : xi ρ = 0) (hΞ : XiC ρ.im ≠ 0)
    {R M : ℝ} (hR : |ρ.re - 1 / 2| < R)
    (hM : ∀ x ∈ sphere (0 : ℂ) R, ‖xiSliceProduct ρ.im x‖ ≤ M)
    {j : ℕ} (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q)
    (hk₀ : j ≤ C₀.card) {D : ℝ} (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - ρ.im‖ ≤ D)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
        |(xiSpectralPoint q).re - ρ.im| < |(xiSpectralPoint q).im|) →
      3 * j * (D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - ρ.im‖ ^ 4) ≤
        (C₀.card : ℝ) - j + 1) :
    (xiSliceCoeff ρ.im 0).re ≤
      M * (|ρ.re - 1 / 2| / R) ^ (2 * j + 1) / (1 - |ρ.re - 1 / 2| / R) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn, hneg⟩ := exists_re_xiSliceCoeff_neg_of_tail_lt hρ hR hM hlt
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact absurd hneg (not_lt.mpr (xiSliceCoeff_zero_re_pos hΞ).le)
    · have hij : i ≤ j := by omega
      have hpos := xiSliceCoeff_re_pos_of_exposed_nearDouble_card hΞ hi C₀ hC₀ (hij.trans hk₀)
        hD fun F hF => by
          have h1 := hoff F hF
          have hS : 0 ≤ D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
              ‖xiSpectralPoint q - ρ.im‖ ^ 4 :=
            mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun q _ => by positivity)
          have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
          nlinarith
      exact absurd hneg (not_lt.mpr hpos.le)
  · rw [xiSliceCoeff_odd_eq_zero] at hneg
    simp at hneg

end

end RHTower
