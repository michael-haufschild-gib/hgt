import GaloisForLFunctions.RHTower.HighBlockDualTail
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualReflection

/-!
# High-block law, brick B1: the exact displaced AFE truncated at `L`

`ζ(s) = D_L + Dual_L − Pole + Tail_L` on `s = ½ − d + iτ`, where `D_L` and `Dual_L` are the two
finite Dirichlet-type sums of length `L` and `Tail_L` collects both series beyond `L`. The tail is
bounded uniformly in `d ∈ (0, ¼]`, `τ`, `x`, `L` by the free-exponent direct tail
(`HighBlockDirectTail`) and the right-shift dual tail (`HighBlockDualTail`): for any `A > 1`,
`K ≥ 1`,
`‖Tail_L‖ ≤ C [x^A L^{½+d−A}/(A−½−d) + (1+|τ|)^{K+½} x^{−(½−d+K)} L^{−K}/K]`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Both AFE series beyond `L`. -/
def highBlockAFETail (d x τ : ℝ) (L : ℕ) : ℂ :=
  ((∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x τ n) -
      ∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) +
  ((∑' n : ℕ, highBlockDualTerm d x τ n) - ∑ n ∈ Finset.range L, highBlockDualTerm d x τ n)

/-- **B1.** The exact displaced Gaussian AFE, truncated at `L`. -/
theorem riemannZeta_displaced_eq_truncated {x d : ℝ} (hx : 0 < x) (hd : 0 < d)
    (hdhalf : d < 1 / 2) (τ : ℝ) (L : ℕ) :
    riemannZeta (displacedLinePt d τ) =
      (∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) +
      (∑ n ∈ Finset.range L, highBlockDualTerm d x τ n) -
      smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x +
      highBlockAFETail d x τ L := by
  have h := riemannZeta_displaced_eq_two_tsum_smoothAFE_dualWeight hx hd hdhalf τ
  have hdir : (∑' n : ℕ, (n + 1 : ℂ) ^ (-displacedLinePt d τ) *
      smoothAFECutoff ((n + 1 : ℝ) / x))
      = ∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x τ n := rfl
  have hdual : (∑' n : ℕ,
      (zetaChi (displacedLinePt d τ) * (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
        smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x))
      = ∑' n : ℕ, highBlockDualTerm d x τ n := rfl
  rw [hdir, hdual] at h
  rw [h]
  unfold highBlockAFETail
  ring

/-- **Uniform tail bound.** -/
theorem exists_norm_highBlockAFETail_le {A : ℝ} (hA : 1 < A) {K'' : ℕ} (hK'' : 1 ≤ K'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d x τ : ℝ), 0 < d → d ≤ 1 / 4 → 0 < x → ∀ L : ℕ, 1 ≤ L →
      ‖highBlockAFETail d x τ L‖ ≤
        C * (x ^ A * ((L : ℝ) ^ (1 - (1 / 2 - d + A)) / ((1 / 2 - d + A) - 1)) +
          (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2) * x ^ (-(1 / 2 - d + K'')) *
            ((L : ℝ) ^ (-(K'' : ℝ)) / K'')) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_smoothAFEZetaDisplacedDirectTerm_tail_le_general hA
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_highBlockDual_tail_le hK''
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun d x τ hd hd4 hx L hL => ?_⟩
  have hb1 := h₁ d x τ hx hd.le hd4 L hL
  have hb2 := h₂ d x τ hd hd4 hx L hL
  have hσ : 0 < (1 / 2 - d + A) - 1 := by linarith
  unfold highBlockAFETail
  refine (norm_add_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [← mul_assoc]
    exact hb1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity))
  · rw [← mul_assoc, ← mul_assoc]
    exact hb2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity))
      (by positivity))

end

end RHTower
