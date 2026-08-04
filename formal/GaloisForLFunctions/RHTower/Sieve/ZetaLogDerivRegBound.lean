import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegular
import GaloisForLFunctions.RHTower.Sieve.InvZetaSegmentBound

/-!
# Bounding the regular part of `-ζ'/ζ`

The regular part is `-ζ'/ζ` with the pole removed, so bounding it needs nothing beyond bounds for
`ζ'` and for `1/ζ` — both already proved for the Möbius route — together with the trivial bound for
the pole term itself:

    ‖zetaLogDerivReg s‖ ≤ ‖ζ'(s)‖·‖1/ζ(s)‖ + ‖(s-1)⁻¹‖.

There is no need to bound `G'/G` directly: rearranging the splitting identity expresses the regular
part in terms of quantities the corpus already controls.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- **The regular part, bounded by the logarithmic derivative and the pole term.** -/
theorem norm_zetaLogDerivReg_le {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    ‖zetaLogDerivReg s‖
      ≤ ‖deriv riemannZeta s‖ * ‖(riemannZeta s)⁻¹‖ + ‖(s - 1)⁻¹‖ := by
  have hsplit := neg_logDeriv_riemannZeta_eq_of_ne_zero hs hz
  have heq : zetaLogDerivReg s = -(deriv riemannZeta s * (riemannZeta s)⁻¹) - (s - 1)⁻¹ := by
    rw [logDeriv_apply, div_eq_mul_inv] at hsplit
    linear_combination -hsplit
  rw [heq]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_neg, norm_mul]

/-- The pole term is small at nonzero height. -/
theorem norm_inv_sub_one_le_height {β γ : ℝ} (hγ : γ ≠ 0) :
    ‖(((β : ℂ) + (γ : ℂ) * Complex.I) - 1)⁻¹‖ ≤ |γ|⁻¹ := by
  have him : (((β : ℂ) + (γ : ℂ) * Complex.I) - 1).im = γ := by simp
  have hge : |γ| ≤ ‖((β : ℂ) + (γ : ℂ) * Complex.I) - 1‖ := by
    have h := Complex.abs_im_le_norm (((β : ℂ) + (γ : ℂ) * Complex.I) - 1)
    rwa [him] at h
  have hγpos : (0 : ℝ) < |γ| := abs_pos.2 hγ
  rw [norm_inv]
  exact inv_anti₀ hγpos hge

/-- **The regular part on a line left of the abscissa.**  Every hypothesis is one already used for
the Möbius route; the pole term contributes only `1/|γ|`. -/
theorem norm_zetaLogDerivReg_left_le {β σ γ R : ℝ} {N : ℕ} (hR : 0 < R)
    (hσ1 : 1 < σ) (hβσ : β ≤ σ) (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N) (hNbig : σ + |γ| + R ≤ (N : ℝ))
    (hzne : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0)
    {B₀ : ℝ} (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hhalf : (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R
        * (σ - β)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) / 2)
    {M : ℝ} (hM : ‖deriv riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ M) (hM0 : 0 ≤ M) :
    ‖zetaLogDerivReg ((β : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ M * (2 / Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4))
          + |γ|⁻¹ := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    simp at hγ
    linarith
  have hs1 : ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    exact hγ0 (by simpa using congrArg Complex.im h)
  have hinv := norm_inv_riemannZeta_left_le_segment hR hσ1 hβσ hβ hlow hγ hN hNbig hB hhalf
  have hpole := norm_inv_sub_one_le_height (β := β) hγ0
  have hbase := norm_zetaLogDerivReg_le hs1 hzne
  have hprod : ‖deriv riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖
      * ‖(riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I))⁻¹‖
      ≤ M * (2 / Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)) := by
    refine mul_le_mul hM hinv (norm_nonneg _) hM0
  linarith

end RHTower.Sieve
