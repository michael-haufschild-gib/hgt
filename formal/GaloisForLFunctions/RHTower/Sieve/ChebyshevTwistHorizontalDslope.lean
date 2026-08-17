import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistLeftEdge
import GaloisForLFunctions.RHTower.Sieve.HorizontalEdgeBound

/-!
# The horizontal edges of the twisted divided difference

At height `T` the divided difference at the twist pole is `(W(s) - W(1-iτ))/(s+iτ-1)`, and the
denominator has imaginary part `T + τ`.  So the pole factor costs `(|T| - |τ|)⁻¹` rather than the
untwisted `|T|⁻¹`: the twist drags the pole vertically towards the horizontal edge, and the edge
only survives if the truncation height beats the twist.

That is the one place in the twisted contour where the twist genuinely costs something, and it is
what forces `|τ| < T` in every statement that keeps the twisted main term.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The horizontal edge stays at distance at least `|T| - |τ|` from the twist pole. -/
theorem norm_inv_sub_twistPole_height_le {x T τ : ℝ} (hT : |τ| < |T|) :
    ‖((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹‖ ≤ (|T| - |τ|)⁻¹ := by
  have him : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1).im = T + τ := by
    simp
  have habs : |T| - |τ| ≤ |T + τ| := by
    have h := abs_sub_abs_le_abs_sub T (-τ)
    rw [abs_neg, sub_neg_eq_add] at h
    exact h
  have hge : (|T| - |τ| : ℝ)
      ≤ ‖(x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)
    rw [him] at h
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hge

/-- The horizontal edge never meets the twist pole once the height beats the twist. -/
theorem height_ne_twistPole {x T τ : ℝ} (hT : |τ| < |T|) :
    ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ twistPole τ := by
  intro h
  have him : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im = T := by simp
  rw [h, twistPole_im] at him
  have : |T| = |τ| := by rw [← him, abs_neg]
  linarith

/-- **The twisted divided difference at height `T`.**  The cutoff's own decay controls `W(s)`; the
whole mass `‖W(1-iτ)‖` is carried across the edge and is only made negligible by the truncation
height, exactly as in the untwisted case. -/
theorem norm_dslope_mellin_twist_height_le {N H C : ℝ} {x T τ : ℝ} (hT : |τ| < |T|) (hx : 0 < x)
    {d : ℝ} (hxd : x ≤ d)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ (C / |T| ^ (1 + 1)
          + ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)) (twistPole τ)‖)
        / (|T| - |τ|) := by
  have hre : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re = x := by simp
  have him : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im = T := by simp
  have hT0 : (0 : ℝ) < |T| := lt_of_le_of_lt (abs_nonneg τ) hT
  have hgap : (0 : ℝ) < |T| - |τ| := by linarith
  have hW : ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
      ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ C / |T| ^ (1 + 1) := by
    have h := hbd ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) (by rw [hre]; exact hx)
      (by rw [hre]; exact hxd)
    rw [him] at h
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hpole : ‖(((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) - twistPole τ)⁻¹‖ ≤ (|T| - |τ|)⁻¹ := by
    rw [sub_twistPole]
    exact norm_inv_sub_twistPole_height_le hT
  rw [dslope_of_ne _ (height_ne_twistPole (x := x) hT), slope_def_field, div_eq_mul_inv, norm_mul]
  refine le_trans (mul_le_mul (norm_sub_le _ _) hpole (norm_nonneg _) (by positivity)) ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by linarith [hW]) (inv_nonneg.2 hgap.le)

/-- **A horizontal edge of the twisted divided difference.** -/
theorem norm_integral_horizontal_twist_dslope_le {N H C : ℝ} {c d T τ : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (hT : |τ| < |T|)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)))
        (twistPole τ) ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ (d - c) * ((C / |T| ^ (1 + 1)
          + ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)) (twistPole τ)‖)
        / (|T| - |τ|)) := by
  have hpt : ∀ x ∈ Set.uIoc c d,
      ‖dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
        ≤ (C / |T| ^ (1 + 1)
            + ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)) (twistPole τ)‖)
          / (|T| - |τ|) := by
    intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    exact norm_dslope_mellin_twist_height_le hT (lt_of_lt_of_le hc hx.1.le) hx.2 hbd
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c)] at h
  linarith [h]

end RHTower.Sieve
