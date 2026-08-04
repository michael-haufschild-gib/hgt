import GaloisForLFunctions.RHTower.Sieve.ChebyshevLeftVerticalBound

/-!
# The horizontal edges of the divided difference

At height `T` the divided difference is `(W(s) - W(1))/(s-1)` with `‖(s-1)⁻¹‖ ≤ 1/|T|`, so each
horizontal edge is at most

    (d - c)·(C/T² + ‖W(1)‖)/|T|.

The term `‖W(1)‖/|T|` does not vanish for fixed `T`, but the main term is `2π·W(1)`, so what matters
is the ratio `(d-c)/(2π|T|)` — which does vanish.  The divided difference carries the cutoff's whole
mass across the top and bottom, and only the truncation height makes it negligible.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The divided difference at height `T`. -/
theorem norm_dslope_mellin_height_le {N H C : ℝ} {x T : ℝ} (hT : T ≠ 0) (hx : 0 < x) {d : ℝ}
    (hxd : x ≤ d)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ (C / |T| ^ (1 + 1)
          + ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)) 1‖) / |T| := by
  have hre : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re = x := by simp
  have him : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im = T := by simp
  have hne : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    apply hT
    have := congrArg Complex.im h
    rwa [him, Complex.one_im] at this
  have hTpos : (0 : ℝ) < |T| := abs_pos.2 hT
  have hW : ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
      ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ C / |T| ^ (1 + 1) := by
    have h := hbd ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) (by rw [hre]; exact hx) (by rw [hre]; exact hxd)
    rw [him] at h
    rw [le_div_iff₀ (by positivity)]
    linarith [h]
  have hpole : ‖(((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) - 1)⁻¹‖ ≤ |T|⁻¹ :=
    norm_inv_sub_one_le hT
  rw [dslope_of_ne _ hne, slope_def_field, div_eq_mul_inv, norm_mul]
  refine le_trans (mul_le_mul (norm_sub_le _ _) hpole (norm_nonneg _) (by positivity)) ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  linarith [hW]

/-- **A horizontal edge of the divided difference.** -/
theorem norm_integral_horizontal_dslope_le {N H C : ℝ} {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hT : T ≠ 0)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ (d - c) * ((C / |T| ^ (1 + 1)
          + ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)) 1‖) / |T|) := by
  have hpt : ∀ x ∈ Set.uIoc c d,
      ‖dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ (C / |T| ^ (1 + 1)
          + ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ)) 1‖) / |T| := by
    intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    exact norm_dslope_mellin_height_le hT (lt_of_lt_of_le hc hx.1.le) hx.2 hbd
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c)] at h
  linarith [h]

end RHTower.Sieve
