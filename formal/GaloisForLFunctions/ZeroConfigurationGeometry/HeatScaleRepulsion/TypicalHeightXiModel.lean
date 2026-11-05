import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TypicalZetaBoxBounds
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.ArchimedeanHorizontalModel
import GaloisForLFunctions.RHTower.XiLineNearOneWindow

/-!
# The horizontal model for `ξ` near typical heights

Polylogarithmic bounds for `ζ` give a logarithmic-derivative error of
order `log log T` on each fixed right-hand box. The archimedean factor
then supplies the main exponential slope, including below `Re s = 1`.
The height may vary within the typical box.
-/

open Complex Set
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The horizontal logarithmic-derivative error at a typical height. -/
def typicalXiSlopeError (η T : ℝ) : ℝ :=
  24 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η ^ 2 + 4

private theorem typicalZetaSlope_nonneg {η T : ℝ} (hT : 1 < T) :
    0 ≤ 24 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η ^ 2 := by
  have hlog : 0 ≤ Real.log (1 + Real.log (4 * T)) :=
    Real.log_nonneg (by linarith only [Real.log_nonneg (show 1 ≤ 4 * T by linarith only [hT])])
  positivity

theorem typicalXiSlopeError_pos {η T : ℝ} (hT : 1 < T) :
    0 < typicalXiSlopeError η T := by
  unfold typicalXiSlopeError
  linarith only [typicalZetaSlope_nonneg (η := η) hT]

private theorem horizontalPoint_disc_bound {η σ X t : ℝ}
    (hσ : 1 / 2 + 2 * η ≤ σ) (hσ2 : σ ≤ 2) (hXt : |X - t| ≤ η) :
    ‖(σ : ℂ) + X * I - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - η := by
  have he : (σ : ℂ) + X * I - (2 + (t : ℂ) * I) =
      ((σ - 2 : ℝ) : ℂ) + ((X - t : ℝ) : ℂ) * I := by push_cast; ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hσ2)]
  linarith only [hσ, hXt]

/-- The local estimate joins the Euler bound to cover the whole right-hand segment. -/
theorem norm_logDeriv_zeta_horizontal_le_of_typical {η T t X σ : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T)
    (hXt : |X - t| ≤ η) (hσ : 1 / 2 + 2 * η ≤ σ) :
    ‖logDeriv riemannZeta ((σ : ℂ) + X * I)‖ ≤
      24 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η ^ 2 + 3 := by
  have hB := typicalZetaSlope_nonneg (η := η) (show 1 < T by linarith only [hT])
  rcases le_or_gt σ 2 with hσ2 | hσ2
  · have hb := norm_logDeriv_le_of_zetaPolylogTypical h hη hη1 hT
      (horizontalPoint_disc_bound hσ hσ2 hXt)
    linarith only [hb]
  · have hb := norm_logDeriv_riemannZeta_le_inv_sub_one_add_two
      (show 1 < σ by linarith only [hσ2]) X
    have hi : 1 / (σ - 1) ≤ 1 := (div_le_one (by linarith only [hσ2])).mpr
      (by linarith only [hσ2])
    linarith only [hb, hi, hB]

/-- The `ξ` slope has logarithmic-logarithmic error, even left of the Euler line. -/
theorem norm_logDeriv_xi_horizontal_le_of_typical {η T t X σ : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hX : 200 ≤ X)
    (hXt : |X - t| ≤ η) (hσ : 1 / 2 + 2 * η ≤ σ) (hσX : σ ≤ X / 32) :
    ‖logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X‖ ≤ typicalXiSlopeError η T := by
  have hσ0 : 0 < σ := by linarith only [hη, hσ]
  have him : ((σ : ℂ) + X * I).im ≠ 0 := by
    simpa using (show X ≠ 0 by linarith only [hX])
  have hne1 : (σ : ℂ) + X * I ≠ 1 := fun he => him (by rw [he]; simp)
  have hζ : riemannZeta ((σ : ℂ) + X * I) ≠ 0 :=
    h.ne_zero (by simp; linarith only [hη, hσ]) (by simpa using hXt.trans (by linarith only [hη1]))
  have he : logDeriv xi ((σ : ℂ) + X * I) =
      logDeriv archG ((σ : ℂ) + X * I) + logDeriv riemannZeta ((σ : ℂ) + X * I) := by
    rw [logDeriv_xi_fourFactor_offReal him hζ, logDeriv_archG (by simpa using hσ0) hne1]
  have harch := norm_logDeriv_archG_sub_horizontalSlope_le_one hσ0 hσX hX
  have hz := norm_logDeriv_zeta_horizontal_le_of_typical h hη hη1 hT hXt hσ
  rw [he, add_sub_right_comm]
  refine (norm_add_le _ _).trans ?_
  unfold typicalXiSlopeError
  linarith only [harch, hz]

/-- Nonvanishing on the horizontal source segment follows from the typical zero shadow. -/
theorem xiLine_ne_zero_of_typical {η T t X w : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hX : 200 ≤ X)
    (hXt : |X - t| ≤ η) (hw : 2 * η ≤ w) : xiLine X w ≠ 0 := by
  have him : (((w + 1 / 2 : ℝ) : ℂ) + X * I).im ≠ 0 := by
    simpa using (show X ≠ 0 by linarith only [hX])
  have hne1 : ((w + 1 / 2 : ℝ) : ℂ) + X * I ≠ 1 := fun he => him (by rw [he]; simp)
  have harch := archG_ne_zero (w := ((w + 1 / 2 : ℝ) : ℂ) + X * I)
    (by simp; linarith only [hη, hw]) hne1
  have hζ : riemannZeta (((w + 1 / 2 : ℝ) : ℂ) + X * I) ≠ 0 :=
    h.ne_zero (by simp; linarith only [hη, hw]) (by simpa using hXt.trans (by linarith only [hη1]))
  rw [xiLine, xiLine_point, xi_eq_archG_mul_zeta_offReal him]
  exact mul_ne_zero harch hζ

theorem norm_xiLineDeriv_sub_le_of_typical {η T t X w : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hX : 200 ≤ X)
    (hXt : |X - t| ≤ η) (hw : 2 * η ≤ w) (hwX : w ≤ X / 32 - 1 / 2) :
    ‖xiLineDeriv X w - horizontalSlope X * xiLine X w‖ ≤
      typicalXiSlopeError η T * ‖xiLine X w‖ := by
  have hne := xiLine_ne_zero_of_typical h hη hη1 hX hXt hw
  have he : xiLineDeriv X w = logDeriv xi (((w + 1 / 2 : ℝ) : ℂ) + X * I) * xiLine X w := by
    unfold xiLineDeriv xiLine at *
    rw [xiLine_point] at hne ⊢
    rw [logDeriv_apply, div_mul_cancel₀ _ hne]
  rw [he, ← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_logDeriv_xi_horizontal_le_of_typical h hη hη1 hT hX hXt
      (by linarith only [hw]) (by linarith only [hwX])) (norm_nonneg _)

/-- The exponential model is uniform over the horizontal segment and nearby heights. -/
theorem norm_xiLine_sub_model_le_of_typical {η T t X u w : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hu : u ∈ Icc (2 * η) (X / 32 - 1 / 2)) (hw : w ∈ Icc (2 * η) (X / 32 - 1 / 2)) :
    ‖xiLine X w - xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ ≤
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) *
        (Real.exp (typicalXiSlopeError η T * |w - u|) - 1) := by
  have hsub : uIcc u w ⊆ Icc (2 * η) (X / 32 - 1 / 2) := uIcc_subset_Icc hu hw
  exact HTGeometry.norm_sub_mul_exp_le (typicalXiSlopeError_pos (by linarith only [hT]))
    (fun x _ => hasDerivAt_xiLine X x)
    (fun x hx => norm_xiLineDeriv_sub_le_of_typical h hη hη1 hT hX hXt (hsub hx).1 (hsub hx).2)

/-- A uniform lower bound for `ζ` on the source segment and nearby heights. -/
theorem norm_zeta_horizontal_ge_of_typical {η T t X σ : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T)
    (hXt : |X - t| ≤ η) (hσ : 1 / 2 + 2 * η ≤ σ) :
    Real.exp (-(12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η)) / 3 ≤
      ‖riemannZeta ((σ : ℂ) + X * I)‖ := by
  rcases le_or_gt σ 2 with hσ2 | hσ2
  · apply norm_zeta_ge_of_zetaPolylogTypical h hη hη1 hT
    exact (horizontalPoint_disc_bound hσ hσ2 hXt).trans (by linarith only [hη])
  · have hlog : 0 ≤ Real.log (1 + Real.log (4 * T)) :=
      Real.log_nonneg (by linarith only [Real.log_nonneg (show 1 ≤ 4 * T by linarith only [hT])])
    have he : Real.exp (-(12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have hz := (norm_riemannZeta_bounds_of_two_le_re
      (s := (σ : ℂ) + X * I) (by simpa using hσ2.le)).1
    linarith only [he, hz]

/-- A typical nonzero source value controls its archimedean factor by a power of `log T`. -/
theorem norm_archG_horizontal_le_of_typical {η T t X u : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hX : 200 ≤ X)
    (hXt : |X - t| ≤ η) (hu : 2 * η ≤ u) :
    ‖archG (((u + 1 / 2 : ℝ) : ℂ) + X * I)‖ ≤
      3 * Real.exp (12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η) * ‖xiLine X u‖ := by
  let D := 12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η
  have hz := norm_zeta_horizontal_ge_of_typical h hη hη1 hT hXt
    (σ := u + 1 / 2) (by linarith only [hu])
  have hb := mul_le_mul_of_nonneg_left hz (show 0 ≤ 3 * Real.exp D by positivity)
  have he : 3 * Real.exp D * (Real.exp (-D) / 3) = 1 := by
    calc _ = Real.exp D * Real.exp (-D) := by ring
      _ = 1 := by rw [← Real.exp_add]; simp
  change 3 * Real.exp D * (Real.exp (-D) / 3) ≤ _ at hb
  rw [he] at hb
  have him : (((u + 1 / 2 : ℝ) : ℂ) + X * I).im ≠ 0 := by
    simpa using (show X ≠ 0 by linarith only [hX])
  have hf : ‖xiLine X u‖ = ‖archG (((u + 1 / 2 : ℝ) : ℂ) + X * I)‖ *
      ‖riemannZeta (((u + 1 / 2 : ℝ) : ℂ) + X * I)‖ := by
    rw [xiLine, xiLine_point, xi_eq_archG_mul_zeta_offReal him, norm_mul]
  change _ ≤ 3 * Real.exp D * ‖xiLine X u‖
  rw [hf]
  have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (archG (((u + 1 / 2 : ℝ) : ℂ) + X * I)))
  nlinarith only [hm]

/-- The lower source interval has the same exponential decay as the saddle model.
Only a power of `log T` is lost, uniformly for `0 ≤ w ≤ 3`. -/
theorem norm_xiLine_lower_interval_le_of_typical {η T t X u w : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hu : 2 * η ≤ u) (hu3 : u ≤ 3) (hw : 0 ≤ w) (hw3 : w ≤ 3) :
    ‖xiLine X w‖ ≤
      (3 * ((1 + Real.log (4 * T)) ^ (4 : ℕ) + 2) *
        Real.exp (12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η + 3)) *
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) := by
  have hu0 : 0 ≤ u := by linarith only [hu, hη]
  have harch := norm_archG_horizontal_le_model hX
    (u := u + 1 / 2) (w := w + 1 / 2)
    ⟨by linarith only [hu0], by linarith only [hu3, hX]⟩
    ⟨by linarith only [hw], by linarith only [hw3, hX]⟩
  have hdiff : w + 1 / 2 - (u + 1 / 2) = w - u := by ring
  rw [hdiff] at harch
  have hanchor := norm_archG_horizontal_le_of_typical h hη hη1 hT hX hXt hu
  have hz := norm_zeta_le_of_zetaPolylogTypical h (by linarith only [hT])
    (s := ((w + 1 / 2 : ℝ) : ℂ) + X * I) (by simp; linarith only [hw])
    (by simpa using hXt.trans (by linarith only [hη1]))
  have hdist : |w - u| ≤ 3 := abs_le.mpr
    ⟨by linarith only [hw, hu3], by linarith only [hw3, hu0]⟩
  have him : (((w + 1 / 2 : ℝ) : ℂ) + X * I).im ≠ 0 := by
    simpa using (show X ≠ 0 by linarith only [hX])
  rw [xiLine, xiLine_point, xi_eq_archG_mul_zeta_offReal him, norm_mul]
  calc
    _ ≤ (3 * Real.exp (12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η) *
        ‖xiLine X u‖) * Real.exp ((w - u) * (horizontalSlope X).re) * Real.exp 3 *
          ((1 + Real.log (4 * T)) ^ (4 : ℕ) + 2) := by
      gcongr
      exact harch.trans (by gcongr)
    _ = _ := by rw [Real.exp_add]; ring

#print axioms norm_xiLine_sub_model_le_of_typical
#print axioms norm_xiLine_lower_interval_le_of_typical

end

end GaloisForLFunctions.ZeroConfigurationGeometry
