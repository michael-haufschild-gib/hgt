import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheSublogarithmicGridsHaveVanishingNormalizedDensity
import GaloisForLFunctions.SurfaceOfSpecZ.TheTraceZetaFunctionAtThePowerDegrees
import GaloisForLFunctions.HTGeometry.SeparatedPointCount
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SubLogarithmicWindowsMissTheMinimalFace

section ThePositiveCalibratedBlocksSurviveSplineSmoothing

/-!
## Positive calibrated blocks survive spline smoothing

The eighth box convolution is a nonnegative probability density supported
on `[-8,8]`. Positivity on a window enlarged by eight therefore gives a
positive spline trace on the original window, even after a common real
exponential shift.
-/

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.SquareRootThreshold Zeta23 RHTower.WeilDeletion

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The squared transform of the cubic box spline, applied to a finite exponential block. -/
def splineExponentialBlock {ι : Type*} [Fintype ι] (w : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ j, sincC (-I * w j) ^ 8 * Complex.exp (w j * (t : ℂ))

private theorem spline_exponential_integrable (w : ℂ) (t : ℝ) :
    Integrable (fun u : ℝ => (upow 1 7 u : ℂ) * Complex.exp (w * ((t + u : ℝ) : ℂ))) := by
  have hi := (integrable_ofReal_mul_exp (integrable_upow 1 7)
    (hasCompactSupport_upow 1 7) (-I * w)).const_mul (Complex.exp (w * (t : ℂ)))
  convert hi using 1
  funext u
  have he : I * (-I * w) * (u : ℂ) = w * (u : ℂ) := by
    rw [← mul_assoc I (-I), mul_neg, I_mul_I]
    ring
  rw [he, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

private theorem integral_spline_exponential (w : ℂ) (t : ℝ) :
    (∫ u : ℝ, (upow 1 7 u : ℂ) * Complex.exp (w * ((t + u : ℝ) : ℂ))) =
      sincC (-I * w) ^ 8 * Complex.exp (w * (t : ℂ)) := by
  have he (u : ℝ) : (upow 1 7 u : ℂ) * Complex.exp (w * ((t + u : ℝ) : ℂ)) =
      ((upow 1 7 u : ℂ) * Complex.exp (I * (-I * w) * (u : ℂ))) * Complex.exp (w * (t : ℂ)) := by
    have hh : I * (-I * w) * (u : ℂ) = w * (u : ℂ) := by
      rw [← mul_assoc I (-I), mul_neg, I_mul_I]
      ring
    rw [hh, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hf := paperFT_boxSpline_eq 7 (-I * w)
  change (∫ u : ℝ, (upow 1 7 u : ℂ) * Complex.exp (I * (-I * w) * (u : ℂ))) =
    sincC (-I * w) ^ 8 at hf
  rw [hf]

/-- Spline smoothing is integration against a positive unit-mass kernel. -/
theorem splineExponentialBlock_re_eq_integral {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (t : ℝ) :
    (splineExponentialBlock w t).re =
      ∫ u : ℝ, upow 1 7 u * (∑ j, Complex.exp (w j * ((t + u : ℝ) : ℂ))).re := by
  classical
  have hi : Integrable (fun u : ℝ => ∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((t + u : ℝ) : ℂ))) :=
    integrable_finset_sum _ (fun j _ => spline_exponential_integrable (w j) t)
  have he : (∫ u : ℝ, ∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((t + u : ℝ) : ℂ))) = splineExponentialBlock w t := by
    rw [integral_finset_sum _ (fun j _ => spline_exponential_integrable (w j) t)]
    simp only [integral_spline_exponential, splineExponentialBlock]
  rw [← he, ← Complex.reCLM.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Complex.reCLM_apply, ← Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A positive calibrated block remains positive after the spline multiplier is applied. -/
theorem splineExponentialBlock_re_ge_of_positive_window {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {x T R v : ℝ} (hx : 0 ≤ x) (hv : |v| ≤ R)
    (hpos : ∀ a : ℝ, |a| ≤ R + 8 →
      (3 / 4 : ℝ) ≤ (∑ j, Complex.exp (((T + a : ℝ) : ℂ) * z j)).re) :
    (3 / 4 : ℝ) * Real.exp (x * (T + v - 8)) ≤
      (splineExponentialBlock (fun j => (x : ℂ) + z j) (T + v)).re := by
  classical
  let w : ι → ℂ := fun j => (x : ℂ) + z j
  let c : ℝ := (3 / 4) * Real.exp (x * (T + v - 8))
  have hi : Integrable (fun u : ℝ => ∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((T + v + u : ℝ) : ℂ))) :=
    integrable_finset_sum _ (fun j _ => spline_exponential_integrable (w j) (T + v))
  have hir : Integrable (fun u : ℝ => upow 1 7 u *
      (∑ j, Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re) := by
    simpa only [← Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hi.re
  have hmono : ∀ u : ℝ, upow 1 7 u * c ≤ upow 1 7 u *
      (∑ j, Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re := by
    intro u
    by_cases hu : upow 1 7 u = 0
    · simp only [hu, zero_mul, le_refl]
    have hs := support_upow_subset (by norm_num : (0 : ℝ) < 1) 7 hu
    have hu8 : |u| ≤ 8 := by
      norm_num at hs
      exact abs_le.mpr hs
    have hva : |v + u| ≤ R + 8 := (abs_add_le _ _).trans (add_le_add hv hu8)
    have hp := hpos (v + u) hva
    have hsum : (∑ j, Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re =
        Real.exp (x * (T + v + u)) *
          (∑ j, Complex.exp (((T + (v + u) : ℝ) : ℂ) * z j)).re := by
      have hterm (j : ι) : Complex.exp (w j * ((T + v + u : ℝ) : ℂ)) =
          (Real.exp (x * (T + v + u)) : ℂ) *
            Complex.exp (((T + (v + u) : ℝ) : ℂ) * z j) := by
        dsimp only [w]
        rw [add_mul, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul]
        congr 2
        push_cast
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum, Complex.re_ofReal_mul]
    rw [hsum]
    apply mul_le_mul_of_nonneg_left _ (upow_nonneg (by norm_num : (0 : ℝ) < 1) 7 u)
    have hexp : Real.exp (x * (T + v - 8)) ≤ Real.exp (x * (T + v + u)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hx
      have hulo := (abs_le.mp hu8).1
      linarith only [hulo]
    dsimp only [c]
    calc
      _ ≤ (3 / 4 : ℝ) * Real.exp (x * (T + v + u)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  have hh := integral_mono ((integrable_upow 1 7).mul_const c) hir hmono
  rw [integral_mul_const, integral_upow (by norm_num : (0 : ℝ) < 1), one_mul] at hh
  rw [splineExponentialBlock_re_eq_integral]
  exact hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end ThePositiveCalibratedBlocksSurviveSplineSmoothing

section TheCalibratedBlocksHaveSmallSplineWeights

/-!
## Spline weights and local counts of calibrated blocks

The squared cubic-spline transform makes each coefficient at ordinate at least `Γ/2`
smaller than `65536 exp(4)/Γ⁸`. Index separation gives at most `1+k/Γ`
ordinates in a unit interval. These are the mass and local-count bounds
needed to assemble the blocks into a tempered configuration.
-/

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.SquareRootThreshold Zeta23

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The squared cubic-spline coefficient has an explicit inverse-eighth-power bound. -/
theorem norm_calibrated_spline_coefficient_le {Γ : ℝ} (hΓ : 0 < Γ)
    {w : ℂ} (hw : |w.re| ≤ 1 / 2) (him : Γ / 2 ≤ w.im) :
    ‖sincC (-I * w) ^ 8‖ ≤ 65536 * Real.exp 4 / Γ ^ 8 := by
  have hwim : |(-I * w).im| ≤ 1 / 2 := by
    simpa only [Complex.mul_im, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
      Complex.neg_im, Complex.I_im, neg_one_mul, zero_add, abs_neg] using hw
  have hy : Γ / 2 ≤ ‖-I * w‖ := by
    have hh := Complex.abs_re_le_norm (-I * w)
    have he : (-I * w).re = w.im := by simp
    rw [he, abs_of_pos (by linarith only [hΓ, him] : 0 < w.im)] at hh
    exact him.trans hh
  have hh := norm_paperFT_boxSpline_le' 7 hwim (by positivity : 0 ≤ Γ / 2) hy
  rw [paperFT_boxSpline_eq] at hh
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hh
  have hden : Γ ^ 8 ≤ 256 * (1 + Γ / 2) ^ 8 := by
    have hp := pow_le_pow_left₀ hΓ.le (show Γ ≤ 2 * (1 + Γ / 2) by linarith) 8
    norm_num only [mul_pow] at hp
    exact hp
  have hden0 : 0 < (1 + Γ / 2) ^ 8 := by positivity
  have hΓ4 : 0 < Γ ^ 8 := by positivity
  have hmul := (le_div_iff₀ hden0).mp hh
  apply (le_div_iff₀ hΓ4).mpr
  calc
    _ ≤ ‖sincC (-I * w) ^ 8‖ * (256 * (1 + Γ / 2) ^ 8) :=
      mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = 256 * (‖sincC (-I * w) ^ 8‖ * (1 + Γ / 2) ^ 8) := by ring
    _ ≤ 256 * (256 * Real.exp 4) := mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = _ := by ring

/-- Twice the coefficient mass controls the real trace of a finite block. -/
def splineBlockWeight {ι : Type*} [Fintype ι] (w : ι → ℂ) : ℝ :=
  2 * ∑ j, ‖sincC (-I * w j) ^ 8‖

theorem splineBlockWeight_nonneg {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    0 ≤ splineBlockWeight w := by unfold splineBlockWeight; positivity

/-- A whole finite block obeys its coefficient mass times its maximal exponential growth. -/
theorem abs_two_re_splineExponentialBlock_le {ι : Type*} [Fintype ι]
    (w : ι → ℂ) {D t : ℝ} (ht : 0 ≤ t) (hw : ∀ j, (w j).re ≤ D) :
    |2 * (splineExponentialBlock w t).re| ≤ splineBlockWeight w * Real.exp (D * t) := by
  classical
  have hnorm : ‖splineExponentialBlock w t‖ ≤
      (∑ j, ‖sincC (-I * w j) ^ 8‖) * Real.exp (D * t) := by
    unfold splineExponentialBlock
    calc
      _ ≤ ∑ j, ‖sincC (-I * w j) ^ 8 * Complex.exp (w j * (t : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖sincC (-I * w j) ^ 8‖ * Real.exp (D * t) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_exp]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          using mul_le_mul_of_nonneg_right (hw j) ht
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := (Complex.abs_re_le_norm (splineExponentialBlock w t)).trans hnorm
  unfold splineBlockWeight
  nlinarith only [hh]

/-- High-frequency strip blocks have small total spline weight. -/
theorem splineBlockWeight_le {ι : Type*} [Fintype ι] {Γ : ℝ} (hΓ : 0 < Γ)
    (w : ι → ℂ) (hw : ∀ j, |(w j).re| ≤ 1 / 2) (him : ∀ j, Γ / 2 ≤ (w j).im) :
    splineBlockWeight w ≤ 131072 * Real.exp 4 * Fintype.card ι / Γ ^ 8 := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    norm_calibrated_spline_coefficient_le hΓ (hw j) (him j))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  unfold splineBlockWeight
  calc
    _ ≤ 2 * ((Fintype.card ι : ℝ) * (65536 * Real.exp 4 / Γ ^ 8)) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- Index-separated ordinates are distinct. -/
theorem ordinate_injective_of_index_separated {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {z : Fin (k + 1) → ℂ}
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |(z i).im - (z j).im|) :
    Function.Injective (fun i => (z i).im) := by
  intro i j he
  by_contra hij
  have hh := hsep i j
  rw [he, sub_self, abs_zero] at hh
  have hi := mul_le_mul_of_nonneg_right (one_le_abs_fin_index_sub hij) hδ.le
  linarith only [hh, hi, hδ]

/-- A unit window contains at most one plus the reciprocal spacing many ordinates. -/
theorem card_calibrated_ordinate_window_le {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin (k + 1) → ℂ)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |(z i).im - (z j).im|)
    (t : ℝ) :
    ((Finset.univ.filter (fun i => t < (z i).im ∧ (z i).im ≤ t + 1)).card : ℝ) ≤ 1 / δ + 1 := by
  classical
  let S := Finset.univ.filter (fun i => t < (z i).im ∧ (z i).im ≤ t + 1)
  let F := S.image (fun i => (z i).im)
  have hinj := ordinate_injective_of_index_separated hδ hsep
  have hcard : F.card = S.card := Finset.card_image_iff.mpr hinj.injOn
  have hh := card_le_of_separated_of_subset_Icc hδ (show t ≤ t + 1 by linarith) F
    (by
      intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hij : i ≠ j := fun he => hab (congrArg (fun i => (z i).im) he)
      have hbase : δ ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (one_le_abs_fin_index_sub hij) hδ.le
      exact hbase.trans (hsep i j))
    (by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hh := (Finset.mem_filter.mp hi).2
      exact ⟨hh.1.le, hh.2⟩)
  rw [hcard] at hh
  simpa only [add_sub_cancel_left] using hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheCalibratedBlocksHaveSmallSplineWeights

section TheCalibratedDepthBandsApproachTheTop

/-!
## Depth bands with an unattained top

Alternating terms of the existing increasing depth sequence supply common
block depths and strict upper bounds. Small calibration disks stay in the
positive strip, and every depth in the bands approaches the same top.
-/

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The common real exponential shift at one calibrated level. -/
def calibratedDepthCenter (Θ : ℝ) (k : ℕ) : ℝ := SplineTower.depth Θ (2 * k + 1)

/-- A strict upper bound for every perturbed depth at one level. -/
def calibratedDepthUpper (Θ : ℝ) (k : ℕ) : ℝ := SplineTower.depth Θ (2 * k + 2)

/-- Calibration tolerance, keeping the whole depth disk positive and below its upper bound. -/
def calibratedDepthTolerance (Θ : ℝ) (k : ℕ) : ℝ :=
  min (calibratedDepthCenter Θ k / 2)
    ((calibratedDepthUpper Θ k - calibratedDepthCenter Θ k) / 2)

/-- Each calibration disk lies strictly between zero and the level's upper depth. -/
theorem calibratedDepth_bounds {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) :
    0 < calibratedDepthTolerance Θ k ∧
      0 < calibratedDepthCenter Θ k - calibratedDepthTolerance Θ k ∧
      calibratedDepthCenter Θ k + calibratedDepthTolerance Θ k < calibratedDepthUpper Θ k ∧
      calibratedDepthUpper Θ k < Θ := by
  have hc : 0 < calibratedDepthCenter Θ k := SplineTower.depth_pos hΘ _
  have hcu : calibratedDepthCenter Θ k < calibratedDepthUpper Θ k :=
    SplineTower.strictMono_depth hΘ (by omega)
  have hu : calibratedDepthUpper Θ k < Θ := SplineTower.depth_lt hΘ _
  have hη0 : 0 < calibratedDepthTolerance Θ k := by
    apply lt_min (half_pos hc)
    exact half_pos (sub_pos.mpr hcu)
  have hηc : calibratedDepthTolerance Θ k ≤ calibratedDepthCenter Θ k / 2 := min_le_left _ _
  have hηu : calibratedDepthTolerance Θ k ≤
      (calibratedDepthUpper Θ k - calibratedDepthCenter Θ k) / 2 := min_le_right _ _
  exact ⟨hη0, by linarith only [hc, hηc], by linarith only [hcu, hηu], hu⟩

/-- Upper depths increase strictly. -/
theorem strictMono_calibratedDepthUpper {Θ : ℝ} (hΘ : 0 < Θ) :
    StrictMono (calibratedDepthUpper Θ) := by
  intro i j hij
  exact SplineTower.strictMono_depth hΘ (by omega)

/-- A new common depth exceeds the preceding level's entire depth band. -/
theorem calibratedDepthUpper_lt_next_center {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) :
    calibratedDepthUpper Θ k < calibratedDepthCenter Θ (k + 1) :=
  SplineTower.strictMono_depth hΘ (by omega)

/-- Even the lower edges of the depth bands approach the prescribed top. -/
theorem exists_calibratedDepth_lower_gt {Θ β : ℝ} (hΘ : 0 < Θ) (hβ : β < Θ) :
    ∃ k, β < calibratedDepthCenter Θ k - calibratedDepthTolerance Θ k := by
  obtain ⟨n, hn⟩ := SplineTower.exists_depth_gt hΘ
    (show (2 * β + Θ) / 3 < Θ by linarith only [hβ])
  have hmono : SplineTower.depth Θ n ≤ calibratedDepthCenter Θ n :=
    (SplineTower.strictMono_depth hΘ).monotone (by omega)
  have hηu : calibratedDepthTolerance Θ n ≤
      (calibratedDepthUpper Θ n - calibratedDepthCenter Θ n) / 2 := min_le_right _ _
  have hu := (calibratedDepth_bounds hΘ n).2.2.2
  exact ⟨n, by linarith only [hn, hmono, hηu, hu]⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheCalibratedDepthBandsApproachTheTop

section TheReflectedCalibratedBlocksHavePositiveWindows

/-!
## Positive windows for reflection-symmetric blocks

Reflecting a positive depth across zero preserves its positive ordinate.
The reflected contribution is bounded by the coefficient mass at positive
heights, while the calibrated main contribution grows exponentially.
-/

open Complex Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- A calibrated exponent together with its reflection across the imaginary axis. -/
def calibratedReflectedExponent {ι : Type*} (x : ℝ) (z : ι → ℂ) (p : ι × Bool) : ℂ :=
  if p.2 then (x : ℂ) + z p.1 else -conj ((x : ℂ) + z p.1)

/-- The reflected block is the sum of its positive- and negative-depth halves. -/
theorem splineExponentialBlock_reflected_eq {ι : Type*} [Fintype ι]
    (x : ℝ) (z : ι → ℂ) (t : ℝ) :
    splineExponentialBlock (calibratedReflectedExponent x z) t =
      splineExponentialBlock (fun i => (x : ℂ) + z i) t +
        splineExponentialBlock (fun i => -conj ((x : ℂ) + z i)) t := by
  classical
  unfold splineExponentialBlock
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, calibratedReflectedExponent, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_add_distrib]
  ring

/-- Coefficient mass splits exactly between the two reflected halves. -/
theorem splineBlockWeight_reflected_eq {ι : Type*} [Fintype ι]
    (x : ℝ) (z : ι → ℂ) :
    splineBlockWeight (calibratedReflectedExponent x z) =
      splineBlockWeight (fun i => (x : ℂ) + z i) +
        splineBlockWeight (fun i => -conj ((x : ℂ) + z i)) := by
  classical
  unfold splineBlockWeight
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, calibratedReflectedExponent, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_add_distrib]
  ring

/-- Reflection preserves ordinates, and both real parts lie below the upper depth bound. -/
theorem calibratedReflectedExponent_geometry {ι : Type*} (z : ι → ℂ)
    {x η D : ℝ} (hη : 0 ≤ η) (hx : η ≤ x) (hD : x + η ≤ D)
    (hz : ∀ i, |(z i).re| ≤ η) (p : ι × Bool) :
    (calibratedReflectedExponent x z p).im = (z p.1).im ∧
      |(calibratedReflectedExponent x z p).re| ≤ D := by
  have hi := abs_le.mp (hz p.1)
  have hlo : 0 ≤ x + (z p.1).re := by linarith only [hi.1, hx]
  have hhi : x + (z p.1).re ≤ D := by linarith only [hi.2, hD]
  rcases p with ⟨i, b⟩
  cases b
  · constructor
    · simp [calibratedReflectedExponent]
    · simpa [calibratedReflectedExponent, abs_of_nonneg hlo] using hhi
  · constructor
    · simp [calibratedReflectedExponent]
    · simpa [calibratedReflectedExponent, abs_of_nonneg hlo] using hhi

/-- The complete reflected block stays positive on the calibrated window, up to its small mass. -/
theorem two_re_reflected_calibrated_block_ge {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {x η T R v : ℝ} (hη : 0 ≤ η) (hx : η ≤ x)
    (hz : ∀ i, |(z i).re| ≤ η) (ht : 0 ≤ T + v) (hv : |v| ≤ R)
    (hpos : ∀ a : ℝ, |a| ≤ R + 8 →
      (3 / 4 : ℝ) ≤ (∑ j, Complex.exp (((T + a : ℝ) : ℂ) * z j)).re) :
    (3 / 2 : ℝ) * Real.exp (x * (T + v - 8)) -
        splineBlockWeight (calibratedReflectedExponent x z) ≤
      2 * (splineExponentialBlock (calibratedReflectedExponent x z) (T + v)).re := by
  have hx0 : 0 ≤ x := hη.trans hx
  have hmain := splineExponentialBlock_re_ge_of_positive_window z hx0 hv hpos
  have hneg : ∀ i, (-conj ((x : ℂ) + z i)).re ≤ 0 := by
    intro i
    simp only [Complex.neg_re, Complex.conj_re, Complex.add_re, Complex.ofReal_re]
    have hi := (abs_le.mp (hz i)).1
    linarith only [hi, hx]
  have hreflect := abs_two_re_splineExponentialBlock_le
    (fun i => -conj ((x : ℂ) + z i)) ht hneg
  simp only [zero_mul, Real.exp_zero, mul_one] at hreflect
  have hweight : splineBlockWeight (fun i => -conj ((x : ℂ) + z i)) ≤
      splineBlockWeight (calibratedReflectedExponent x z) := by
    rw [splineBlockWeight_reflected_eq]
    exact le_add_of_nonneg_left (splineBlockWeight_nonneg _)
  have hlo := (abs_le.mp (hreflect.trans hweight)).1
  rw [splineExponentialBlock_reflected_eq, Complex.add_re]
  linarith only [hmain, hlo]

/-- Normalization at the upper depth leaves a uniformly bounded coefficient function. -/
theorem abs_normalized_spline_block_le {ι : Type*} [Fintype ι]
    (w : ι → ℂ) {D t : ℝ} (ht : 0 ≤ t) (hw : ∀ i, (w i).re ≤ D) :
    |Real.exp (-(D * t)) * (2 * (splineExponentialBlock w t).re)| ≤ splineBlockWeight w := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hh := mul_le_mul_of_nonneg_left (abs_two_re_splineExponentialBlock_le w ht hw)
    (Real.exp_pos (-(D * t))).le
  have he : Real.exp (-(D * t)) * (splineBlockWeight w * Real.exp (D * t)) =
      splineBlockWeight w := by
    rw [mul_left_comm, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, mul_one]
  rwa [he] at hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheReflectedCalibratedBlocksHavePositiveWindows
