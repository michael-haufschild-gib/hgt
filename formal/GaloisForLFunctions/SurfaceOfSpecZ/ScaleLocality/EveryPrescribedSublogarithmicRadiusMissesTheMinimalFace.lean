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
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

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
  rw [← he]
  change Complex.reCLM (∫ u : ℝ, ∑ j, (upow 1 7 u : ℂ) *
    Complex.exp (w j * ((t + u : ℝ) : ℂ))) = _
  rw [← Complex.reCLM.integral_comp_comm hi]
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
    have hir' := hi.re
    change Integrable (fun u : ℝ => (∑ j, (upow 1 7 u : ℂ) *
      Complex.exp (w j * ((T + v + u : ℝ) : ℂ))).re) at hir'
    simpa only [← Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hir'
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
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

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
  change (z i).im = (z j).im at he
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
    ↓reduceIte, Finset.sum_add_distrib] <;> ring

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
    · change |-(x + (z i).re)| ≤ D
      rwa [abs_neg, abs_of_nonneg hlo]
  · constructor
    · simp [calibratedReflectedExponent]
    · change |x + (z i).re| ≤ D
      rwa [abs_of_nonneg hlo]

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

section TheSublogarithmicWindowsLeaveRoomForSparseBlocks

/-!
## Arbitrarily late sparse calibrated blocks

A sublogarithmic window has left endpoint tending to infinity. The
normalized node mass and local density vanish, while every fixed positive
depth gap supplies unbounded exponential gain. These limits allow each
new calibrated block to satisfy the preceding blocks' tail constraints.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The left endpoints of sublogarithmic windows tend to infinity. -/
theorem tendsto_sublogarithmic_window_left {R : ℝ → ℝ}
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => T - R T) atTop atTop := by
  have hlog := RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le
    1 1 (by norm_num) 1 (by norm_num : (0 : ℝ) < 1 / 2)
  apply Filter.tendsto_atTop.2
  intro A
  filter_upwards [eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1),
    hlog, eventually_ge_atTop (2 * A)] with T hT hLT hTA
  have hh : Real.log T / T ≤ 1 / 2 := by
    simpa only [one_mul, pow_one, Real.rpow_neg_one, div_eq_mul_inv, mul_comm] using hLT
  have hlogT := (div_le_iff₀ hT.1).mp hh
  linarith only [hT.2.2.2.2.2.2.1, hlogT, hTA]

/-- Both normalized mass and the allowed fraction of local density become arbitrarily small. -/
theorem eventually_calibrated_grid_mass_and_count {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      let Γ := calibratedGridFrequency T
      let k := calibratedGridDegree Γ (R T)
      4 ≤ Γ ∧ 0 < k ∧
        4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ ∧
        16 * (k : ℝ) / Γ ^ 2 ≤ ε ∧
        524288 * Real.exp 4 * (k : ℝ) / Γ ^ 2 ≤ ε := by
  have hΓtop : Tendsto calibratedGridFrequency atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hLtop : Tendsto (fun T => Real.log (calibratedGridFrequency T)) atTop atTop :=
    Real.tendsto_log_atTop.comp hΓtop
  have hinv : Tendsto (fun T => (Real.log (calibratedGridFrequency T))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLtop
  have hden := tendsto_sublogarithmic_grid_logarithmic_density hR0 hR
  have hd : Tendsto (fun T => 4 * ((Real.log (calibratedGridFrequency T))⁻¹ +
      (calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
        (calibratedGridFrequency T * Real.log (calibratedGridFrequency T)))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hinv.add hden).const_mul 4
  have hm := tendsto_sublogarithmic_grid_quadratic_mass hR0 hR
  have hm16 : Tendsto (fun T => 16 *
      ((calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
        calibratedGridFrequency T ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul 16
  have hmw : Tendsto (fun T => (524288 * Real.exp 4) *
      ((calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
        calibratedGridFrequency T ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul (524288 * Real.exp 4)
  filter_upwards [hΓtop.eventually_ge_atTop 4, hLtop.eventually_ge_atTop 1,
    hd.eventually_le_const hC, hm16.eventually_le_const hε, hmw.eventually_le_const hε,
    eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1)]
    with T hΓ4 hL1 hdi hmi hwi hT
  let Γ := calibratedGridFrequency T
  let k := calibratedGridDegree Γ (R T)
  have hΓ : 0 < Γ := by linarith only [hΓ4]
  have hL : 0 < Real.log Γ := zero_lt_one.trans_le hL1
  have hbounds := growing_calibrated_grid_bounds hT.2.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.1 (hR0 T) hT.2.2.2.2.2.2.1 hT.2.2.2.2.2.2.2
  refine ⟨hΓ4, hbounds.1, ?_, ?_, ?_⟩
  · have he : 4 * (1 + (k : ℝ) / Γ) / Real.log Γ =
        4 * ((Real.log Γ)⁻¹ + (k : ℝ) / (Γ * Real.log Γ)) := by
      field_simp [hΓ.ne', hL.ne'] <;> ring
    apply (div_le_iff₀ hL).mp
    rwa [he]
  · simpa only [mul_div_assoc] using hmi
  · simpa only [mul_div_assoc] using hwi

/-- A calibrated block can be chosen beyond arbitrary ordinate and window bounds, with any small mass
and any prescribed gain from a fixed positive depth gap. -/
theorem exists_sparse_calibrated_block {R : ℝ → ℝ} (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {C ε η d : ℝ} (hC : 0 < C) (hε : 0 < ε) (hη : 0 < η) (hd : 0 < d)
    (H P M x : ℝ) :
    ∃ T : ℝ,
      let Γ := calibratedGridFrequency T
      let k := calibratedGridDegree Γ (R T)
      H ≤ Γ ∧ P ≤ T - R T ∧ 4 ≤ Γ ∧ 0 < k ∧
      4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ ∧
      16 * (k : ℝ) / Γ ^ 2 ≤ ε ∧
      524288 * Real.exp 4 * (k : ℝ) / Γ ^ 2 ≤ ε ∧
      M ≤ (3 / 2 : ℝ) * Real.exp (d * (T - R T) - 8 * x) ∧
      ∃ z : Fin (k + 1) → ℂ,
        (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
        (∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
        ∀ v : ℝ, |v| ≤ R T + 8 →
          (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  have hΓtop : Tendsto calibratedGridFrequency atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hleft := tendsto_sublogarithmic_window_left hR
  have hexp : Tendsto (fun T => (3 / 2 : ℝ) * Real.exp (d * (T - R T) - 8 * x))
      atTop atTop :=
    (Real.tendsto_exp_atTop.comp ((hleft.const_mul_atTop hd).sub_const (8 * x))).const_mul_atTop
      (by norm_num)
  have hevent : ∀ᶠ T : ℝ in atTop,
      H ≤ calibratedGridFrequency T ∧ P ≤ T - R T ∧
      M ≤ (3 / 2 : ℝ) * Real.exp (d * (T - R T) - 8 * x) ∧
      (let Γ := calibratedGridFrequency T
       let k := calibratedGridDegree Γ (R T)
       4 ≤ Γ ∧ 0 < k ∧ 4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ ∧
        16 * (k : ℝ) / Γ ^ 2 ≤ ε ∧ 524288 * Real.exp 4 * (k : ℝ) / Γ ^ 2 ≤ ε) ∧
      (let Γ := calibratedGridFrequency T
       let k := calibratedGridDegree Γ (R T)
       ∃ z : Fin (k + 1) → ℂ,
        Function.Injective z ∧
        (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
        (∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
        ∀ v : ℝ, |v| ≤ R T + 8 →
          (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re) := by
    filter_upwards [hΓtop.eventually_ge_atTop H, hleft.eventually_ge_atTop P,
      hexp.eventually_ge_atTop M, eventually_calibrated_grid_mass_and_count hR0 hR hC hε,
      eventually_exists_sublogarithmic_calibrated_grid hR0 hR hη]
      with T hH hP hM hm hz
    exact ⟨hH, hP, hM, hm, hz⟩
  obtain ⟨T, hH, hP, hM, hm, z, _, hz, hsep, hpos⟩ := hevent.exists
  exact ⟨T, hH, hP, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2,
    hM, z, hz, hsep, hpos⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheSublogarithmicWindowsLeaveRoomForSparseBlocks

section TheSparseCalibratedWindowTowerExists

/-!
## A sparse tower of calibrated windows

Successive blocks have disjoint ordinate bands, summable normalized mass,
and spline weights small enough for all earlier windows. Their common
depths give the exponential gain needed to dominate the preceding levels.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
namespace CalibratedWindowTower

/-- One finite calibrated block, with its static strip, density and tempering bounds. -/
structure Block (γmin C Θ : ℝ) (R : ℝ → ℝ) (j : ℕ) where
  T : ℝ
  Γ : ℝ
  k : ℕ
  z : Fin (k + 1) → ℂ
  four_le : 4 ≤ Γ
  lowest : γmin ≤ Γ / 2
  index_le : (j : ℝ) + 1 ≤ Γ / 2
  left_le : (j : ℝ) + 1 ≤ T - R T
  degree_pos : 0 < k
  geometry : ∀ i, |(z i).re| ≤ calibratedDepthTolerance Θ j ∧
    Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ
  separation : ∀ i l : Fin (k + 1), |((i : ℕ) : ℝ) - ((l : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z l).im|
  positive : ∀ v : ℝ, |v| ≤ R T + 8 →
    (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re
  local_count : 4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ
  tempered_mass : 16 * (k : ℝ) / Γ ^ 2 ≤ (1 / 2 : ℝ) ^ j

/-- A block can satisfy arbitrary additional separation, weight and depth-gap bounds. -/
theorem exists_block {γmin C Θ : ℝ} {R : ℝ → ℝ}
    (hC : 0 < C) (hΘ : 0 < Θ) (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    (j : ℕ) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (H P M : ℝ) :
    ∃ B : Block γmin C Θ R j,
      H ≤ B.Γ ∧ P ≤ B.T - R B.T ∧
      524288 * Real.exp 4 * (B.k : ℝ) / B.Γ ^ 2 ≤ ε ∧
      M ≤ (3 / 2 : ℝ) * Real.exp
        (d * (B.T - R B.T) - 8 * calibratedDepthCenter Θ j) := by
  let e : ℝ := min ε ((1 / 2 : ℝ) ^ j)
  have he : 0 < e := lt_min hε (by positivity)
  let H' : ℝ := max H (max (2 * γmin) (2 * ((j : ℝ) + 1)))
  let P' : ℝ := max P ((j : ℝ) + 1)
  obtain ⟨T, hH, hP, hΓ4, hk, hcount, hmass, hweight, hgain, z, hz, hsep, hpos⟩ :=
    exists_sparse_calibrated_block hR0 hR hC he (calibratedDepth_bounds hΘ j).1 hd
      H' P' M (calibratedDepthCenter Θ j)
  let Γ := calibratedGridFrequency T
  let k := calibratedGridDegree Γ (R T)
  have hlow : γmin ≤ Γ / 2 := by
    have hh := (le_max_left (2 * γmin) (2 * ((j : ℝ) + 1))).trans (le_max_right H _)
    linarith only [hh, hH]
  have hidx : (j : ℝ) + 1 ≤ Γ / 2 := by
    have hh := (le_max_right (2 * γmin) (2 * ((j : ℝ) + 1))).trans (le_max_right H _)
    linarith only [hh, hH]
  have hleft : (j : ℝ) + 1 ≤ T - R T := (le_max_right P _).trans hP
  let B : Block γmin C Θ R j :=
    { T := T, Γ := Γ, k := k, z := z, four_le := hΓ4, lowest := hlow,
      index_le := hidx, left_le := hleft, degree_pos := hk, geometry := hz,
      separation := hsep, positive := hpos, local_count := hcount,
      tempered_mass := hmass.trans (min_le_right _ _) }
  exact ⟨B, (le_max_left _ _).trans hH, (le_max_left _ _).trans hP,
    hweight.trans (min_le_left _ _), hgain⟩

/-- The separation and tail conditions linking the calibrated levels. -/
structure Tower (γmin C Θ : ℝ) (R : ℝ → ℝ) where
  block : ∀ j, Block γmin C Θ R j
  weight_zero : 524288 * Real.exp 4 * ((block 0).k : ℝ) / (block 0).Γ ^ 2 ≤ 1
  frequency_gap : ∀ j, 8 * (block j).Γ + 4 ≤ (block (j + 1)).Γ
  window_gap : ∀ j, (block j).T + R (block j).T + 1 ≤
    (block (j + 1)).T - R (block (j + 1)).T
  weight_succ : ∀ j, 524288 * Real.exp 4 * ((block (j + 1)).k : ℝ) /
      (block (j + 1)).Γ ^ 2 ≤
    (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * ((block j).T + R (block j).T)))
  gain : ∀ j, (j : ℝ) + 12 ≤ (3 / 2 : ℝ) * Real.exp
    ((calibratedDepthCenter Θ (j + 1) - calibratedDepthUpper Θ j) *
      ((block (j + 1)).T - R (block (j + 1)).T) - 8 * calibratedDepthCenter Θ (j + 1))

variable {γmin C Θ : ℝ} {R : ℝ → ℝ}

/-- Every prescribed nonnegative sublogarithmic radius admits such a sparse tower. -/
theorem exists_tower (hC : 0 < C) (hΘ : 0 < Θ) (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Nonempty (Tower γmin C Θ R) := by
  classical
  obtain ⟨B₀, _, _, hw₀, _⟩ := exists_block (γmin := γmin) hC hΘ hR0 hR 0
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) 0 0 0
  have hnext (j : ℕ) (B : Block γmin C Θ R j) :
      ∃ B' : Block γmin C Θ R (j + 1),
        8 * B.Γ + 4 ≤ B'.Γ ∧ B.T + R B.T + 1 ≤ B'.T - R B'.T ∧
        524288 * Real.exp 4 * (B'.k : ℝ) / B'.Γ ^ 2 ≤
          (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * (B.T + R B.T))) ∧
        (j : ℝ) + 12 ≤ (3 / 2 : ℝ) * Real.exp
          ((calibratedDepthCenter Θ (j + 1) - calibratedDepthUpper Θ j) *
            (B'.T - R B'.T) - 8 * calibratedDepthCenter Θ (j + 1)) :=
    exists_block hC hΘ hR0 hR (j + 1) (by positivity)
      (sub_pos.mpr (calibratedDepthUpper_lt_next_center hΘ j))
      (8 * B.Γ + 4) (B.T + R B.T + 1) ((j : ℝ) + 12)
  choose next hnext_spec using hnext
  let B : ∀ j, Block γmin C Θ R j := fun j => Nat.rec B₀ (fun j Bj => next j Bj) j
  have hzero : B 0 = B₀ := rfl
  have hsucc (j : ℕ) : B (j + 1) = next j (B j) := rfl
  refine ⟨{ block := B, weight_zero := ?_, frequency_gap := ?_, window_gap := ?_,
    weight_succ := ?_, gain := ?_ }⟩
  · simpa only [hzero] using hw₀
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).1
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).2.1
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).2.2.1
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).2.2.2

end CalibratedWindowTower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheSparseCalibratedWindowTowerExists

section TheCalibratedTowerIsATemperedConfiguration

/-!
## The calibrated tower as a tempered zero configuration

Disjoint ordinate bands make the level index locally finite. Within each
band the ordinates are distinct, and positive depths separate the two
reflected points. Inverse-square masses are bounded by a geometric series.
The depth bands approach their top without reaching it.
-/

open Complex Filter Set Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

/-- Positive-ordinate points, indexed by level, node and depth reflection. -/
abbrev Idx := Σ j : ℕ, Fin ((W.block j).k + 1) × Bool

/-- The point associated to a calibrated exponent. -/
def pt (p : W.Idx) : ℂ :=
  (1 / 2 : ℂ) + calibratedReflectedExponent (calibratedDepthCenter Θ p.1) (W.block p.1).z p.2

theorem pt_im (j : ℕ) (i : Fin ((W.block j).k + 1)) (b : Bool) :
    (W.pt ⟨j, (i, b)⟩).im = ((W.block j).z i).im := by
  cases b <;> simp [pt, calibratedReflectedExponent]

theorem pt_im_bounds (p : W.Idx) :
    (W.block p.1).Γ / 2 ≤ (W.pt p).im ∧ (W.pt p).im ≤ 4 * (W.block p.1).Γ := by
  rcases p with ⟨j, i, b⟩
  rw [pt_im]
  exact ⟨((W.block j).geometry i).2.1, ((W.block j).geometry i).2.2.1⟩

theorem positive_depth (hΘ : 0 < Θ) (j : ℕ) (i : Fin ((W.block j).k + 1)) :
    0 < calibratedDepthCenter Θ j + ((W.block j).z i).re := by
  have hlo := (abs_le.mp ((W.block j).geometry i).1).1
  have hb := (calibratedDepth_bounds hΘ j).2.1
  linarith only [hlo, hb]

theorem exponent_abs_re_le (hΘ : 0 < Θ) (j : ℕ) (p : Fin ((W.block j).k + 1) × Bool) :
    |(calibratedReflectedExponent (calibratedDepthCenter Θ j) (W.block j).z p).re| ≤
      calibratedDepthUpper Θ j := by
  obtain ⟨hη, hlo, hhi, _⟩ := calibratedDepth_bounds hΘ j
  exact (calibratedReflectedExponent_geometry (W.block j).z hη.le
    (by linarith only [hlo]) hhi.le (fun i => ((W.block j).geometry i).1) p).2

theorem monotone_frequency : Monotone (fun j => (W.block j).Γ) := by
  apply monotone_nat_of_le_succ
  intro j
  have hg := W.frequency_gap j
  have hΓ := (W.block j).four_le
  linarith only [hg, hΓ]

theorem frequency_gap_of_lt {i j : ℕ} (hij : i < j) :
    8 * (W.block i).Γ + 4 ≤ (W.block j).Γ :=
  (W.frequency_gap i).trans (W.monotone_frequency (Nat.succ_le_of_lt hij))

/-- A unit ordinate interval meets at most one level. -/
theorem level_eq_of_common_unit_window (p q : W.Idx) {t : ℝ}
    (hp0 : t < (W.pt p).im) (hp1 : (W.pt p).im ≤ t + 1)
    (hq0 : t < (W.pt q).im) (hq1 : (W.pt q).im ≤ t + 1) : p.1 = q.1 := by
  have hp := W.pt_im_bounds p
  have hq := W.pt_im_bounds q
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · have hh := W.frequency_gap_of_lt hlt
    linarith only [hh, hp.2, hq.1, hp0, hq1]
  · exact heq
  · have hh := W.frequency_gap_of_lt hgt
    linarith only [hh, hq.2, hp.1, hq0, hp1]

/-- Every indexed point is distinct. -/
theorem pt_injective (hΘ : 0 < Θ) : Function.Injective W.pt := by
  rintro ⟨j, i, b⟩ ⟨l, i', b'⟩ he
  have him := congrArg Complex.im he
  have hj : j = l := by
    have hp := W.pt_im_bounds ⟨j, (i, b)⟩
    have hq := W.pt_im_bounds ⟨l, (i', b')⟩
    rcases lt_trichotomy j l with hlt | heq | hgt
    · have hg := W.frequency_gap_of_lt hlt
      linarith only [him, hp.2, hq.1, hg]
    · exact heq
    · have hg := W.frequency_gap_of_lt hgt
      linarith only [him, hq.2, hp.1, hg]
  subst l
  have hΓ : 0 < (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hk : (0 : ℝ) < (W.block j).k := by exact_mod_cast (W.block j).degree_pos
  have hi : i = i' := ordinate_injective_of_index_separated (div_pos hΓ hk)
    (W.block j).separation (by simpa only [pt_im] using him)
  subst i'
  have hre := congrArg Complex.re he
  have hd := W.positive_depth hΘ j i
  cases b <;> cases b' <;> try rfl
  all_goals
    simp only [pt, calibratedReflectedExponent, Bool.false_eq_true, ↓reduceIte,
      Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re] at hre
    norm_num only [Complex.div_ofNat_re, Complex.one_re] at hre
    linarith only [hre, hd]

theorem reflect_pt (j : ℕ) (i : Fin ((W.block j).k + 1)) (b : Bool) :
    reflect (W.pt ⟨j, (i, b)⟩) = W.pt ⟨j, (i, !b)⟩ := by
  cases b <;> simp [pt, calibratedReflectedExponent, reflect] <;> ring

/-- A simple zero configuration supported on the calibrated reflected blocks. -/
def config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range W.pt
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨p, rfl⟩
    have hb := W.exponent_abs_re_le hΘ p.1 p.2
    have hu := (calibratedDepth_bounds hΘ p.1).2.2.2
    have hp := abs_le.mp hb
    simp only [pt, Complex.add_re]
    norm_num only [Complex.div_ofNat_re, Complex.one_re]
    constructor <;> linarith only [hp.1, hp.2, hu, hΘ2]
  reflect_mem := by
    rintro ρ ⟨⟨j, i, b⟩, rfl⟩
    exact ⟨⟨j, (i, !b)⟩, (W.reflect_pt j i b).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    let S : Set W.Idx := {p : W.Idx | p.1 ≤ ⌊T₂⌋₊}
    have hS : S.Finite := by
      refine ((Set.finite_univ (α := ↥(Finset.Iic ⌊T₂⌋₊))).biUnion
        fun j _ => (Set.finite_univ (α := Fin ((W.block j.1).k + 1) × Bool)).image
          (fun p => (⟨j.1, p⟩ : W.Idx))).subset ?_
      intro p hp
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
      exact ⟨⟨p.1, Finset.mem_Iic.mpr hp⟩, trivial, p.2, rfl⟩
    refine (hS.image W.pt).subset ?_
    rintro ρ ⟨⟨p, rfl⟩, _, hT⟩
    refine ⟨p, ?_, rfl⟩
    have hi := (W.block p.1).index_le
    have him := (W.pt_im_bounds p).1
    exact Nat.le_floor (by linarith only [hi, him, hT])

/-- The spectral coordinate of the point is minus `i` times its exponent. -/
theorem gammaOf_pt (p : W.Idx) :
    gammaOf (W.pt p) = -I * calibratedReflectedExponent
      (calibratedDepthCenter Θ p.1) (W.block p.1).z p.2 := by
  apply Complex.ext <;> simp [gammaOf, pt, Complex.div_I] <;> ring

theorem normSq_gammaOf_pt_ge (p : W.Idx) :
    ((W.block p.1).Γ / 2) ^ 2 ≤ Complex.normSq (gammaOf (W.pt p)) := by
  have hre : (gammaOf (W.pt p)).re = (W.pt p).im := by
    simp [gammaOf, Complex.div_I]
  rw [Complex.normSq_apply, hre]
  have him := (W.pt_im_bounds p).1
  have hΓ : 0 ≤ (W.block p.1).Γ / 2 := by linarith only [(W.block p.1).four_le]
  have hh := pow_le_pow_left₀ hΓ him 2
  nlinarith only [hh, sq_nonneg (gammaOf (W.pt p)).im]

/-- The tower is tempered: its inverse-square ordinate mass is bounded levelwise by `2⁻ʲ`. -/
theorem temperedConfig_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (W.config hΘ hΘ2) := by
  classical
  unfold TemperedConfig
  let e := Equiv.ofInjective W.pt (W.pt_injective hΘ)
  show Summable fun ρ : Set.range W.pt => ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  let F : W.Idx → ℝ := fun p => 1 / (1 + Complex.normSq (gammaOf (W.pt p)))
  change Summable F
  have hF0 : ∀ p, 0 ≤ F p := fun p => by
    dsimp only [F]
    exact div_nonneg zero_le_one (by linarith only [Complex.normSq_nonneg (gammaOf (W.pt p))])
  rw [summable_sigma_of_nonneg hF0]
  refine ⟨fun j => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => hF0 _) (fun j => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [tsum_fintype]
  have hΓ : 0 < (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hterm : ∀ p : Fin ((W.block j).k + 1) × Bool,
      F ⟨j, p⟩ ≤ 4 / (W.block j).Γ ^ 2 := by
    intro p
    dsimp only [F]
    have hh := W.normSq_gammaOf_pt_ge ⟨j, p⟩
    apply (div_le_div_iff₀ (by linarith only [Complex.normSq_nonneg (gammaOf (W.pt ⟨j, p⟩))])
      (by positivity : 0 < (W.block j).Γ ^ 2)).mpr
    nlinarith only [hh]
  have hk1 : (1 : ℝ) ≤ (W.block j).k := by exact_mod_cast (W.block j).degree_pos
  calc
    _ ≤ ∑ _p : Fin ((W.block j).k + 1) × Bool, 4 / (W.block j).Γ ^ 2 :=
      Finset.sum_le_sum fun p _ => hterm p
    _ = 8 * ((W.block j).k + 1 : ℝ) / (W.block j).Γ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool]
      push_cast
      ring
    _ ≤ 16 * ((W.block j).k : ℝ) / (W.block j).Γ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hk1]
    _ ≤ _ := (W.block j).tempered_mass

/-- No zero reaches the top depth. -/
theorem re_lt_half_add (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    {ρ : ℂ} (hρ : ρ ∈ (W.config hΘ hΘ2).carrier) : ρ.re < 1 / 2 + Θ := by
  obtain ⟨p, rfl⟩ := hρ
  have hh := W.exponent_abs_re_le hΘ p.1 p.2
  have hu := (calibratedDepth_bounds hΘ p.1).2.2.2
  have hr := le_abs_self (calibratedReflectedExponent
    (calibratedDepthCenter Θ p.1) (W.block p.1).z p.2).re
  simp only [pt, Complex.add_re]
  norm_num only [Complex.div_ofNat_re, Complex.one_re]
  linarith only [hh, hu, hr]

/-- Zeros nevertheless approach the prescribed top arbitrarily closely. -/
theorem exists_re_gt_half_add_sub (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ ∈ (W.config hΘ hΘ2).carrier, 1 / 2 + Θ - ε < ρ.re := by
  obtain ⟨j, hj⟩ := exists_calibratedDepth_lower_gt hΘ (show Θ - ε < Θ by linarith only [hε])
  let i : Fin ((W.block j).k + 1) := ⟨0, Nat.succ_pos _⟩
  refine ⟨W.pt ⟨j, (i, true)⟩, ⟨⟨j, (i, true)⟩, rfl⟩, ?_⟩
  have hi := (abs_le.mp ((W.block j).geometry i).1).1
  simp only [pt, calibratedReflectedExponent, ↓reduceIte, Complex.add_re, Complex.ofReal_re]
  norm_num only [Complex.div_ofNat_re, Complex.one_re]
  linarith only [hj, hi]

end CalibratedWindowTower.Tower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheCalibratedTowerIsATemperedConfiguration

section TheCalibratedTowerHasLogarithmicLocalCounts

/-!
## Logarithmic local counts for the calibrated tower

A unit ordinate window meets one level. Each calibrated node contributes
two reflected zeros, and index separation bounds the node count by
`1+k/Γ`. The chosen logarithmic density bound puts the configuration in
class `𝒵(γmin,C)`.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

/-- Every unit ordinate window satisfies the prescribed logarithmic zero-count bound. -/
theorem localCount_config (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (t : ℝ) :
    ((W.config hΘ hΘ2).N t (t + 1) : ℝ) ≤ C * Real.log (|t| + 3) := by
  classical
  let Z := W.config hΘ hΘ2
  have hlog0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
  rcases (Z.window t (t + 1)).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have hN0 : Z.N t (t + 1) = 0 := by simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [hN0, Nat.cast_zero]
    exact mul_nonneg hC.le hlog0
  rcases hρ₀ with ⟨⟨p₀, rfl⟩, htlo, hthi⟩
  let j₀ := p₀.1
  let S := Finset.univ.filter (fun i : Fin ((W.block j₀).k + 1) =>
    t < ((W.block j₀).z i).im ∧ ((W.block j₀).z i).im ≤ t + 1)
  let F : Finset ℂ := (S ×ˢ (Finset.univ : Finset Bool)).image (fun p => W.pt ⟨j₀, p⟩)
  have hfin := Z.finite_window t (t + 1)
  have hsub : hfin.toFinset ⊆ F := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rcases hρ with ⟨⟨⟨j, i, b⟩, rfl⟩, hlo, hhi⟩
    have hj : j = j₀ := W.level_eq_of_common_unit_window ⟨j, (i, b)⟩ p₀ hlo hhi htlo hthi
    subst j
    apply Finset.mem_image.mpr
    refine ⟨(i, b), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa only [W.pt_im] using And.intro hlo hhi⟩
  have hN : Z.N t (t + 1) ≤ 2 * S.card := by
    calc
      _ = ∑ ρ ∈ hfin.toFinset, Z.mult ρ := finsum_mem_eq_finite_toFinset_sum _ hfin
      _ = hfin.toFinset.card := by simp [Z, config]
      _ ≤ F.card := Finset.card_le_card hsub
      _ ≤ (S ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, Nat.mul_comm]
  have hΓ : 0 < (W.block j₀).Γ := by linarith only [(W.block j₀).four_le]
  have hk : (0 : ℝ) < (W.block j₀).k := by exact_mod_cast (W.block j₀).degree_pos
  have hcount := card_calibrated_ordinate_window_le (div_pos hΓ hk) (W.block j₀).z
    (W.block j₀).separation t
  have hrecip : 1 / ((W.block j₀).Γ / (W.block j₀).k) =
      (W.block j₀).k / (W.block j₀).Γ := by field_simp
  rw [hrecip] at hcount
  have hNr : (Z.N t (t + 1) : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hN
  have hΓsq : (W.block j₀).Γ ≤ (|t| + 3) ^ 2 := by
    have him := (W.pt_im_bounds p₀).1
    have ht := le_abs_self t
    nlinarith only [him, hthi, ht, abs_nonneg t, sq_nonneg |t|]
  have hlog : Real.log (W.block j₀).Γ ≤ 2 * Real.log (|t| + 3) := by
    have hh := Real.log_le_log hΓ hΓsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hClog := mul_le_mul_of_nonneg_left hlog hC.le
  have hdensity := (W.block j₀).local_count
  change (S.card : ℝ) ≤ (W.block j₀).k / (W.block j₀).Γ + 1 at hcount
  nlinarith only [hNr, hcount, hdensity, hClog]

/-- The calibrated tower belongs to the prescribed density class. -/
theorem inClassZ_config (hγ : 0 < γmin) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    InClassZ γmin C (W.config hΘ hΘ2) := by
  refine ⟨W.temperedConfig_config hΘ hΘ2, ?_, ?_, W.localCount_config hC hΘ hΘ2⟩
  · rintro ρ ⟨p, rfl⟩
    have hh := (W.block p.1).lowest.trans (W.pt_im_bounds p).1
    exact (hγ.trans_le hh).ne'
  · rintro ρ ⟨p, rfl⟩
    have hh := (W.block p.1).lowest.trans (W.pt_im_bounds p).1
    rw [abs_of_pos (hγ.trans_le hh)]
    exact hh

end CalibratedWindowTower.Tower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheCalibratedTowerHasLogarithmicLocalCounts

section TheCalibratedTowerHasItsLiteralSplineTrace

/-!
## Literal spline trace of the calibrated tower

The squared transform of `boxSpline 1 3` is `sinc⁸`. Reindexing its
absolutely convergent zero sum by levels therefore gives exactly the
calibrated reflected blocks, with the coefficient masses used in the
sparse tower construction.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

def exponent (j : ℕ) : Fin ((W.block j).k + 1) × Bool → ℂ :=
  calibratedReflectedExponent (calibratedDepthCenter Θ j) (W.block j).z

def weight (j : ℕ) : ℝ := splineBlockWeight (W.exponent j)

def blockTrace (j : ℕ) (u : ℝ) : ℝ := 2 * (splineExponentialBlock (W.exponent j) u).re

def right (j : ℕ) : ℝ := (W.block j).T + R (W.block j).T

theorem weight_nonneg (j : ℕ) : 0 ≤ W.weight j := splineBlockWeight_nonneg _

/-- The actual spline mass satisfies the bound used when selecting the blocks. -/
theorem weight_le_bound (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (j : ℕ) :
    W.weight j ≤ 524288 * Real.exp 4 * ((W.block j).k : ℝ) / (W.block j).Γ ^ 2 := by
  have hΓ : 0 < (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hΓ1 : 1 ≤ (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hη := (calibratedDepth_bounds hΘ j).1
  have hd := (calibratedDepth_bounds hΘ j).2.1
  have hu := (calibratedDepth_bounds hΘ j).2.2.1
  have hgeom := calibratedReflectedExponent_geometry (W.block j).z hη.le
    (by linarith only [hd]) hu.le (fun i => ((W.block j).geometry i).1)
  have hw : ∀ p, |(W.exponent j p).re| ≤ 1 / 2 := fun p =>
    (W.exponent_abs_re_le hΘ j p).trans ((calibratedDepth_bounds hΘ j).2.2.2.le.trans hΘ2)
  have him : ∀ p, (W.block j).Γ / 2 ≤ (W.exponent j p).im := by
    intro p
    rw [(hgeom p).1]
    exact ((W.block j).geometry p.1).2.1
  have hh := splineBlockWeight_le hΓ (W.exponent j) hw him
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hh
  push_cast at hh
  have hk1 : (1 : ℝ) ≤ (W.block j).k := by exact_mod_cast (W.block j).degree_pos
  have hnum : 131072 * Real.exp 4 * (((W.block j).k + 1 : ℝ) * 2) ≤
      524288 * Real.exp 4 * ((W.block j).k : ℝ) := by
    have he := Real.exp_pos (4 : ℝ)
    nlinarith only [mul_nonneg he.le (sub_nonneg.mpr hk1)]
  have hpow : (W.block j).Γ ^ 2 ≤ (W.block j).Γ ^ 8 := by
    calc
      _ = (W.block j).Γ ^ 2 * 1 := by ring
      _ ≤ (W.block j).Γ ^ 2 * (W.block j).Γ ^ 6 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hΓ1) (sq_nonneg _)
      _ = _ := by ring
  exact hh.trans ((div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow))

theorem weight_zero_le (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : W.weight 0 ≤ 1 :=
  (W.weight_le_bound hΘ hΘ2 0).trans W.weight_zero

theorem weight_succ_le (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (j : ℕ) :
    W.weight (j + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * W.right j)) :=
  (W.weight_le_bound hΘ hΘ2 (j + 1)).trans (W.weight_succ j)

theorem right_nonneg (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) : 0 ≤ W.right j := by
  have hh := (W.block j).left_le
  have hr := hR0 (W.block j).T
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  dsimp only [right]
  linarith only [hh, hr, hj]

theorem monotone_right (hR0 : ∀ T, 0 ≤ R T) : Monotone W.right := by
  apply monotone_nat_of_le_succ
  intro j
  have hh := W.window_gap j
  have hr := hR0 (W.block (j + 1)).T
  dsimp only [right]
  linarith only [hh, hr]

/-- The complete configuration trace is the sum of its literal finite spline blocks. -/
theorem two_re_lagStructure_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (W.config hΘ hΘ2) (boxSpline 1 3) u).re = ∑' j, W.blockTrace j u := by
  classical
  let Z := W.config hΘ hΘ2
  have hs := summable_lagStructure Z (W.temperedConfig_config hΘ hΘ2)
    (SplineTower.contDiff_two_boxSpline (o := 3) le_rfl) (boxSpline_support (r := 1) one_pos 3) u
  let e := Equiv.ofInjective W.pt (W.pt_injective hΘ)
  let F : W.Idx → ℂ := fun p =>
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (W.pt p)) *
      Complex.exp (I * gammaOf (W.pt p) * u)
  have hcomp : ∀ p, ((Z.mult (e p) : ℂ) *
      paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (e p)) *
      Complex.exp (I * gammaOf (e p) * u)) = F p := by
    intro p
    simp [Z, config, e, F]
  have hS : HasSum F (lagStructure Z (boxSpline 1 3) u) := by
    have hh := (e.hasSum_iff).mpr hs.hasSum
    simpa only [Function.comp_def, hcomp] using hh
  have hI (w : ℂ) : I * (-I * w) = w := by
    rw [← mul_assoc, mul_neg, I_mul_I]
    ring
  have hfib : ∀ j, HasSum (fun p : Fin ((W.block j).k + 1) × Bool => F ⟨j, p⟩)
      (splineExponentialBlock (W.exponent j) u) := by
    intro j
    have hh := hasSum_fintype (fun p : Fin ((W.block j).k + 1) × Bool => F ⟨j, p⟩)
    simpa only [F, W.gammaOf_pt, SplineTower.paperFT_weilTest_spline (o := 3) le_rfl,
      show 2 * (3 + 1) = 8 by rfl, hI, exponent, splineExponentialBlock] using hh
  have hG := hS.sigma hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simpa only [Complex.reCLM_apply, blockTrace] using hre.tsum_eq.symm

end CalibratedWindowTower.Tower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheCalibratedTowerHasItsLiteralSplineTrace

section EveryPrescribedSublogarithmicRadiusMissesTheMinimalFace

/-!
## Every prescribed sublogarithmic radius misses the minimal face

Self-consistent interpolation blocks produce positive windows for any
prescribed nonnegative `R(T)=o(log T)`. The sparse reflected tower is a
simple tempered configuration in the required logarithmic density class,
with an unattained positive top and window floors tending to infinity.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

private theorem weight_le_one (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) : W.weight j ≤ 1 := by
  cases j with
  | zero => exact W.weight_zero_le hΘ hΘ2
  | succ j =>
    have hp : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have he : Real.exp (-(Θ * W.right j)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hΘ.le (W.right_nonneg hR0 j)))
    exact (W.weight_succ_le hΘ hΘ2 j).trans (by
      simpa only [one_mul] using mul_le_mul hp he (Real.exp_pos _).le zero_le_one)

/-- The selected block dominates the previous upper depth throughout its prescribed window. -/
private theorem normalized_block_dominates (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) {u : ℝ}
    (hu : |u - (W.block (j + 1)).T| ≤ R (W.block (j + 1)).T) :
    (j : ℝ) + 10 ≤ Real.exp
      ((calibratedDepthUpper Θ (j + 1) - calibratedDepthUpper Θ j) * u) *
        (Real.exp (-(calibratedDepthUpper Θ (j + 1) * u)) * W.blockTrace (j + 1) u) := by
  have hul : (W.block (j + 1)).T - R (W.block (j + 1)).T ≤ u := by
    linarith only [(abs_le.mp hu).1]
  have hu0 : 0 ≤ u := by
    have hh := (W.block (j + 1)).left_le
    have hj : (0 : ℝ) ≤ j + 1 := by positivity
    linarith only [hul, hh, hj]
  obtain ⟨hη, hlo, _, _⟩ := calibratedDepth_bounds hΘ (j + 1)
  have htvu : (W.block (j + 1)).T + (u - (W.block (j + 1)).T) = u := by ring
  have hfinite := two_re_reflected_calibrated_block_ge (W.block (j + 1)).z hη.le
    (by linarith only [hlo]) (fun i => ((W.block (j + 1)).geometry i).1
    (T := (W.block (j + 1)).T) (v := u - (W.block (j + 1)).T)
    (by simpa only [htvu] using hu0) hu (W.block (j + 1)).positive
  have hfinite' : (3 / 2 : ℝ) * Real.exp (calibratedDepthCenter Θ (j + 1) * (u - 8)) -
      W.weight (j + 1) ≤ W.blockTrace (j + 1) u := by
    simpa only [htvu, weight, blockTrace, exponent] using hfinite
  let b := calibratedDepthUpper Θ j
  let x := calibratedDepthCenter Θ (j + 1)
  have hb0 : 0 ≤ b := SplineTower.depth_nonneg hΘ _
  have hgap : 0 < x - b := sub_pos.mpr (calibratedDepthUpper_lt_next_center hΘ j)
  have hexp : Real.exp (-(b * u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hb0 hu0))
  have hw : Real.exp (-(b * u)) * W.weight (j + 1) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hexp (W.weight_le_one hΘ hΘ2 hR0 (j + 1))
      (W.weight_nonneg (j + 1)) zero_le_one
  have hgain : (j : ℝ) + 12 ≤ (3 / 2 : ℝ) * Real.exp ((x - b) * u - 8 * x) :=
    (W.gain j).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left hul hgap.le) _))
      (by norm_num))
  have hm := mul_le_mul_of_nonneg_left hfinite' (Real.exp_pos (-(b * u))).le
  have hp : Real.exp (-(b * u)) * Real.exp (x * (u - 8)) =
      Real.exp ((x - b) * u - 8 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm' : (3 / 2 : ℝ) * Real.exp ((x - b) * u - 8 * x) -
      Real.exp (-(b * u)) * W.weight (j + 1) ≤
        Real.exp (-(b * u)) * W.blockTrace (j + 1) u := by
    convert hm using 1
    rw [mul_sub]
    rw [show Real.exp (-(b * u)) * ((3 / 2 : ℝ) * Real.exp (x * (u - 8))) =
      (3 / 2 : ℝ) * (Real.exp (-(b * u)) * Real.exp (x * (u - 8))) by ring, hp]
  have he : Real.exp ((calibratedDepthUpper Θ (j + 1) - calibratedDepthUpper Θ j) * u) *
      (Real.exp (-(calibratedDepthUpper Θ (j + 1) * u)) * W.blockTrace (j + 1) u) =
        Real.exp (-(b * u)) * W.blockTrace (j + 1) u := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp only [b]
    ring
  rw [he]
  linarith only [hm', hgain, hw]

/-- The whole trace exceeds the level index throughout the selected window. -/
theorem window_floor (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) {u : ℝ}
    (hu : |u - (W.block (j + 1)).T| ≤ R (W.block (j + 1)).T) :
    (j : ℝ) + 1 ≤ 2 * (lagStructure (W.config hΘ hΘ2) (boxSpline 1 3) u).re := by
  let a : ℕ → ℝ := fun k => Real.exp (-(calibratedDepthUpper Θ k * u)) * W.blockTrace k u
  have hul : (W.block (j + 1)).T - R (W.block (j + 1)).T ≤ u := by
    linarith only [(abs_le.mp hu).1]
  have hu0 : 0 ≤ u := by
    have hh := (W.block (j + 1)).left_le
    have hj : (0 : ℝ) ≤ j + 1 := by positivity
    linarith only [hul, hh, hj]
  have hur : u ≤ W.right (j + 1) := by
    dsimp only [right]
    linarith only [(abs_le.mp hu).2]
  have ha : ∀ k, |a k| ≤ W.weight k := by
    intro k
    apply abs_normalized_spline_block_le (W.exponent k) hu0
    intro p
    exact (le_abs_self _).trans (W.exponent_abs_re_le hΘ k p)
  have hdom := W.normalized_block_dominates hΘ hΘ2 hR0 j hu
  have hg := tsum_ge_of_top_window hΘ
    (x := calibratedDepthUpper Θ) (w := W.weight) (U := W.right) (a := a) (b := fun _ => 0)
    (fun k => SplineTower.depth_nonneg hΘ _)
    (fun k => (calibratedDepth_bounds hΘ k).2.2.2.le)
    (strictMono_calibratedDepthUpper hΘ).monotone W.weight_nonneg
    (W.weight_zero_le hΘ hΘ2) (W.weight_succ_le hΘ hΘ2)
    (W.monotone_right hR0) (W.right_nonneg hR0 0) ha
    (fun k => by simpa only [abs_zero] using W.weight_nonneg k)
    hu0 (M := (j : ℝ) + 1) (by positivity) hur (by simpa only [a, add_assoc, show (1 : ℝ) + 9 = 10 by norm_num] using hdom)
  have he (k : ℕ) : Real.exp (calibratedDepthUpper Θ k * u) * a k +
      Real.exp (-(calibratedDepthUpper Θ k * u)) * 0 = W.blockTrace k u := by
    dsimp only [a]
    rw [mul_zero, add_zero, ← mul_assoc, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, one_mul]
  rw [W.two_re_lagStructure_config hΘ hΘ2]
  simpa only [he] using hg

end CalibratedWindowTower.Tower

/-- Every prescribed nonnegative sublogarithmic radius admits one simple configuration in class `𝒵`
with an unattained positive top and arbitrarily late windows exceeding every fixed floor. -/
theorem exists_classZ_prescribed_sublogarithmic_windows_bddBelow_beyond_every_bound
    {γmin C Θ : ℝ} (hγ : 0 < γmin) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (R : ℝ → ℝ) (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    ∃ Z : ZeroConfig,
      InClassZ γmin C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧
        ∀ u : ℝ, |u - T| ≤ R T → K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  obtain ⟨W⟩ := CalibratedWindowTower.exists_tower (γmin := γmin) hC hΘ hR0 hR
  refine ⟨W.config hΘ hΘ2, W.inClassZ_config hγ hC hΘ hΘ2, fun _ _ => rfl,
    fun _ hρ => W.re_lt_half_add hΘ hΘ2 hρ,
    fun ε hε => W.exists_re_gt_half_add_sub hΘ hΘ2 hε, ?_⟩
  intro K U
  let j := max ⌈max K 0⌉₊ ⌈max U 0⌉₊
  have hK : K ≤ (j : ℝ) := by
    exact ((le_max_left K 0).trans (Nat.le_ceil _)).trans
      (by exact_mod_cast le_max_left ⌈max K 0⌉₊ ⌈max U 0⌉₊)
  have hU : U ≤ (j : ℝ) := by
    exact ((le_max_left U 0).trans (Nat.le_ceil _)).trans
      (by exact_mod_cast le_max_right ⌈max K 0⌉₊ ⌈max U 0⌉₊)
  refine ⟨(W.block (j + 1)).T, ?_, fun u hu => ?_⟩
  · have hh := (W.block (j + 1)).left_le
    have hr := hR0 (W.block (j + 1)).T
    push_cast at hh
    linarith only [hh, hr, hU]
  · have hh := W.window_floor hΘ hΘ2 hR0 j hu
    linarith only [hh, hK]

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end EveryPrescribedSublogarithmicRadiusMissesTheMinimalFace
