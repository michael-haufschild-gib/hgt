import GaloisForLFunctions.RHTower.ThetaGammaPolarCrossingExchange
import GaloisForLFunctions.RHTower.ThetaGammaPolarGroundDifference

/-!
# Integrating the literal continuous source diagonal

Both endpoint source actions are absolutely integrable on the complete
shift-position space. Translation of the second endpoint and Fubini identify
their sum with the symmetric Gamma/pole source. This keeps the cancellation
inside the original Gamma integrand at zero shift.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def thetaGammaPolarSourceDiagonal (chi : 𝓢(ℝ, ℂ)) (reflected : Bool) (p : ℝ × ℝ) : ℝ :=
  thetaCuspFullSource p.2 *
    (thetaGammaPolarSourceTerm (if reflected then -p.2 else p.2) p.1).re * ‖chi p.2‖ ^ 2

private def sourceMajorant (u : ℝ) : ℝ :=
  gammaSourceBound u + thetaCuspDerivativeExpConstant 0 *
    (Real.exp ((-1 / 2 : ℝ) * u) + Real.exp ((-3 / 2 : ℝ) * u))

private theorem integrable_sourceMajorant : IntegrableOn sourceMajorant (Ioi (0 : ℝ)) :=
  gammaSourceBound_integrable.fun_add
    (((integrableOn_exp_mul_Ioi (a := -1 / 2) (by norm_num) 0).fun_add
      (integrableOn_exp_mul_Ioi (a := -3 / 2) (by norm_num) 0)).const_mul
        (thetaCuspDerivativeExpConstant 0))

private theorem source_bound (x : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖thetaGammaPolarSourceTerm x u‖ ≤ Real.exp |x| * sourceMajorant u := by
  have hg : 0 ≤ gammaSourceBound u :=
    (abs_nonneg _).trans (abs_gammaSourceTerm_le_bound 0 hu)
  have he : 1 ≤ Real.exp |x| := Real.one_le_exp_iff.mpr (abs_nonneg x)
  have h := mul_le_mul_of_nonneg_left he hg
  calc
    _ ≤ gammaSourceBound u + thetaCuspDerivativeExpConstant 0 * Real.exp |x| *
        (Real.exp ((-1 / 2 : ℝ) * u) + Real.exp ((-3 / 2 : ℝ) * u)) :=
      norm_thetaGammaPolarSourceTerm_le x hu
    _ ≤ Real.exp |x| * sourceMajorant u := by dsimp [sourceMajorant]; nlinarith

/-- The compensated forward or reflected source diagonal is absolutely integrable. -/
theorem integrable_thetaGammaPolarSourceDiagonal (chi : 𝓢(ℝ, ℂ)) (reflected : Bool) :
    Integrable (thetaGammaPolarSourceDiagonal chi reflected) thetaContinuousLinkMeasure := by
  obtain ⟨C, hC, hb⟩ := thetaCuspTiltSource.decay 2
  let N := ‖chi.toBoundedContinuousFunction‖
  have hix : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
    simpa only [pow_zero, one_mul, neg_mul] using
      HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (show (0 : ℝ) < 1 by norm_num)
  have hm : Measurable (thetaGammaPolarSourceDiagonal chi reflected) := by
    have hk := contDiff_thetaCuspFullSource.continuous.measurable
    have hc := chi.continuous.measurable
    cases reflected <;>
      unfold thetaGammaPolarSourceDiagonal thetaGammaPolarSourceTerm gammaSourceTerm polarSourceTerm <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      fun_prop
  have hmajor := (integrable_sourceMajorant.mul_prod hix).const_mul (C * N ^ 2)
  apply hmajor.mono' hm.aestronglyMeasurable
  have hpos : ∀ᵐ p : ℝ × ℝ ∂thetaContinuousLinkMeasure, 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Eventually.of_forall fun _ => hu
  filter_upwards [hpos] with p hp
  have hr : |if reflected then -p.2 else p.2| = |p.2| := by cases reflected <;> simp
  have hs := source_bound (if reflected then -p.2 else p.2) hp
  rw [hr] at hs
  have hn : ‖chi p.2‖ ^ 2 ≤ N ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (chi.toBoundedContinuousFunction.norm_coe_le_norm _) 2
  have hB : 0 ≤ sourceMajorant p.1 := by
    exact nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hs) (Real.exp_pos _)
  have hexp : Real.exp (-(2 * |p.2|)) * Real.exp |p.2| = Real.exp (-|p.2|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [thetaGammaPolarSourceDiagonal, Real.norm_eq_abs, abs_mul,
    abs_of_pos (show 0 < thetaCuspFullSource p.2 from thetaCuspTiltSource.pos p.2),
    abs_of_nonneg (sq_nonneg ‖chi p.2‖)]
  calc
    _ ≤ (C * Real.exp (-(2 * |p.2|))) *
        (Real.exp |p.2| * sourceMajorant p.1) * N ^ 2 :=
      mul_le_mul (mul_le_mul (hb p.2) ((Complex.abs_re_le_norm _).trans hs)
        (abs_nonneg _) (by positivity)) hn (sq_nonneg _) (by positivity)
    _ = C * N ^ 2 * (sourceMajorant p.1 * Real.exp (-|p.2|)) := by
      calc
        _ = C * N ^ 2 * sourceMajorant p.1 *
            (Real.exp (-(2 * |p.2|)) * Real.exp |p.2|) := by ring
        _ = _ := by rw [hexp]; ring

theorem integral_thetaGammaPolarSourceDiagonal_shift (chi : 𝓢(ℝ, ℂ)) (reflected : Bool) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), thetaGammaPolarSourceDiagonal chi reflected (u, x)) =
      thetaCuspFullSource x *
        (thetaArchimedeanShiftSource (if reflected then -x else x)).re * ‖chi x‖ ^ 2 := by
  change (∫ u in Ioi (0 : ℝ), thetaCuspFullSource x *
    (thetaGammaPolarSourceTerm (if reflected then -x else x) u).re * ‖chi x‖ ^ 2) = _
  rw [integral_mul_const, integral_const_mul]
  have h := integral_re (integrable_thetaGammaPolarSourceTerm (if reflected then -x else x))
  simp only [RCLike.re_to_complex] at h
  rw [h, integral_thetaGammaPolarSourceTerm]

theorem integrable_thetaGammaPolarSourceMarginal (chi : 𝓢(ℝ, ℂ)) (reflected : Bool) :
    Integrable (fun x : ℝ => thetaCuspFullSource x *
      (thetaArchimedeanShiftSource (if reflected then -x else x)).re * ‖chi x‖ ^ 2) := by
  simpa only [integral_thetaGammaPolarSourceDiagonal_shift] using
    (integrable_thetaGammaPolarSourceDiagonal chi reflected).integral_prod_right

theorem integral_thetaGammaPolarSourceDiagonal (chi : 𝓢(ℝ, ℂ)) (reflected : Bool) :
    (∫ p, thetaGammaPolarSourceDiagonal chi reflected p ∂thetaContinuousLinkMeasure) =
      ∫ x : ℝ, thetaCuspFullSource x *
        (thetaArchimedeanShiftSource (if reflected then -x else x)).re * ‖chi x‖ ^ 2 := by
  rw [integral_prod_symm _ (integrable_thetaGammaPolarSourceDiagonal chi reflected)]
  simp only [integral_thetaGammaPolarSourceDiagonal_shift]

private theorem measurePreserving_shift :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 + p.1))
      thetaContinuousLinkMeasure thetaContinuousLinkMeasure := by
  apply (MeasurePreserving.id (volume.restrict (Ioi (0 : ℝ)))).skew_product
    (g := fun u x : ℝ => x + u) (by fun_prop)
  exact Eventually.of_forall fun u => (measurePreserving_add_right volume u).map_eq

theorem thetaGammaPolarDiagonalDensity_eq_sources (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) :
    thetaGammaPolarDiagonalDensity thetaCuspTiltSource chi p =
      thetaGammaPolarSourceDiagonal chi false p +
        thetaGammaPolarSourceDiagonal chi true (p.1, p.2 + p.1) := by
  rw [thetaGammaPolarDiagonalDensity_actual]
  simp only [thetaGammaPolarSourceDiagonal, Bool.false_eq_true, ↓reduceIte,
    thetaGammaPolarSourceTerm, show -p.2 - p.1 = -(p.2 + p.1) by ring]

theorem integrable_thetaGammaPolarDiagonalDensity (chi : 𝓢(ℝ, ℂ)) :
    Integrable (thetaGammaPolarDiagonalDensity thetaCuspTiltSource chi) thetaContinuousLinkMeasure := by
  have h := (integrable_thetaGammaPolarSourceDiagonal chi false).fun_add
    (measurePreserving_shift.integrable_comp_of_integrable
      (integrable_thetaGammaPolarSourceDiagonal chi true))
  simpa only [Function.comp_apply, ← thetaGammaPolarDiagonalDensity_eq_sources] using h

theorem integral_thetaGammaPolarDiagonalDensity (chi : 𝓢(ℝ, ℂ)) :
    (∫ p, thetaGammaPolarDiagonalDensity thetaCuspTiltSource chi p ∂thetaContinuousLinkMeasure) =
      (∫ x : ℝ, thetaCuspFullSource x * (thetaArchimedeanShiftSource x).re * ‖chi x‖ ^ 2) +
        ∫ x : ℝ, thetaCuspFullSource x * (thetaArchimedeanShiftSource (-x)).re * ‖chi x‖ ^ 2 := by
  have hi : Integrable (fun p : ℝ × ℝ => thetaGammaPolarSourceDiagonal chi true (p.1, p.2 + p.1))
      thetaContinuousLinkMeasure := measurePreserving_shift.integrable_comp_of_integrable
        (integrable_thetaGammaPolarSourceDiagonal chi true)
  simp_rw [thetaGammaPolarDiagonalDensity_eq_sources]
  rw [integral_add (integrable_thetaGammaPolarSourceDiagonal chi false) hi]
  rw [integral_thetaGammaPolarSourceDiagonal]
  congr 1
  rw [integral_prod _ hi]
  have hshift : (∫ u in Ioi (0 : ℝ), ∫ x : ℝ,
      thetaGammaPolarSourceDiagonal chi true (u, x + u)) =
      ∫ u in Ioi (0 : ℝ), ∫ x : ℝ, thetaGammaPolarSourceDiagonal chi true (u, x) := by
    apply integral_congr_ae
    filter_upwards with u
    exact integral_add_right_eq_self (fun x => thetaGammaPolarSourceDiagonal chi true (u, x)) u
  rw [hshift, ← integral_prod _ (integrable_thetaGammaPolarSourceDiagonal chi true),
    integral_thetaGammaPolarSourceDiagonal]
  simp only [↓reduceIte]

end RHTower.ThetaSourceWard
