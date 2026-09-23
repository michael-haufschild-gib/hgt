import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFourier
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Archimedean bottom edge for the sharp rectangular Guinand--Weil test

The squared rectangular transform decays like `(1 + xi^(2 : ℕ))^-1` on the Euler line.  The
completed archimedean logarithmic derivative grows only logarithmically there; the repository's
unconditional vertical digamma estimate gives the slightly weaker but convenient power bound
`O((1 + xi^(2 : ℕ))^(1/4))`.  Their product is therefore dominated by the integrable profile
`(1 + xi^(2 : ℕ))^(-3/4)`.

This closes the absolute-integrability gate for the Gamma part of the piecewise-linear
rectangular explicit formula.  The final declarations transport the result into the literal
centered-Xi bottom-edge coordinate and resolve the `2 pi i` contour normalization.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

def rectangularEulerArchPoint (xi : ℝ) : ℂ :=
  3 / 2 - ((2 * Real.pi * xi : ℝ) : ℂ) * I

theorem rectangularEulerArchPoint_re (xi : ℝ) :
    (rectangularEulerArchPoint xi).re = 3 / 2 := by
  simp [rectangularEulerArchPoint, Complex.mul_re]

theorem rectangularEulerArchPoint_ne_zero (xi : ℝ) :
    rectangularEulerArchPoint xi ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [rectangularEulerArchPoint_re] at hre
  norm_num at hre

theorem rectangularEulerArchPoint_ne_one (xi : ℝ) :
    rectangularEulerArchPoint xi ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [rectangularEulerArchPoint_re] at hre
  norm_num at hre

theorem continuous_rectangularEulerArchLogDeriv :
    Continuous (fun xi : ℝ => logDeriv archFactor (rectangularEulerArchPoint xi)) := by
  let s : ℝ → ℂ := rectangularEulerArchPoint
  have hs : Continuous s := by
    change Continuous (fun xi : ℝ =>
      3 / 2 - ((2 * Real.pi * xi : ℝ) : ℂ) * I)
    fun_prop
  have hmaps : MapsTo s univ {z : ℂ | 0 < z.re} := by
    intro xi _
    simp only [mem_setOf_eq, s, rectangularEulerArchPoint_re]
    norm_num
  have hderiv : Continuous (fun xi : ℝ => archFactorDeriv (s xi)) :=
    continuousOn_archFactorDeriv.comp_continuous hs (fun xi => hmaps (mem_univ xi))
  have hfactor : Continuous (fun xi : ℝ => archFactor (s xi)) :=
    archFactor_analyticOnNhd_re_pos.continuousOn.comp_continuous hs
      (fun xi => hmaps (mem_univ xi))
  have hfactor0 : ∀ xi : ℝ, archFactor (s xi) ≠ 0 := by
    intro xi
    exact archFactor_ne_zero (rectangularEulerArchPoint_ne_zero xi)
      (rectangularEulerArchPoint_ne_one xi)
      (Gammaℝ_ne_zero_of_re_pos (by simp [s, rectangularEulerArchPoint_re]))
  rw [show (fun xi : ℝ => logDeriv archFactor (rectangularEulerArchPoint xi)) =
      fun xi : ℝ => archFactorDeriv (s xi) / archFactor (s xi) by
    funext xi
    rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos
      (by simp [s, rectangularEulerArchPoint_re] : 0 < (s xi).re)).deriv]]
  exact hderiv.div hfactor hfactor0

def rectangularEulerArchIntegrand (L a : ℝ) (xi : ℝ) : ℂ :=
  rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
    logDeriv archFactor (rectangularEulerArchPoint xi)

theorem continuous_rectangularEulerArchIntegrand (L a : ℝ) :
    Continuous (rectangularEulerArchIntegrand L a) := by
  unfold rectangularEulerArchIntegrand
  have htransform : Continuous (fun xi : ℝ =>
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I)) :=
    (rectangularTwoEdgeTransform_differentiable L a).continuous.comp (by fun_prop)
  exact (htransform.pow 2).mul continuous_rectangularEulerArchLogDeriv

theorem norm_digamma_rectangularEulerArchPoint_half_le
    {xi : ℝ} (hxi : 1 ≤ |xi|) :
    ‖Complex.digamma (rectangularEulerArchPoint xi / 2)‖ ≤
      Real.log (Real.pi * |xi|) +
        GaloisForLFunctions.digammaVerticalLogConstant := by
  let t : ℝ := Real.pi * |xi|
  have ht1 : 1 ≤ t := by
    dsimp only [t]
    have hp1 : 1 ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
    nlinarith [abs_nonneg xi]
  have hsigmat : (3 / 4 : ℝ) ≤ t := by linarith
  have hbound := GaloisForLFunctions.norm_digamma_vertical_le_log
    (σ := (3 / 4 : ℝ)) (t := t) (by norm_num) ht1 hsigmat
  by_cases hx : 0 ≤ xi
  · have harg : rectangularEulerArchPoint xi / 2 =
        (starRingEnd ℂ) (((3 / 4 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;>
        simp [rectangularEulerArchPoint, t, abs_of_nonneg hx, Complex.div_re,
          Complex.div_im, Complex.mul_re, Complex.mul_im] <;> ring
    rw [harg, ReflectedDigammaAnomaly.digamma_conj, norm_conj]
    exact hbound
  · have hxneg : xi < 0 := lt_of_not_ge hx
    have harg : rectangularEulerArchPoint xi / 2 =
        ((3 / 4 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I := by
      apply Complex.ext <;>
        simp [rectangularEulerArchPoint, t, abs_of_neg hxneg,
          Complex.mul_re, Complex.mul_im] <;> ring
    rw [harg]
    exact hbound

def rectangularEulerArchGrowthConstant : ℝ :=
  4 + |Real.log Real.pi| / 2 +
    (Real.log Real.pi + GaloisForLFunctions.digammaVerticalLogConstant) / 2

theorem rectangularEulerArchGrowthConstant_nonneg :
    0 ≤ rectangularEulerArchGrowthConstant := by
  unfold rectangularEulerArchGrowthConstant
  have hlogpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hD : 0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
    unfold GaloisForLFunctions.digammaVerticalLogConstant
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  positivity

theorem norm_logDeriv_archFactor_rectangularEuler_le
    {xi : ℝ} (hxi : 1 ≤ |xi|) :
    ‖logDeriv archFactor (rectangularEulerArchPoint xi)‖ ≤
      rectangularEulerArchGrowthConstant * (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
  let s : ℂ := rectangularEulerArchPoint xi
  have hsre : s.re = 3 / 2 := rectangularEulerArchPoint_re xi
  have hs0 : s ≠ 0 := rectangularEulerArchPoint_ne_zero xi
  have hs1 : s ≠ 1 := rectangularEulerArchPoint_ne_one xi
  have hsNorm : 1 ≤ ‖s‖ := by
    have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    rw [hsre, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)] at hre
    linarith
  have hsSubNorm : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have hre : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre, Complex.one_re] at hre
    norm_num at hre ⊢
    exact hre
  have hInv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (norm_pos_iff.mpr hs0)).2 hsNorm
  have hInvSub : ‖1 / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
    calc
      1 / ‖s - 1‖ ≤ 1 / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hsSubNorm
      _ = 2 := by norm_num
  have hgamma : ‖GaloisForLFunctions.gammaRealLogConnection s‖ ≤
      |Real.log Real.pi| / 2 +
        (Real.log (Real.pi * |xi|) +
          GaloisForLFunctions.digammaVerticalLogConstant) / 2 := by
    unfold GaloisForLFunctions.gammaRealLogConnection
    change ‖-((Real.log Real.pi : ℂ) / 2) +
        Complex.digamma (s / 2) / 2‖ ≤ _
    calc
      ‖-((Real.log Real.pi : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤
          ‖-((Real.log Real.pi : ℂ) / 2)‖ +
            ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma (s / 2)‖ / 2 := by
        simp only [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_ofNat]
      _ ≤ _ := by
        have hdig := norm_digamma_rectangularEulerArchPoint_half_le hxi
        nlinarith
  have hclosed := logDeriv_archFactor_closed
    (s := s) (by rw [hsre]; norm_num) hs0 hs1
  have hraw : ‖logDeriv archFactor s‖ ≤
      3 + |Real.log Real.pi| / 2 +
        (Real.log (Real.pi * |xi|) +
          GaloisForLFunctions.digammaVerticalLogConstant) / 2 := by
    rw [hclosed]
    calc
      ‖1 / s + 1 / (s - 1) + GaloisForLFunctions.gammaRealLogConnection s‖ ≤
          ‖1 / s + 1 / (s - 1)‖ +
            ‖GaloisForLFunctions.gammaRealLogConnection s‖ := norm_add_le _ _
      _ ≤
          ‖1 / s‖ + ‖1 / (s - 1)‖ +
            ‖GaloisForLFunctions.gammaRealLogConnection s‖ := by
              have h := norm_add_le (1 / s) (1 / (s - 1))
              linarith
      _ ≤ (1 + 2) +
          (|Real.log Real.pi| / 2 +
            (Real.log (Real.pi * |xi|) +
              GaloisForLFunctions.digammaVerticalLogConstant) / 2) :=
        add_le_add (add_le_add hInv hInvSub) hgamma
      _ = _ := by ring
  have habspos : 0 < |xi| := lt_of_lt_of_le zero_lt_one hxi
  have hlogmul : Real.log (Real.pi * |xi|) =
      Real.log Real.pi + Real.log |xi| := by
    rw [Real.log_mul (ne_of_gt Real.pi_pos) (ne_of_gt habspos)]
  have hbase : (1 : ℝ) ≤ 1 + xi ^ 2 := by nlinarith [sq_nonneg xi]
  have hquarterOne : 1 ≤ (1 + xi ^ 2) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hlogabs : Real.log |xi| / 2 ≤
      (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
    have hlogsq : 2 * Real.log |xi| = Real.log (xi ^ 2) := by
      rw [← sq_abs, Real.log_pow]
      ring
    have hlogle : Real.log (xi ^ 2) ≤ Real.log (1 + xi ^ 2) := by
      exact Real.log_le_log (sq_pos_of_ne_zero (abs_ne_zero.mp habspos.ne')) (by linarith)
    have hrawpow := Real.log_le_rpow_div
      (x := 1 + xi ^ 2) (by positivity) (by norm_num : (0 : ℝ) < 1 / 4)
    have hquarter : Real.log (1 + xi ^ 2) / 4 ≤
        (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
      nlinarith
    linarith
  rw [hlogmul] at hraw
  change ‖logDeriv archFactor s‖ ≤ _
  calc
    ‖logDeriv archFactor s‖ ≤
        (rectangularEulerArchGrowthConstant - 1) + Real.log |xi| / 2 := by
      unfold rectangularEulerArchGrowthConstant
      linarith
    _ ≤ (rectangularEulerArchGrowthConstant - 1) *
          (1 + xi ^ 2) ^ (1 / 4 : ℝ) +
        (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
      have hCminus : 0 ≤ rectangularEulerArchGrowthConstant - 1 := by
        unfold rectangularEulerArchGrowthConstant
        have hlogpi : 0 ≤ Real.log Real.pi :=
          Real.log_nonneg (by linarith [Real.pi_gt_three])
        have hD : 0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
          unfold GaloisForLFunctions.digammaVerticalLogConstant
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          positivity
        nlinarith [abs_nonneg (Real.log Real.pi)]
      exact add_le_add (le_mul_of_one_le_right hCminus hquarterOne) hlogabs
    _ = rectangularEulerArchGrowthConstant *
          (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by ring

def rectangularEulerArchTailMajorant (L a : ℝ) (xi : ℝ) : ℝ :=
  rectangularEulerFourierMajorant L a * rectangularEulerArchGrowthConstant *
    (1 + xi ^ 2) ^ (-3 / 4 : ℝ)

theorem integrable_rectangularEulerArchTailMajorant (L a : ℝ) :
    Integrable (rectangularEulerArchTailMajorant L a) := by
  have h := integrable_rpow_neg_one_add_norm_sq
    (E := ℝ) (μ := MeasureTheory.volume) (r := (3 / 2 : ℝ)) (by
      rw [Module.finrank_self]
      norm_num)
  have hbase : Integrable (fun xi : ℝ => (1 + xi ^ 2) ^ (-3 / 4 : ℝ)) := by
    refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
    change (1 + ‖xi‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) =
      (1 + xi ^ 2) ^ (-3 / 4 : ℝ)
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  exact hbase.const_mul
    (rectangularEulerFourierMajorant L a * rectangularEulerArchGrowthConstant)

theorem norm_rectangularEulerArchIntegrand_le_tailMajorant
    (L a : ℝ) {xi : ℝ} (hxi : 1 ≤ |xi|) :
    ‖rectangularEulerArchIntegrand L a xi‖ ≤
      rectangularEulerArchTailMajorant L a xi := by
  have htransform := norm_rectangularTwoEdgeTransform_eulerLine_sq_le L a xi
  have harch := norm_logDeriv_archFactor_rectangularEuler_le hxi
  have hM : 0 ≤ rectangularEulerFourierMajorant L a := by
    unfold rectangularEulerFourierMajorant
    positivity
  have hC : 0 ≤ rectangularEulerArchGrowthConstant :=
    rectangularEulerArchGrowthConstant_nonneg
  have hbase : 0 < 1 + xi ^ 2 := by positivity
  rw [rectangularEulerArchIntegrand, norm_mul]
  calc
    ‖rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
        ‖logDeriv archFactor (rectangularEulerArchPoint xi)‖ ≤
      (rectangularEulerFourierMajorant L a * (1 + xi ^ 2)⁻¹) *
        (rectangularEulerArchGrowthConstant *
          (1 + xi ^ 2) ^ (1 / 4 : ℝ)) := by
            exact mul_le_mul htransform harch (norm_nonneg _)
              (mul_nonneg hM (inv_nonneg.mpr hbase.le))
    _ = rectangularEulerArchTailMajorant L a xi := by
      rw [rectangularEulerArchTailMajorant]
      rw [show (1 + xi ^ 2)⁻¹ = (1 + xi ^ 2) ^ (-1 : ℝ) by
        exact (Real.rpow_neg_one (1 + xi ^ 2)).symm]
      rw [show rectangularEulerFourierMajorant L a * (1 + xi ^ 2) ^ (-1 : ℝ) *
          (rectangularEulerArchGrowthConstant * (1 + xi ^ 2) ^ (1 / 4 : ℝ)) =
        rectangularEulerFourierMajorant L a * rectangularEulerArchGrowthConstant *
          ((1 + xi ^ 2) ^ (-1 : ℝ) * (1 + xi ^ 2) ^ (1 / 4 : ℝ)) by ring]
      rw [← Real.rpow_add hbase]
      norm_num

theorem integrable_rectangularEulerArchIntegrand (L a : ℝ) :
    Integrable (rectangularEulerArchIntegrand L a) := by
  let S : Set ℝ := {xi : ℝ | 1 ≤ |xi|}
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (rectangularEulerArchIntegrand L a) S := by
    refine (integrable_rectangularEulerArchTailMajorant L a).integrableOn.mono' ?_ ?_
    · exact (continuous_rectangularEulerArchIntegrand L a).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict hS] with xi hxi
      exact norm_rectangularEulerArchIntegrand_le_tailMajorant L a hxi
  have hcompact : IntegrableOn (rectangularEulerArchIntegrand L a) (Icc (-1) 1) :=
    (continuous_rectangularEulerArchIntegrand L a).integrableOn_Icc
  have hcover : Icc (-1 : ℝ) 1 ∪ S = univ := by
    ext xi
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |xi| ≤ 1
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

def rectangularBottomArchIntegrand (L a : ℝ) (x : ℝ) : ℂ :=
  xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ 2 *
    logDeriv archFactor (((3 / 2 : ℝ) : ℂ) + x * I)

theorem rectangularBottomArchIntegrand_scale (L a xi : ℝ) :
    rectangularBottomArchIntegrand L a ((-2 * Real.pi) * xi) =
      rectangularEulerArchIntegrand L a xi := by
  unfold rectangularBottomArchIntegrand rectangularEulerArchIntegrand
    rectangularEulerArchPoint xiRectangularTwoEdgeTransform
  congr 2
  · congr 2
    push_cast
    rw [mul_sub, Complex.I_mul_I]
    ring_nf
  ·
    push_cast
    ring_nf

theorem integrable_rectangularBottomArchIntegrand (L a : ℝ) :
    Integrable (rectangularBottomArchIntegrand L a) := by
  have hscaled : Integrable (fun xi : ℝ =>
      rectangularBottomArchIntegrand L a ((-2 * Real.pi) * xi)) := by
    simpa only [rectangularBottomArchIntegrand_scale] using
      integrable_rectangularEulerArchIntegrand L a
  exact (integrable_comp_mul_left_iff (rectangularBottomArchIntegrand L a)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mp hscaled

def normalizedRectangularBottomArchContribution (L a : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x : ℝ, I * rectangularBottomArchIntegrand L a x)

theorem normalizedRectangularBottomArchContribution_eq
    (L a : ℝ) :
    normalizedRectangularBottomArchContribution L a =
      ((Real.pi⁻¹ : ℝ) : ℂ) *
        ∫ x : ℝ, rectangularBottomArchIntegrand L a x := by
  rw [normalizedRectangularBottomArchContribution,
    MeasureTheory.integral_const_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.ofReal_inv]
  field_simp [hpi]

end RHTower
