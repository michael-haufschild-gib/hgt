import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestLabeledOccupationSource
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Polarized Hodge--Beta transgression of the Euler source

The cofinal head/tail occupation split forces the odd Hodge scale
`sqrt (exp t - 1)`.  Equivalently, the square of the Hodge scale is the
tail/head likelihood ratio.  Its cross-channel density is therefore the
Hellinger geometric mean of the complementary arithmetic occupations.
This file computes what that source-derived Hodge rotation does to the
elementary head source.

The common Laplace test sees the head source as the rational resolvent

`1 / (1 + a)`.

It sees the odd-Hodge conjugate as

`-B(a + 1/2, 3/2)
  = -Gamma(a + 1/2) Gamma(3/2) / Gamma(a + 2)`.

Thus a Gamma quotient is not an external completion factor in this source
geometry.  It is the exact Hodge conjugate of the elementary Euler
resolvent.  The pole-centered Fisher score is the first logarithmic source
jet of this same polarized pair.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Elementary compact-head source before odd Hodge rotation. -/
def eulerPrimitiveBoundaryPolarizedUnitSeed :
    EulerPrimitiveBoundaryPolarizedFeature :=
  (fun _ => 1, fun _ => 0)

/-- Real half-line column produced by the odd-Hodge conjugate of the unit
head source. -/
def eulerPrimitiveBoundaryHodgeBetaColumn (a : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0,
    eulerPrimitiveBoundaryTailWeight t * Real.exp (-a * t) *
      (-1 / eulerPrimitiveBoundaryHodgeScale t)

/-- Hellinger geometric mean of the complementary head/tail occupations. -/
def eulerPrimitiveBoundaryOccupationHellingerDensity (t : ℝ) : ℝ :=
  Real.sqrt
    (eulerPrimitiveBoundaryHeadWeight t *
      eulerPrimitiveBoundaryTailWeight t)

/--
Fisher information density of the Bernoulli head/tail occupation family
with respect to the source-depth parameter.
-/
def eulerPrimitiveBoundaryOccupationFisherDensity (t : ℝ) : ℝ :=
  eulerPrimitiveBoundaryHeadWeight t +
    eulerPrimitiveBoundaryHeadWeight t ^ 2 /
      eulerPrimitiveBoundaryTailWeight t

theorem eulerPrimitiveBoundaryOccupationFisherDensity_eq_head_div_tail
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryOccupationFisherDensity t =
      eulerPrimitiveBoundaryHeadWeight t /
        eulerPrimitiveBoundaryTailWeight t := by
  have htail :
      eulerPrimitiveBoundaryTailWeight t ≠ 0 :=
    (eulerPrimitiveBoundaryTailWeight_pos ht).ne'
  rw [eulerPrimitiveBoundaryOccupationFisherDensity]
  field_simp
  rw [add_comm
    (eulerPrimitiveBoundaryTailWeight t)
    (eulerPrimitiveBoundaryHeadWeight t),
    eulerPrimitiveBoundaryHeadWeight_add_tailWeight]
  ring

/--
The source-forced Hodge scale is exactly reciprocal Fisher whitening:
its square times the occupation Fisher density is one.
-/
theorem eulerPrimitiveBoundaryHodgeScale_sq_mul_fisherDensity
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryHodgeScale t ^ 2 *
        eulerPrimitiveBoundaryOccupationFisherDensity t =
      1 := by
  rw [eulerPrimitiveBoundaryOccupationFisherDensity_eq_head_div_tail ht]
  have htail :
      eulerPrimitiveBoundaryTailWeight t ≠ 0 :=
    (eulerPrimitiveBoundaryTailWeight_pos ht).ne'
  rw [← mul_div_assoc,
    eulerPrimitiveBoundaryHodgeScale_sq_mul_headWeight ht,
    div_self htail]

/--
Multiplying the head occupation by the forced Hodge scale gives the
Hellinger cross-channel density exactly.
-/
theorem eulerPrimitiveBoundaryHeadWeight_mul_hodgeScale_eq_hellinger
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryHeadWeight t *
        eulerPrimitiveBoundaryHodgeScale t =
      eulerPrimitiveBoundaryOccupationHellingerDensity t := by
  rw [eulerPrimitiveBoundaryOccupationHellingerDensity,
    ← eulerPrimitiveBoundaryHodgeScale_sq_mul_headWeight ht]
  rw [show
    eulerPrimitiveBoundaryHeadWeight t *
          (eulerPrimitiveBoundaryHodgeScale t ^ 2 *
            eulerPrimitiveBoundaryHeadWeight t) =
        (eulerPrimitiveBoundaryHeadWeight t *
          eulerPrimitiveBoundaryHodgeScale t) ^ 2 by ring]
  rw [Real.sqrt_sq]
  exact mul_nonneg
    (eulerPrimitiveBoundaryHeadWeight_pos t).le
    (eulerPrimitiveBoundaryHodgeScale_pos ht).le

/--
Dividing the tail occupation by the forced Hodge scale gives the same
Hellinger cross-channel density exactly.
-/
theorem eulerPrimitiveBoundaryTailWeight_div_hodgeScale_eq_hellinger
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryTailWeight t /
        eulerPrimitiveBoundaryHodgeScale t =
      eulerPrimitiveBoundaryOccupationHellingerDensity t := by
  have hq := (eulerPrimitiveBoundaryHodgeScale_pos ht).ne'
  rw [← eulerPrimitiveBoundaryHodgeScale_sq_mul_headWeight ht,
    pow_two]
  field_simp
  simpa [mul_comm] using
    eulerPrimitiveBoundaryHeadWeight_mul_hodgeScale_eq_hellinger ht

/--
The odd-Hodge column is the negative Laplace transform of the Hellinger
geometric mean of the complementary arithmetic occupations.
-/
theorem eulerPrimitiveBoundaryHodgeBetaColumn_eq_neg_hellingerLaplace
    (a : ℝ) :
    eulerPrimitiveBoundaryHodgeBetaColumn a =
      -(∫ t : ℝ in Ioi 0,
        Real.exp (-a * t) *
          eulerPrimitiveBoundaryOccupationHellingerDensity t) := by
  rw [eulerPrimitiveBoundaryHodgeBetaColumn, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show
    eulerPrimitiveBoundaryOccupationHellingerDensity t =
      eulerPrimitiveBoundaryTailWeight t /
        eulerPrimitiveBoundaryHodgeScale t by
      exact
        (eulerPrimitiveBoundaryTailWeight_div_hodgeScale_eq_hellinger
          (mem_Ioi.mp ht)).symm]
  ring

/-- The polarized pairing with the odd-Hodge unit source is the literal
half-line Hodge--Beta column. -/
theorem eulerPrimitiveBoundaryPolarizedPairing_test_oddHodge_unitSeed
    (a : ℝ) :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest (a : ℂ))
        (eulerPrimitiveBoundaryOddHodge
          eulerPrimitiveBoundaryPolarizedUnitSeed) =
      (eulerPrimitiveBoundaryHodgeBetaColumn a : ℂ) := by
  rw [eulerPrimitiveBoundaryPolarizedPairing]
  simp [eulerPrimitiveBoundaryOddHodge,
    eulerPrimitiveBoundaryPolarizedUnitSeed,
    eulerPrimitiveBoundaryPolarizedTest]
  have hfun :
      (fun t : ℝ =>
        (eulerPrimitiveBoundaryTailWeight t : ℂ) *
          Complex.exp (-((a : ℂ) * (t : ℂ))) *
            (-1 / (eulerPrimitiveBoundaryHodgeScale t : ℂ))) =
        fun t : ℝ =>
          ((eulerPrimitiveBoundaryTailWeight t * Real.exp (-a * t) *
            (-1 / eulerPrimitiveBoundaryHodgeScale t) : ℝ) : ℂ) := by
    funext t
    rw [show
      Complex.exp (-((a : ℂ) * (t : ℂ))) =
        (Real.exp (-a * t) : ℝ) by
      rw [show -((a : ℂ) * (t : ℂ)) =
          ((-a * t : ℝ) : ℂ) by
        push_cast
        ring,
        ← Complex.ofReal_exp]]
    push_cast
    rfl
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun t => congrFun hfun t),
    integral_complex_ofReal]
  rfl

/-- The common test sees the unit head source as the elementary rational
resolvent. -/
theorem eulerPrimitiveBoundaryPolarizedPairing_test_unitSeed
    {a : ℝ} (ha : -1 < a) :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest (a : ℂ))
        eulerPrimitiveBoundaryPolarizedUnitSeed =
      1 / (1 + a : ℂ) := by
  rw [eulerPrimitiveBoundaryPolarizedPairing]
  simp [eulerPrimitiveBoundaryPolarizedUnitSeed,
    eulerPrimitiveBoundaryPolarizedTest]
  have hden : 0 < ((1 + a : ℝ) : ℂ).re := by
    simp
    linarith
  have hrhs :
      (1 + (a : ℂ))⁻¹ = 1 / ((1 + a : ℝ) : ℂ) := by
    push_cast
    simp [div_eq_mul_inv]
  rw [hrhs]
  rw [← integral_cauchyFeaturePair hden]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  change
    (eulerPrimitiveBoundaryHeadWeight t : ℂ) *
        Complex.exp (-((a : ℂ) * (t : ℂ))) =
      Complex.exp (-((1 + a : ℝ) : ℂ) * (t : ℂ))
  rw [eulerPrimitiveBoundaryHeadWeight, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem negLog_image_Ioo :
    (fun x : ℝ => -Real.log x) '' Ioo 0 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact neg_pos.mpr (Real.log_neg hx.1 hx.2)
  · intro ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    refine ⟨Real.exp (-t), ?_, ?_⟩
    · exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
    · dsimp
      rw [Real.log_exp]
      ring

private theorem negLog_injOn :
    Set.InjOn (fun x : ℝ => -Real.log x) (Ioo 0 1) := by
  intro x hx y hy hxy
  apply Real.strictMonoOn_log.injOn hx.1 hy.1
  linarith

private theorem hodgeBeta_logJacobian
    (a : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |-(x⁻¹)| *
        (eulerPrimitiveBoundaryTailWeight (-Real.log x) *
          Real.exp (-a * (-Real.log x)) *
            (-1 /
              eulerPrimitiveBoundaryHodgeScale (-Real.log x))) =
      -(x ^ (a - 1 / 2) * (1 - x) ^ ((3 / 2 : ℝ) - 1)) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have hy : 0 < x⁻¹ - 1 := by
    rw [sub_pos, one_lt_inv₀ hx0]
    exact hx1
  have hsqrt : 0 < Real.sqrt (x⁻¹ - 1) :=
    Real.sqrt_pos.2 hy
  have htail :
      eulerPrimitiveBoundaryTailWeight (-Real.log x) = 1 - x := by
    rw [eulerPrimitiveBoundaryTailWeight]
    rw [show -(-Real.log x) = Real.log x by ring, Real.exp_log hx0]
  have hscale :
      eulerPrimitiveBoundaryHodgeScale (-Real.log x) =
        Real.sqrt (x⁻¹ - 1) := by
    rw [eulerPrimitiveBoundaryHodgeScale]
    congr 2
    rw [Real.exp_neg, Real.exp_log hx0]
  have hexp :
      Real.exp (-a * (-Real.log x)) = x ^ a := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [htail, hscale, hexp, abs_of_neg (by
    exact neg_neg_of_pos (inv_pos.mpr hx0))]
  rw [neg_neg]
  have hyEq : x⁻¹ - 1 = (1 - x) / x := by
    field_simp
  rw [hyEq, Real.sqrt_div h1x.le]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by ring]
  rw [Real.rpow_sub hx0]
  have hxhalf : x ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hx0 _).ne'
  have hxpow : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx0.le]
    norm_num
  have h1xpow : ((1 - x) ^ (1 / 2 : ℝ)) ^ 2 = 1 - x := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul h1x.le]
    norm_num
  field_simp
  rw [hxpow, h1xpow]
  ring

/--
**Hodge--Beta transgression.**  The odd-Hodge conjugate of the elementary
Euler head source is exactly a Beta/Gamma quotient.
-/
theorem eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    eulerPrimitiveBoundaryHodgeBetaColumn a =
      -(Real.Gamma (a + 1 / 2) * Real.Gamma (3 / 2) /
        Real.Gamma (a + 2)) := by
  let g : ℝ → ℝ := fun t =>
    eulerPrimitiveBoundaryTailWeight t * Real.exp (-a * t) *
      (-1 / eulerPrimitiveBoundaryHodgeScale t)
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioo
      (f := fun x : ℝ => -Real.log x)
      (f' := fun x : ℝ => -(x⁻¹))
      (fun x hx =>
        (Real.hasDerivAt_log hx.1.ne').neg.hasDerivWithinAt)
      negLog_injOn g
  rw [negLog_image_Ioo] at hchange
  have hcongr :
      (∫ x : ℝ in Ioo 0 1,
        |-(x⁻¹)| • g (-Real.log x)) =
        -(∫ x : ℝ in Ioo 0 1,
          x ^ ((a + 1 / 2) - 1) *
            (1 - x) ^ ((3 / 2 : ℝ) - 1)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change
      |-(x⁻¹)| * g (-Real.log x) =
        -(x ^ ((a + 1 / 2) - 1) *
          (1 - x) ^ ((3 / 2 : ℝ) - 1))
    rw [show (a + 1 / 2) - 1 = a - 1 / 2 by ring]
    exact hodgeBeta_logJacobian a hx
  rw [eulerPrimitiveBoundaryHodgeBetaColumn]
  change (∫ t : ℝ in Ioi 0, g t) = _
  rw [hchange, hcongr,
    HTGeometry.integral_rpow_mul_one_sub_rpow
      (show 0 < a + 1 / 2 by linarith)
      (show (0 : ℝ) < 3 / 2 by norm_num)]
  rw [show a + 1 / 2 + 3 / 2 = a + 2 by ring]

/--
**Polarized rational/Gamma source law.**  One common test applied to a
source and its forced odd-Hodge conjugate returns, respectively, the Euler
rational resolvent and its Gamma quotient.
-/
theorem eulerPrimitiveBoundaryPolarizedHodgeBetaTransgression
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    eulerPrimitiveBoundaryPolarizedPairing
          (eulerPrimitiveBoundaryPolarizedTest (a : ℂ))
          eulerPrimitiveBoundaryPolarizedUnitSeed =
        1 / (1 + a : ℂ) ∧
      eulerPrimitiveBoundaryPolarizedPairing
          (eulerPrimitiveBoundaryPolarizedTest (a : ℂ))
          (eulerPrimitiveBoundaryOddHodge
            eulerPrimitiveBoundaryPolarizedUnitSeed) =
        (-(Real.Gamma (a + 1 / 2) * Real.Gamma (3 / 2) /
          Real.Gamma (a + 2)) : ℝ) := by
  constructor
  · exact eulerPrimitiveBoundaryPolarizedPairing_test_unitSeed (by linarith)
  · rw [eulerPrimitiveBoundaryPolarizedPairing_test_oddHodge_unitSeed,
      eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio ha]

/--
The Hodge-generated Gamma column obeys the exact first-order coface law
forced by its Beta parameters.
-/
theorem eulerPrimitiveBoundaryHodgeBetaColumn_add_one
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    eulerPrimitiveBoundaryHodgeBetaColumn (a + 1) =
      ((a + 1 / 2) / (a + 2)) *
        eulerPrimitiveBoundaryHodgeBetaColumn a := by
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio
      (show -(1 / 2 : ℝ) < a + 1 by linarith),
    eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio ha]
  have haHalf : a + 1 / 2 ≠ 0 := by linarith
  have haTwo : a + 2 ≠ 0 := by linarith
  rw [show a + 1 + 1 / 2 = (a + 1 / 2) + 1 by ring,
    Real.Gamma_add_one haHalf,
    show a + 1 + 2 = (a + 2) + 1 by ring,
    Real.Gamma_add_one haTwo]
  have hGammaHalf :
      Real.Gamma (a + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGammaThreeHalf :
      Real.Gamma (3 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hGammaTwo :
      Real.Gamma (a + 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp

end

end RHTower
