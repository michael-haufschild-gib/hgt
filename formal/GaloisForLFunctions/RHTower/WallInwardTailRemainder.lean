import GaloisForLFunctions.RHTower.WallInwardRayReflection

/-!
# The tail on the inward frequency ray

Of the four terms of the propagated tail, the remainder is the only genuinely one-sided one: the
weighted Hardy inequality compares a moving average `x^{-p}∫_1^x` with its density, and that
comparison has a direction.  The amplitude it averages is even — it is controlled by `|t|` alone —
so on the inward ray the same estimate holds after reflecting the *integration variable*, which is
what `lintegral_neg_set_eq` does for the inner interval and `lintegral_sq_Iio_neg_eq` for the outer
one.

The threshold is taken strictly above one here.  That costs nothing (the block threshold is at least
`max(C₀,2)`) and it is what makes the reflected interval `[Y,-x)` sit inside the Hardy interval
`(1,-x]` without an appeal to the null set `{1}`.

The second boundary term needs only the evenness of its own majorant `(1+|x|)^{-1}`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **The propagated remainder is square integrable on the inward ray.** -/
theorem exists_bound_lintegral_sq_negRay_tailRemainder {σ μ₀ : ℝ}
    (hT : IsSelfAdjoint T) (hEbr : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m Y : ℝ, 1 < Y → ∀ g : ℝ → X, IntegrableOn g (Icc m (m + 1)) →
      (∀ t : ℝ, Y ≤ |t| → ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ t + L) →
      (∫⁻ x in Iio (-Y), ‖tailRemainder E T g m σ (-Y) x‖ₑ ^ 2)
        ≤ ENNReal.ofReal C * (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ) ^ 2 := by
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_stripPropagator_line hT hEbr hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hEbr hσ0 hσ1
  set p : ℝ := 1 / 2 + σ with hpdef
  have hp2 : 1 / 2 < p := by rw [hpdef]; linarith
  set Camp : ℝ := wallAmplitudeConst μ₀ with hCampdef
  have hCampnn : 0 ≤ Camp := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [hCampdef, wallAmplitudeConst]
    positivity
  set Mwtd : ℝ≥0∞ := ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (wallTailDensity p t) ^ 2 with hMdef
  have hMfin : Mwtd ≠ ⊤ := by
    rw [hMdef]
    exact (lintegral_sq_wallTailDensity_lt_top (by linarith)).ne
  refine ⟨K₁ ^ 2 * ((p - 1 / 2)⁻¹ ^ 2 * ((K₂ * Camp) ^ 2 * Mwtd.toReal)), by positivity,
    fun m Y hY g hg hfloor => ?_⟩
  set Ne : ℝ≥0∞ := ∫⁻ L in Icc m (m + 1), ‖g L‖ₑ with hNedef
  have hNefin : Ne ≠ ⊤ := by
    rw [hNedef]
    exact hg.2.ne
  set D : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (K₂ * Camp * wallTailDensity p t) with hDdef
  set H : ℝ → ℝ≥0∞ := fun t => Ne * D t with hHdef
  have hDmeas : Measurable D := by
    rw [hDdef]
    unfold wallTailDensity
    fun_prop
  have hHmeas : AEMeasurable H (volume.restrict (Ioi (1 : ℝ))) :=
    (hDmeas.const_mul Ne).aemeasurable
  -- the pointwise Hardy bound on the inward ray
  have hpt : ∀ x ∈ Iio (-Y), ‖tailRemainder E T g m σ (-Y) x‖ₑ
      ≤ ENNReal.ofReal (K₁ * (-x) ^ (-p))
        * ∫⁻ t in Ioc (1 : ℝ) (-x), ENNReal.ofReal (t ^ (p - 1)) * H t := by
    intro x hx
    have hxlt : x < -Y := mem_Iio.mp hx
    have hxY : x ≤ -Y := hxlt.le
    have hx1 : (1 : ℝ) < -x := by linarith
    have hx0 : (0 : ℝ) < -x := lt_trans zero_lt_one hx1
    have habsx : |x| = -x := abs_of_neg (by linarith)
    set J : ℝ≥0∞ := ∫⁻ t in Ioc (1 : ℝ) (-x), ENNReal.ofReal (t ^ (p - 1)) * D t with hJdef
    have hAe : ∀ L ∈ Icc m (m + 1),
        ‖∫ t in (-Y)..x, wallPhaseMap E T σ L t
          * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
              (wallGeneratorD2 X σ) t‖ₑ ≤ J := by
      intro L hL
      refine le_trans (enorm_intervalIntegral_le _ (-Y) x) ?_
      rw [uIoc_of_ge hxY]
      have hmono : (∫⁻ t in Ioc x (-Y), ‖wallPhaseMap E T σ L t
            * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) t‖ₑ)
          ≤ ∫⁻ t in Ioc x (-Y), ENNReal.ofReal ((-t) ^ (p - 1)) * D (-t) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        have htneg : t ≤ -Y := ht.2
        have hYt : Y ≤ -t := by linarith
        have ht0 : t < 0 := by linarith
        have habst : |t| = -t := abs_of_neg ht0
        have ht1 : (1 : ℝ) < |t| := by rw [habst]; linarith
        have hbase := norm_wallPhaseAmplitude_le (E := E) hσ0 hσ1 hμ hb₂ hK₂ ht1
          (hfloor t (by rw [habst]; exact hYt) L hL)
        rw [habst, ← hpdef, ← hCampdef] at hbase
        have htpos : (0 : ℝ) < -t := by linarith
        rw [← ofReal_norm, hDdef]
        refine le_trans (ENNReal.ofReal_le_ofReal hbase) (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg htpos.le _)]
      refine hmono.trans ?_
      rw [lintegral_neg_set_eq measurableSet_Ioc
        (fun t : ℝ => ENNReal.ofReal ((-t) ^ (p - 1)) * D (-t)), neg_Ioc, neg_neg]
      simp only [neg_neg]
      rw [hJdef]
      exact lintegral_mono_set (fun u hu => ⟨lt_of_lt_of_le hY hu.1, hu.2.le⟩)
    have hstep : ‖tailRemainder E T g m σ (-Y) x‖ₑ
        ≤ ∫⁻ L in Icc m (m + 1), ENNReal.ofReal (K₁ * (1 + -x) ^ (-p)) * (J * ‖g L‖ₑ) := by
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine setLIntegral_mono' measurableSet_Icc fun L hL => ?_
      have hprop : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
          ≤ K₁ * (1 + -x) ^ (-p) := by
        have hb := hb₁ x
        rwa [habsx] at hb
      have h1 : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            ((∫ t in (-Y)..x, wallPhaseMap E T σ L t
              * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                  (wallGeneratorD2 X σ) t) (g L))‖ₑ
          ≤ ENNReal.ofReal (K₁ * (1 + -x) ^ (-p))
            * ‖(∫ t in (-Y)..x, wallPhaseMap E T σ L t
                * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                    (wallGeneratorD2 X σ) t) (g L)‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right hprop (norm_nonneg _))
      have h2 : ‖(∫ t in (-Y)..x, wallPhaseMap E T σ L t
            * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) t) (g L)‖ₑ ≤ J * ‖g L‖ₑ := by
        refine le_trans ?_ (mul_le_mul' (hAe L hL) le_rfl)
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
      exact le_trans h1 (mul_le_mul' le_rfl h2)
    have hconst : (∫⁻ L in Icc m (m + 1),
        ENNReal.ofReal (K₁ * (1 + -x) ^ (-p)) * (J * ‖g L‖ₑ))
        = ENNReal.ofReal (K₁ * (1 + -x) ^ (-p)) * (J * Ne) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hNedef]
      congr 1
      exact lintegral_const_mul'' _ hg.1.enorm
    have hJH : J * Ne = ∫⁻ t in Ioc (1 : ℝ) (-x), ENNReal.ofReal (t ^ (p - 1)) * H t := by
      rw [hJdef, mul_comm, ← lintegral_const_mul' _ _ hNefin]
      refine lintegral_congr fun t => ?_
      rw [hHdef]
      ring
    have hxle : ENNReal.ofReal (K₁ * (1 + -x) ^ (-p)) ≤ ENNReal.ofReal (K₁ * (-x) ^ (-p)) := by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hK₁.le)
      refine Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
    calc ‖tailRemainder E T g m σ (-Y) x‖ₑ
        ≤ ∫⁻ L in Icc m (m + 1),
            ENNReal.ofReal (K₁ * (1 + -x) ^ (-p)) * (J * ‖g L‖ₑ) := hstep
      _ = ENNReal.ofReal (K₁ * (1 + -x) ^ (-p)) * (J * Ne) := hconst
      _ = ENNReal.ofReal (K₁ * (1 + -x) ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) (-x), ENNReal.ofReal (t ^ (p - 1)) * H t := by rw [hJH]
      _ ≤ ENNReal.ofReal (K₁ * (-x) ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) (-x), ENNReal.ofReal (t ^ (p - 1)) * H t :=
          mul_le_mul' hxle le_rfl
  -- the Hardy transfer
  have hHsq : (∫⁻ t in Ioi (1 : ℝ), H t ^ 2)
      ≤ Ne ^ 2 * (ENNReal.ofReal ((K₂ * Camp) ^ 2) * Mwtd) := by
    have hDsq : (∫⁻ t in Ioi (1 : ℝ), D t ^ 2)
        ≤ ENNReal.ofReal ((K₂ * Camp) ^ 2)
          * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (wallTailDensity p t) ^ 2 := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hnn : 0 ≤ wallTailDensity p t := wallTailDensity_nonneg ht0
      rw [hDdef, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hnn,
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    have hNe2 : Ne ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hNefin
    have hrw : (∫⁻ t in Ioi (1 : ℝ), H t ^ 2) = Ne ^ 2 * ∫⁻ t in Ioi (1 : ℝ), D t ^ 2 := by
      rw [← lintegral_const_mul' _ _ hNe2]
      refine lintegral_congr fun t => ?_
      rw [hHdef, mul_pow]
    rw [hrw]
    exact mul_le_mul' le_rfl (hDsq.trans (le_of_eq (by rw [hMdef])))
  refine le_trans (lintegral_sq_negRay_le_of_hardyBound_scalar hp2 hY.le hK₁.le hpt hHmeas) ?_
  refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hHsq)) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hMfin]
  ring

section Reflected

variable {V : Type*} [NormedAddCommGroup V]

/-- **A power tail on the inward ray**, by reflection: the majorant `(1+|x|)^{-p}` is even. -/
theorem lintegral_sq_negRay_powerTail_le {f : ℝ → V} {C p Y : ℝ} (hp : 1 / 2 < p) (hY : 0 < Y)
    (hf : ∀ x ∈ Iio (-Y), ‖f x‖ ≤ C * (1 + |x|) ^ (-p)) :
    (∫⁻ x in Iio (-Y), ‖f x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (Y ^ (1 - 2 * p) / (2 * p - 1)) := by
  rw [lintegral_sq_Iio_neg_eq]
  refine lintegral_sq_ray_powerTail_le (f := fun x : ℝ => f (-x)) hp hY (fun x hx => ?_)
  have hxneg : -x ∈ Iio (-Y) := by
    simp only [mem_Iio]
    have := mem_Ioi.mp hx
    linarith
  have h := hf (-x) hxneg
  rwa [abs_neg] at h

end Reflected

omit [Nontrivial X] in
/-- **The propagated second boundary term is square integrable on the inward ray.** -/
theorem lintegral_sq_negRay_secondBoundary_le {σ m μ₀ Y : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) (hY : 1 ≤ Y)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1)))
    (hfloor : ∀ x ∈ Iio (-Y), ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L) :
    (∫⁻ x in Iio (-Y), ‖secondBoundary T g m σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal
          ((((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * ∫ L in Icc m (m + 1), ‖g L‖) ^ 2) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  refine (lintegral_sq_negRay_powerTail_le (f := secondBoundary T g m σ)
    (C := ((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * ∫ L in Icc m (m + 1), ‖g L‖) (p := 1) (Y := Y)
    (by norm_num) hY0 (fun x hx => ?_)).trans ?_
  · refine norm_secondBoundary_le hσ0 hσ1 hμ hg ?_ (hfloor x hx)
    have hxlt : x < -Y := mem_Iio.mp hx
    rw [abs_of_neg (by linarith)]
    linarith
  · calc ENNReal.ofReal
          ((((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * ∫ L in Icc m (m + 1), ‖g L‖) ^ 2)
          * ENNReal.ofReal (Y ^ (1 - 2 * (1 : ℝ)) / (2 * (1 : ℝ) - 1))
        ≤ ENNReal.ofReal
            ((((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * ∫ L in Icc m (m + 1), ‖g L‖) ^ 2) * 1 :=
          mul_le_mul' le_rfl (ofReal_powerTail_one_le hY)
      _ = ENNReal.ofReal
            ((((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * ∫ L in Icc m (m + 1), ‖g L‖) ^ 2) := mul_one _

end GaloisForLFunctions.RHTower
