import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.HTGeometry.OrbitInductionEssentialization
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# The literal reciprocal time--band calibration

**Theorem 9.2** of the orbit-induction law, on the concrete carrier `L²(ℝ)`.

* `timeBand` `(OI.26)` is `C_{a,b} = Q_b P_a`, the Fourier cutoff of aperture `b` after the
  physical cutoff of aperture `a`;
* `isCompactOperator_timeBand` and `timeBand_ne_zero` — item (1): it is compact and nonzero, the
  latter because the aperture indicator has a continuous Fourier transform of value `2a` at the
  origin;
* `timeBand_mul_dilationCLM` `(OI.27)` — item (2): dilation transports it by reciprocal scaling
  of the two apertures;
* `timeBand_aperture_product` and `timeBand_rapidity_shift` — item (3): the aperture product is
  invariant and the rapidity is shifted by `log r`;
* `fourierUnitary_timeBand_conj` and `adjoint_timeBand` — item (4): Fourier conjugation exchanges
  the two apertures and produces the adjoint of the exchanged operator;
* `orbitBlock_timeBand` `(OI.28)` and `rectEssentialNorm_allRapidity` `(OI.29)` — item (5): the
  all-rapidity formation over the dilation orbit `{r^n}_{n ∈ ℤ}` has essential norm exactly
  `‖C_{a,b}‖ > 0`, so the time--band residual admits no global compact repair at any rapidity.
-/

namespace RHTower

open MeasureTheory FourierTransform GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

/-- `(OI.26)`  The time--band operator `C_{a,b} = Q_b P_a`. -/
def timeBand (a b : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  fourierCutoff (centralInterval b) (measurableSet_centralInterval b) *
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)

@[simp] theorem timeBand_apply (a b : ℝ) (f : SoninL2) :
    timeBand a b f = fourierCutoff (centralInterval b) (measurableSet_centralInterval b)
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) := rfl

/-- **Theorem 9.2 (2), `(OI.27)`.**  Dilation transports the time--band operator by reciprocal
scaling of the two apertures. -/
theorem timeBand_mul_dilationCLM (a b r : ℝ) (hr : 0 < r) :
    timeBand a b * dilationCLM r hr = dilationCLM r hr * timeBand (r * a) (r⁻¹ * b) := by
  rw [timeBand, timeBand, mul_assoc, indicatorCutoff_mul_dilationCLM, ← mul_assoc,
    fourierCutoff_mul_dilationCLM, mul_assoc]

/-- **Theorem 9.2 (3).**  The aperture product is a dilation invariant. -/
theorem timeBand_aperture_product (a b r : ℝ) (hr : r ≠ 0) : (r * a) * (r⁻¹ * b) = a * b := by
  field_simp

/-- **Theorem 9.2 (3).**  The rapidity is shifted by `-log r`. -/
theorem timeBand_rapidity_shift (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (1 / 2 : ℝ) * Real.log ((r⁻¹ * b) / (r * a))
      = (1 / 2 : ℝ) * Real.log (b / a) - Real.log r := by
  have hlog : Real.log ((r⁻¹ * b) / (r * a)) = Real.log (b / a) - 2 * Real.log r := by
    rw [show (r⁻¹ * b) / (r * a) = (b / a) * (r ^ 2)⁻¹ by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow]
    ring
  rw [hlog]
  ring

/-- **Theorem 9.2 (1).**  The time--band operator is compact. -/
theorem isCompactOperator_timeBand (a b : ℝ) (hb : 0 < b) :
    IsCompactOperator (timeBand a b) :=
  isCompactOperator_fourierCutoff_indicatorCutoff_central b a hb

/-! ## The time--band operator is nonzero -/

theorem volume_centralInterval_ne_top (a : ℝ) : (volume (centralInterval a)) ≠ ∞ := by
  rw [centralInterval, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The physical probe: the indicator of the aperture `[-a,a]`. -/
def bandProbe (a : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_centralInterval a) (volume_centralInterval_ne_top a) (1 : ℂ)

theorem bandProbe_ae (a : ℝ) :
    ((bandProbe a : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] (centralInterval a).indicator fun _ => (1 : ℂ) :=
  indicatorConstLp_coeFn

theorem indicatorCutoff_bandProbe (a : ℝ) :
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) (bandProbe a)
      = bandProbe a := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
    (bandProbe a), bandProbe_ae a] with x k1 k2
  rw [k1]
  by_cases hx : x ∈ centralInterval a
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, k2, Set.indicator_of_notMem hx]

theorem integrable_bandProbe (a : ℝ) : Integrable ((bandProbe a : SoninL2) : ℝ → ℂ) := by
  refine Integrable.congr ?_ (bandProbe_ae a).symm
  rw [integrable_indicator_iff (measurableSet_centralInterval a)]
  exact integrableOn_const (volume_centralInterval_ne_top a)

theorem fourierIntegral_bandProbe_zero (a : ℝ) (ha : 0 < a) :
    𝓕 ((bandProbe a : SoninL2) : ℝ → ℂ) 0 = ((2 * a : ℝ) : ℂ) := by
  have hint : ∫ x : ℝ, ((bandProbe a : SoninL2) : ℝ → ℂ) x = ((2 * a : ℝ) : ℂ) := by
    rw [integral_congr_ae (bandProbe_ae a),
      integral_indicator (measurableSet_centralInterval a), setIntegral_const,
      centralInterval, Real.volume_real_Icc,
      max_eq_left (by linarith : (0:ℝ) ≤ a - -a), Complex.real_smul, mul_one]
    push_cast
    ring
  simpa [Real.fourier_eq] using hint

theorem continuous_fourierIntegral_bandProbe (a : ℝ) :
    Continuous (𝓕 ((bandProbe a : SoninL2) : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (integrable_bandProbe a)

/-- **Theorem 9.2 (1).**  The time--band operator is nonzero: the aperture indicator has a
continuous transform that does not vanish at the origin. -/
theorem timeBand_ne_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : timeBand a b ≠ 0 := by
  intro hzero
  set g : ℝ → ℂ := 𝓕 ((bandProbe a : SoninL2) : ℝ → ℂ) with hg
  have hprobe : fourierCutoff (centralInterval b) (measurableSet_centralInterval b)
      (bandProbe a) = 0 := by
    have h := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T (bandProbe a)) hzero
    simpa [timeBand_apply, indicatorCutoff_bandProbe] using h
  have hP : indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
      (fourierUnitary (bandProbe a)) = 0 := by
    have h := congrArg fourierUnitary hprobe
    rwa [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply, map_zero] at h
  have hae : ∀ᵐ x ∂volume, x ∈ centralInterval b → g x = 0 := by
    have h1 := indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b)
      (fourierUnitary (bandProbe a))
    have h2 : ((fourierUnitary (bandProbe a) : SoninL2) : ℝ → ℂ) =ᵐ[volume] g :=
      coeFn_fourierTransform_eq_fourierIntegral _ (integrable_bandProbe a)
    have h3 : ((indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
        (fourierUnitary (bandProbe a)) : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [hP]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
    filter_upwards [h1, h2, h3] with x k1 k2 k3 hx
    have hk : (centralInterval b).indicator
        (fun y => ((fourierUnitary (bandProbe a) : SoninL2) : ℝ → ℂ) y) x = 0 := by
      rw [← k1]; exact k3
    rw [Set.indicator_of_mem hx] at hk
    rw [← k2]
    exact hk
  have hne0 : g 0 ≠ 0 := by
    rw [hg, fourierIntegral_bandProbe_zero a ha]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h
    linarith
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball (0 : ℝ) ε ⊆ {x : ℝ | g x ≠ 0} := by
    have hopen : IsOpen {x : ℝ | g x ≠ 0} :=
      (continuous_fourierIntegral_bandProbe a).isOpen_preimage {(0 : ℂ)}ᶜ
        isOpen_compl_singleton
    exact Metric.isOpen_iff.mp hopen 0 hne0
  set δ : ℝ := min ε b with hδ
  have hδpos : 0 < δ := lt_min hε hb
  have hsub : Set.Ioo (-δ) δ ⊆ {x : ℝ | g x ≠ 0} := by
    intro x hx
    refine hball ?_
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε b)) hx.1,
      lt_of_lt_of_le hx.2 (min_le_left ε b)⟩
  have hSb : Set.Ioo (-δ) δ ⊆ centralInterval b := by
    intro x hx
    exact ⟨le_of_lt (lt_of_le_of_lt (neg_le_neg (min_le_right ε b)) hx.1),
      le_of_lt (lt_of_lt_of_le hx.2 (min_le_right ε b))⟩
  have hnull : volume (Set.Ioo (-δ) δ) = 0 := by
    have hmem : ∀ᵐ x ∂volume, x ∉ Set.Ioo (-δ) δ := by
      filter_upwards [hae] with x hx hxmem
      exact hsub hxmem (hx (hSb hxmem))
    rw [ae_iff] at hmem
    have hset : {x : ℝ | ¬ (x ∉ Set.Ioo (-δ) δ)} = Set.Ioo (-δ) δ := by
      ext x
      simp
    rwa [hset] at hmem
  rw [Real.volume_Ioo] at hnull
  rw [ENNReal.ofReal_eq_zero] at hnull
  linarith

/-! ## Fourier exchange of the two apertures -/

theorem fourierUnitary_indicatorCutoff_symm (a : ℝ) (f : SoninL2) :
    fourierUnitary (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (fourierUnitary.symm f))
      = fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f := by
  rw [fourierUnitary_symm_eq_reflection_fourier, ← l2Reflection_indicatorCutoff_central,
    fourierUnitary_l2Reflection, fourierCutoff_apply,
    fourierUnitary_symm_eq_reflection_fourier]

/-- **Theorem 9.2 (4).**  Fourier conjugation exchanges the physical and frequency apertures. -/
theorem fourierUnitary_timeBand_conj (a b : ℝ) (f : SoninL2) :
    fourierUnitary (timeBand a b (fourierUnitary.symm f))
      = indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
          (fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f) := by
  rw [timeBand_apply, fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply,
    fourierUnitary_indicatorCutoff_symm]

/-- **Theorem 9.2 (4).**  The Fourier conjugate of `C_{a,b}` is the adjoint of `C_{b,a}`. -/
theorem adjoint_timeBand (a b : ℝ) :
    ContinuousLinearMap.adjoint (timeBand b a)
      = indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) *
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a) := by
  have hP : ContinuousLinearMap.adjoint
      (indicatorCutoff (centralInterval b) (measurableSet_centralInterval b))
      = indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) :=
    (indicatorCutoff_isStarProjection (centralInterval b)
      (measurableSet_centralInterval b)).isSelfAdjoint
  have hQ : ContinuousLinearMap.adjoint
      (fourierCutoff (centralInterval a) (measurableSet_centralInterval a))
      = fourierCutoff (centralInterval a) (measurableSet_centralInterval a) :=
    (fourierCutoff_isStarProjection (centralInterval a)
      (measurableSet_centralInterval a)).isSelfAdjoint
  rw [timeBand]
  rw [show ContinuousLinearMap.adjoint
      (fourierCutoff (centralInterval a) (measurableSet_centralInterval a) *
        indicatorCutoff (centralInterval b) (measurableSet_centralInterval b))
      = ContinuousLinearMap.adjoint
          (indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)) *
        ContinuousLinearMap.adjoint
          (fourierCutoff (centralInterval a) (measurableSet_centralInterval a)) from
    star_mul _ _]
  rw [hP, hQ]

/-! ## The all-rapidity formation -/

/-- The rapidity orbit: dilations by the integer powers of `r`. -/
def rapidityOrbit (r : ℝ) (hr : 0 < r) (n : ℤ) : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  dilationUnitary (r ^ n) (zpow_pos hr n)

/-- `(OI.28)`  Every block of the all-rapidity formation is a reciprocally scaled time--band
operator. -/
theorem orbitBlock_timeBand (a b r : ℝ) (hr : 0 < r) (n : ℤ) (f : SoninL2) :
    orbitBlock (timeBand a b) (rapidityOrbit r hr) (rapidityOrbit r hr) n f
      = timeBand ((r ^ n)⁻¹ * a) (r ^ n * b) f := by
  have hpos : (0 : ℝ) < r ^ n := zpow_pos hr n
  have hinv : (0 : ℝ) < (r ^ n)⁻¹ := inv_pos.mpr hpos
  have hstep := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f)
    (timeBand_mul_dilationCLM a b (r ^ n)⁻¹ hinv)
  simp only [mul_apply_eq_comp, dilationCLM_apply, inv_inv] at hstep
  show (rapidityOrbit r hr n) (timeBand a b ((rapidityOrbit r hr n).symm f)) = _
  rw [rapidityOrbit, dilationUnitary_symm_apply, dilationUnitary_apply, hstep,
    dilation_dilation_inv]

/-- **Theorem 9.2 (5), `(OI.29)`.**  The all-rapidity formation of the time--band operator has
essential norm exactly the local norm, which is strictly positive. -/
theorem rectEssentialNorm_allRapidity (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    rectEssentialNorm
        (orbitInduction (timeBand a b) (rapidityOrbit r hr) (rapidityOrbit r hr))
        = ‖timeBand a b‖
      ∧ 0 < ‖timeBand a b‖ := by
  refine ⟨rectEssentialNorm_orbitInduction _ _ _, ?_⟩
  exact norm_pos_iff.mpr (timeBand_ne_zero a b ha hb)

end

end RHTower
