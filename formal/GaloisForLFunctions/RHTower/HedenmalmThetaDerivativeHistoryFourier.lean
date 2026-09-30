import GaloisForLFunctions.RHTower.HedenmalmShiftedSourceEquation
import GaloisForLFunctions.RHTower.HedenmalmThetaDerivativeHistoryQuotient

/-!
# Literal left Fourier functionals on actual theta derivative history

The actual weighted theta conormal defines a bounded Fourier functional for
every complex parameter. Its literal source-space integral, exact mass test,
and centered-primitive action identify the paper's left eigenfunctional.
At an actual Xi zero it annihilates every derivative generator and their
closed history, then descends to the literal Hilbert quotient.
-/

open MeasureTheory Set Filter Topology Complex Module

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmHilbertSchmidt
  HedenmalmClosedWeightedDerivative HedenmalmFredholmRange

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev HS := SourceSpace thetaSource
private abbrev RH := thetaQuantileDerivativeHistory

/-- The actual bounded Fourier functional in quantile coordinates. -/
def thetaHistoryFourierFunctional (z : ℂ) : H →L[ℂ] ℂ := thetaCokernelFunctional z

/-- The same bounded functional on the literal weighted source space. -/
def thetaSourceFourierFunctional (z : ℂ) : HS →L[ℂ] ℂ :=
  (thetaHistoryFourierFunctional z).comp
    (quantileUnitary thetaSource).toContinuousLinearEquiv.toContinuousLinearMap

theorem thetaHistoryFourierFunctional_quantileUnitary (z : ℂ) (f : HS) :
    thetaHistoryFourierFunctional z (quantileUnitary thetaSource f) =
      ∫ x : ℝ, f x * sourceChar z x := by
  change inner ℂ (thetaCokernelVector z) (quantileUnitary thetaSource f) = _
  rw [thetaCokernelVector, (quantileUnitary thetaSource).inner_map_map]
  rw [inner_sourceSpace_eq_integral_div (thetaCokernelSourceVector_ae z)
    (Eventually.of_forall fun _ => rfl)]
  apply integral_congr_ae
  filter_upwards with x
  calc
    (starRingEnd ℂ) (cokernelVector thetaSource z x) * f x / (thetaSource.k x : ℂ) =
        ((starRingEnd ℂ) (cokernelVector thetaSource z x) / (thetaSource.k x : ℂ)) * f x := by
      ring
    _ = sourceChar z x * f x := by rw [conj_cokernelVector_div]
    _ = f x * sourceChar z x := mul_comm _ _

theorem thetaSourceFourierFunctional_apply (z : ℂ) (f : HS) :
    thetaSourceFourierFunctional z f = ∫ x : ℝ, f x * sourceChar z x :=
  thetaHistoryFourierFunctional_quantileUnitary z f

theorem integrable_thetaSourceFourierIntegrand (z : ℂ) (f : HS) :
    Integrable (fun x : ℝ => f x * Complex.exp (Complex.I * z * (x : ℂ))) :=
  integrable_sourceSpace_mul_sourceChar f z

theorem thetaSourceFourierFunctional_eq_literal_integral (z : ℂ) (f : HS) :
    thetaSourceFourierFunctional z f =
      ∫ x : ℝ, f x * Complex.exp (Complex.I * z * (x : ℂ)) :=
  thetaSourceFourierFunctional_apply z f

theorem norm_thetaSourceFourierIntegral_le (z : ℂ) (f : HS) :
    ‖∫ x : ℝ, f x * Complex.exp (Complex.I * z * (x : ℂ))‖ ≤
      ‖thetaSourceFourierFunctional z‖ * ‖f‖ := by
  rw [← thetaSourceFourierFunctional_eq_literal_integral]
  exact (thetaSourceFourierFunctional z).le_opNorm f

/-- The admitted source test `k(x) exp(-izx)` for every complex parameter. -/
def thetaFourierTestSource (z : ℂ) : HS := thetaCokernelSourceVector ((starRingEnd ℂ) z)

theorem thetaFourierTestSource_coe (z : ℂ) :
    (thetaFourierTestSource z : ℝ → ℂ) =ᵐ[volume]
      fun x => (thetaSource.k x : ℂ) * Complex.exp (-(Complex.I * z * (x : ℂ))) := by
  have h := (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mp (thetaCokernelSourceVector_ae ((starRingEnd ℂ) z))
  filter_upwards [h] with x hx
  change thetaCokernelSourceVector ((starRingEnd ℂ) z) x = _
  rw [hx]
  change (thetaSource.k x : ℂ) * Complex.exp (-(Complex.I * star (star z)) * (x : ℂ)) = _
  rw [star_star]
  congr 1
  congr 1
  ring

/-- Its literal Fourier integral is exactly the positive total source mass. -/
theorem thetaSourceFourierFunctional_test (z : ℂ) :
    thetaSourceFourierFunctional z (thetaFourierTestSource z) = (thetaSource.mass : ℂ) := by
  rw [thetaSourceFourierFunctional_apply]
  calc
    (∫ x : ℝ, thetaFourierTestSource z x * sourceChar z x) =
        ∫ x : ℝ, (thetaSource.k x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [thetaFourierTestSource_coe z] with x hx
      rw [hx, sourceChar, mul_assoc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, mul_one]
    _ = (thetaSource.mass : ℂ) := by rw [integral_complex_ofReal]; rfl

theorem thetaSourceFourierFunctional_ne_zero (z : ℂ) : thetaSourceFourierFunctional z ≠ 0 := by
  intro hzero
  have h := thetaSourceFourierFunctional_test z
  rw [hzero] at h
  change (0 : ℂ) = (thetaSource.mass : ℂ) at h
  exact (by exact_mod_cast thetaSource.mass_ne_zero : (thetaSource.mass : ℂ) ≠ 0) h.symm

theorem thetaHistoryFourierFunctional_surjective (z : ℂ) :
    Function.Surjective (thetaHistoryFourierFunctional z) := thetaCokernelFunctional_surjective z

theorem thetaHistoryFourierFunctional_derivative_zero (z : ℂ) :
    thetaHistoryFourierFunctional z (thetaQuantileDerivativeVector 0) = XiC z := by
  rw [thetaQuantileDerivativeVector, thetaHistoryFourierFunctional_quantileUnitary]
  calc
    (∫ x : ℝ, thetaSourceDerivativeVector 0 x * sourceChar z x) = xiC thetaSource z := by
      apply integral_congr_ae
      filter_upwards [thetaSourceDerivativeVector_coe 0] with x hx
      rw [hx]
      simp only [thetaSourceDerivativeFunction, iteratedDeriv_zero, thetaSource_k]
    _ = XiC z := xiC_thetaSource_all z

/-- Exact left action on the complete centered Hilbert hyperplane. -/
theorem thetaHistoryFourierFunctional_centered_inverse (z : ℂ) (f : thetaCentered) :
    thetaHistoryFourierFunctional z f +
      z * thetaHistoryFourierFunctional z (thetaCompactSourceInverse f) = 0 := by
  have hmem : thetaShiftedRangeMap z f ∈ (thetaCokernelFunctional z).ker := by
    rw [← thetaShiftedRangeMap_range_eq_ker_cokernelFunctional]
    exact ⟨f, rfl⟩
  change thetaHistoryFourierFunctional z ((f : H) + z • thetaCompactSourceInverse f) = 0 at hmem
  rwa [map_add, map_smul, smul_eq_mul] at hmem

/-- The exact mass correction for arbitrary full-space inputs and every complex parameter. -/
theorem thetaHistoryFourierFunctional_inverse (z : ℂ) (f : H) :
    thetaHistoryFourierFunctional z f +
      z * thetaHistoryFourierFunctional z (thetaCompactSourceInverse f) =
        (pinnedMean f / (Real.sqrt thetaSource.mass : ℂ)) * XiC z := by
  have hM : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  let m : ℂ := pinnedMean f / (Real.sqrt thetaSource.mass : ℂ)
  let f0 : thetaCentered := ⟨f - m • thetaQuantileDerivativeVector 0, by
    rw [mem_thetaCentered_iff]
    calc
      pinnedMean (f - m • thetaQuantileDerivativeVector 0) =
          thetaPinnedMeanCLM (f - m • thetaQuantileDerivativeVector 0) :=
        (thetaPinnedMeanCLM_apply _).symm
      _ = 0 := by
        rw [map_sub, map_smul, thetaPinnedMeanCLM_apply,
          thetaPinnedMeanCLM_apply, thetaQuantileDerivativeVector_zero,
          pinnedMean_smul, pinnedMean_pinnedOne]
        simp [m, smul_eq_mul, hM]⟩
  have hB : thetaCompactSourceInverse f0 = thetaCompactSourceInverse f := by
    change thetaCompactSourceInverse (f - m • thetaQuantileDerivativeVector 0) = _
    rw [map_sub, map_smul, thetaCompactSourceInverse_thetaQuantileDerivativeVector_zero,
      smul_zero, sub_zero]
  have h := thetaHistoryFourierFunctional_centered_inverse z f0
  rw [hB] at h
  change thetaHistoryFourierFunctional z (f - m • thetaQuantileDerivativeVector 0) + _ = 0 at h
  rw [map_sub, map_smul, smul_eq_mul, thetaHistoryFourierFunctional_derivative_zero] at h
  dsimp only [m] at h
  linear_combination h

/-- Literal source-coordinate version, with the paper's exact total-mass correction. -/
theorem thetaSourceFourierFunctional_inverse (z : ℂ) (f : HS) :
    thetaSourceFourierFunctional z f +
      z * thetaHistoryFourierFunctional z
        (thetaCompactSourceInverse (quantileUnitary thetaSource f)) =
      ((∫ x : ℝ, f x) / (thetaSource.mass : ℂ)) * XiC z := by
  have hsquare : (Real.sqrt thetaSource.mass : ℂ) ^ 2 = (thetaSource.mass : ℂ) := by
    exact_mod_cast Real.sq_sqrt thetaSource.mass_pos.le
  change thetaHistoryFourierFunctional z (quantileUnitary thetaSource f) + _ = _
  rw [thetaHistoryFourierFunctional_inverse, pinnedMean_quantileUnitary,
    integral_quantileTransform thetaSource (integrable_sourceSpace thetaSource f).aestronglyMeasurable]
  congr 1
  rw [div_div, ← pow_two, hsquare]

private theorem thetaSourceInverse_ae_inverseRepresentative (f : HS) :
    sourceInverse thetaSource (fun x => f x) =ᵐ[volume]
      fun x => ((quantileUnitary thetaSource).symm
        (thetaCompactSourceInverse (quantileUnitary thetaSource f))) x := by
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    sourceInverse_ae_eq_quantileSymm_thetaCompactSourceInverse
      (quantileUnitary thetaSource f)

/-- Every literal centered primitive admits every complex Fourier tilt. -/
theorem integrable_thetaSourceInverseFourierIntegrand (z : ℂ) (f : HS) :
    Integrable (fun x : ℝ => sourceInverse thetaSource (fun y => f y) x *
      Complex.exp (Complex.I * z * (x : ℂ))) := by
  apply (integrable_sourceSpace_mul_sourceChar
    ((quantileUnitary thetaSource).symm
      (thetaCompactSourceInverse (quantileUnitary thetaSource f))) z).congr
  filter_upwards [thetaSourceInverse_ae_inverseRepresentative f] with x hx
  rw [hx]
  rfl

theorem thetaHistoryFourierFunctional_inverse_eq_literal_integral (z : ℂ) (f : HS) :
    thetaHistoryFourierFunctional z
        (thetaCompactSourceInverse (quantileUnitary thetaSource f)) =
      ∫ x : ℝ, sourceInverse thetaSource (fun y => f y) x *
        Complex.exp (Complex.I * z * (x : ℂ)) := by
  have h := thetaHistoryFourierFunctional_quantileUnitary z
    ((quantileUnitary thetaSource).symm
      (thetaCompactSourceInverse (quantileUnitary thetaSource f)))
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  apply h.trans
  apply integral_congr_ae
  filter_upwards [thetaSourceInverse_ae_inverseRepresentative f] with x hx
  rw [hx]
  rfl

/-- The paper's centered-primitive identity as literal physical integrals, for all `z`. -/
theorem thetaSourceFourierIntegral_inverse (z : ℂ) (f : HS) :
    (∫ x : ℝ, f x * Complex.exp (Complex.I * z * (x : ℂ))) +
      z * (∫ x : ℝ, sourceInverse thetaSource (fun y => f y) x *
        Complex.exp (Complex.I * z * (x : ℂ))) =
      ((∫ x : ℝ, f x) / (thetaSource.mass : ℂ)) * XiC z := by
  rw [← thetaSourceFourierFunctional_eq_literal_integral,
    ← thetaHistoryFourierFunctional_inverse_eq_literal_integral]
  exact thetaSourceFourierFunctional_inverse z f

/-- The exact reciprocal form, with only the paper's necessary `z ≠ 0` condition. -/
theorem thetaSourceFourierIntegral_inverse_reciprocal {z : ℂ} (hz : z ≠ 0) (f : HS) :
    (∫ x : ℝ, sourceInverse thetaSource (fun y => f y) x *
      Complex.exp (Complex.I * z * (x : ℂ))) =
      -z⁻¹ * ((∫ x : ℝ, f x * Complex.exp (Complex.I * z * (x : ℂ))) -
        ((∫ x : ℝ, f x) / (thetaSource.mass : ℂ)) * XiC z) := by
  have h := thetaSourceFourierIntegral_inverse z f
  calc
    (∫ x : ℝ, sourceInverse thetaSource (fun y => f y) x *
        Complex.exp (Complex.I * z * (x : ℂ))) =
        z⁻¹ * (z * (∫ x : ℝ, sourceInverse thetaSource (fun y => f y) x *
          Complex.exp (Complex.I * z * (x : ℂ)))) := by field_simp [hz]
    _ = _ := by linear_combination z⁻¹ * h

theorem thetaHistoryFourierFunctional_derivative_succ (z : ℂ) (n : ℕ) :
    thetaHistoryFourierFunctional z (thetaQuantileDerivativeVector (n + 1)) =
      (-Complex.I * z) * thetaHistoryFourierFunctional z (thetaQuantileDerivativeVector n) := by
  have h := thetaHistoryFourierFunctional_centered_inverse z
    ⟨thetaQuantileDerivativeVector (n + 1), thetaQuantileDerivativeVector_succ_mem_centered n⟩
  change thetaHistoryFourierFunctional z (thetaQuantileDerivativeVector (n + 1)) +
    z * thetaHistoryFourierFunctional z
      (thetaCompactSourceInverse (thetaQuantileDerivativeVector (n + 1))) = 0 at h
  rw [thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ,
    map_smul, smul_eq_mul] at h
  linear_combination h

/-- Exact integration-by-parts transform for every actual ordinary derivative. -/
theorem thetaHistoryFourierFunctional_derivative (z : ℂ) (n : ℕ) :
    thetaHistoryFourierFunctional z (thetaQuantileDerivativeVector n) =
      (-Complex.I * z) ^ n * XiC z := by
  induction n with
  | zero => simpa using thetaHistoryFourierFunctional_derivative_zero z
  | succ n ih =>
    rw [thetaHistoryFourierFunctional_derivative_succ, ih, pow_succ]
    ring

/-- All ordinary source derivatives admit every complex Fourier tilt. -/
theorem integrable_thetaSourceDerivativeFourierIntegrand (z : ℂ) (n : ℕ) :
    Integrable (fun x : ℝ => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) *
      Complex.exp (Complex.I * z * (x : ℂ))) := by
  apply (integrable_sourceSpace_mul_sourceChar (thetaSourceDerivativeVector n) z).congr
  filter_upwards [thetaSourceDerivativeVector_coe n] with x hx
  rw [hx]
  rfl

/-- Exact physical integration-by-parts transform, without a strip restriction. -/
theorem thetaSourceDerivativeFourierIntegral (z : ℂ) (n : ℕ) :
    (∫ x : ℝ, ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) *
      Complex.exp (Complex.I * z * (x : ℂ))) = (-Complex.I * z) ^ n * XiC z := by
  rw [← thetaHistoryFourierFunctional_derivative]
  rw [thetaQuantileDerivativeVector, thetaHistoryFourierFunctional_quantileUnitary]
  apply integral_congr_ae
  filter_upwards [thetaSourceDerivativeVector_coe n] with x hx
  rw [hx]
  rfl

/-- The functional annihilates the entire closed derivative history at every actual Xi zero. -/
theorem thetaQuantileDerivativeHistory_le_ker_thetaHistoryFourierFunctional
    {z : ℂ} (hz : XiC z = 0) :
    thetaQuantileDerivativeHistory ≤ (thetaHistoryFourierFunctional z).ker := by
  apply (Submodule.span ℂ (range thetaQuantileDerivativeVector)).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (thetaHistoryFourierFunctional z).isClosed_ker
  rintro _ ⟨n, rfl⟩
  change thetaHistoryFourierFunctional z (thetaQuantileDerivativeVector n) = 0
  rw [thetaHistoryFourierFunctional_derivative, hz, mul_zero]

theorem thetaHistoryFourierFunctional_history {z : ℂ} (hz : XiC z = 0) {f : H}
    (hf : f ∈ thetaQuantileDerivativeHistory) : thetaHistoryFourierFunctional z f = 0 :=
  thetaQuantileDerivativeHistory_le_ker_thetaHistoryFourierFunctional hz hf

theorem thetaHistoryFourierFunctional_left_eigen {z : ℂ} (hz : XiC z = 0) (f : H) :
    thetaHistoryFourierFunctional z (thetaCompactSourceInverse f) =
      -z⁻¹ * thetaHistoryFourierFunctional z f := by
  have hz0 : z ≠ 0 := fun hzero => XiC_zero_ne (hzero ▸ hz)
  have h := thetaHistoryFourierFunctional_inverse z f
  rw [hz, mul_zero] at h
  calc
    thetaHistoryFourierFunctional z (thetaCompactSourceInverse f) =
        z⁻¹ * (z * thetaHistoryFourierFunctional z (thetaCompactSourceInverse f)) := by
      field_simp [hz0]
    _ = -z⁻¹ * thetaHistoryFourierFunctional z f := by
      linear_combination z⁻¹ * h

/-- The intrinsic parameter space contains precisely the actual completed Xi zeros. -/
abbrev ThetaFourierZero := {z : ℂ // XiC z = 0}

/-- The literal nonzero bounded left functional on the actual history quotient. -/
def thetaDerivativeHistoryFourierFunctional (z : ThetaFourierZero) :
    ThetaDerivativeHistoryQuotient →L[ℂ] ℂ :=
  RH.liftQL (thetaHistoryFourierFunctional z)
    (thetaQuantileDerivativeHistory_le_ker_thetaHistoryFourierFunctional z.property)

theorem thetaDerivativeHistoryFourierFunctional_projection (z : ThetaFourierZero) (f : H) :
    thetaDerivativeHistoryFourierFunctional z (thetaDerivativeHistoryQuotientProjection f) =
      thetaHistoryFourierFunctional z f := rfl

theorem thetaDerivativeHistoryFourierFunctional_source (z : ThetaFourierZero) (f : HS) :
    thetaDerivativeHistoryFourierFunctional z
      (thetaDerivativeHistoryQuotientProjection (quantileUnitary thetaSource f)) =
      ∫ x : ℝ, f x * Complex.exp (Complex.I * (z : ℂ) * (x : ℂ)) :=
  thetaHistoryFourierFunctional_quantileUnitary z f

theorem thetaDerivativeHistoryFourierFunctional_test (z : ThetaFourierZero) :
    thetaDerivativeHistoryFourierFunctional z
      (thetaDerivativeHistoryQuotientProjection
        (quantileUnitary thetaSource (thetaFourierTestSource z))) = (thetaSource.mass : ℂ) :=
  thetaSourceFourierFunctional_test z

theorem thetaDerivativeHistoryFourierFunctional_surjective (z : ThetaFourierZero) :
    Function.Surjective (thetaDerivativeHistoryFourierFunctional z) := by
  intro c
  obtain ⟨f, hf⟩ := thetaHistoryFourierFunctional_surjective z c
  exact ⟨thetaDerivativeHistoryQuotientProjection f, hf⟩

theorem thetaDerivativeHistoryFourierFunctional_ne_zero (z : ThetaFourierZero) :
    thetaDerivativeHistoryFourierFunctional z ≠ 0 := by
  intro hzero
  have h := thetaDerivativeHistoryFourierFunctional_test z
  rw [hzero] at h
  change (0 : ℂ) = (thetaSource.mass : ℂ) at h
  exact (by exact_mod_cast thetaSource.mass_ne_zero : (thetaSource.mass : ℂ) ≠ 0) h.symm

theorem thetaDerivativeHistoryFourierFunctional_left_eigen (z : ThetaFourierZero)
    (f : ThetaDerivativeHistoryQuotient) :
    thetaDerivativeHistoryFourierFunctional z (thetaDerivativeHistoryQuotientInverse f) =
      -(z : ℂ)⁻¹ * thetaDerivativeHistoryFourierFunctional z f := by
  obtain ⟨g, rfl⟩ := thetaQuantileDerivativeHistory.mkQ_surjective f
  change thetaDerivativeHistoryFourierFunctional z
    (thetaDerivativeHistoryQuotientInverse (thetaDerivativeHistoryQuotientProjection g)) = _
  rw [thetaDerivativeHistoryQuotientInverse_projection,
    thetaDerivativeHistoryFourierFunctional_projection]
  change thetaHistoryFourierFunctional z (thetaCompactSourceInverse g) =
    -(z : ℂ)⁻¹ * thetaHistoryFourierFunctional z g
  exact thetaHistoryFourierFunctional_left_eigen z.property g

end

end RHTower.HedenmalmThetaSource
