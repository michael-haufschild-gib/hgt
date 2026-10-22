import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSpectrumExact

/-!
# Nonzero monopole of every theta source-inverse eigenvector

The full compact source inverse has divisor eigenvectors, but none lies in the centered
hyperplane.  This is the analytic input making every translate of the closed derivative
injective.
-/

open Complex Function MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmPrimeTranslation

private abbrev H := Lp ℂ 2 unitIntervalMeasure

/-- Every eigenvector at a nonzero eigenvalue has nonzero quantile mean. In particular, the
centered restriction of the source inverse has no nonzero point spectrum. -/
theorem pinnedMean_ne_zero_of_thetaCompactSourceInverse_eigen
    {c : ℂ} (hc : c ≠ 0) {f : H} (hf0 : f ≠ 0)
    (hf : thetaCompactSourceInverse f = c • f) :
    pinnedMean f ≠ 0 := by
  intro hmean
  let v : SourceSpace thetaSource := (quantileUnitary thetaSource).symm f
  let u : ℝ → ℂ := sourceInverse thetaSource (fun x => v x)
  let z : ℂ := -c⁻¹
  have hvf : quantileUnitary thetaSource v = f := by
    simp [v]
  have hvint : Integrable (fun x => (v x : ℂ)) (volume : Measure ℝ) :=
    integrable_sourceSpace thetaSource v
  have hsource : u =ᵐ[(volume : Measure ℝ)] fun x => c * v x := by
    simpa only [u, v] using
      (sourceInverse_ae_eq_smul_of_thetaCompactSourceInverse_eigen hf)
  have hucont : Continuous u := continuous_sourceInverse_of_integrable hvint
  have huit : Integrable u (volume : Measure ℝ) := by
    refine (hvint.const_mul c).congr hsource.symm
  let g : ℝ → ℂ := fun x => c⁻¹ * u x
  have hgcont : Continuous g := continuous_const.mul hucont
  have hgv : g =ᵐ[(volume : Measure ℝ)] fun x => v x := by
    filter_upwards [hsource] with x hx
    dsimp only [g]
    rw [hx]
    field_simp [hc]
  have hgint : Integrable g (volume : Measure ℝ) := hvint.congr hgv.symm
  have hueq : u = sourceInverse thetaSource g := by
    funext x
    exact sourceInverse_congr_ae thetaSource hgv.symm x
  have hvIntegral : ∫ x, (v : SourceSpace thetaSource) x = 0 := by
    have hformula := pinnedMean_quantileUnitary thetaSource v
    rw [integral_quantileTransform thetaSource hvint.aestronglyMeasurable,
      hvf, hmean] at hformula
    have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
    exact (div_eq_zero_iff.mp hformula.symm).resolve_right hsqrt
  have hgIntegral : ∫ x, g x = 0 := by
    rw [integral_congr_ae hgv]
    exact hvIntegral
  let up : ℝ → ℂ := fun x => Complex.I * g x
  have huderiv : ∀ x : ℝ, HasDerivAt u (up x) x := by
    intro x
    have h := hasDerivAt_sourceInverse_of_continuous_integrable hgcont hgint x
    rw [← hueq] at h
    simpa only [up, hgIntegral, zero_div, zero_mul, sub_zero] using h
  have heq : ∀ x : ℝ, -Complex.I * up x + z * u x = 0 := by
    intro x
    have hcancel (A : ℂ) : -Complex.I * (Complex.I * A) = A := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]
      ring
    dsimp only [up, g, z]
    rw [hcancel]
    ring
  have htilt : Integrable (fun x => u x * sourceChar z x)
      (volume : Measure ℝ) := by
    have hvtilt := integrable_sourceSpace_mul_sourceChar v z
    refine (hvtilt.const_mul c).congr ?_
    filter_upwards [hsource] with x hx
    rw [hx]
    ring
  have hchar : ∀ x : ℝ, HasDerivAt (sourceChar z)
      (Complex.I * z * sourceChar z x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * z * ((t : ℝ) : ℂ))
        (Complex.I * z) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * z)
    have h := hlin.cexp
    refine h.congr_deriv ?_
    rw [sourceChar]
    ring
  have hprod : ∀ x : ℝ, HasDerivAt (fun t => u t * sourceChar z t) 0 x := by
    intro x
    have h := (huderiv x).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hx := heq x
    linear_combination (Complex.I * sourceChar z x) * hx
      + (sourceChar z x * up x) * hI
  have hbot : Tendsto (fun x => u x * sourceChar z x) atBot (nhds 0) :=
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
      (a := 0) (fun x _ => hprod x)
      (integrable_zero ℝ ℂ (volume : Measure ℝ)).integrableOn htilt.integrableOn
  have hzeroDeriv : ∀ x : ℝ,
      HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 x := fun x => hasDerivAt_const x 0
  have hzeroEq : ∀ x : ℝ,
      -Complex.I * 0 + z * 0 = (0 : ℂ) * (thetaSource.k x : ℂ) := by
    intro x
    ring
  have hu0all := HedenmalmPrimeTranslation.eq_of_sourceEquation thetaSource
    huderiv hzeroDeriv (fun x => by simpa using heq x) hzeroEq (by simpa using hbot)
  have hvzeroLeb : (fun x => (v x : ℂ)) =ᵐ[(volume : Measure ℝ)]
      fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hsource] with x hx
    rw [hu0all x] at hx
    exact (mul_eq_zero.mp hx.symm).resolve_left hc
  have hvzeroWeighted : (fun x => (v x : ℂ)) =ᵐ[
      (volume : Measure ℝ).withDensity (realDensity (sourceWeight thetaSource))]
      fun _ : ℝ => (0 : ℂ) :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mpr hvzeroLeb
  have hv0 : v = 0 := by
    apply Lp.ext
    have hzeroCoe := Lp.coeFn_zero ℂ 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight thetaSource)))
    filter_upwards [hvzeroWeighted, hzeroCoe] with x hx h0x
    calc
      v x = 0 := hx
      _ = (0 : SourceSpace thetaSource) x := by simpa using h0x.symm
  apply hf0
  rw [← hvf, hv0, map_zero]

end HedenmalmThetaSource

end

end RHTower
