import GaloisForLFunctions.RHTower.HedenmalmShiftedSourceEquation

/-!
# Closed-operator identification with Hedenmalm's explicit solution

The shifted closed derivative's unique source-equation solution is pulled through the quantile
unitary and identified with `i * sourceModeU`.  The proof uses the literal source inverse,
all-shift integrability, automatic left boundary decay, and first-order uniqueness.
-/

open Complex Function MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmPrimeTranslation
  HedenmalmFredholmRange HedenmalmClosedWeightedDerivative

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev HS := SourceSpace thetaSource

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The literal quantile forcing pulls back to `-i k` in weighted source space. -/
theorem quantileSymm_thetaSourceForcingVector :
    (quantileUnitary thetaSource).symm thetaSourceForcingVector =
      (-Complex.I) • thetaCokernelSourceVector 0 := by
  apply (quantileUnitary thetaSource).injective
  rw [(quantileUnitary thetaSource).apply_symm_apply, map_smul]
  rfl

/-- Any closed-operator solution of the shifted theta source equation has Hedenmalm's explicit
source-coordinate representative.  Existence itself forces the representative into the weighted
Hilbert space, so no spectral strip assumption is needed. -/
theorem thetaShifted_sourceEquation_source_representation
    (α : ℂ) (u : (thetaShiftedWeightedDerivative α).domain)
    (hu : thetaShiftedWeightedDerivative α u = thetaSourceForcingVector) :
    let w : HS := (quantileUnitary thetaSource).symm (u : H)
    (fun x => w x) =ᵐ[(volume : Measure ℝ)]
      fun x => Complex.I * sourceModeU thetaSource α x := by
  let u₀ : thetaWeightedDerivative.domain :=
    ⟨(u : H), by
      simpa only [thetaShiftedWeightedDerivative_domain] using u.property⟩
  have hurange : (u : H) ∈ thetaCenteredSourceInverse.range := by
    simpa only [thetaWeightedDerivative, closedHyperplaneInverse_domain] using u₀.property
  rcases hurange with ⟨k, hk⟩
  have hAapply : thetaWeightedDerivative u₀ = (k : H) := by
    have happly := (closedHyperplaneInverse_apply_B thetaCentered
      thetaCenteredSourceInverse thetaCenteredSourceInverse_injective k).2
    have heq : u₀ =
        ⟨thetaCenteredSourceInverse k,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective k).1⟩ := Subtype.ext hk.symm
    simpa only [thetaWeightedDerivative, heq] using happly
  have hsourceH : (k : H) + α • (u : H) = thetaSourceForcingVector := by
    calc
      (k : H) + α • (u : H) = thetaWeightedDerivative u₀ + α • (u : H) := by
        rw [hAapply]
      _ = thetaShiftedWeightedDerivative α u := by
        simpa only [u₀] using (thetaShiftedWeightedDerivative_apply α u).symm
      _ = thetaSourceForcingVector := hu
  let v : HS := (quantileUnitary thetaSource).symm (k : H)
  let w : HS := (quantileUnitary thetaSource).symm (u : H)
  have hvk : quantileUnitary thetaSource v = (k : H) := by simp [v]
  have hwu : quantileUnitary thetaSource w = (u : H) := by simp [w]
  have hcompact : thetaCompactSourceInverse (k : H) = (u : H) := by
    change thetaCenteredSourceInverse k = (u : H)
    exact hk
  have hsourceInverse :
      sourceInverse thetaSource (fun x => v x) =ᵐ[(volume : Measure ℝ)]
        fun x => w x := by
    simpa only [v, w, hcompact] using
      (sourceInverse_ae_eq_quantileSymm_thetaCompactSourceInverse (k : H))
  have hLp : v + α • w = (-Complex.I) • thetaCokernelSourceVector 0 := by
    apply (quantileUnitary thetaSource).injective
    rw [map_add, map_smul, hvk, hwu]
    rw [← quantileSymm_thetaSourceForcingVector, (quantileUnitary thetaSource).apply_symm_apply]
    exact hsourceH
  have hLpCoe :
      ((v + α • w : HS) : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).withDensity
          (realDensity (sourceWeight thetaSource))]
      (((-Complex.I) • thetaCokernelSourceVector 0 : HS) : ℝ → ℂ) := by
    rw [hLp]
  have hsourceEq :
      (fun x => v x + α * w x) =ᵐ[(volume : Measure ℝ)]
        fun x => -Complex.I * (thetaSource.k x : ℂ) := by
    have hLpCoeLeb := (withDensity_realDensity_ae_eq
      (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp hLpCoe
    filter_upwards [hLpCoeLeb, Lp.coeFn_add v (α • w), Lp.coeFn_smul α w,
      Lp.coeFn_smul (-Complex.I) (thetaCokernelSourceVector 0),
      thetaCokernelSourceVector_ae 0]
      with x heq hadd hsmul hrsmul hcok
    calc
      v x + α * w x = (v + α • w : HS) x := by rw [hadd, hsmul]
      _ = ((-Complex.I) • thetaCokernelSourceVector 0 : HS) x := heq
      _ = -Complex.I * thetaCokernelSourceVector 0 x := hrsmul
      _ = -Complex.I * cokernelVector thetaSource 0 x := by rw [hcok]
      _ = -Complex.I * (thetaSource.k x : ℂ) := by
        rw [cokernelVector_eq_k_mul_sourceChar]
        simp [sourceChar]
  have hvint : Integrable (fun x => (v x : ℂ)) (volume : Measure ℝ) :=
    integrable_sourceSpace thetaSource v
  let U : ℝ → ℂ := sourceInverse thetaSource (fun x => v x)
  have hUcont : Continuous U := continuous_sourceInverse_of_integrable hvint
  have hUw : U =ᵐ[(volume : Measure ℝ)] fun x => w x := hsourceInverse
  let g : ℝ → ℂ :=
    fun x => -Complex.I * (thetaSource.k x : ℂ) - α * U x
  have hgcont : Continuous g :=
    (continuous_const.mul (Complex.continuous_ofReal.comp thetaSource.continuous_k)).sub
      (continuous_const.mul hUcont)
  have hgv : g =ᵐ[(volume : Measure ℝ)] fun x => v x := by
    filter_upwards [hUw, hsourceEq] with x hUw_x hsourceEq_x
    dsimp only [g]
    rw [hUw_x]
    linear_combination hsourceEq_x
  have hgint : Integrable g (volume : Measure ℝ) := hvint.congr hgv.symm
  have hUeq : U = sourceInverse thetaSource g := by
    funext x
    exact sourceInverse_congr_ae thetaSource hgv.symm x
  have hvIntegral : ∫ x, (v x : ℂ) = 0 := by
    have hformula := pinnedMean_quantileUnitary thetaSource v
    rw [integral_quantileTransform thetaSource hvint.aestronglyMeasurable,
      hvk, (mem_thetaCentered_iff k).mp k.property] at hformula
    have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
    exact (div_eq_zero_iff.mp hformula.symm).resolve_right hsqrt
  have hgIntegral : ∫ x, g x = 0 := by
    rw [integral_congr_ae hgv]
    exact hvIntegral
  let Up : ℝ → ℂ := fun x => Complex.I * g x
  have hUderiv : ∀ x : ℝ, HasDerivAt U (Up x) x := by
    intro x
    have h := hasDerivAt_sourceInverse_of_continuous_integrable hgcont hgint x
    rw [← hUeq] at h
    simpa only [Up, hgIntegral, zero_div, zero_mul, sub_zero] using h
  have hUequation : ∀ x : ℝ,
      -Complex.I * Up x + α * U x =
        -Complex.I * (thetaSource.k x : ℂ) := by
    intro x
    have hcancel (A : ℂ) : -Complex.I * (Complex.I * A) = A := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]
      ring
    dsimp only [Up, g]
    rw [hcancel]
    ring
  have hUtilt : Integrable (fun x => U x * sourceChar α x)
      (volume : Measure ℝ) := by
    have hwtilt := integrable_sourceSpace_mul_sourceChar w α
    refine hwtilt.congr ?_
    filter_upwards [hUw] with x hx
    rw [hx]
  have hchar : ∀ x : ℝ, HasDerivAt (sourceChar α)
      (Complex.I * α * sourceChar α x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * α * ((t : ℝ) : ℂ))
        (Complex.I * α) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * α)
    have h := hlin.cexp
    refine h.congr_deriv ?_
    rw [sourceChar]
    ring
  have hprod : ∀ x : ℝ, HasDerivAt (fun t => U t * sourceChar α t)
      ((thetaSource.k x : ℂ) * sourceChar α x) x := by
    intro x
    have h := (hUderiv x).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hx := hUequation x
    linear_combination (Complex.I * sourceChar α x) * hx
      + (sourceChar α x * (Up x - (thetaSource.k x : ℂ))) * hI
  have hUbot : Tendsto (fun x => U x * sourceChar α x) atBot (nhds 0) :=
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
      (a := 0) (fun x _ => hprod x)
      (integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource_all α)).integrableOn
      hUtilt.integrableOn
  have hExplicitDeriv : ∀ x : ℝ,
      HasDerivAt (fun t => Complex.I * sourceModeU thetaSource α t)
        (Complex.I * sourceModeD thetaSource α x) x :=
    fun x => hasDerivAt_twoEndedSolution thetaSource
      (hasShiftedTail_thetaSource_all α) x
  have hExplicitEquation : ∀ x : ℝ,
      -Complex.I * (Complex.I * sourceModeD thetaSource α x) +
          α * (Complex.I * sourceModeU thetaSource α x) =
        -Complex.I * (thetaSource.k x : ℂ) :=
    twoEndedSolution_equation thetaSource α
  have hExplicitTilted :
      (fun x : ℝ => (Complex.I * sourceModeU thetaSource α x) * sourceChar α x) =
        sourceModeI thetaSource α := by
    funext x
    rw [sourceModeU, sourceChar, ← Complex.exp_add]
    have hI : Complex.I * (-Complex.I) = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      ring
    rw [← mul_assoc, hI, one_mul]
    simp
  have hExplicitBot : Tendsto
      (fun x : ℝ => (Complex.I * sourceModeU thetaSource α x) * sourceChar α x)
      atBot (nhds 0) := by
    rw [hExplicitTilted]
    exact MeasureTheory.tendsto_integral_Iic_zero tendsto_id
  have hdiffBot : Tendsto
      (fun x => (U x - Complex.I * sourceModeU thetaSource α x) * sourceChar α x)
      atBot (nhds 0) := by
    have hsub := hUbot.sub hExplicitBot
    convert hsub using 1 <;> funext x <;> ring
  have hall := HedenmalmPrimeTranslation.eq_of_sourceEquation thetaSource
    hUderiv hExplicitDeriv hUequation hExplicitEquation hdiffBot
  exact hUw.symm.trans (Filter.Eventually.of_forall hall)

end HedenmalmThetaSource

end

end RHTower
