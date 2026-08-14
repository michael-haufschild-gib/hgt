import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassFourier
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact

/-!
# Literal semilocal support and Sonin spaces

This file formalizes Connes--Consani--Moscovici Definition 4.5 on the actual
finite-stage quotient `X_S`.  The physical space `P^S_λ` is cut out by the
descended adelic module on the literal closed ball `{x | |x|_S ≤ λ}`.  The
semilocal Sonin space is then the common kernel of this sharp cutoff and the
same cutoff after the independently constructed semilocal Fourier unitary.

Crucially, neither support nor the Sonin space is defined as an image under
`θ_S`.  The final a.e. theorem below is the literal L² meaning of simultaneous
vanishing of `f` and `𝔽_S f` on the source aperture.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set IsDedekindDomain

/-! ### The source aperture and `P^S_λ` -/

/-- Closed source aperture `{x ∈ X_S | |x|_S ≤ λ}`. -/
def fieldOneFiniteStageClassAperture
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    Set (FieldOneFiniteStageClassSpace S) :=
  {x | (fieldOneFiniteStageClassModule S x : ℝ) ≤ lam}

theorem fieldOneFiniteStageClassAperture_measurable
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    MeasurableSet (fieldOneFiniteStageClassAperture S lam) := by
  change MeasurableSet
    ((fun x => (fieldOneFiniteStageClassModule S x : ℝ)) ⁻¹' Set.Iic lam)
  exact measurableSet_Iic.preimage
    (NNReal.continuous_coe.comp
      (fieldOneFiniteStageClassModule_continuous S)).measurable

/-- Sharp multiplication by the indicator of the literal source aperture. -/
def fieldOneFiniteStageClassSupportCutoff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    FieldOneFiniteStageClassL2 S →L[ℂ]
      FieldOneFiniteStageClassL2 S :=
  RHTower.lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ)
    (fieldOneFiniteStageClassAdditiveMeasure S) 2
    (fieldOneFiniteStageClassAperture S lam)
    (fieldOneFiniteStageClassAperture_measurable S lam)

theorem fieldOneFiniteStageClassSupportCutoff_ae
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassSupportCutoff S lam f =ᵐ[
        fieldOneFiniteStageClassAdditiveMeasure S]
      (fieldOneFiniteStageClassAperture S lam).indicator fun x => f x := by
  exact RHTower.lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ)
    (fieldOneFiniteStageClassAdditiveMeasure S) 2
    (fieldOneFiniteStageClassAperture S lam)
    (fieldOneFiniteStageClassAperture_measurable S lam) f

/-- Literal CCM space `P^S_λ`: invariant L² vectors supported in the module
ball.  Membership is expressed through the range of the actual sharp source
cutoff, not through `η_S` or `θ_S`. -/
def fieldOneFiniteStageClassPhysicalSupportSubmodule
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    Submodule ℂ
      (fieldOneFiniteStageClassModuleOneInvariantSubmodule S) :=
  (LinearMap.range
      (fieldOneFiniteStageClassSupportCutoff S lam).toLinearMap).comap
    (fieldOneFiniteStageClassModuleOneInvariantSubmodule S).subtype

/-! ### Definition 4.5 -/

/-- Physical vanishing constraint on `L²(X_S)^{K_S}`. -/
def fieldOneFiniteStageClassPhysicalConstraint
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    fieldOneFiniteStageClassModuleOneInvariantSubmodule S →L[ℂ]
      FieldOneFiniteStageClassL2 S :=
  fieldOneFiniteStageClassSupportCutoff S lam ∘L
    (fieldOneFiniteStageClassModuleOneInvariantSubmodule S).subtypeL

/-- Fourier-side vanishing constraint on `L²(X_S)^{K_S}`. -/
def fieldOneFiniteStageClassFourierConstraint
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    fieldOneFiniteStageClassModuleOneInvariantSubmodule S →L[ℂ]
      FieldOneFiniteStageClassL2 S :=
  fieldOneFiniteStageClassSupportCutoff S lam ∘L
    (fieldOneFiniteStageClassFourierUnitary S).toLinearIsometry.toContinuousLinearMap ∘L
      (fieldOneFiniteStageClassModuleOneInvariantSubmodule S).subtypeL

/-- CCM Definition 4.5: literal semilocal Sonin space inside
`L²(X_S)^{K_S}`. -/
def fieldOneFiniteStageSemilocalSoninSubmodule
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    Submodule ℂ
      (fieldOneFiniteStageClassModuleOneInvariantSubmodule S) :=
  LinearMap.ker
      (fieldOneFiniteStageClassPhysicalConstraint S lam).toLinearMap ⊓
    LinearMap.ker
      (fieldOneFiniteStageClassFourierConstraint S lam).toLinearMap

theorem fieldOneFiniteStage_mem_semilocalSonin_iff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)
    (f : fieldOneFiniteStageClassModuleOneInvariantSubmodule S) :
    f ∈ fieldOneFiniteStageSemilocalSoninSubmodule S lam ↔
      fieldOneFiniteStageClassSupportCutoff S lam f.1 = 0 ∧
      fieldOneFiniteStageClassSupportCutoff S lam
        (fieldOneFiniteStageClassFourierUnitary S f.1) = 0 := by
  rfl

theorem fieldOneFiniteStageClassSupportCutoff_eq_zero_iff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassSupportCutoff S lam f = 0 ↔
      (fieldOneFiniteStageClassAperture S lam).indicator
          (fun x => f x) =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S] 0 := by
  constructor
  · intro hzero
    have hae := fieldOneFiniteStageClassSupportCutoff_ae S lam f
    rw [hzero] at hae
    filter_upwards [hae,
      Lp.coeFn_zero (E := ℂ) (p := 2)
        (μ := fieldOneFiniteStageClassAdditiveMeasure S)] with x hcut hzero'
    rw [← hcut, hzero']
  · intro hae
    apply Lp.ext
    filter_upwards [fieldOneFiniteStageClassSupportCutoff_ae S lam f, hae,
      Lp.coeFn_zero (E := ℂ) (p := 2)
        (μ := fieldOneFiniteStageClassAdditiveMeasure S)] with x hcut hind hzero
    rw [hcut, hind, hzero]

/-- Literal a.e. statement of CCM Definition 4.5: both the vector and its
normalized semilocal Fourier transform vanish on `{|x|_S ≤ λ}`. -/
theorem fieldOneFiniteStage_mem_semilocalSonin_iff_ae
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)
    (f : fieldOneFiniteStageClassModuleOneInvariantSubmodule S) :
    f ∈ fieldOneFiniteStageSemilocalSoninSubmodule S lam ↔
      (fieldOneFiniteStageClassAperture S lam).indicator
          (fun x => f.1 x) =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S] 0 ∧
      (fieldOneFiniteStageClassAperture S lam).indicator
          (fun x => fieldOneFiniteStageClassFourierUnitary S f.1 x) =ᵐ[
            fieldOneFiniteStageClassAdditiveMeasure S] 0 := by
  rw [fieldOneFiniteStage_mem_semilocalSonin_iff,
    fieldOneFiniteStageClassSupportCutoff_eq_zero_iff,
    fieldOneFiniteStageClassSupportCutoff_eq_zero_iff]

end

end GaloisForLFunctions.RHTower
