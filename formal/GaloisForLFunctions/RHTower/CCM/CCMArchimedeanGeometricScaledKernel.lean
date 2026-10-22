import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanGeometricCompositeKernel

/-!
# Scaled distributional kernel of the CCM archimedean phase

Connes--Consani Proposition `lemsch7(i)` scales the first variable of the kernel of
`u∞* [P,u∞]` by applying the regular representation `vrep(ρ⁻¹)` on multiplicative-Haar
`L²`.  The published pointwise integral is not a Bochner integral, as shown in
`CCMArchimedeanGeometricCompositeKernel`; its unconditional meaning is therefore the pullback of
the composite Schwartz kernel as a distribution.  This file proves that pullback law on the dense
normalized even-Schwartz core.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- Normalized Schwartz dilation `g ↦ √ρ g(ρ·)`, matching the unitary dilation on
Lebesgue `L²`. -/
def ccmNormalizedSchwartzDilation (rho : ℝ) (hrho : 0 < rho)
    (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (Real.sqrt rho : ℂ) • schwartzDilate g hrho.ne'

@[simp] theorem ccmNormalizedSchwartzDilation_apply
    (rho : ℝ) (hrho : 0 < rho) (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ccmNormalizedSchwartzDilation rho hrho g x =
      (Real.sqrt rho : ℂ) * g (rho * x) := by
  rfl

theorem schwartzEvenPart_ccmNormalizedSchwartzDilation
    (rho : ℝ) (hrho : 0 < rho) (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzEvenPart (ccmNormalizedSchwartzDilation rho hrho g) x =
      (Real.sqrt rho : ℂ) * schwartzEvenPart g (rho * x) := by
  rw [schwartzEvenPart_apply, schwartzEvenPart_apply]
  simp only [ccmNormalizedSchwartzDilation_apply]
  rw [show rho * -x = -(rho * x) by ring]
  ring

/-- The dense even-Schwartz carrier is exactly equivariant for normalized dilation. -/
theorem ccmEvenSchwartzSource_normalizedDilation
    (rho : ℝ) (hrho : 0 < rho) (g : SchwartzMap ℝ ℂ) :
    ccmEvenSchwartzSource (ccmNormalizedSchwartzDilation rho hrho g) =
      evenDilationUnitary rho hrho (ccmEvenSchwartzSource g) := by
  apply Subtype.ext
  apply Lp.ext
  have hsourceScaled := ccmEvenSchwartzSource_coeFn
    (ccmNormalizedSchwartzDilation rho hrho g)
  have hsource := (ccmEvenSchwartzSource_coeFn g).comp_tendsto
    (realMul_quasiMeasurePreserving rho hrho.ne').tendsto_ae
  filter_upwards [hsourceScaled,
    dilation_ae rho hrho (ccmEvenSchwartzSource g), hsource]
      with x hscaled hdil hsource_x
  rw [hscaled]
  change schwartzEvenPart (ccmNormalizedSchwartzDilation rho hrho g) x =
    (((dilation rho hrho (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ) x)
  rw [hdil, schwartzEvenPart_ccmNormalizedSchwartzDilation]
  simpa only [Function.comp_apply] using
    (congrArg ((Real.sqrt rho : ℂ) * ·) hsource_x).symm

/-- Multiplicative-Haar realization of `vrep(ρ⁻¹)`: `ξ(ν) ↦ ξ(ρν)`. -/
def ccmMultiplicativeScalingUnitary (rho : ℝ) (hrho : 0 < rho) :
    CCMMultiplicativeL2 ≃ₗᵢ[ℂ] CCMMultiplicativeL2 :=
  evenToMultiplicativeHaarUnitary.symm.trans
    ((evenDilationUnitary rho hrho).trans evenToMultiplicativeHaarUnitary)

/-- Exact scaling law on the dense multiplicative-Haar Schwartz source. -/
theorem ccmMultiplicativeScalingUnitary_schwartzSource
    (rho : ℝ) (hrho : 0 < rho) (g : SchwartzMap ℝ ℂ) :
    ccmMultiplicativeScalingUnitary rho hrho
        (ccmMultiplicativeSchwartzSource g) =
      ccmMultiplicativeSchwartzSource
        (ccmNormalizedSchwartzDilation rho hrho g) := by
  unfold ccmMultiplicativeScalingUnitary ccmMultiplicativeSchwartzSource
  simp only [LinearIsometryEquiv.trans_apply]
  rw [evenToMultiplicativeHaarUnitary.symm_apply_apply]
  rw [ccmEvenSchwartzSource_normalizedDilation]

/-- The inverse regular action pulls a normalized Schwartz test back by `ρ⁻¹`. -/
theorem ccmMultiplicativeScalingUnitary_symm_schwartzSource
    (rho : ℝ) (hrho : 0 < rho) (g : SchwartzMap ℝ ℂ) :
    (ccmMultiplicativeScalingUnitary rho hrho).symm
        (ccmMultiplicativeSchwartzSource g) =
      ccmMultiplicativeSchwartzSource
        (ccmNormalizedSchwartzDilation rho⁻¹ (inv_pos.mpr hrho) g) := by
  unfold ccmMultiplicativeScalingUnitary ccmMultiplicativeSchwartzSource
  change evenToMultiplicativeHaarUnitary
      ((evenDilationUnitary rho hrho).symm
        (evenToMultiplicativeHaarUnitary.symm
          (evenToMultiplicativeHaarUnitary (ccmEvenSchwartzSource g)))) =
    evenToMultiplicativeHaarUnitary
      (ccmEvenSchwartzSource
        (ccmNormalizedSchwartzDilation rho⁻¹ (inv_pos.mpr hrho) g))
  rw [evenToMultiplicativeHaarUnitary.symm_apply_apply,
    ccmEvenSchwartzSource_normalizedDilation]
  rfl

/-- Distributional pullback of the composite kernel in its first variable.  In the conventional
kernel notation this is `ℓρ(ν,μ)=ℓ(ρν,μ)`; unlike the source's raw pointwise integral,
this pairing is canonically defined. -/
def ccmArchimedeanGeometricScaledCompositeKernelPairing
    (rho : ℝ) (hrho : 0 < rho) (g h : SchwartzMap ℝ ℂ) : ℂ :=
  ccmArchimedeanGeometricCompositeKernelPairing
    (ccmNormalizedSchwartzDilation rho⁻¹ (inv_pos.mpr hrho) g) h

/-- **Connes--Consani Proposition `lemsch7(i)`, unconditional distributional form.**
The regular translate `vrep(ρ⁻¹) u∞* [P,u∞]` has the first-variable-scaled
Schwartz kernel on every pair of dense normalized even-Schwartz sources. -/
theorem inner_ccmMultiplicativeScaling_comp_geometricComposite_eq_scaledKernelPairing
    (rho : ℝ) (hrho : 0 < rho) (g h : SchwartzMap ℝ ℂ) :
    inner ℂ (ccmMultiplicativeSchwartzSource g)
        (ccmMultiplicativeScalingUnitary rho hrho
          (ccmArchimedeanGeometricComposite
            (ccmMultiplicativeSchwartzSource h))) =
      ccmArchimedeanGeometricScaledCompositeKernelPairing rho hrho g h := by
  have hinner := (ccmMultiplicativeScalingUnitary rho hrho).inner_map_map
    ((ccmMultiplicativeScalingUnitary rho hrho).symm
      (ccmMultiplicativeSchwartzSource g))
    (ccmArchimedeanGeometricComposite (ccmMultiplicativeSchwartzSource h))
  rw [LinearIsometryEquiv.apply_symm_apply] at hinner
  rw [hinner, ccmMultiplicativeScalingUnitary_symm_schwartzSource,
    inner_ccmArchimedeanGeometricComposite_eq_kernelPairing]
  rfl

end RHTower
