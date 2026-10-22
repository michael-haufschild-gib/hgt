import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalTimeLaplace
import GaloisForLFunctions.HTGeometry.L2NegativeHalfLineRestriction
/-! The original cutoff commutators applied to the constructed principal causal responses. -/
open MeasureTheory Set Filter GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section

private theorem horizonSymbol_measurable : Measurable (fun t : ℝ => (horizonCoordinate t:ℂ)) :=
  (Complex.continuous_ofReal.comp horizonCoordinate_continuous).measurable

private theorem horizonSymbol_bound (t : ℝ) : ‖(horizonCoordinate t:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (horizonCoordinate_nonneg t)]
  exact horizonCoordinate_le_one t

/-- Literal horizon factor followed by restriction to the original infinite negative ray. -/
def principalCutoffRadialOp : FourierRealL2 →L[ℂ] Lp ℂ 2 radialMeasure :=
  negativeRestriction.comp (lpBoundedMulCLM horizonSymbol_measurable zero_le_one horizonSymbol_bound)

theorem principalCutoffRadialOp_ae (f : FourierRealL2) :
    principalCutoffRadialOp f =ᵐ[radialMeasure] (fun t => (horizonCoordinate t:ℂ)*f t) := by
  have hm := (lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
    horizonSymbol_measurable zero_le_one horizonSymbol_bound f).filter_mono
      (ae_mono (show radialMeasure ≤ volume from Measure.restrict_le_self))
  exact (negativeRestriction_ae _).trans hm

/-- Each channel includes its actual angular cutoff commutator and the original horizon factor. -/
def principalCutoffSpatialOp (q : XiZeroCopy) (i : Fin 3) : FourierRealL2 →L[ℂ] SpatialSpace :=
  (l2SeparatedProductContinuousBilinear.flip (cutoffCommutatorVector (principalExponent q i))).comp
    principalCutoffRadialOp

theorem principalCutoffSpatialOp_apply (q : XiZeroCopy) (i : Fin 3) (f : FourierRealL2) :
    principalCutoffSpatialOp q i f = l2SeparatedProduct (principalCutoffRadialOp f)
      (cutoffCommutatorVector (principalExponent q i)) := rfl

def principalCutoffTimeVector (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) : SpatialSpace :=
  principalCutoffSpatialOp q i (principalTimeResponse q branch a i τ)

theorem principalCutoffTimeVector_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (principalCutoffTimeVector q branch a i) :=
  (principalCutoffSpatialOp q i).continuous.comp (principalTimeResponse_continuous q branch a i)

theorem principalCutoffTimeVector_zero_of_nonpos (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (τ : ℝ) (hτ : τ ≤ 0) : principalCutoffTimeVector q branch a i τ = 0 := by
  rw [principalCutoffTimeVector,principalTimeResponse_zero_of_nonpos q branch a i τ hτ,map_zero]

theorem principalCutoffTimeVector_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ) (Ioi 0) := by
  apply ((principalCutoffSpatialOp q i).integrable_comp
    (principalTimeResponse_laplace_integrable q branch a i w hw)).congr
  filter_upwards [] with τ
  rw [map_smul]
  rfl

/-- Norm-convergent response transform commutes with the exact cutoff and angular completion. -/
theorem principalCutoffTimeVector_laplace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ) =
      principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) := by
  have he (τ : ℝ) : Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ =
      principalCutoffSpatialOp q i (Complex.exp (-w*(τ:ℂ)) • principalTimeResponse q branch a i τ) := by
    rw [map_smul]
    rfl
  simp only [he]
  exact (principalCutoffSpatialOp q i).integral_comp_comm
    (principalTimeResponse_laplace_integrable q branch a i w hw)

end
end RHTower.D4BMJointSource
