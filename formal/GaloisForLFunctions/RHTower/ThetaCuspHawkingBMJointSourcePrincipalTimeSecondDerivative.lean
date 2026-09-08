import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeDerivative
import GaloisForLFunctions.HTGeometry.UnitWaveEllipticRange
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeRegularity

/-! The actual principal causal responses satisfy a second-order Hilbert-space wave equation. -/
open MeasureTheory Set GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem native_differentiable (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Differentiable ℝ (timeRadialSourceVector (physicalRate q branch) a) := by
  have hs : (2*physicalRate q branch).re ≤ 0 := (currentRate_re_lt q branch).le.trans (by norm_num)
  exact fun τ => (timeRadialSourceVector_hasDerivAt _ a hs τ).differentiableAt

private theorem native_deriv_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (deriv (timeRadialSourceVector (physicalRate q branch) a)) := by
  have hs : (2*physicalRate q branch).re ≤ 0 := (currentRate_re_lt q branch).le.trans (by norm_num)
  have he := funext (fun τ => (timeRadialSourceVector_hasDerivAt _ a hs τ).deriv)
  rw [he]
  exact timeRadialSourceFirst_continuous _ a hs

/-- The actual odd-extended principal source is differentiable at every physical time. -/
theorem principalTimeForcing_differentiable (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Differentiable ℝ (principalTimeForcing q branch a i) := by
  let L := (principalAmplitude q i • negativeOddExtension).restrictScalars ℝ
  exact L.differentiable.comp (native_differentiable q branch a)

/-- Both retained onset derivatives give a continuous norm derivative of each principal source. -/
theorem principalTimeForcing_deriv_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (deriv (principalTimeForcing q branch a i)) := by
  let L := (principalAmplitude q i • negativeOddExtension).restrictScalars ℝ
  have hd (τ : ℝ) : HasDerivAt (principalTimeForcing q branch a i)
      (L (deriv (timeRadialSourceVector (physicalRate q branch) a) τ)) τ :=
    L.hasFDerivAt.comp_hasDerivAt τ ((native_differentiable q branch a τ).hasDerivAt)
  rw [funext (fun τ => (hd τ).deriv)]
  exact L.continuous.comp (native_deriv_continuous q branch a)

/-- Differentiating the effective forcing retains the actual complex potential and response velocity. -/
theorem principalEffectiveForcing_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    HasDerivAt (principalEffectiveForcing q branch a i)
      (deriv (principalTimeForcing q branch a i) τ+
        principalWavePotentialOp q i (deriv (principalTimeResponse q branch a i) τ)) τ := by
  have hU := (principalTimeResponse_hasDerivAt q branch a i τ).differentiableAt.hasDerivAt
  exact ((principalTimeForcing_differentiable q branch a i τ).hasDerivAt).add
    (((principalWavePotentialOp q i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt τ hU)

theorem principalEffectiveForcing_deriv_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (deriv (principalEffectiveForcing q branch a i)) := by
  rw [funext (fun τ => (principalEffectiveForcing_hasDerivAt q branch a i τ).deriv)]
  exact (principalTimeForcing_deriv_continuous q branch a i).add
    ((principalWavePotentialOp q i).continuous.comp (principalTimeResponse_deriv_continuous q branch a i))

private theorem effective_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    principalEffectiveForcing q branch a i 0 = 0 := by
  simp only [principalEffectiveForcing,principalTimeForcing_zero_of_nonpos q branch a i 0 le_rfl,
    (principalTimeResponse_initial_data q branch a i).1,map_zero,add_zero]

/-- The original principal response has a genuine second time derivative in L². -/
theorem principalTimeResponse_second_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    HasDerivAt (deriv (principalTimeResponse q branch a i))
      (∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ))
        (deriv (principalEffectiveForcing q branch a i) σ)) τ := by
  rw [principalTimeResponse_convolution]
  exact unitWaveDuhamel_second_hasDerivAt _ _ (principalEffectiveForcing_continuous q branch a i)
    (principalEffectiveForcing_deriv_continuous q branch a i)
    (fun σ => (principalEffectiveForcing_hasDerivAt q branch a i σ).differentiableAt.hasDerivAt)
    (effective_zero q branch a i) τ

theorem principalTimeResponse_second_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (deriv (deriv (principalTimeResponse q branch a i))) := by
  rw [funext (fun τ => (principalTimeResponse_second_hasDerivAt q branch a i τ).deriv)]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous ?_ continuous_id
  exact continuous_kgCosOp_comp (continuous_const.mul (continuous_fst.sub continuous_snd))
    ((principalEffectiveForcing_deriv_continuous q branch a i).comp continuous_snd)

/-- The original forcing and complex potential satisfy the exact twice-regularized wave equation. -/
theorem principalTimeResponse_wave_graph (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeResponse q branch a i τ = unitWaveEllipticInv
      (principalTimeForcing q branch a i τ+
        principalWavePotentialOp q i (principalTimeResponse q branch a i τ)-
        deriv (deriv (principalTimeResponse q branch a i)) τ) := by
  change principalTimeResponse q branch a i τ = unitWaveEllipticInv
    (principalEffectiveForcing q branch a i τ-deriv (deriv (principalTimeResponse q branch a i)) τ)
  rw [principalTimeResponse_convolution]
  exact unitWaveDuhamel_wave_graph _ _ (principalEffectiveForcing_continuous q branch a i)
    (principalEffectiveForcing_deriv_continuous q branch a i)
    (fun σ => (principalEffectiveForcing_hasDerivAt q branch a i σ).differentiableAt.hasDerivAt)
    (effective_zero q branch a i) τ

end
end RHTower.D4BMJointSource
