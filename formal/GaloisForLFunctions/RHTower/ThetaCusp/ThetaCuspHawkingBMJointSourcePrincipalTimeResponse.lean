import GaloisForLFunctions.HTGeometry.UnitWaveDuhamel
import GaloisForLFunctions.HTGeometry.UnitWavePotentialKernel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalWavePotential
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalTimeForcing
/-! Constructed causal principal responses for the literal theta-cusp source and potentials. -/
open MeasureTheory Set GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

def principalResponseGrowth (q : XiZeroCopy) (i : Fin 3) : ℝ :=
  (2*Real.pi)⁻¹*‖principalWavePotentialOp q i‖

def principalResponseSize (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) : ℝ :=
  (2*Real.pi)⁻¹*(∫ τ in Ioi (0:ℝ), ‖principalTimeForcing q branch a i τ‖)

theorem principalResponseGrowth_nonneg (q : XiZeroCopy) (i : Fin 3) :
    0 ≤ principalResponseGrowth q i := by unfold principalResponseGrowth; positivity

theorem principalResponseSize_nonneg (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    0 ≤ principalResponseSize q branch a i :=
  mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))

private theorem principalFree_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    ‖unitWaveDuhamel (principalTimeForcing q branch a i) τ‖ ≤ principalResponseSize q branch a i :=
  unitWaveDuhamel_norm_le _ (principalTimeForcing_continuous q branch a i)
    (principalTimeForcing_integrable q branch a i) (principalTimeForcing_zero_of_nonpos q branch a i) τ

/-- One frequency-independent principal response, built from its actual retarded forcing. -/
def principalTimeResponse (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) : ℝ → FourierRealL2 :=
  volterraSolution (unitWaveDuhamel (principalTimeForcing q branch a i))
    (unitWaveKernel (principalWavePotentialOp q i))

theorem principalTimeResponse_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (principalTimeResponse q branch a i) :=
  continuous_volterraSolution_of_strong
    (unitWaveDuhamel_continuous _ (principalTimeForcing_continuous q branch a i))
    (unitWaveKernel_strong _) (principalResponseGrowth_nonneg q i)
    (principalResponseSize_nonneg q branch a i) (unitWaveKernel_norm_le _) (principalFree_bound q branch a i)

/-- The actual response solves the physical sine-kernel Volterra equation. -/
theorem principalTimeResponse_duhamel (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeResponse q branch a i τ = unitWaveDuhamel (principalTimeForcing q branch a i) τ+
      ∫ σ in (0:ℝ)..τ, unitWaveSine (τ-σ) (principalWavePotentialOp q i (principalTimeResponse q branch a i σ)) :=
  volterraSolution_eq_of_strong
    (unitWaveDuhamel_continuous _ (principalTimeForcing_continuous q branch a i))
    (unitWaveKernel_strong _) (principalResponseGrowth_nonneg q i)
    (principalResponseSize_nonneg q branch a i) (unitWaveKernel_norm_le _) (principalFree_bound q branch a i) τ

theorem principalTimeResponse_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    ‖principalTimeResponse q branch a i τ‖ ≤
      principalResponseSize q branch a i*Real.exp (principalResponseGrowth q i*|τ|) :=
  norm_volterraSolution_le_of_strong
    (unitWaveDuhamel_continuous _ (principalTimeForcing_continuous q branch a i))
    (unitWaveKernel_strong _) (principalResponseGrowth_nonneg q i)
    (principalResponseSize_nonneg q branch a i) (unitWaveKernel_norm_le _) (principalFree_bound q branch a i) τ

/-- No response precedes the original fixed source onset. -/
theorem principalTimeResponse_zero_of_nonpos (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (τ : ℝ) (hτ : τ ≤ 0) : principalTimeResponse q branch a i τ = 0 :=
  volterraSolution_zero_of_nonpos _ _
    (unitWaveDuhamel_zero_of_nonpos _ (principalTimeForcing_zero_of_nonpos q branch a i)) τ hτ

/-- The genuine evolution remains in the odd spatial carrier needed for the original Dirichlet problem. -/
theorem principalTimeResponse_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    l2Reflection (principalTimeResponse q branch a i τ) = -principalTimeResponse q branch a i τ := by
  have h := volterraSolution_fixed _ _
    (unitWaveDuhamel_continuous _ (principalTimeForcing_continuous q branch a i))
    (unitWaveKernel_strong _) (principalResponseGrowth q i) (principalResponseSize q branch a i)
    (principalResponseGrowth_nonneg q i) (principalResponseSize_nonneg q branch a i)
    (unitWaveKernel_norm_le _) (principalFree_bound q branch a i) ((-l2Reflection).restrictScalars ℝ)
    (fun t => ?_) (fun t s f => ?_) τ
  · change -l2Reflection (principalTimeResponse q branch a i τ) = principalTimeResponse q branch a i τ at h
    simpa only [neg_neg] using congrArg Neg.neg h
  · change -l2Reflection (unitWaveDuhamel (principalTimeForcing q branch a i) t) = _
    rw [unitWaveDuhamel_reflection _ (principalTimeForcing_continuous q branch a i)
      (principalTimeForcing_reflection q branch a i),neg_neg]
  · change -l2Reflection (unitWaveKernel (principalWavePotentialOp q i) t s f) =
      unitWaveKernel (principalWavePotentialOp q i) t s (-l2Reflection f)
    rw [map_neg,unitWaveKernel_reflection _ (principalWavePotentialOp_reflection q i)]

/-- This actual source and potential have exactly one continuous retarded integral solution. -/
theorem principalTimeResponse_unique (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (u : ℝ → FourierRealL2) (hu : Continuous u)
    (he : ∀ τ, u τ = unitWaveDuhamel (principalTimeForcing q branch a i) τ+
      ∫ σ in (0:ℝ)..τ, unitWaveSine (τ-σ) (principalWavePotentialOp q i (u σ))) :
    u = principalTimeResponse q branch a i :=
  volterra_eq_of_eq_of_eq_of_strong (unitWaveKernel_strong _) (principalResponseGrowth_nonneg q i)
    (unitWaveKernel_norm_le _) hu (principalTimeResponse_continuous q branch a i)
    he (principalTimeResponse_duhamel q branch a i)

end
end RHTower.D4BMJointSource
