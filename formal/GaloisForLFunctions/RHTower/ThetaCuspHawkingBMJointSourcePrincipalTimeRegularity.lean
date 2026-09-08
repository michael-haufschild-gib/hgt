import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeResponse
import GaloisForLFunctions.HTGeometry.UnitWaveDuhamelDerivative
/-! Actual first time derivative and gained spatial inverse frequency of the principal responses. -/
open MeasureTheory Set GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

def principalEffectiveForcing (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) : FourierRealL2 :=
  principalTimeForcing q branch a i τ+principalWavePotentialOp q i (principalTimeResponse q branch a i τ)

theorem principalEffectiveForcing_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (principalEffectiveForcing q branch a i) :=
  (principalTimeForcing_continuous q branch a i).add
    ((principalWavePotentialOp q i).continuous.comp (principalTimeResponse_continuous q branch a i))

/-- The source and complex potential are retained in one genuine physical retarded convolution. -/
theorem principalTimeResponse_convolution (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    principalTimeResponse q branch a i = unitWaveDuhamel (principalEffectiveForcing q branch a i) := by
  funext τ
  rw [principalTimeResponse_duhamel,unitWaveDuhamel,unitWaveDuhamel]
  simp only [principalEffectiveForcing,map_add]
  symm
  apply intervalIntegral.integral_add
  · exact (unitWaveSine_continuous_comp (fun σ : ℝ => τ-σ) _ (continuous_const.sub continuous_id)
      (principalTimeForcing_continuous q branch a i)).intervalIntegrable 0 τ
  · exact (unitWaveSine_continuous_comp (fun σ : ℝ => τ-σ) _ (continuous_const.sub continuous_id)
      ((principalWavePotentialOp q i).continuous.comp
        (principalTimeResponse_continuous q branch a i))).intervalIntegrable 0 τ

theorem principalTimeResponse_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    HasDerivAt (principalTimeResponse q branch a i)
      (∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (principalEffectiveForcing q branch a i σ)) τ := by
  rw [principalTimeResponse_convolution]
  exact unitWaveDuhamel_hasDerivAt _ (principalEffectiveForcing_continuous q branch a i) τ

theorem principalTimeResponse_deriv_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (deriv (principalTimeResponse q branch a i)) := by
  rw [principalTimeResponse_convolution]
  exact unitWaveDuhamel_deriv_continuous _ (principalEffectiveForcing_continuous q branch a i)

/-- Both physical Cauchy data at the source onset are zero. -/
theorem principalTimeResponse_initial_data (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    principalTimeResponse q branch a i 0 = 0 ∧ deriv (principalTimeResponse q branch a i) 0 = 0 := by
  refine ⟨principalTimeResponse_zero_of_nonpos q branch a i 0 le_rfl,?_⟩
  rw [(principalTimeResponse_hasDerivAt q branch a i 0).deriv,intervalIntegral.integral_same]

/-- The actual principal response gains the spatial inverse-frequency regularity required for a trace proof. -/
theorem principalTimeResponse_freqInv (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeResponse q branch a i τ = kgFreqInvOp (((2*Real.pi)⁻¹:ℝ) •
      ∫ σ in (0:ℝ)..τ, kgSinOp (2*Real.pi*(τ-σ)) (principalEffectiveForcing q branch a i σ)) := by
  rw [principalTimeResponse_convolution]
  exact unitWaveDuhamel_freqInv _ (principalEffectiveForcing_continuous q branch a i) τ

end
end RHTower.D4BMJointSource
