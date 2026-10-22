import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceAmplitudeLinearity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalSelfResponseContinuation

/-! The complete physical response isolates one exact angular coefficient with all cutoff channels retained. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Actual residual angular period minus all three exact principal-channel corrections. -/
def physicalSelfSourceCoefficient (q : XiZeroCopy) : ℂ :=
  scalarResidualPeriod q (physicalAngularParameter q)-
    ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
      principalAmplitude q i/physicalAngularGap q q i

/-- The retained original principal responses, before their regularity at the target poles is proved. -/
def physicalSelfPrincipalResponse (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/physicalAngularGap q q i*
    continuedPrincipalDifference q branch w a i t

/-- Exact decomposition of the continued complete physical response; no source or pole coefficient is assigned. -/
theorem continuedPhysicalSelfResponse_decomposition (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) :
    continuedPhysicalSelfResponse q branch w a t =
      physicalSelfSourceCoefficient q*continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q branch) a 1 t+
      physicalSelfPrincipalResponse q branch w a t := by
  let U := continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q branch) a 1 t
  have hU (J : ℂ) : continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q branch) a J t = J*U :=
    continuedReducedGreen_amplitude w (physicalRadialFrequency q) (physicalRate q branch) a J t
  have hD := physicalAngularGapProduct_self_ne_zero q
  have hE (i : Fin 3) : physicalAngularGapCofactor q q i/physicalAngularGapProduct q q =
      (physicalAngularGap q q i)⁻¹ := by
    apply (div_eq_iff hD).mpr
    rw [← physicalAngularGapCofactor_mul q q i]
    field_simp [physicalAngularGap_self_ne_zero q i]
  have hterm (i : Fin 3) :
      (physicalAngularGapCofactor q q i*scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
        (continuedPrincipalDifference q branch w a i t-principalAmplitude q i*U))/physicalAngularGapProduct q q =
      scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/physicalAngularGap q q i*
        continuedPrincipalDifference q branch w a i t-
      (scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*principalAmplitude q i/physicalAngularGap q q i)*U := by
    calc
      _ = (physicalAngularGapCofactor q q i/physicalAngularGapProduct q q)*
          scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
          (continuedPrincipalDifference q branch w a i t-principalAmplitude q i*U) := by ring
      _ = _ := by rw [hE]; ring
  unfold continuedPhysicalSelfResponse clearedPhysicalGreen physicalResolventAssembly
    physicalSelfSourceCoefficient physicalSelfPrincipalResponse
  simp_rw [hU]
  change (physicalAngularGapProduct q q*(scalarResidualPeriod q (physicalAngularParameter q)*U)+
    ∑ i : Fin 3, (physicalAngularGapCofactor q q i*scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i))*
      (continuedPrincipalDifference q branch w a i t-principalAmplitude q i*U))/physicalAngularGapProduct q q = _
  rw [add_div,Finset.sum_div]
  simp_rw [hterm]
  have hmain : physicalAngularGapProduct q q*(scalarResidualPeriod q (physicalAngularParameter q)*U)/
      physicalAngularGapProduct q q = scalarResidualPeriod q (physicalAngularParameter q)*U := by field_simp
  rw [hmain,Finset.sum_sub_distrib,← Finset.sum_mul]
  ring

end
end RHTower.D4BMJointSource
