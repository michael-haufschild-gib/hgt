import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalPrincipalNoncollision
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalSourceCoefficient
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedPrincipal

/-! The retained principal responses are analytic at the actual same-copy physical target poles. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Away from its actual source and connection poles, the original principal response is analytic, not merely meromorphic. -/
theorem continuedPrincipalDifference_analyticAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (i : Fin 3)
    (hs : w-2*physicalRate q branch ≠ 0) (hc : connection w (principalFrequency q i) ≠ 0)
    (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => continuedPrincipalDifference q branch v a i t) w := by
  have hN := (clearedPrincipalDifference_analyticAt q branch w a hw hwr i t ht).1
  have hC := connection_frequency_analyticAt w (principalFrequency q i) hw
  have hS : AnalyticAt ℂ (fun v : ℂ => v-2*physicalRate q branch) w := by fun_prop
  have hD : AnalyticAt ℂ (fun v => principalClearingFactor q branch v i) w := hS.neg.mul hC
  have hD0 : principalClearingFactor q branch w i ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hs) hc
  apply (hN.div hD hD0).congr
  filter_upwards [hS.continuousAt.eventually_ne hs,hC.continuousAt.eventually_ne hc] with v hvs hvc
  simp only [Pi.div_apply]
  rw [clearedPrincipalDifference_eq q branch v a i hvs hvc t]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (neg_ne_zero.mpr hvs) hvc)

/-- All three literal principal corrections are regular at both fundamental resonances of their source copy. -/
theorem physicalFundamental_principal_analyticAt (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (i : Fin 3) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => continuedPrincipalDifference q branch v a i t) (physicalFundamentalFrequency q side) := by
  have hw := physicalFundamentalFrequency_strip q side
  exact continuedPrincipalDifference_analyticAt q branch _ a hw.1 (abs_lt.mp hw.2).1 i
    (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side)
    (physicalFundamental_principal_connection_ne_zero q side i) t ht

/-- The entire retained principal part of the finite response assembly is analytic at each actual target pole. -/
theorem physicalSelfPrincipalResponse_analyticAt (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => physicalSelfPrincipalResponse q branch v a t) (physicalFundamentalFrequency q side) := by
  unfold physicalSelfPrincipalResponse
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (physicalFundamental_principal_analyticAt q branch side a i t ht)

end
end RHTower.D4BMJointSource
