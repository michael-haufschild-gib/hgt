import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePrincipalMellinValue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeLambdaMeromorphy

/-! A meromorphic continuation is identified with the complete original native period in its convergence chamber. -/
open Complex MeasureTheory Set
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

/-- The derived full period, retaining both original principal corrections and their completion factors. -/
def nativePeriodContinuation (q : XiZeroCopy) (s : ℂ) : ℂ :=
  (reflectedCompletedLambda (s+2*center q)*reflectedCompletedLambda s^(2 : ℕ)*
    reflectedCompletedLambda (s-2*center q))/2+
  reflectedCompletedLambda (2*s)*nativePrincipalMomentContinuation q (s-1)+
  reflectedCompletedLambda (2*s-1)*nativePrincipalMomentContinuation q (-s)

/-- The constructed continuation agrees with the actual original quotient integral in its proved chamber. -/
theorem nativePeriodContinuation_eq_original (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    nativePeriodContinuation q s = scalarResidualPeriod q (s-1/2) := by
  rw [scalarResidualPeriod_fourLambda_with_cutoff q hq s hs,
    nativePrincipalRemainder_mellin_value q s hs,nativeSquareCutoffHeight_mellin_value q s hs]
  unfold nativePeriodContinuation
  ring

/-- The source-identified full period expression is meromorphic at every complex testing parameter. -/
theorem nativePeriodContinuation_meromorphic (q : XiZeroCopy) (s : ℂ) :
    MeromorphicAt (nativePeriodContinuation q) s := by
  have hl (a b : ℂ) : MeromorphicAt (fun z : ℂ => reflectedCompletedLambda (a*z+b)) s :=
    (nativeCompletedLambda_meromorphic (a*s+b)).comp_analyticAt
      (g := fun z : ℂ => a*z+b) (x := s) ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
  have hm (a b : ℂ) : MeromorphicAt (fun z : ℂ => nativePrincipalMomentContinuation q (a*z+b)) s :=
    (nativePrincipalMomentContinuation_meromorphic q (a*s+b)).comp_analyticAt
      (g := fun z : ℂ => a*z+b) (x := s) ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
  have hp : MeromorphicAt (fun z : ℂ => reflectedCompletedLambda (z+2*center q)) s := by
    simpa only [one_mul] using hl 1 (2*center q)
  have h0 : MeromorphicAt reflectedCompletedLambda s := by simpa using hl 1 0
  have hn : MeromorphicAt (fun z : ℂ => reflectedCompletedLambda (z-2*center q)) s := by
    simpa only [one_mul,sub_eq_add_neg,neg_mul] using hl 1 (-2*center q)
  have h2 : MeromorphicAt (fun z : ℂ => reflectedCompletedLambda (2*z)) s := by simpa using hl 2 0
  have h21 : MeromorphicAt (fun z : ℂ => reflectedCompletedLambda (2*z-1)) s := by
    simpa only [sub_eq_add_neg] using hl 2 (-1)
  have hm1 : MeromorphicAt (fun z : ℂ => nativePrincipalMomentContinuation q (z-1)) s := by
    simpa only [one_mul,sub_eq_add_neg] using hm 1 (-1)
  have hmn : MeromorphicAt (fun z : ℂ => nativePrincipalMomentContinuation q (-z)) s := by
    simpa only [neg_one_mul,add_zero] using hm (-1) 0
  exact (((((hp.mul (h0.pow 2)).mul hn).div analyticAt_const.meromorphicAt).add
    (h2.mul hm1)).add (h21.mul hmn))

end
end RHTower.D4BMJointSource
