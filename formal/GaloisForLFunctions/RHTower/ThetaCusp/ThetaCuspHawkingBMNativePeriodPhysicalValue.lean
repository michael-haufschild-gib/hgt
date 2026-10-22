import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativePeriodContinuation

/-! The original period continuation is analytic at the physical parameter and retains its reflected correction. -/
open Complex
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

private theorem affine_lambda_physical_analytic (q : XiZeroCopy) (a b c : ℝ) (h : a/2+b ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => reflectedCompletedLambda ((a:ℂ)*z+(b:ℂ)*(q.1:ℂ)+(c:ℂ))) ((q.1:ℂ)/2) := by
  have hi : ((a:ℂ)*((q.1:ℂ)/2)+(b:ℂ)*(q.1:ℂ)+(c:ℂ)).im ≠ 0 := by
    have he : ((a:ℂ)*((q.1:ℂ)/2)+(b:ℂ)*(q.1:ℂ)+(c:ℂ)).im = (a/2+b)*(q.1:ℂ).im := by
      simp
      ring
    rw [he]
    exact mul_ne_zero h (xi_divisor_support_im_ne_zero q.1)
  exact (nativeCompletedLambda_analytic hi).comp
    (f := fun z : ℂ => (a:ℂ)*z+(b:ℂ)*(q.1:ℂ)+(c:ℂ)) (x := (q.1:ℂ)/2) (by fun_prop)

private theorem forward_moment_physical_analytic (q : XiZeroCopy) :
    AnalyticAt ℂ (fun z : ℂ => nativePrincipalMomentContinuation q (z-1)) ((q.1:ℂ)/2) := by
  have ht : ∀ j : Fin 3, ((q.1:ℂ)/2-1)+nativePrincipalPowerExponent q j ≠ 0 := by
    intro j
    fin_cases j <;> intro h <;> apply xi_divisor_support_im_ne_zero q.1
    all_goals
      have he := congrArg Complex.im h
      norm_num [nativePrincipalPowerExponent] at he
      linarith
  exact (nativePrincipalMomentContinuation_analytic q _ ht).comp
    (f := fun z : ℂ => z-1) (x := (q.1:ℂ)/2) (analyticAt_id.sub analyticAt_const)

private theorem reverse_moment_physical_analytic (q : XiZeroCopy) :
    AnalyticAt ℂ (fun z : ℂ => nativePrincipalMomentContinuation q (-z)) ((q.1:ℂ)/2) := by
  have ht : ∀ j : Fin 3, -((q.1:ℂ)/2)+nativePrincipalPowerExponent q j ≠ 0 := by
    intro j
    fin_cases j <;> intro h <;> apply xi_divisor_support_im_ne_zero q.1
    all_goals
      have he := congrArg Complex.im h
      norm_num [nativePrincipalPowerExponent] at he
      linarith
  exact (nativePrincipalMomentContinuation_analytic q _ ht).comp
    (f := fun z : ℂ => -z) (x := (q.1:ℂ)/2) analyticAt_id.neg

/-- The complete source-identified period continuation has an analytic physical value at every Xi source. -/
theorem nativePeriodContinuation_physical_analytic (q : XiZeroCopy) :
    AnalyticAt ℂ (nativePeriodContinuation q) ((q.1:ℂ)/2) := by
  have hp : AnalyticAt ℂ (fun z : ℂ => reflectedCompletedLambda (z+2*center q)) ((q.1:ℂ)/2) := by
    convert affine_lambda_physical_analytic q 1 2 (-1) (by norm_num) using 1
    funext z
    congr 1
    dsimp [D4BMGlobalAngularResponse.center]
    push_cast
    ring
  have hm : AnalyticAt ℂ (fun z : ℂ => reflectedCompletedLambda (z-2*center q)) ((q.1:ℂ)/2) := by
    convert affine_lambda_physical_analytic q 1 (-2) 1 (by norm_num) using 1
    funext z
    congr 1
    dsimp [D4BMGlobalAngularResponse.center]
    push_cast
    ring
  have h0 : AnalyticAt ℂ reflectedCompletedLambda ((q.1:ℂ)/2) := by
    simpa using affine_lambda_physical_analytic q 1 0 0 (by norm_num)
  have h2 : AnalyticAt ℂ (fun z : ℂ => reflectedCompletedLambda (2*z)) ((q.1:ℂ)/2) := by
    simpa using affine_lambda_physical_analytic q 2 0 0 (by norm_num)
  have h21 : AnalyticAt ℂ (fun z : ℂ => reflectedCompletedLambda (2*z-1)) ((q.1:ℂ)/2) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,Complex.ofReal_neg,mul_zero,zero_mul,
      add_zero,sub_eq_add_neg,Complex.ofReal_one] using affine_lambda_physical_analytic q 2 0 (-1) (by norm_num)
  exact (((hp.mul (h0.pow 2)).mul hm).div_const.add
    (h2.mul (forward_moment_physical_analytic q))).add
    (h21.mul (reverse_moment_physical_analytic q))

/-- At the physical parameter only the forward principal correction is killed by the original Xi zero. -/
theorem nativePeriodContinuation_physical_value (q : XiZeroCopy) :
    nativePeriodContinuation q ((q.1:ℂ)/2) =
      (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^(2 : ℕ)*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2+
      reflectedCompletedLambda ((q.1:ℂ)-1)*nativePrincipalMomentContinuation q (-((q.1:ℂ)/2)) := by
  unfold nativePeriodContinuation
  rw [show 2*((q.1:ℂ)/2)=(q.1:ℂ) by ring,nativeCompletedLambda_at_xi,zero_mul,add_zero]
  rw [show (q.1:ℂ)/2+2*center q=5*(q.1:ℂ)/2-1 by dsimp [D4BMGlobalAngularResponse.center]; ring,
    show (q.1:ℂ)/2-2*center q=1-3*(q.1:ℂ)/2 by dsimp [D4BMGlobalAngularResponse.center]; ring]

/-- Equality with the diagonal alone requires exactly the displayed remaining original cutoff moment to vanish. -/
theorem nativePhysicalPeriod_eq_diagonal_iff (q : XiZeroCopy) :
    nativePeriodContinuation q ((q.1:ℂ)/2) =
      (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^(2 : ℕ)*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2 ↔
      nativePrincipalMomentContinuation q (-((q.1:ℂ)/2)) = 0 := by
  rw [nativePeriodContinuation_physical_value,add_eq_left,mul_eq_zero]
  simp only [nativeCompletedLambda_before_xi_ne_zero q,false_or]

end
end RHTower.D4BMJointSource
