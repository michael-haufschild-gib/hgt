import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFourierCompletedValue
import Mathlib.Analysis.Meromorphic.Complex

/-! The literal completion factors are meromorphic and analytic at every nonreal physical argument. -/
open Complex Set
namespace RHTower.D4BMJointSource
noncomputable section

/-- The unchanged completion factor is meromorphic at every complex argument. -/
theorem nativeCompletedLambda_meromorphic (s : ℂ) : MeromorphicAt reflectedCompletedLambda s := by
  have hz : MeromorphicAt riemannZeta s := by
    by_cases hs : s=1
    · subst s
      exact GaloisForLFunctions.meromorphicAt_riemannZeta_one
    · exact (analyticOn_riemannZeta s hs).meromorphicAt
  have hp : Differentiable ℂ (fun z : ℂ => (Real.pi:ℂ)^(-z/2)) :=
    (differentiable_id.neg.div_const (2:ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hg : MeromorphicAt (fun z : ℂ => Complex.Gamma (z/2)) s :=
    (Meromorphic.Gamma (s/2)).comp_analyticAt (g := fun z : ℂ => z/2) (x := s)
      (analyticAt_id.div_const)
  exact (((hp.analyticAt s).meromorphicAt.mul hg).mul hz)

/-- Every nonreal argument is an analytic point of the original completion factor. -/
theorem nativeCompletedLambda_analytic {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ reflectedCompletedLambda s := by
  have hs1 : s ≠ 1 := by intro h; exact hs (by rw [h]; rfl)
  exact (Gammaℝ_analyticAt (gammaR_ne_zero_of_im_ne hs)).mul (analyticOn_riemannZeta s hs1)

/-- The original completion vanishes at each actual Xi source. -/
theorem nativeCompletedLambda_at_xi (q : XiZeroCopy) : reflectedCompletedLambda (q.1:ℂ) = 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hne1 : (q.1:ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
    linarith [hstrip.2]
  have hz := (xi_eq_zero_iff hstrip.1 hne1).mp (xi_eq_zero_of_mem_divisor_support q.1)
  rw [reflectedCompletedLambda,hz,mul_zero]

/-- The reflected completion prefactor in the original physical cutoff correction is nonzero. -/
theorem nativeCompletedLambda_before_xi_ne_zero (q : XiZeroCopy) :
    reflectedCompletedLambda ((q.1:ℂ)-1) ≠ 0 := by
  have hi : ((q.1:ℂ)-1).im ≠ 0 := by simpa using xi_divisor_support_im_ne_zero q.1
  have h0 : (q.1:ℂ)-1 ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have he : reflectedCompletedLambda ((q.1:ℂ)-1) = completedRiemannZeta ((q.1:ℂ)-1) := by
    rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero h0]
    field_simp [gammaR_ne_zero_of_im_ne hi]
  have hr : 1 < (2-(q.1:ℂ)).re := by
    change 1 < 2-(q.1:ℂ).re
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  have hn : 2-(q.1:ℂ) ≠ 0 := by
    intro h
    have hj : (2-(q.1:ℂ)).im ≠ 0 := by simpa using neg_ne_zero.mpr (xi_divisor_support_im_ne_zero q.1)
    exact hj (by rw [h]; rfl)
  rw [he,← completedRiemannZeta_one_sub ((q.1:ℂ)-1),
    show 1-((q.1:ℂ)-1)=2-(q.1:ℂ) by ring]
  intro hz
  apply riemannZeta_ne_zero_of_one_lt_re hr
  rw [riemannZeta_def_of_ne_zero hn,hz,zero_div]

end
end RHTower.D4BMJointSource
