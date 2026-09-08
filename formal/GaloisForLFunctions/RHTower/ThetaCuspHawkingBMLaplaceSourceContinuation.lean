import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceFrequencyContinuation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceProfile
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalBlackHoleHypergeometricJostIncidence

/-! Meromorphic continuation of the actual source-weighted radial Green integrands.
The full endpoint moments and the joint angular response are separate obligations. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Fixed radial/angular amplitudes give an entire source profile at every physical interior point. -/
theorem sourceProfile_frequency_entire (s a J K T : ℂ) {z : ℝ} (hz : 0 < z) :
    Differentiable ℂ (fun w => sourceProfile s w a J K T z) := by
  have hpow := (power_exponent_entire hz).comp
    (show Differentiable ℂ (fun w : ℂ => w/2) by fun_prop)
  have hr := (power_exponent_entire (show 0 < 1+Real.sqrt (1-z) by positivity)).comp
    (show Differentiable ℂ (fun w : ℂ => 2*s-w) by fun_prop)
  have h := hpow.mul (((hr.mul_const (a^2)).mul_const
    (((5*s^2+15*s+4)/4)*J+(1-(z:ℂ))*s*(s-1)/4*((s+2)^2*J-K))).mul_const T)
  simpa only [sourceProfile,sourceRemainder,Function.comp_def,Pi.mul_def] using! h

/-- Continuation retains the fixed smooth onset correction and its original source pole. -/
def continuedSourceProfile (s a J K : ℂ) (w : ℂ) (z : ℝ) : ℂ :=
  sourceProfile s w a J K (1/(w-2*s)+onsetCorrection (2*s) w) z

/-- Equality to the actual source transform is proved in its convergence chamber. -/
theorem continuedSourceProfile_eq (s a J K w : ℂ) (hw : (2*s).re < w.re) (z : ℝ) :
    continuedSourceProfile s a J K w z = sourceProfile s w a J K (onsetTransform (2*s) w) z := by
  rw [onsetTransform_eq (2*s) w hw]
  rfl

/-- The actual smooth-onset source profile continues meromorphically, with all fixed source factors retained. -/
theorem continuedSourceProfile_meromorphic (s a J K : ℂ) {z : ℝ} (hz : 0 < z) :
    Meromorphic (fun w => continuedSourceProfile s a J K w z) := by
  intro w
  have hp := ((sourceProfile_frequency_entire s a J K 1 hz).analyticAt w).meromorphicAt
  have hi : MeromorphicAt (fun u : ℂ => 1/(u-2*s)) w :=
    (show AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) w from analyticAt_const).meromorphicAt.div ((show AnalyticAt ℂ (fun u : ℂ => u-2*s) w by fun_prop).meromorphicAt)
  have hc := ((onsetCorrection_entire (2*s)).analyticAt w).meromorphicAt
  have h := hp.mul (hi.add hc)
  have he : (fun u => sourceProfile s u a J K 1 z * (1/(u-2*s)+onsetCorrection (2*s) u)) =
      (fun u => continuedSourceProfile s a J K u z) := by
    funext u
    unfold continuedSourceProfile sourceProfile sourceRemainder
    ring
  simp only [Pi.mul_def,Pi.add_def] at h
  rw [he] at h
  exact h

/-- Both original endpoint Green integrands have frequency-meromorphic germs in the
physical interior, including their full normalization and fixed onset. This does not exchange
continuation with either improper endpoint integral. -/
theorem sourceGreenIntegrands_frequency_meromorphicAt (w chi s a J K : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo 0 1) :
    MeromorphicAt (fun u => horizon u chi z*continuedSourceProfile s a J K u z/(-connection u chi)) w ∧
    MeromorphicAt (fun u => normalizable u chi z*continuedSourceProfile s a J K u z/(-connection u chi)) w := by
  have hs := continuedSourceProfile_meromorphic s a J K hz.1 w
  have hc := (connection_frequency_analyticAt w chi hw).meromorphicAt.neg
  exact ⟨((horizon_frequency_analyticAt w chi hw hz).meromorphicAt.mul hs).div hc,
    (((normalizable_frequency_entire chi hz).analyticAt w).meromorphicAt.mul hs).div hc⟩

private theorem xiQNM_laplace_im_ne_zero (n : ℕ) (q : XiZeroCopy) :
    (-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)).im ≠ 0 ∧
    (-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)).im ≠ 0 := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,Complex.mul_im,Complex.sub_re,Complex.neg_re,
    Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_im,Complex.mul_re,
    Complex.add_re,Complex.div_re]
  norm_num
  exact hq

/-- Every Xi copy on either physical QNM branch admits the original source-weighted
radial Green germs. No RH, continuation, nonresonance, or numerator-nonvanishing premise is used. -/
theorem sourceGreenIntegrands_allXi_qnm_meromorphic (n : ℕ) (q : XiZeroCopy) (s a J K : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)} : Set ℂ),
    ∀ z ∈ Ioo (0:ℝ) 1,
      MeromorphicAt (fun u => horizon u (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) z*
        continuedSourceProfile s a J K u z/(-connection u (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)))) w ∧
      MeromorphicAt (fun u => normalizable u (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) z*
        continuedSourceProfile s a J K u z/(-connection u (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)))) w := by
  intro w hw z hz
  have hi : w.im ≠ 0 := by
    rcases hw with rfl | hw
    · exact (xiQNM_laplace_im_ne_zero n q).1
    · rw [Set.mem_singleton_iff] at hw
      subst w
      exact (xiQNM_laplace_im_ne_zero n q).2
  exact sourceGreenIntegrands_frequency_meromorphicAt w _ s a J K hi hz

end
end RHTower.D4BMLaplaceRadial
