import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonMomentContinuation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceOuterMomentContinuation
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule

/-! The original radial Green response continued to both fundamental Xi-QNM branches.
Endpoint integration is performed with the actual source, before any QNM specialization. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The continued original response formed from its two actual endpoint moments. -/
def continuedResponse (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  normalizable w chi b*continuedHorizonMoment s chi a J K b w+
    horizon w chi b*continuedOuterMoment s chi a J K b w

/-- The original radial Green response has a meromorphic continuation across the
larger nonreal frequency strip. No endpoint-integrability or continuation premise is supplied. -/
theorem continuedResponse_meromorphicAt (s chi a J K w : ℂ) (hw : w.im ≠ 0) (hwre : -2 < w.re)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) : MeromorphicAt (continuedResponse s chi a J K b) w :=
  ((((normalizable_frequency_entire chi ⟨hb,hb1⟩).analyticAt w).meromorphicAt).mul
    (continuedHorizonMoment_meromorphicAt s chi a J K w hw hwre hb hb1)).add
      ((horizon_frequency_analyticAt w chi hw ⟨hb,hb1⟩).meromorphicAt.mul
        (continuedOuterMoment_meromorphicAt s chi a J K w hw hb hb1))

/-- The continuation agrees with the literal source-forced Green response in its
original convergence chamber, including the fixed smooth onset. -/
theorem continuedResponse_eq_original (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -1 < w.re) (hsource : (2*s).re < w.re) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    continuedResponse s chi a J K b w = response w chi s a J K (onsetTransform (2*s) w) b := by
  rw [continuedResponse,continuedHorizonMoment_eq_original s chi a J K w hw hwre hsource hb hb1,
    continuedOuterMoment_eq_original s chi a J K w hsource hb1.le]
  rfl

private theorem fundamentalQNMLaplace_in_strip (q : XiZeroCopy) :
    ((-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)).im ≠ 0 ∧
      -2 < (-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)).re) ∧
    ((-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)).im ≠ 0 ∧
      -2 < (-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)).re) := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hs := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hs
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
  norm_num
  exact ⟨⟨hq,by linarith [hs.1]⟩,⟨hq,by linarith [hs.2]⟩⟩

/-- Every Xi copy has the original source-forced radial response continued to both
fundamental physical QNM frequencies. Meromorphy alone asserts neither pole incidence nor extinction. -/
theorem continuedResponse_allXi_fundamental_meromorphic (q : XiZeroCopy) (s a J K : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
    ∀ b ∈ Ioo (0:ℝ) 1,
      MeromorphicAt (continuedResponse s (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) a J K b) w := by
  intro w hw b hb
  have hs : w.im ≠ 0 ∧ -2 < w.re := by
    rcases hw with rfl | hw
    · exact (fundamentalQNMLaplace_in_strip q).1
    · rw [Set.mem_singleton_iff] at hw
      subst w
      exact (fundamentalQNMLaplace_in_strip q).2
  exact continuedResponse_meromorphicAt s _ a J K w hs.1 hs.2 hb.1 hb.2

end
end RHTower.D4BMLaplaceRadial
