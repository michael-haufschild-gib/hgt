import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSourcePeriodAttachment

/-! The complete source-derived entire numerator belongs to the original canonical QNM action. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore D4BMOriginalSourceResolvent D4BMOriginalCanonicalAction
  GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

theorem fundamentalSourceTortoiseMoment_monodromy (w s a : ℂ)
    (hw : -2<w.re) (hw1 : w+1≠0) (hE : Complex.exp (2*Real.pi*I*w)-1≠0) :
    (Complex.exp (2*Real.pi*I*w)-1)^(2 : ℕ)*fundamentalSourceTortoiseMoment w s a=
      (Complex.exp (2*Real.pi*I*w)-1)*fundamentalSourceTortoiseContour w s a-
        Real.pi*I*Complex.exp (2*Real.pi*I*w)*fundamentalSourceContour w s a := by
  have h2 := fundamentalJacobiTortoiseMoment_monodromy 2 w s hw hw1 hE
  have h4 := fundamentalJacobiTortoiseMoment_monodromy 4 w s hw hw1 hE
  dsimp only [fundamentalSourceTortoiseMoment,fundamentalSourceTortoiseContour,fundamentalSourceContour]
  linear_combination 2*a^(2 : ℕ)*fundamentalMomentConstant s*h2+
    2*a^(2 : ℕ)*fundamentalMomentQuadratic w s*h4

theorem fundamentalSourceForcingMoment_monodromy (w s a : ℂ)
    (hw : -2<w.re) (hw1 : w+1≠0) :
    fundamentalSourceForcingContour w s a=
      (Complex.exp (2*Real.pi*I*w)-1)*fundamentalSourceForcingMoment w s a := by
  dsimp only [fundamentalSourceForcingContour,fundamentalSourceForcingMoment,
    fundamentalJacobiForcingContour,fundamentalJacobiForcingMoment]
  simp_rw [fundamentalJacobiContour_eq_moment _ _ _ hw hw1]
  ring

theorem physicalFundamentalSourceMoment_monodromy (q : XiZeroCopy) (br side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    fundamentalSourceContour w s a=
      (Complex.exp (2*Real.pi*I*w)-1)*fundamentalSourceMoment w s a := by
  dsimp only
  have hw := physicalFundamentalFrequency_strip q side
  have hw1 : physicalFundamentalFrequency q side+1≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  rw [physicalFundamentalSourceMoment_polynomial q br side a]
  dsimp only [fundamentalSourceContour]
  simp_rw [fundamentalJacobiContour_eq_moment _ _ _ (abs_lt.mp hw.2).1 hw1]
  ring

theorem physicalFundamentalFrequency_monodromy_ne_zero (q : XiZeroCopy) (side : Bool) :
    Complex.exp (2*Real.pi*I*physicalFundamentalFrequency q side)-1≠0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [Complex.norm_exp,norm_one,Real.exp_eq_one_iff] at he
  have hi := (physicalFundamentalFrequency_strip q side).1
  apply hi
  norm_num [Complex.mul_re,Complex.mul_im] at he
  nlinarith [Real.pi_pos]

/-- Exact attachment of the full contour numerator to the original physical
canonical action. No matching, continuation, nonvanishing or finite-part
identification premise is supplied. -/
theorem canonicalQNMValue_cleared_eq_fundamentalContour (q : XiZeroCopy) :
    let w := physicalFundamentalFrequency q true
    (Complex.exp (2*Real.pi*I*w)-1)^(2 : ℕ)*(5*w+8)^(2 : ℕ)*canonicalQNMValue q true true 1=
      -(physicalAngularParameter q^(2 : ℕ)-1/4)*physicalSelfSourceCoefficient q*
        fundamentalCanonicalContourNumerator w := by
  let w := physicalFundamentalFrequency q true
  let s := physicalRate q true
  have hw := physicalFundamentalFrequency_strip q true
  have hwr : -2<w.re := (abs_lt.mp hw.2).1
  have hw1 : w+1≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  have hs : s=-2*w-4 := by
    dsimp only [s,w,physicalRate]
    rw [physicalFundamentalFrequency_eq]
    simp only [↓reduceIte]
    ring
  have hgap : w-2*s=5*w+8 := by rw [hs];ring
  have hmu : physicalAngularParameter q^(2 : ℕ)-1/4=(w+1)*(w+2) := by
    dsimp only [w]
    rw [physicalAngularParameter_eq,physicalFundamentalFrequency_eq]
    simp only [↓reduceIte]
    ring
  have hT := clearedOnset_source_gap s w
    (physicalFundamentalFrequency_sub_sourceRate_ne_zero q true true)
  have hD := clearedOnset_source_gap_derivative s w
    (physicalFundamentalFrequency_sub_sourceRate_ne_zero q true true)
  rw [hgap] at hT hD
  have hM := physicalFundamentalSourceMoment_monodromy q true true (1:ℂ)
  have hX := fundamentalSourceTortoiseMoment_monodromy w s 1 hwr hw1
    (physicalFundamentalFrequency_monodromy_ne_zero q true)
  have hY := fundamentalSourceForcingMoment_monodromy w s 1 hwr hw1
  have hC := canonicalQNMValue_eq_source_periods q true true (1:ℂ)
  change canonicalQNMValue q true true 1=-(physicalAngularParameter q^(2 : ℕ)-1/4)*physicalSelfSourceCoefficient q*
    ((physicalAngularParameter q^(2 : ℕ)-1/4-2)*(deriv (continuedOnset s) w*fundamentalSourceMoment w s 1+
      continuedOnset s w*fundamentalSourceTortoiseMoment w s 1)+
        continuedOnset s w*fundamentalSourceForcingMoment w s 1) at hC
  change fundamentalSourceContour w s 1=(Complex.exp (2*Real.pi*I*w)-1)*fundamentalSourceMoment w s 1 at hM
  dsimp only
  change (Complex.exp (2*Real.pi*I*w)-1)^(2 : ℕ)*(5*w+8)^(2 : ℕ)*canonicalQNMValue q true true 1=
    -(physicalAngularParameter q^(2 : ℕ)-1/4)*physicalSelfSourceCoefficient q*fundamentalCanonicalContourNumerator w
  rw [hC,hmu,fundamentalCanonicalContourNumerator,← hs,← hX,hM,hY,← hD,hT]
  ring

end
end RHTower.D4BMJointSource
