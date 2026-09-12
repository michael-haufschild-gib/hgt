import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceEndpointPolynomial
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalBoundaryRecovery
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalNonstationarySource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingPairingEndpoint

/-! All-height survival of the original intrinsic horizon contact, with the fixed onset retained. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

theorem physicalFundamentalSourceCore_endpoint_ne_zero (q : XiZeroCopy) (a : ℂ) (ha : a ≠ 0) :
    fundamentalSourceCore (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a 0 ≠ 0 := by
  let w := physicalFundamentalFrequency q true
  let s := D4BMModularCore.physicalRate q true
  have hs := physicalNonstationaryFrequency_strip q
  have hp := nonstationarySourceEndpointPolynomial_ne_zero (w+1)
    (by dsimp only [w]; simp only [Complex.add_re,Complex.one_re]; constructor <;> linarith [hs.1,hs.2])
  have he : nonstationarySourceEndpointPolynomial (w+1)=
      4*(fundamentalMomentConstant s+fundamentalMomentQuadratic w s) := by
    dsimp only [w,s]
    rw [physicalNonstationaryRate,nonstationarySourceConstant,nonstationarySourceQuadratic]
    unfold nonstationarySourceEndpointPolynomial
    ring
  have hcoef : fundamentalMomentConstant s+fundamentalMomentQuadratic w s ≠ 0 := by
    intro hz
    apply hp
    rw [he,hz,mul_zero]
  change fundamentalSourceCore w s a 0 ≠ 0
  rw [fundamentalSourceCore_zero_polynomial]
  exact mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (by norm_num)))
    (pow_ne_zero _ ha)) hcoef

/-- The unchanged angular-gradient prescription gives the same original endpoint source. -/
theorem physicalFundamentalSourceRemainder_endpoint (q : XiZeroCopy) (a : ℂ) :
    let w := physicalFundamentalFrequency q true
    let s := D4BMModularCore.physicalRate q true
    sourceRemainder s w a 1 (reducedGreenGradient (physicalRadialFrequency q) s 1) 1 0=
      fundamentalSourceCore w s a 0 := by
  let w := physicalFundamentalFrequency q true
  let s := D4BMModularCore.physicalRate q true
  have hf : w=-3/2-Complex.I*physicalRadialFrequency q ∨ w=-3/2+Complex.I*physicalRadialFrequency q := by
    left
    exact physicalFundamentalFrequency_connection_root q true
  dsimp only
  rw [reducedGreenGradient_fundamental w _ s hf]
  simp only [fundamentalSourceCore,sub_zero,power,Complex.ofReal_one,Complex.one_cpow,one_mul]
  rfl

/-- The retained intrinsic slope cannot disappear at any physical Xi height. -/
theorem physicalFundamentalIntrinsicContact_ne_zero (q : XiZeroCopy) (a : ℂ) (ha : a ≠ 0) :
    fundamentalSourceCore (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a 0/
      (2*(physicalFundamentalFrequency q true+1)) ≠ 0 := by
  have hw := (physicalFundamentalFrequency_strip q true).1
  have hv : physicalFundamentalFrequency q true+1 ≠ 0 := by
    intro hz
    apply hw
    have hi := congrArg Complex.im hz
    simpa only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] using hi
  exact div_ne_zero (physicalFundamentalSourceCore_endpoint_ne_zero q a ha)
    (mul_ne_zero (by norm_num) hv)

/-- This is the existing incoming-response slope, with its original onset factor displayed. -/
theorem physicalFundamentalIncomingSlope_factor (q : XiZeroCopy) (a : ℂ) :
    let w := physicalFundamentalFrequency q true
    let s := D4BMModularCore.physicalRate q true
    incomingResponseSlope s a 1 (reducedGreenGradient (physicalRadialFrequency q) s 1) w=
      (fundamentalSourceCore w s a 0/(2*(w+1)))*continuedOnset s w := by
  dsimp only
  unfold incomingResponseSlope
  rw [physicalFundamentalSourceRemainder_endpoint]
  unfold continuedOnset
  ring

/-- All-height intrinsic cancellation is closed; the specified onset is kept as the exact remaining factor. -/
theorem physicalFundamentalIncomingSlope_zero_iff (q : XiZeroCopy) (a : ℂ) (ha : a ≠ 0) :
    let w := physicalFundamentalFrequency q true
    let s := D4BMModularCore.physicalRate q true
    incomingResponseSlope s a 1 (reducedGreenGradient (physicalRadialFrequency q) s 1) w=0 ↔
      continuedOnset s w=0 := by
  dsimp only
  rw [physicalFundamentalIncomingSlope_factor,mul_eq_zero]
  exact or_iff_right (physicalFundamentalIntrinsicContact_ne_zero q a ha)

/-- Near the original horizon, the actual analytically continued quotient derivative survives
exactly when the unchanged onset factor does. This remains valid at the target connection zero. -/
theorem physicalFundamentalIncomingTransport_survival_iff (q : XiZeroCopy) (a : ℂ) (ha : a ≠ 0) :
    let w := physicalFundamentalFrequency q true
    let s := D4BMModularCore.physicalRate q true
    (∀ᶠ b : ℝ in 𝓝[>] 0,
      incomingSourceTransport s (physicalRadialFrequency q) a 1
        (reducedGreenGradient (physicalRadialFrequency q) s 1) w b ≠ 0) ↔
      continuedOnset s w ≠ 0 := by
  let w := physicalFundamentalFrequency q true
  let s := D4BMModularCore.physicalRate q true
  let K := reducedGreenGradient (physicalRadialFrequency q) s 1
  have hw := physicalFundamentalFrequency_strip q true
  change (∀ᶠ b : ℝ in 𝓝[>] 0, incomingSourceTransport s (physicalRadialFrequency q) a 1 K w b ≠ 0) ↔
    continuedOnset s w ≠ 0
  constructor
  · intro he hz
    have hall : ∀ b : ℝ, incomingSourceTransport s (physicalRadialFrequency q) a 1 K w b=0 := by
      intro b
      change _*continuedOnset s w/_=0
      rw [hz,mul_zero,zero_div]
    have hf : ∀ᶠ b : ℝ in 𝓝[>] 0, False := he.mono (fun b hb => hb (hall b))
    exact Filter.eventually_const.mp hf
  · intro hz
    have hne : incomingResponseSlope s a 1 K w ≠ 0 := by
      intro he
      exact hz ((physicalFundamentalIncomingSlope_zero_iff q a ha).mp he)
    have hl := incomingSourceTransport_tendsto_horizon s (physicalRadialFrequency q) a 1 K w
      hw.1 ((abs_lt.mp hw.2).1)
    change Tendsto (incomingSourceTransport s (physicalRadialFrequency q) a 1 K w)
      (𝓝[>] (0:ℝ)) (𝓝 (incomingResponseSlope s a 1 K w)) at hl
    exact hl.eventually_ne hne

/-- No member of the four physical source/frequency choices can lose both retained moments. -/
theorem physicalFundamentalJacobi_second_fourth_survival (q : XiZeroCopy) (branch side : Bool) :
    let w := physicalFundamentalFrequency q side
    let s := D4BMModularCore.physicalRate q branch
    fundamentalJacobiMoment 2 w s ≠ 0 ∨ fundamentalJacobiMoment 4 w s ≠ 0 := by
  let w := physicalFundamentalFrequency q side
  let s := D4BMModularCore.physicalRate q branch
  have hw := physicalFundamentalFrequency_strip q side
  have hv : w+1 ≠ 0 := by
    intro hz
    apply hw.1
    have hi := congrArg Complex.im hz
    simpa only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] using hi
  have hd : 2*s-w ≠ 0 := by
    have hq := xi_divisor_support_im_ne_zero q.1
    dsimp only [w,s]
    rw [physicalFundamentalFrequency_eq]
    cases branch <;> cases side <;> simp only [D4BMModularCore.physicalRate,Bool.false_eq_true,↓reduceIte]
    all_goals
      intro hz
      have hi := congrArg Complex.im hz
      norm_num [Complex.mul_im,Complex.div_im] at hi
      apply hq
      linarith
  have he := fundamentalJacobiMoment_boundary_recovery w s ((abs_lt.mp hw.2).1) hv
  dsimp only at he ⊢
  by_cases h2 : fundamentalJacobiMoment 2 w s=0
  · right
    intro h4
    rw [h2,h4,mul_zero,mul_zero,sub_self] at he
    exact (mul_ne_zero (by norm_num : (2:ℂ)≠0) hd) he.symm
  · exact Or.inl h2

end
end RHTower.D4BMJointSource
