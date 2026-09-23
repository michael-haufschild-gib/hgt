import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJacobiRodrigues
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedOnsetOvertoneSurvival
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalMomentPolynomial

/-! Rodrigues reduction of the original physical overtone source, with fixed angular data. -/
namespace RHTower.D4BMJointSource
open Complex Set D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The terminating Jacobi factor is exactly the original outer radial factor on both ladders. -/
theorem gaussFactor_outer_overtone (w₀ chi z : ℂ) (n : ℕ)
    (hf : w₀=-3/2-Complex.I*chi ∨ w₀=-3/2+Complex.I*chi) :
    gaussFactor (w₀-2*(n:ℂ)) chi true z=
      bmJacobiFactor n (3/2) (w₀-2*(n:ℂ)) z := by
  simp only [gaussFactor,radialSeries,↓reduceIte,outerSeries,bmJacobiFactor,
    Complex.ofReal_div,Complex.ofReal_ofNat,ordinaryHypergeometric]
  apply congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.sum z)
  rcases hf with rfl | rfl
  · have hA : gaussC (-3/2-Complex.I*chi-2*(n:ℂ))-gaussA (-3/2-Complex.I*chi-2*(n:ℂ)) chi =
        (n:ℂ)+3/2+(-3/2-Complex.I*chi-2*(n:ℂ)) := by unfold gaussC gaussA; ring
    have hB : gaussC (-3/2-Complex.I*chi-2*(n:ℂ))-gaussB (-3/2-Complex.I*chi-2*(n:ℂ)) chi =
        -(n:ℂ) := by unfold gaussC gaussB; ring
    rw [hA,hB]
    exact ordinaryHypergeometricSeries_symm _ _ _
  · have hA : gaussC (-3/2+Complex.I*chi-2*(n:ℂ))-gaussA (-3/2+Complex.I*chi-2*(n:ℂ)) chi =
        -(n:ℂ) := by unfold gaussC gaussA; ring
    have hB : gaussC (-3/2+Complex.I*chi-2*(n:ℂ))-gaussB (-3/2+Complex.I*chi-2*(n:ℂ)) chi =
        (n:ℂ)+3/2+(-3/2+Complex.I*chi-2*(n:ℂ)) := by unfold gaussC gaussB; ring
    rw [hA,hB]

private theorem physicalFundamental_root (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

theorem physicalOvertoneFrequency_im_ne_zero (q : XiZeroCopy) (side : Bool) (n : ℕ) :
    (physicalOvertoneFrequency q side n).im≠0 := by
  rw [physicalOvertoneFrequency_eq]
  simpa using (physicalFundamentalFrequency_strip q side).1

/-- The original source core: source rate and angular polynomial remain fixed along the ladder. -/
def physicalOvertoneSourceCore (q : XiZeroCopy) (branch side : Bool) (n : ℕ) (t : ℝ) : ℂ :=
  power (2*physicalRate q branch-physicalOvertoneFrequency q side n) (1+Real.sqrt t)*
    (fundamentalMomentConstant (physicalRate q branch)+
      fundamentalMomentQuadratic (physicalFundamentalFrequency q side) (physicalRate q branch)*(t:ℂ))

/-- Exact source identity at every interior point; no endpoint term is discarded. -/
theorem physicalOvertoneSource_rodrigues (q : XiZeroCopy) (branch side : Bool)
    (n : ℕ) (a T : ℂ) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    (ascPochhammer ℂ n).eval (3/2)*
      (normalizable (physicalOvertoneFrequency q side n) (physicalRadialFrequency q) z*
        sourceProfile (physicalRate q branch) (physicalOvertoneFrequency q side n) a 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) T z)=
      a^(2 : ℕ)*physicalOvertoneSourceCore q branch side n (1-z)*T*
        iteratedDeriv n (bmJacobiSeed n (3/2) (physicalOvertoneFrequency q side n)) (1-z) := by
  let w := physicalOvertoneFrequency q side n
  let w₀ := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  have hf : w₀=-3/2-Complex.I*chi ∨ w₀=-3/2+Complex.I*chi := physicalFundamental_root q side
  have hfactor : gaussFactor w chi true ((1-z:ℝ):ℂ)=
      bmJacobiFactor n (3/2) w ((1-z:ℝ):ℂ) := by
    dsimp only [w,chi]
    rw [physicalOvertoneFrequency_eq]
    exact gaussFactor_outer_overtone _ _ _ n hf
  have hR := bmJacobiDensity_rodrigues n (3/2) w (by norm_num)
    (physicalOvertoneFrequency_im_ne_zero q side n)
    (show 1-z∈Ioo (0:ℝ) 1 from ⟨sub_pos.mpr hz.2,by linarith only [hz.1]⟩)
  have hp : power (w/2) z*power (w/2) z=power w z := by
    dsimp only [power]
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.1.ne')]
    congr 1
    ring
  have hsource : sourceRemainder s w a 1 (reducedGreenGradient chi s 1) T z=
      a^(2 : ℕ)*physicalOvertoneSourceCore q branch side n (1-z)*T := by
    rw [reducedGreenGradient_fundamental w₀ chi s hf]
    dsimp only [sourceRemainder,physicalOvertoneSourceCore,fundamentalMomentConstant,
      fundamentalMomentQuadratic]
    change power (2*s-w) (1+Real.sqrt (1-z))*a^(2 : ℕ)*
      (((5*s^(2 : ℕ)+15*s+4)/4)*1+(1-(z:ℂ))*s*(s-1)/4*
        ((s+2)^(2 : ℕ)*1-((w₀+1)*(w₀+2)/2-(s+1)*(s+2))))*T =
      a^(2 : ℕ)*(power (2*s-w) (1+Real.sqrt (1-z))*
        ((5*s^(2 : ℕ)+15*s+4)/4+s*(s-1)*((s+2)*(2*s+3)-(w₀+1)*(w₀+2)/2)/4*((1-z:ℝ):ℂ)))*T
    push_cast
    ring
  change (ascPochhammer ℂ n).eval (3/2)*(normalizable w chi z*
    sourceProfile s w a 1 (reducedGreenGradient chi s 1) T z)=_
  dsimp only [normalizable,dress,outerFactor,sourceProfile]
  push_cast at hfactor
  rw [hfactor,hsource,hR]
  simp only [bmJacobiDensity,sub_sub_cancel,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num only [show (3/2:ℂ)-1=1/2 by norm_num]
  push_cast
  linear_combination (ascPochhammer ℂ n).eval (3/2)*power (1/2) (1-z)*
    bmJacobiFactor n (3/2) w (1-(z:ℂ))*
    (a^(2 : ℕ)*physicalOvertoneSourceCore q branch side n (1-z)*T)*hp

end
end RHTower.D4BMJointSource
