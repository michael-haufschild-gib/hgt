import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalSelfResponseContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalNormalizableDomain

/-! Exact original fundamental frequencies and their source-rate separation at every Xi copy. -/
open Complex Set
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The two original physical fundamental QNM frequencies in the Laplace coordinate. -/
def physicalFundamentalFrequency (q : XiZeroCopy) (side : Bool) : ℂ :=
  if side then -I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)
    else -I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)

theorem physicalFundamentalFrequency_connection_root (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side =
      if side then -3/2-I*physicalRadialFrequency q else -3/2+I*physicalRadialFrequency q := by
  rw [physicalRadialFrequency_eq]
  cases side <;> simp only [physicalFundamentalFrequency,Bool.false_eq_true,↓reduceIte,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  all_goals norm_num; ring_nf; simp only [Complex.I_sq]; ring

/-- No spectral coordinate is replaced: these are the original frequencies expressed in the original Xi zero. -/
theorem physicalFundamentalFrequency_eq (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side = if side then -1-(q.1:ℂ)/2 else -2+(q.1:ℂ)/2 := by
  rw [physicalFundamentalFrequency_connection_root,physicalRadialFrequency,physicalAngularParameter_eq]
  cases side <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

theorem physicalFundamentalFrequency_strip (q : XiZeroCopy) (side : Bool) :
    (physicalFundamentalFrequency q side).im ≠ 0 ∧ |(physicalFundamentalFrequency q side).re| < 2 := by
  apply allXi_fundamental_frequency_strip q
  cases side <;> simp [physicalFundamentalFrequency]

/-- The original smooth-onset source pole does not collide with either target fundamental resonance. -/
theorem physicalFundamentalFrequency_sub_sourceRate_ne_zero (q : XiZeroCopy) (branch side : Bool) :
    physicalFundamentalFrequency q side-2*physicalRate q branch ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  rw [physicalFundamentalFrequency_eq]
  cases side <;> cases branch <;> simp only [Bool.false_eq_true,↓reduceIte,physicalRate]
  all_goals
    intro he
    have hh := congrArg Complex.im he
    norm_num [Complex.mul_im,Complex.mul_re] at hh
    apply hi
    linarith

/-- Both original physical connection coefficients vanish at their respective fundamental frequencies. -/
theorem physicalFundamentalFrequency_connection_zero (q : XiZeroCopy) (side : Bool) :
    connection (physicalFundamentalFrequency q side) (physicalRadialFrequency q) = 0 := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side
  · exact (connection_fundamental_zero _).2
  · exact (connection_fundamental_zero _).1

end
end RHTower.D4BMJointSource
