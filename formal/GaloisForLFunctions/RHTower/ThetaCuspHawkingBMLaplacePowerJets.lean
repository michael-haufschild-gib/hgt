import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalMonodromyMaster
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerCore

/-! Actual complex-power radial derivatives in the positive real chart. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def powerFirst (a : ℂ) (z : ℝ) : ℂ := a*power a z/(z:ℂ)
def powerSecond (a : ℂ) (z : ℝ) : ℂ := a*(a-1)*power a z/(z:ℂ)^2

/-- The actual first and second derivatives of the original positive-radius
power, with no restriction on its complex exponent. -/
theorem power_derivatives (a : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (power a) (powerFirst a z) z ∧
    HasDerivAt (powerFirst a) (powerSecond a z) z := by
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hcut : (z:ℂ) ∈ Complex.slitPlane := by simp [Complex.mem_slitPlane_iff,hz]
  have h := (Complex.hasStrictDerivAt_cpow_const (c := a) hcut).hasDerivAt.comp_ofReal
  have hfirst : HasDerivAt (power a) (powerFirst a z) z := by
    simpa only [power,powerFirst,Complex.cpow_sub _ _ hz0,Complex.cpow_one,mul_div_assoc] using! h
  refine ⟨hfirst,?_⟩
  have hd := ((hfirst.const_mul a).div (hasDerivAt_id z).ofReal_comp hz0)
  apply hd.congr_deriv
  dsimp [powerFirst,powerSecond]
  field_simp

theorem power_ne_zero (a : ℂ) {z : ℝ} (hz : 0 < z) : power a z ≠ 0 := by
  rw [power,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))]
  exact Complex.exp_ne_zero _

/-- The positive-radius branch equals the original physical horizon dressing. -/
theorem power_physical_factor (w : ℂ) {z : ℝ} (hz : 0 < z) :
    power (w/2) z = D4BMPhysicalMaster.factor (Complex.I*w) z := by
  rw [power,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))]
  unfold D4BMPhysicalMaster.factor d4BMIngoingHorizonExponent
  congr 1
  ring_nf
  simp only [Complex.I_sq]
  ring

end
end RHTower.D4BMLaplaceRadial
