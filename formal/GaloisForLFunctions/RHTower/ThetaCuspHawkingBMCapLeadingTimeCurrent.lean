import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceOnsetLaplace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedIngoingCurrent

/-! Leading cap time projection at each original independent physical reader.

The literal fixed onset supplies its derivative transform in the required
source-reader strip. Consequently its weighted time-boundary term is zero.
The leading cap coefficient projects to exactly the difference of its two
angular pairings. Those pairings remain explicit: no angular cutoff limit or
complete nonlinear action cancellation is assumed or proved here.
-/

set_option autoImplicit false
open Set MeasureTheory
namespace RHTower.D4BMCapLeadingTimeCurrent
open D4BMJointSource D4BMModularCore
noncomputable section

private theorem source_before_reader (q r : XiZeroCopy) (branch side : Bool) :
    (2*physicalRate q branch).re < (physicalFundamentalFrequency r side).re := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  exact hs.trans (abs_lt.mp (physicalFundamentalFrequency_strip r side).2).1

/-- The original source time derivative, including its fixed switching derivative,
has zero weighted boundary term at each independent original fundamental reader. -/
theorem original_time_boundary_zero (q r : XiZeroCopy) (branch side : Bool) :
    (∫ v in Ioi (0:ℝ), Complex.exp (-physicalFundamentalFrequency r side*(v:ℂ))*
      (timeOnsetFirst (2*physicalRate q branch) v-
        physicalFundamentalFrequency r side*timeOnset (2*physicalRate q branch) v))=0 := by
  let s := 2*physicalRate q branch
  let w := physicalFundamentalFrequency r side
  have hw : s.re < w.re := source_before_reader q r branch side
  have hi := timeOnset_integrable s w hw
  have hd := timeOnsetFirst_integrable s w hw
  have he : (fun v : ℝ => Complex.exp (-w*(v:ℂ))*(timeOnsetFirst s v-w*timeOnset s v))=
      fun v : ℝ => Complex.exp (-w*(v:ℂ))*timeOnsetFirst s v-
        w*(Complex.exp (-w*(v:ℂ))*timeOnset s v) := by funext v; ring
  change (∫ v in Ioi (0:ℝ), Complex.exp (-w*(v:ℂ))*(timeOnsetFirst s v-w*timeOnset s v))=0
  rw [he,integral_sub hd (hi.const_mul w),integral_const_mul,
    timeOnsetFirst_laplace s w hw,timeOnset_laplace,sub_self]

/-- Exact temporal projection of the leading cap coefficient. The two independent
angular pairings stay explicit; their difference is the angular-cutoff work. -/
theorem leading_coefficient_time_projection (q r : XiZeroCopy) (branch side : Bool)
    (l mu phi psi : ℂ) :
    let s := 2*physicalRate q branch
    let w := physicalFundamentalFrequency r side
    (∫ v in Ioi (0:ℝ), Complex.exp (-w*(v:ℂ))*
      (l*((mu-2)*timeOnsetFirst s v*phi-w*timeOnset s v*psi)))=
      -l*w*onsetTransform s w*(psi-(mu-2)*phi) := by
  let s := 2*physicalRate q branch
  let w := physicalFundamentalFrequency r side
  have hw : s.re < w.re := source_before_reader q r branch side
  have hi := timeOnset_integrable s w hw
  have hd := timeOnsetFirst_integrable s w hw
  have he : (fun v : ℝ => Complex.exp (-w*(v:ℂ))*
      (l*((mu-2)*timeOnsetFirst s v*phi-w*timeOnset s v*psi)))=
      fun v : ℝ => (l*(mu-2)*phi)*(Complex.exp (-w*(v:ℂ))*timeOnsetFirst s v)-
        (l*w*psi)*(Complex.exp (-w*(v:ℂ))*timeOnset s v) := by funext v; ring
  change (∫ v in Ioi (0:ℝ), Complex.exp (-w*(v:ℂ))*
      (l*((mu-2)*timeOnsetFirst s v*phi-w*timeOnset s v*psi)))=_
  rw [he,integral_sub (hd.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul,
    timeOnsetFirst_laplace s w hw,timeOnset_laplace]
  ring

end
end RHTower.D4BMCapLeadingTimeCurrent
