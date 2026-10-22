import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWWeakSourceOpticalWard
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularSourceReflection

/-!
# PW-B optical/CTP reflection-parity obstruction

The source-fixed crossed weak optical flux is reflection-even: reflection swaps
the two physical branch responses and forcing vectors. The literal completed
ordered CTP numerator is reflection-odd. Their un-oriented difference therefore
has the exact reflection-pair residual shown below. Multiplication by the
spectral ordinate gives an even CTP observable, which is parity-compatible
with optical flux, but no incidence or extinction is asserted.
-/

open Complex

namespace RHTower.D4BMPWOpticalCTPParity
open D4BMModularCore D4BMGlobalAngularResponse D4BMFullAngularSourceReflection
noncomputable section
set_option autoImplicit false

def crossedOpticalFlux (q : XiZeroCopy) : ℝ :=
  weakSourceFlux q true * weakSourceMass q false +
    weakSourceFlux q false * weakSourceMass q true

theorem weakSourceMass_reflect (q : XiZeroCopy) (b : Bool) :
    weakSourceMass (xiZeroCopyReflectEquiv q) b = weakSourceMass q (!b) := by
  simp only [weakSourceMass, D4BMFullAngularSourceReflection.weakResponse_reflect]

theorem weakSourceFlux_reflect (q : XiZeroCopy) (b : Bool) :
    weakSourceFlux (xiZeroCopyReflectEquiv q) b = weakSourceFlux q (!b) := by
  simp only [weakSourceFlux, D4BMFullAngularSourceReflection.weakResponse_reflect,
    D4BMFullAngularSourceReflection.forcingVector_reflect]

theorem crossedOpticalFlux_reflect (q : XiZeroCopy) :
    crossedOpticalFlux (xiZeroCopyReflectEquiv q) = crossedOpticalFlux q := by
  simp only [crossedOpticalFlux, weakSourceFlux_reflect, weakSourceMass_reflect,
    Bool.not_true, Bool.not_false]
  ring

theorem spectralOrdinate_reflect (q : XiZeroCopy) :
    (((xiZeroCopyReflectEquiv q).1 : ℂ).im) = -((q.1 : ℂ).im) := by
  change (1 - (q.1 : ℂ)).im = -((q.1 : ℂ).im)
  simp

theorem orientedCTP_reflection_even (q : XiZeroCopy) (X k : ℝ) :
    (((xiZeroCopyReflectEquiv q).1 : ℂ).im) *
      (fullCircleCrossBranchSymmetricCausalPair (xiZeroCopyReflectEquiv q) 1 X k).re =
    ((q.1 : ℂ).im) * (fullCircleCrossBranchSymmetricCausalPair q 1 X k).re := by
  rw [spectralOrdinate_reflect,
    fullCircleCrossBranchSymmetricCausalPair_re_reflection_odd]
  ring

def opticalCTPDefect (q : XiZeroCopy) (X k : ℝ) : ℝ :=
  (fullCircleCrossBranchSymmetricCausalPair q 1 X k).re - crossedOpticalFlux q

theorem opticalCTPDefect_reflection_sum (q : XiZeroCopy) (X k : ℝ) :
    opticalCTPDefect q X k +
      opticalCTPDefect (xiZeroCopyReflectEquiv q) X k =
        -2 * crossedOpticalFlux q := by
  simp only [opticalCTPDefect,
    fullCircleCrossBranchSymmetricCausalPair_re_reflection_odd,
    crossedOpticalFlux_reflect]
  ring

theorem crossedOpticalFlux_eq (q : XiZeroCopy) :
    crossedOpticalFlux q =
      -16 * (((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) *
        (weakSourceMass q true * weakSourceMass q false) :=
  weakSourceFlux_pair q

theorem opticalCTPDefect_reflection_sum_exact (q : XiZeroCopy) (X k : ℝ) :
    opticalCTPDefect q X k +
      opticalCTPDefect (xiZeroCopyReflectEquiv q) X k =
        32 * (((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) *
          (weakSourceMass q true * weakSourceMass q false) := by
  rw [opticalCTPDefect_reflection_sum, crossedOpticalFlux_eq]
  ring

end
end RHTower.D4BMPWOpticalCTPParity

