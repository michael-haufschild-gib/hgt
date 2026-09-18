import GaloisForLFunctions.HTGeometry.HyperbolicRadialZeroJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleGreen

/-!
# Literal full-circle zero jet

The full circular response obeys its actual hyperbolic radial equation with
the literal native half-square forcing.  Its compact-radius second jet is
therefore fixed by the constructed full and square fields, rather than left as
an independent characteristic contact.

Proof-chain role:
`literal full circle ODE -> forced zero jet -> direct Peierls cap coefficient
-> corrected-future/lift-defect versus actual left-QNM contact -> HB B2`.
-/

namespace RHTower.D4BMFullAngularCircle

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMNativeCircle

noncomputable section
set_option autoImplicit false

/-- The literal full circle's zero-radius second jet is the forced
full-plus-half-square coefficient. -/
theorem angularMean_second_deriv_zero (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    deriv (deriv (fun d => angularMean q branch d x k)) 0 =
      parameter q branch *
        (fullAngularField q branch ![x, Real.exp k] +
          fullSquarePotential q ![x, Real.exp k]) / 2 := by
  have h := second_deriv_zero_of_hyperbolic_radial_eq
    (fun d => angularMean q branch d x k) (fun d => D4BMNativeCircle.mean q d x k)
    (parameter q branch) (angularMean_smooth q branch x k)
    (D4BMNativeCircle.mean_radial_smooth q x k) (by
      intro d
      have hforced := angularMean_forced q branch d x k
      convert hforced using 1 <;> ring)
  rw [angularMean_zero, D4BMNativeCircle.mean_zero] at h
  exact h

end

end RHTower.D4BMFullAngularCircle
