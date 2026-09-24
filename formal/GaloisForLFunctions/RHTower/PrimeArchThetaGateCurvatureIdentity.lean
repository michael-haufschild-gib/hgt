import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exact curvature decomposition of the K-RVM four-moment gate

The coefficient of the fourth theta moment squared in the first open source determinant
has two explicit negative contributions: the earlier K-RVM effective-rank gap and the
shifted theta Gram minor. This is an unconditional polynomial identity; positivity of
those two gaps is proved in separate source modules.
-/

namespace RHTower

/-- Write `v,w` for the first two nontrivial prime--archimedean cumulant moments,
`d` for their leading Hankel minor, `q` for the shifted theta minor, and `r` for
the nine-atom effective-rank gap. The gate's quadratic coefficient is governed by
an exact sum of the two gaps. -/
theorem thetaGateCurvature_exact (a b c : ℝ) :
    let v := a ^ 2 / 2 - b / 6
    let w := c / 120 - a * b / 8 + a ^ 3 / 4
    let d := a * w - v ^ 2
    let q := a * c - b ^ 2
    let r := a ^ 2 - 18 * v
    d - q / 70 = -b * (77 * a ^ 2 + 49 * r) / 7560 - q / 168 := by
  dsimp only
  ring

/-- Exact interpolation law for a quadratic gate. When its leading coefficient is negative,
the final term is the interior surplus above the endpoint chord. -/
theorem quadraticGate_chord_exact (A₂ A₁ A₀ L U e : ℝ) :
    let G := fun z : ℝ => A₂ * z ^ 2 + A₁ * z + A₀
    (U - L) * G e = (U - e) * G L + (e - L) * G U -
      A₂ * (U - L) * (e - L) * (U - e) := by
  dsimp only
  ring

end RHTower
