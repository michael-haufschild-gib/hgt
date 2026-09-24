import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace RHTower

/-- Exact affine reduction of the size-three prime--archimedean source determinant.
The identity holds for arbitrary real moment coordinates. -/
theorem primeArch_scoreAffineGate_algebra (a b c e f v w u : ℝ) :
    let m := u - e / 5040
    let d := a * w - v ^ 2
    let q := a * c - b ^ 2
    let p := a * e ^ 2 - 2 * b * c * e + c ^ 3
    let B := 9 * a * e - 504 * v * c + 15120 * w * b - 181440 * m * a
    let C := a * m ^ 2 - 2 * v * w * m + w ^ 3
    let K₀ := c ^ 3 / 70 -
      d * (-504 * v * c + 15120 * w * b - 181440 * a * u) -
      362880 * (a * u ^ 2 - 2 * v * w * u + w ^ 3)
    let K₁ := -b * c / 35 - 45 * a * d - 144 * (v * w - a * u) +
      145 * d / 303 - 145 * q / 21210
    362880 * (d * ((f - B) / 362880) - C) =
      (q * f - p) / 70 + (K₀ + K₁ * e) +
        (q / 70 - d) * (145 * e - 303 * f) / 303 := by
  dsimp only
  ring

end RHTower
