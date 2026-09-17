import GaloisForLFunctions.HTGeometry.ElementaryHorizonJets
import GaloisForLFunctions.HTGeometry.UniformThirdOrderJet

/-!
The literal cubic horizon jet of the exterior square-root coordinate.

This is the endpoint geometry required by the three-counterterm source-pole
continuation.  It retains the actual `sqrt (1-z)` chart rather than replacing it
by an asymptotic profile.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Complex
noncomputable section
set_option autoImplicit false

/-- The actual square-root coordinate has its degree-two Taylor polynomial with a
uniform cubic remainder on the physical half-cutoff interval. -/
theorem abs_sqrt_one_sub_quadratic_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    |Real.sqrt (1 - z) - (1 - z / 2 - z ^ 2 / 8)| ≤ z ^ 3 := by
  let q : ℝ := 1 - z / 2 - z ^ 2 / 8
  let p : ℝ := q - z ^ 3
  have hsq : z ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hcub : z ^ 3 ≤ 1 / 8 := by
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz1)]
  have hq : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hupperSq : 1 - z ≤ q ^ 2 := by
    dsimp [q]
    nlinarith [sq_nonneg z]
  have hupper : Real.sqrt (1 - z) ≤ q := by
    calc Real.sqrt (1 - z) ≤ Real.sqrt (q ^ 2) := Real.sqrt_le_sqrt hupperSq
      _ = q := Real.sqrt_sq hq
  have hqhalf : 1 / 2 ≤ q := by
    dsimp [q]
    nlinarith
  have hbr : 0 ≤ 2 * q - 1 / 8 - z / 64 - z ^ 3 := by
    nlinarith
  have hpSq : p ^ 2 ≤ 1 - z := by
    have hfac : 1 - z - p ^ 2 = z ^ 3 * (2 * q - 1 / 8 - z / 64 - z ^ 3) := by
      dsimp [p, q]
      ring
    apply sub_nonneg.mp
    rw [hfac]
    positivity
  have hlower : p ≤ Real.sqrt (1 - z) := Real.le_sqrt_of_sq_le hpSq
  have hmain : |Real.sqrt (1 - z) - q| ≤ z ^ 3 := by
    rw [abs_le]
    constructor <;> dsimp [p] at hlower <;> linarith
  simpa [q] using hmain

/-- The literal square-root coordinate supplies a parameter-uniform cubic horizon jet. -/
theorem hasUniformJet3_sqrt_one_sub (S : Set ℂ) :
    HasUniformJet3 S (1 / 2) (fun _ z => (Real.sqrt (1 - z) : ℂ))
      (fun _ => 1) (fun _ => -1 / 2) (fun _ => -1 / 8) 1 := by
  intro u hu z hz
  have h := abs_sqrt_one_sub_quadratic_le hz.1.le hz.2
  have he : (Real.sqrt (1 - z) : ℂ) - 1 - (-1 / 2) * (z : ℂ) -
      (-1 / 8) * (z : ℂ) ^ 2 =
        ((Real.sqrt (1 - z) - (1 - z / 2 - z ^ 2 / 8) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  simpa using h

end
end GaloisForLFunctions.HTGeometry
