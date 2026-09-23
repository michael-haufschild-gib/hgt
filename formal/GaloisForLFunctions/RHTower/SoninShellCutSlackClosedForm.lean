import GaloisForLFunctions.RHTower.SoninShellCutSharpSchedule

/-!
# The band slack in closed form

A band term of the budget is the root of the band's length times a squared bound, and the floor is
the root of half the half-width times a mass.  Their quotient collapses: the roots combine into one,
the half-width cancels down to a single power, and what is left is the bound's own factor times the
root of `t δ / I`.

Read this way the slack shows what governs it — the tail at the gap, and the product of the band's
radius with the half-width.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open scoped FourierTransform

/-- The quotient of a band root by the floor root, in closed form. -/
theorem sqrt_band_div_sqrt_floor (t X δ I : ℝ) (ht : 0 ≤ t) (hX : 0 ≤ X) (hδ : 0 < δ)
    (hI : 0 < I) :
    Real.sqrt (2 * t * X ^ (2 : ℕ)) / Real.sqrt (δ * I / 2) = 2 * X * Real.sqrt (t / (δ * I)) := by
  have hfloor : (0 : ℝ) < δ * I / 2 := by positivity
  have hne : Real.sqrt (δ * I / 2) ≠ 0 := (Real.sqrt_pos.mpr hfloor).ne'
  have h1 : Real.sqrt (2 * t * X ^ (2 : ℕ)) = Real.sqrt (2 * t) * X := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * t), Real.sqrt_sq hX]
  have h3 : Real.sqrt (t / (δ * I)) * Real.sqrt (δ * I / 2) = Real.sqrt (t / 2) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ t / (δ * I))]
    congr 1
    field_simp
  have h4 : Real.sqrt (2 * t) = 2 * Real.sqrt (t / 2) := by
    rw [show (2 : ℝ) * Real.sqrt (t / 2) = Real.sqrt 4 * Real.sqrt (t / 2) by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)],
      ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  rw [h1, div_eq_iff hne, h4]
  calc 2 * Real.sqrt (t / 2) * X
      = 2 * X * Real.sqrt (t / 2) := by ring
    _ = 2 * X * (Real.sqrt (t / (δ * I)) * Real.sqrt (δ * I / 2)) := by rw [h3]
    _ = 2 * X * Real.sqrt (t / (δ * I)) * Real.sqrt (δ * I / 2) := by ring

/-- **The band slack of a cut.**  The tail at the gap, times the root of the band's radius against
the half-width and the reference square's mass. -/
theorem sqrt_soninShellCutSharpBandBoundAt_div_floor
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (w t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (soninShellCutSharpBandBoundAt b c N w t) / soninShellCutNormFloor b c N =
      2 * (2 * soninShellCutWidth b c N *
            soninRefTailSup (soninShellCutWidth b c N * (w - t)) *
          (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
        Real.sqrt (t / (soninShellCutWidth b c N * ∫ y : ℝ, soninUnitBumpSq y)) := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hI : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  have hJ₀ : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  have hXnn : (0 : ℝ) ≤ 2 * soninShellCutWidth b c N *
      soninRefTailSup (soninShellCutWidth b c N * (w - t)) *
      (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y)) := by
    have h1 := soninRefTailSup_nonneg (soninShellCutWidth b c N * (w - t))
    have h2 := soninRefTailSup_nonneg (0 : ℝ)
    have h3 : (0 : ℝ) ≤ 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y) := by positivity
    have h4 : (0 : ℝ) ≤ 1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y) := by linarith
    positivity
  rw [soninShellCutSharpBandBoundAt, soninShellCutNormFloor]
  exact sqrt_band_div_sqrt_floor t _ (soninShellCutWidth b c N)
    (∫ y : ℝ, soninUnitBumpSq y) ht hXnn hδ hI

end RHTower
