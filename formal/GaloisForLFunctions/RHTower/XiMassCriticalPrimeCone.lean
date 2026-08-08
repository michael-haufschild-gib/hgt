import GaloisForLFunctions.RHTower.PrimeMassSharpUpper
import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux

/-!
# Sharp prime-mass control on the critical moving cone

The corpus estimate `chebyshevPsi_le_seven`, combined with exact discrete Abel
summation, removes the logarithmic loss from the critical prime mass.  At the
moving height

`H = d * u / (d - 1 / 2)`,

the resulting `exp (H / 2)` growth cancels exactly against the deep-shift
Fourier decay `exp (d * u - d * H)`.  Thus the completed-error endpoint is
uniformly bounded along the full cone.  All integrals below are actual Bochner
integrals; no finite or numerical approximation is used.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The critical Mellin prime mass has the sharp square-root upper bound.

This is the real-height form of `primeMassHalf_le_sqrt`. -/
theorem criticalMellinPrimeMass_le_sqrt
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinPrimeMass h ≤ 21 * Real.exp (h / 2) := by
  rw [criticalMellinPrimeMass_eq_primeMassHalf]
  have hmass := primeMassHalf_le_sqrt (Real.one_le_exp hh)
  rw [← Real.exp_half] at hmass
  exact hmass

/-- The completed critical Mellin error grows by at most the critical
square-root scale. -/
theorem abs_criticalMellinCompletedError_le_sqrt
    {h : ℝ} (hh : 0 ≤ h) :
    |criticalMellinCompletedError h| ≤ 23 * Real.exp (h / 2) := by
  have hsinh0 : 0 ≤ Real.sinh (h / 2) := by
    rw [Real.sinh_eq]
    have hexp := Real.exp_le_exp.mpr (show -(h / 2) ≤ h / 2 by linarith)
    linarith
  have hpolar : 4 * Real.sinh (h / 2) ≤ 2 * Real.exp (h / 2) := by
    rw [Real.sinh_eq]
    have hneg0 : 0 ≤ Real.exp (-(h / 2)) := Real.exp_nonneg _
    linarith
  have hmass0 : 0 ≤ criticalMellinPrimeMass h :=
    criticalMellinPrimeMass_nonneg h
  have hmass := criticalMellinPrimeMass_le_sqrt hh
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass]
  calc
    |4 * Real.sinh (h / 2) - criticalMellinPrimeMass h| ≤
        |4 * Real.sinh (h / 2)| + |criticalMellinPrimeMass h| := abs_sub _ _
    _ = 4 * Real.sinh (h / 2) + criticalMellinPrimeMass h := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hsinh0), abs_of_nonneg hmass0]
    _ ≤ 2 * Real.exp (h / 2) + 21 * Real.exp (h / 2) :=
      add_le_add hpolar hmass
    _ = 23 * Real.exp (h / 2) := by ring

/-- On every supercritical moving cone, the completed-error terminal flux is
uniformly bounded by one fixed actual integral.  The exponent vanishes exactly:

`H / 2 + d * u - d * H = 0`

when `H = d * u / (d - 1 / 2)`. -/
theorem norm_xiMassCompletedError_terminal_at_cone_le
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    let H := d * u / (d - 1 / 2)
    ‖(criticalMellinCompletedError H : ℂ) *
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (H : ℂ)‖ ≤
      23 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  dsimp only
  let H : ℝ := d * u / (d - 1 / 2)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hden : 0 < d - 1 / 2 := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hE := abs_criticalMellinCompletedError_le_sqrt hH
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := sigma) (d := d) (by linarith) hda hsigma u H
  rw [abs_of_nonneg hu] at hF
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |criticalMellinCompletedError H| *
        ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * I)) (H : ℂ)‖ ≤
      (23 * Real.exp (H / 2)) * (Real.exp (u * d - H * d) * J) :=
        mul_le_mul hE (by simpa only [J] using hF) (norm_nonneg _) (by positivity)
    _ = 23 * J * Real.exp (d * u - (d - 1 / 2) * H) := by
      rw [show (23 * Real.exp (H / 2)) * (Real.exp (u * d - H * d) * J) =
        23 * J * (Real.exp (H / 2) * Real.exp (u * d - H * d)) by ring_nf,
        ← Real.exp_add]
      ring_nf
    _ = 23 * J := by
      have hcancel : d * u - (d - 1 / 2) * H = 0 := by
        have hdenne : d - 1 / 2 ≠ 0 := ne_of_gt hden
        dsimp [H]
        rw [show (d - 1 / 2) * (d * u / (d - 1 / 2)) = d * u by
          calc
            (d - 1 / 2) * (d * u / (d - 1 / 2)) =
                (d * u / (d - 1 / 2)) * (d - 1 / 2) := by ring
            _ = d * u := div_mul_cancel₀ _ hdenne]
        ring
      rw [hcancel, Real.exp_zero, mul_one]
    _ = 23 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by rfl

end

end RHTower
