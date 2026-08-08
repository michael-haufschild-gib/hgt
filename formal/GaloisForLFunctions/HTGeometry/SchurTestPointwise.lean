import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The pointwise step of Schur's test

Schur's test bounds an integral operator with nonnegative kernel by splitting the kernel against a
positive weight, `k(s,t) f(t) = (k(s,t) w(t)) · (f(t)/w(t))`, and applying Cauchy–Schwarz against
the measure `k(s,·) w(·)`.  The row bound `∫ k(s,t) w(t) dt ≤ C w(s)` then converts the total mass
into `C w(s)`, giving

`(∫ k(s,t) f(t) dt)² ≤ C w(s) ∫ k(s,t) f(t)²/w(t) dt`

at every point.  Integrating in `s` and using the column bound is the rest of Schur's test; the
swap there is the same Tonelli pattern as Young's inequality.

mathlib has neither Schur's test nor its ingredients.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **The pointwise Schur step.**  Against a positive weight with a row bound, the square of the
kernel average is controlled by the weighted average of the square. -/
theorem sq_kernelIntegral_le {μ : Measure ℝ} {kr w f : ℝ → ℝ} {C c : ℝ}
    (hk0 : ∀ t, 0 ≤ kr t) (hw0 : ∀ t, 0 < w t)
    (hrow : (∫ t, kr t * w t ∂μ) ≤ C * c)
    (hkw : AEStronglyMeasurable (fun t => kr t * w t) μ)
    (hgm : AEStronglyMeasurable (fun t => f t / w t) μ)
    (hint1 : Integrable (fun t => kr t * w t) μ)
    (hint2 : Integrable (fun t => kr t * w t * (f t / w t) ^ 2) μ) :
    (∫ t, kr t * f t ∂μ) ^ 2 ≤ (C * c) * ∫ t, kr t * f t ^ 2 / w t ∂μ := by
  have hsplit : (fun t => kr t * w t * (f t / w t)) = fun t => kr t * f t := by
    funext t
    have hne : w t ≠ 0 := (hw0 t).ne'
    rw [mul_assoc]
    congr 1
    field_simp
  have hsq : (fun t => kr t * w t * (f t / w t) ^ 2) = fun t => kr t * f t ^ 2 / w t := by
    funext t
    have hne : w t ≠ 0 := (hw0 t).ne'
    rw [div_pow]
    field_simp
  have hcs := sq_integral_weighted_le (μ := μ) (w := fun t => kr t * w t)
    (g := fun t => f t / w t)
    (fun t => mul_nonneg (hk0 t) (hw0 t).le) hkw hgm hint1 hint2
  rw [hsplit, hsq] at hcs
  refine le_trans hcs ?_
  have hnn : 0 ≤ ∫ t, kr t * f t ^ 2 / w t ∂μ := by
    rw [← hsq]
    exact integral_nonneg fun t => by
      have := hk0 t
      have := (hw0 t).le
      positivity
  exact mul_le_mul_of_nonneg_right hrow hnn

end GaloisForLFunctions.HTGeometry
