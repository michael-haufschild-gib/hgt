/-
Schwarz reflection preserves analyticity.

Mathlib proves the differentiable version, `DifferentiableAt.conj_conj`, but has no analytic
counterpart, so three modules of this corpus each rederive the same seven-line argument: unfold
`AnalyticAt` into eventual differentiability, pull the neighbourhood back along the (continuous)
conjugation, and apply the mathlib lemma pointwise.

This file states it once.
-/
import Mathlib

/-- **Schwarz reflection preserves analyticity.**  If `H` is analytic at `conj w`, then the
conjugate-reflected function `z ↦ conj (H (conj z))` is analytic at `w`. -/
theorem AnalyticAt.conj_comp_conj {H : ℂ → ℂ} {w : ℂ}
    (hH : AnalyticAt ℂ H ((starRingEnd ℂ) w)) :
    AnalyticAt ℂ (fun z => (starRingEnd ℂ) (H ((starRingEnd ℂ) z))) w := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hpull := (Complex.continuous_conj.tendsto w).eventually
    (Complex.analyticAt_iff_eventually_differentiableAt.mp hH)
  filter_upwards [hpull] with z hz
  have h := DifferentiableAt.conj_conj hz
  rw [Complex.conj_conj] at h
  exact h
