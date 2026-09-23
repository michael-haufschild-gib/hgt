import GaloisForLFunctions.RHTower.Sieve.InvZetaLeftLine
import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift

/-!
# The three edge bounds for the concrete rectangle

Taking the right abscissa to be exactly `σ = 1 + c/(2 log⁹N)` — the abscissa the zero-free
comparison already uses — makes the horizontal edges free: the whole segment from `1 - c/(16 log⁹N)`
to `σ` lies in the range covered by `norm_invZeta_left_le_range`, so no case split on the abscissa
is needed and the horizontal bound is the same expression as the left-edge bound.

The right line needs a different estimate, but an easy one: on `Re s > 1` the reciprocal of `ζ` is
bounded by the Euler product, uniformly in the height.
-/

namespace RHTower.Sieve

open Complex

/-- **The right line.**  On `Re s = d > 1` the regular reciprocal is bounded uniformly in the
height by the Euler-product estimate. -/
theorem norm_invZeta_right_le {d y : ℝ} (hd : 1 < d) :
    ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Real.exp (22 / 4) * (1 + 1 / (d - 1)) := by
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have hne : ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have h := norm_LSeries_moebius_le_uniform (σ := d) (t := y) hd
  rw [LSeries_moebius_eq_inv (by rw [hre]; exact hd), ← invZeta_eq_inv hne] at h
  exact h

/-- **The horizontal edges.**  Every abscissa between the left line and `σ` is covered by the same
estimate, so the horizontal segments cost no new argument. -/
theorem norm_invZeta_horizontal_le {x T : ℝ} {N : ℕ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N) (hT : 1 ≤ |T|)
    (hNbig : 3 + 2 * |T| ≤ (N : ℝ))
    (hxlo : 1 - zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) ≤ x)
    (hxhi : x ≤ 1 + zeroFreeConst / (2 * (Real.log N) ^ (9 : ℕ))) :
    ‖invZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ 2 / Real.exp ((-22
          - 3 * Real.log (1 + 1 / (zeroFreeConst / (2 * (Real.log N) ^ (9 : ℕ))))
          - Real.log (5 / 2 + Real.log N)) / 4) :=
  norm_invZeta_left_le_range hlogN hN hT hNbig hxlo hxhi

/-- **Continuity on the left edge.**  Between the zero-free rectangle and the removable-singularity
correction, `invZeta` is continuous along the truncated left line. -/
theorem continuousOn_invZeta_left_line {c d T : ℝ} (hcd : c ≤ 1) (hd1 : 1 ≤ d)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    ContinuousOn (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I)) (Set.uIcc (-T) T) := by
  intro y hy
  have hmem : ((c : ℂ) + (y : ℝ) * Complex.I) ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T := by
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · have hre : ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by simp
      rw [hre, Set.uIcc_of_le (le_trans hcd hd1)]
      exact ⟨le_rfl, le_trans hcd hd1⟩
    · have him : ((c : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
      rw [him]
      exact hy
  have hin : Continuous fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I) := by fun_prop
  rcases eq_or_ne ((c : ℂ) + (y : ℝ) * Complex.I) 1 with heq | hne
  · refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.comp (g := invZeta) (f := fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I))
      ?_ hin.continuousAt
    rw [heq]
    exact differentiableAt_invZeta_one.continuousAt
  · refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.comp (g := invZeta) (f := fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I))
      ?_ hin.continuousAt
    exact (differentiableAt_invZeta_of_zeta_ne_zero hne (hzf _ hmem hne)).continuousAt

end RHTower.Sieve
