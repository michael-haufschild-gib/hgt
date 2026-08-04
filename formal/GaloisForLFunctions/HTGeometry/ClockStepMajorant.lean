import GaloisForLFunctions.HTGeometry.ClockIterateBound

/-!
# A summable majorant for the step applied to the iterates

Summing the recursion requires passing the sum through the two integrations, which asks for a bound
on the integrand `(W_m(s,t))'' + V·W_m(s,t)` that is uniform over the rectangle and summable in `m`.

Taking the intermediate radius to be the midpoint `(ρ + ρ₀)/2` makes both gaps equal to
`(ρ₀ - ρ)/2`, and the bound is the iterate bound at that radius multiplied by the norm of the step
operator between the two strips.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The majorant of the step applied to the `m`-th iterate on a rectangle of side `T`. -/
noncomputable def stepMajorant (Mv ρ₀ ρ T : ℝ) (m : ℕ) : ℝ :=
  (16 / (ρ₀ - ρ) ^ 2 + Mv / 4)
    * ((4 + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
      / ((m.factorial : ℝ) ^ 2 * ((ρ₀ - ρ) / 2) ^ (2 * m)))

/-- **The step applied to an iterate is dominated by the majorant.** -/
theorem norm_clockStripStep_clockIterate_le {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (m : ℕ) {s t : ℝ} (hsT : |s| ≤ T) (htT : |t| ≤ T)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    ‖clockStripStep (V s t) (clockIterate V m s t) z‖ ≤ stepMajorant Mv ρ₀ ρ T m := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  set σ : ℝ := (ρ + ρ₀) / 2 with hσdef
  have hρσ : ρ < σ := by rw [hσdef]; linarith
  have hσρ₀ : σ < ρ₀ := by rw [hσdef]; linarith
  have hσ0 : (0 : ℝ) ≤ σ := le_trans hρ0 hρσ.le
  have hgap : σ - ρ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  have hrem : ρ₀ - σ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  have hT0 : (0 : ℝ) ≤ T := le_trans (abs_nonneg s) hsT
  obtain ⟨holo, _⟩ := clockIterate_regular hV m
  have hwσ : DifferentiableOn ℂ (clockIterate V m s t) (imStrip σ) :=
    (holo s t).mono (imStrip_mono hσρ₀.le)
  have hMvσ : ∀ w ∈ imStrip σ, ‖V s t w‖ ≤ Mv :=
    fun w hw => hMv s t hsT htT w (imStrip_mono hσρ₀.le hw)
  -- the iterate bound at the intermediate radius, uniform over the rectangle
  have hMw : ∀ w ∈ imStrip σ, ‖clockIterate V m s t w‖
      ≤ (4 + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ 2 * ((ρ₀ - ρ) / 2) ^ (2 * m)) := by
    intro w hw
    have hbase := clockIterate_norm_le hρ₀ hV hMv0 hMv m σ hσ0 hσρ₀ s t hsT htT w
      (le_of_lt (mem_imStrip.mp hw))
    rw [hrem] at hbase
    refine hbase.trans ?_
    gcongr
  have hstep := norm_clockStripStep_le hρσ hMv0 hwσ hMw hMvσ hz
  rw [hgap] at hstep
  have hrw : 4 / ((ρ₀ - ρ) / 2) ^ 2 = 16 / (ρ₀ - ρ) ^ 2 := by
    rw [div_pow]
    field_simp
    norm_num
  rw [hrw] at hstep
  exact hstep

/-- The smallness condition at the half gap implies the one at the full gap. -/
theorem ovsyannikov_smallness_of_half {ρ₀ Mv ρ T : ℝ} (hMv0 : 0 ≤ Mv) (hρ : ρ < ρ₀)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1) :
    (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / (ρ₀ - ρ) ^ 2 < 1 :=
  ovsyannikov_smallness_of_half_const (by positivity) (by linarith) hsmall

/-- **The majorant is summable when the rectangle is small.** -/
theorem summable_stepMajorant {ρ₀ Mv ρ T : ℝ} (hMv0 : 0 ≤ Mv) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1) :
    Summable (stepMajorant Mv ρ₀ ρ T) := by
  have hK0 : (0 : ℝ) ≤ 4 + Mv * ρ₀ ^ 2 / 4 := by positivity
  have hG : (0 : ℝ) < (ρ₀ - ρ) / 2 := by linarith
  exact (summable_ovsyannikov_bound hK0 hG hT hsmall).mul_left _

end GaloisForLFunctions.HTGeometry
