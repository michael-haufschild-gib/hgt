import GaloisForLFunctions.HTGeometry.ClockTubeIterateBound

/-!
# The sum of the iterates on a tube

The Ovsyannikov bound with `k` transverse coordinates is dominated by the same geometric series as in
one variable, with `K = 4k + ‖V‖ρ₀²/4`, so on a rectangle small compared with the radius of
analyticity the series

`u(ξ, η, z) = ∑ₘ W_m(ξ, η, z)`

converges absolutely on the tube. This file defines that sum, proves the convergence, and supplies
the summable majorant for the step applied to the iterates — the bound that lets the sum be taken
through both integrations.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The solution of the characteristic clock equation on a tube, as the sum of the iterates. -/
noncomputable def tubeSolution (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ξ η : ℝ) (z : Fin k → ℂ) : ℂ :=
  ∑' m : ℕ, tubeIterate V m ξ η z

/-- **The series of iterates converges absolutely on a small rectangle.** -/
theorem summable_tubeIterate {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / (ρ₀ - ρ) ^ (2 : ℕ) < 1)
    {s t : ℝ} (hsT : |s| ≤ T) (htT : |t| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    Summable fun m : ℕ => tubeIterate V m s t z := by
  have hK0 : (0 : ℝ) ≤ 4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4 := by positivity
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  have hmaj := summable_ovsyannikov_bound (K := 4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) (G := ρ₀ - ρ) (T := T)
    hK0 hG hT hsmall
  refine Summable.of_norm_bounded hmaj fun m => ?_
  have hbase := tubeIterate_norm_le hρ₀ hV hMv0 hMv m ρ hρ0 hρ s t hsT htT z hz
  refine hbase.trans ?_
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  gcongr

/-- The majorant of the step applied to the `m`-th iterate on a rectangle of side `T`. -/
noncomputable def tubeStepMajorant (k : ℕ) (Mv ρ₀ ρ T : ℝ) (m : ℕ) : ℝ :=
  (16 * k / (ρ₀ - ρ) ^ (2 : ℕ) + Mv / 4)
    * ((4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
      / ((m.factorial : ℝ) ^ (2 : ℕ) * ((ρ₀ - ρ) / 2) ^ (2 * m)))

/-- **The step applied to an iterate is dominated by the majorant.** -/
theorem norm_tubeStep_tubeIterate_le {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (m : ℕ) {s t : ℝ} (hsT : |s| ≤ T) (htT : |t| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    ‖tubeStep (V s t) (tubeIterate V m s t) z‖ ≤ tubeStepMajorant k Mv ρ₀ ρ T m := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  set σ : ℝ := (ρ + ρ₀) / 2 with hσdef
  have hρσ : ρ < σ := by rw [hσdef]; linarith
  have hσρ₀ : σ < ρ₀ := by rw [hσdef]; linarith
  have hσ0 : (0 : ℝ) ≤ σ := le_trans hρ0 hρσ.le
  have hgap : σ - ρ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  have hrem : ρ₀ - σ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  have hT0 : (0 : ℝ) ≤ T := le_trans (abs_nonneg s) hsT
  obtain ⟨holo, _⟩ := tubeIterate_regular hρ₀ hV m
  have hwσ : SliceHolo (tubeIterate V m s t) σ := sliceHolo_mono (holo s t) hσρ₀.le
  have hMvσ : ∀ w ∈ tube k σ, ‖V s t w‖ ≤ Mv :=
    fun w hw => hMv s t hsT htT w (tube_mono hσρ₀.le hw)
  -- the iterate bound at the intermediate radius, uniform over the rectangle
  have hMw : ∀ w ∈ tube k σ, ‖tubeIterate V m s t w‖
      ≤ (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ (2 : ℕ) * ((ρ₀ - ρ) / 2) ^ (2 * m)) := by
    intro w hw
    have hbase := tubeIterate_norm_le hρ₀ hV hMv0 hMv m σ hσ0 hσρ₀ s t hsT htT w
      fun i => (hw i).le
    rw [hrem] at hbase
    refine hbase.trans ?_
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    gcongr
  have hstep := norm_tubeStep_le_of_sliceHolo hρσ hMv0 hwσ hMw hMvσ hz
  rw [hgap] at hstep
  have hrw : 4 * (k : ℝ) / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) = 16 * k / (ρ₀ - ρ) ^ (2 : ℕ) := by
    rw [div_pow]
    field_simp
    ring
  rw [hrw] at hstep
  exact hstep

/-- **The majorant is summable when the rectangle is small.** -/
theorem summable_tubeStepMajorant {ρ₀ Mv ρ T : ℝ} (hMv0 : 0 ≤ Mv) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1) :
    Summable (tubeStepMajorant k Mv ρ₀ ρ T) := by
  have hK0 : (0 : ℝ) ≤ 4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4 := by positivity
  have hG : (0 : ℝ) < (ρ₀ - ρ) / 2 := by linarith
  exact (summable_ovsyannikov_bound hK0 hG hT hsmall).mul_left _

end GaloisForLFunctions.HTGeometry
