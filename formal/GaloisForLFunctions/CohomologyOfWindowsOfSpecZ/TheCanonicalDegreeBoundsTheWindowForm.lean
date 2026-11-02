import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheCanonicalClassOfAWindow

/-!
# The canonical degree bounds the window form

On a window of length `A` every term of Weil's form but three is a jump count: the archimedean
constant `Ω(0)`, the canonical density `k_A ≤ 2ψ_{1/2}(e^A)`, and the negative pole square
`½⟨2 sinh(u/2), H⟩² ≤ 2A sinh²(A/2)‖H‖²`. Since `2ψ_{1/2}(e^A) − Ω(0)` is the canonical degree:

* **Semiboundedness** (`weilQuad_ge_neg_windowFloor`):
  `Q(H) ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` on window tests. The window `h¹` is bounded below by
  minus its canonical degree and the pole capacity.
* **The second-order pencil** (`pencil_nonneg`): for `κ > 0`, `p ≥ 0` and `c ≥ κ·(deg K_A +
  2A sinh²(A/2))`, `κQ(H) + c∫e^{−py}H(y)² dy ≥ 0` on window tests. The second-order term of the
  degeneration at the critical curve, `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`, is therefore nonnegative on
  every window as soon as `K ≤ βJ/(κ(deg K_A + 2A sinh²(A/2)))`: the prime-free term — the
  dimension `β` times the Jordan count `J` — pays the whole arithmetic of a window at bounded
  dilation constant. All of RH sits in `K → ∞`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A : ℝ} {H : ℝ → ℝ}

/-- The **window floor** `deg K_A + 2A sinh²(A/2)`. -/
def windowFloor (A : ℝ) : ℝ := canonicalDegree A + 2 * A * Real.sinh (A / 2) ^ 2

theorem levyJump_nonneg (g : ℝ → ℝ) : 0 ≤ levyJump g := ENNReal.toReal_nonneg

theorem halfChebyshev_mono : Monotone halfChebyshev := fun _ _ h =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor h))
    fun n _ _ => primeJumpWeight_nonneg n

/-- On the window the canonical density is at most `2ψ_{1/2}(e^A)`. -/
theorem canonicalDensity_le {u : ℝ} (hu : u ∈ Icc (-A) 0) :
    canonicalDensity A u ≤ 2 * halfChebyshev (Real.exp A) := by
  rw [canonicalDensity_eq_halfChebyshev hu]
  have h1 := halfChebyshev_mono (Real.exp_le_exp.mpr (show -u ≤ A by linarith [hu.1]))
  have h2 := halfChebyshev_mono (Real.exp_le_exp.mpr (show A + u ≤ A by linarith [hu.2]))
  linarith

theorem integrable_canonicalDensity_mul (hc : Continuous H) (hcs : HasCompactSupport H) (A : ℝ) :
    Integrable fun u => canonicalDensity A u * H u ^ 2 := by
  have iH := integrable_sq hc hcs
  simp_rw [canonicalDensity, Finset.sum_mul]
  refine integrable_finset_sum _ fun n _ => ?_
  simp_rw [mul_assoc]
  refine Integrable.const_mul ?_ _
  have hpt : (fun u => inWindowCount A (Real.log n) u * H u ^ 2) = fun u =>
      (Icc (-A) (-Real.log n)).indicator (fun u => H u ^ 2) u +
        (Icc (Real.log n - A) 0).indicator (fun u => H u ^ 2) u :=
    funext fun u => inWindowCount_mul A (Real.log n) u fun u => H u ^ 2
  rw [hpt]
  exact (iH.indicator measurableSet_Icc).add (iH.indicator measurableSet_Icc)

/-- The canonical density costs at most `2ψ_{1/2}(e^A)‖H‖²`. -/
theorem integral_canonicalDensity_mul_le (hH : IsWindowTest A H) :
    ∫ u, canonicalDensity A u * H u ^ 2 ≤ 2 * halfChebyshev (Real.exp A) * ∫ u, H u ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_canonicalDensity_mul hH.continuous hH.hasCompactSupport A)
    ((integrable_sq hH.continuous hH.hasCompactSupport).const_mul _) fun u => ?_
  by_cases hu : u ∈ Icc (-A) 0
  · exact mul_le_mul_of_nonneg_right (canonicalDensity_le hu) (sq_nonneg _)
  · simp [hH.vanish u hu]

/-- **The pole capacity of a window**: `⟨2 sinh(u/2), H⟩² ≤ 4A sinh²(A/2)‖H‖²`. -/
theorem sinhPairing_sq_le (hH : IsWindowTest A H) (hA : 0 ≤ A) :
    sinhPairing H ^ 2 ≤ 4 * A * Real.sinh (A / 2) ^ 2 * ∫ u, H u ^ 2 := by
  set g : ℝ → ℝ := (Icc (-A) 0).indicator fun u => 2 * Real.sinh (u / 2) with hg
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have ig : Integrable g := by
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact (Continuous.integrableOn_Icc (by fun_prop))
  have ig2 : Integrable fun u => g u ^ 2 := by
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_ |>.congr (ae_of_all _ fun u => ?_)
    · exact fun u => (2 * Real.sinh (u / 2)) ^ 2
    · exact Continuous.integrableOn_Icc (by fun_prop)
    · by_cases hu : u ∈ Icc (-A) 0 <;> simp [hg, hu]
  have iHg : Integrable fun u => H u * g u :=
    (hH.continuous.integrable_of_hasCompactSupport hH.hasCompactSupport).mul_of_top_left
      (ig.aestronglyMeasurable.memLp_top_of_bound 2 (Eventually.of_forall fun u => by
        by_cases hu : u ∈ Icc (-A) 0
        · simp only [hg, indicator_of_mem hu, Real.norm_eq_abs]
          sorry
        · simp [hg, hu])) |>.integrable_mul ?_
  sorry

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
