import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreTiling

/-!
# Interior fundamental-domain core--tail partition

A mesh `1 / M` tiles the whole open horizontal fundamental interval.  Every
interior fundamental-domain point is therefore either in the finite grid core
up to height `√3 / 2 + K / M`, or in the strict cusp tail above that height.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The open fundamental domain splits exactly between the finite reciprocal-mesh
core and the strict cusp tail. -/
theorem fdo_mem_fdUpperChartGridCore_or_tail {M K : ℕ} (hM : 0 < M)
    (z : ℍ) (hz : z ∈ ModularGroup.fdo) :
    z ∈ fdUpperChartGridCore (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) ∨
      Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹ < z.im := by
  let c : ℝ := Real.sqrt 3 / 2
  let h : ℝ := (M : ℝ)⁻¹
  have hM0 : (M : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hM
  have hMh : (M : ℝ) * h = 1 := by
    simp [h, hM0]
  have hinv0 : 0 ≤ h := inv_nonneg.mpr (Nat.cast_nonneg M)
  have hycore : c < z.im := by
    have hthree : 3 < 4 * z.im ^ (2 : ℕ) :=
      ModularGroup.three_lt_four_mul_im_sq_of_mem_fdo hz
    have hsqrt0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt 3) ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
    by_contra hnot
    have hle : z.im ≤ c := le_of_not_gt hnot
    have hnonneg : 0 ≤ Real.sqrt 3 - 2 * z.im := by
      dsimp [c] at hle
      linarith
    have hsum : 0 ≤ Real.sqrt 3 + 2 * z.im := by
      nlinarith [z.im_pos]
    have hprod : 0 ≤ (Real.sqrt 3 - 2 * z.im) * (Real.sqrt 3 + 2 * z.im) :=
      mul_nonneg hnonneg hsum
    nlinarith
  rcases le_or_gt z.im (c + (K : ℝ) * h) with hy | hy
  · left
    rw [fdUpperChartGridCore_eq_fd_inter_upperChartGridCore,
      upperChartGridCore_eq_coordinateRect]
    · refine ⟨ModularGroup.fdo_subset_fd hz, ?_⟩
      constructor
      · constructor
        · have hxabs : |z.re| < (1 : ℝ) / 2 := hz.2
          nlinarith [neg_le_abs z.re]
        · have hxlt : z.re < (1 : ℝ) / 2 :=
            lt_of_le_of_lt (le_abs_self z.re) hz.2
          rw [hMh]
          linarith
      · exact ⟨hycore, hy⟩
    · exact hinv0
    · exact hinv0
  · right
    exact hy

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
