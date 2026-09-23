import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGridWitness

/-!
# Archimedean reciprocal-grid budget selection

A single natural parameter gives both a reciprocal mesh and a quadratic cusp
height.  Both error terms then tend to zero, yielding a grid for every target
tolerance.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The reciprocal-mesh and quadratic-height error budget tends to zero. -/
theorem tendsto_reciprocal_square_grid_budget (N : ℕ) :
    Filter.Tendsto (fun n : ℕ =>
      Real.sqrt ((((Real.sqrt 3 / 2) ^ (2 : ℕ))⁻¹ * 16) *
        ((((n + 1 : ℕ) : ℝ)⁻¹) ^ (2 : ℕ))) +
      Real.sqrt ((((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) *
        (Real.sqrt 3 / 2 + ((n + 1 : ℕ) : ℝ))⁻¹ ^ (2 : ℕ)))
      Filter.atTop (nhds 0) := by
  let C : ℝ := ((Real.sqrt 3 / 2) ^ (2 : ℕ))⁻¹ * 16
  let D : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)
  let c : ℝ := Real.sqrt 3 / 2
  have hinv : Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hshift : Filter.Tendsto (fun n : ℕ => c + ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_const_nhds.add_atTop
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  have hshiftInv : Filter.Tendsto (fun n : ℕ =>
      (c + ((n + 1 : ℕ) : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    hshift.inv_tendsto_atTop
  have hcoreCont : Continuous (fun x : ℝ => Real.sqrt (C * x ^ (2 : ℕ))) :=
    Real.continuous_sqrt.comp (continuous_const.mul (continuous_id.pow 2))
  have htailCont : Continuous (fun x : ℝ => Real.sqrt (D * x ^ (2 : ℕ))) :=
    Real.continuous_sqrt.comp (continuous_const.mul (continuous_id.pow 2))
  have hcore : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (C * (((n + 1 : ℕ) : ℝ)⁻¹) ^ (2 : ℕ)))
      Filter.atTop (nhds 0) := by
    convert (hcoreCont.tendsto 0).comp hinv using 1 <;> simp [Function.comp_def]
  have htail : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (D * (c + ((n + 1 : ℕ) : ℝ))⁻¹ ^ (2 : ℕ)))
      Filter.atTop (nhds 0) := by
    convert (htailCont.tendsto 0).comp hshiftInv using 1 <;> simp [Function.comp_def]
  simpa [C, D, c] using hcore.add htail

/-- Every positive tolerance admits a natural reciprocal mesh and a natural
quadratic cusp height whose combined finite-grid budget is smaller. -/
theorem exists_reciprocal_grid_budget_lt (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M K : ℕ, 0 < M ∧
      1 ≤ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹ ∧
      Real.sqrt (((Real.sqrt 3 / 2) ^ (2 : ℕ))⁻¹ * (16 * ((M : ℝ)⁻¹) ^ (2 : ℕ))) +
        Real.sqrt ((((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) *
          (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ (2 : ℕ)) < ε := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    ((tendsto_reciprocal_square_grid_budget N).eventually (gt_mem_nhds hε))
  refine ⟨n + 1, (n + 1) * (n + 1), Nat.succ_pos n, ?_, ?_⟩
  · have hmesh : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hquad : (((n + 1) * (n + 1) : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ =
        ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      field_simp
    rw [hquad]
    have hmeshOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [Real.sqrt_nonneg 3]
  · have hmesh : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hquad : (((n + 1) * (n + 1) : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ =
        ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      field_simp
    rw [hquad]
    simpa [mul_assoc] using hn n le_rfl

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
