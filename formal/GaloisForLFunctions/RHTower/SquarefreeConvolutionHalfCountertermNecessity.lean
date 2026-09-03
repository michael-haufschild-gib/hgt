import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCofinalScheduleNoGo

/-!
# Counterterm necessity for squarefree-half regularizations

Any correction that makes a cofinal Cayley--Dirichlet family locally bounded must itself be
unbounded at the fixed exterior point.  In particular, pointwise-vanishing or uniformly bounded
perturbations cannot repair the raw truncations.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- A counterterm-corrected Cayley--Dirichlet approximation. -/
def poleClearedFirstTraceCountertermScheduledApprox
    (counterterm : ℕ → ℂ → ℂ) (kappa : ℕ → ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox (kappa N) s *
      (squarefreeHalfDirichletPartialSum N s + counterterm N s) /
    squarefreeCarlemanHalfDet s

/-- Local boundedness of a counterterm-corrected scheduled family. -/
def PoleClearedFirstTraceCountertermScheduledLocallyBounded
    (counterterm : ℕ → ℂ → ℂ) (kappa : ℕ → ℕ) : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N w‖ ≤ C

/-- If the corrected arithmetic values have a bounded tail, the correction cannot also have one. -/
theorem counterterm_not_eventually_bounded_of_corrected_eventually_bounded
    {counterterm : ℕ → ℂ}
    (hcorrected : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint + counterterm N‖ ≤ C) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N → ‖counterterm N‖ ≤ B := by
  obtain ⟨C, N₀, hC⟩ := hcorrected
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
  refine ⟨C + B, max N₀ M₀, fun N hN => ?_⟩
  have hNC : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNB : M₀ ≤ N := le_trans (le_max_right _ _) hN
  calc
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ =
        ‖(squarefreeHalfDirichletPartialSum N boundaryExteriorPoint + counterterm N) -
          counterterm N‖ := by ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint + counterterm N‖ +
          ‖counterterm N‖ := norm_sub_le _ _
    _ ≤ C + B := add_le_add (hC N hNC) (hB N hNB)

/-- Every locally bounded cofinal corrected family pays an unbounded counterterm at `s = 6/11`. -/
theorem counterterm_not_eventually_bounded_of_cofinal_locallyBounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N boundaryExteriorPoint‖ ≤ B := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N
        boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 24))
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  apply counterterm_not_eventually_bounded_of_corrected_eventually_bounded
  refine ⟨K, N₀, fun N hN => ?_⟩
  have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow (hN₀ N hN)
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
            counterterm N boundaryExteriorPoint‖ ≤ K := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hone : (1 : ℝ) ≤ (5 : ℝ) ^ (kappa N - 24) := one_le_pow₀ (by norm_num)
  calc
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
        counterterm N boundaryExteriorPoint‖ =
        1 * ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
          counterterm N boundaryExteriorPoint‖ := by ring
    _ ≤ (5 : ℝ) ^ (kappa N - 24) *
        ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
          counterterm N boundaryExteriorPoint‖ :=
      mul_le_mul_of_nonneg_right hone (norm_nonneg _)
    _ ≤ ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
        ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
          counterterm N boundaryExteriorPoint‖ :=
      mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ ≤ K := hprod

/-- An eventually bounded correction cannot repair any cofinal raw schedule. -/
theorem no_cofinal_locallyBounded_of_counterterm_eventually_bounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm : ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N boundaryExteriorPoint‖ ≤ B) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  exact (counterterm_not_eventually_bounded_of_cofinal_locallyBounded hkappa hloc)
    hcounterterm

/-- A correction tending to zero at the exterior point cannot repair any cofinal raw schedule. -/
theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm : Tendsto (fun N => counterterm N boundaryExteriorPoint) atTop (𝓝 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  apply no_cofinal_locallyBounded_of_counterterm_eventually_bounded hkappa
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

end

end RHTower
