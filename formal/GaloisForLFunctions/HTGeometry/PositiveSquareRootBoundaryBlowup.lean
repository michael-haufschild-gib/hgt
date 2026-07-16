import GaloisForLFunctions.HTGeometry.ScaledCentralBinomialAbelTransfer

open Filter Topology
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A positive square-root boundary coefficient forces the unscaled function to diverge to
positive infinity along the interior radial filter. -/
theorem tendsto_atTop_of_positive_sqrt_scaled_boundary
    {S : ℝ → ℝ} {B L : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hboundary : Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ 2 * t) * S t)
      (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2))) (nhds L)) :
    Tendsto S
      (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2))) atTop := by
  let F := nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2))
  let g : ℝ → ℝ := fun t => Real.sqrt (1 - B ^ 2 * t)
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hg_nhds : Tendsto g F (nhds 0) := by
    have hc : ContinuousAt g (1 / B ^ 2) := by
      dsimp only [g]
      fun_prop
    have hvalue : g (1 / B ^ 2) = 0 := by
      dsimp only [g]
      rw [show B ^ 2 * (1 / B ^ 2) = 1 by field_simp [hBsq.ne']]
      simp
    rw [← hvalue]
    exact hc.mono_left inf_le_left
  have hg_pos : ∀ᶠ t : ℝ in F, 0 < g t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    dsimp only [g]
    apply Real.sqrt_pos.2
    apply sub_pos.mpr
    have := (lt_div_iff₀ hBsq).1 ht.2
    simpa only [mul_comm] using this
  have hg_nhdsGT : Tendsto g F (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within g hg_nhds hg_pos
  have hginv : Tendsto (fun t => (g t)⁻¹) F atTop :=
    tendsto_inv_nhdsGT_zero.comp hg_nhdsGT
  have hproduct : Tendsto (fun t => (g t * S t) * (g t)⁻¹) F atTop := by
    have hb : Tendsto (fun t => g t * S t) F (nhds L) := by
      simpa only [g, F] using hboundary
    exact hb.pos_mul_atTop hL hginv
  apply hproduct.congr'
  filter_upwards [hg_pos] with t ht
  field_simp [ht.ne']

end

end GaloisForLFunctions.HTGeometry

