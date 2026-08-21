import GaloisForLFunctions.RHTower.ConnesSobolevMeasure
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Continuity of translation on Connes' Sobolev space

Appendix I (3)-(5) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The translation `V(v)ξ = ξ(· − v)` is bounded on `L²_δ(ℝ) = L²(ρ_δ(u) du)` with norm at most
`(2^{δ/2} ρ_δ(v))^{1/2}`, uniformly bounded for `|v| ≤ 1`.  Because `ρ_δ` is continuous the
weighted measure is finite on compacts, hence regular, so continuous compactly supported
functions are dense; on those, translation continuity is dominated convergence against the
finite mass of a fixed compact neighbourhood of the support.  The uniform operator bound then
transports the continuity to every vector of the space.  This is what makes `V(f)` a genuine
approximate unit in the Sobolev space.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_aestronglyMeasurable_sobolev {δ : ℝ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable f (connesSobolevMeasure δ) :=
  (HTGeometry.aestronglyMeasurable_withDensity_realDensity_iff
    (measurable_connesSobolevWeight δ) (connesSobolevWeight_pos δ)).mpr hf

theorem connes_aestronglyMeasurable_volume {δ : ℝ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (connesSobolevMeasure δ)) :
    AEStronglyMeasurable f volume :=
  (HTGeometry.aestronglyMeasurable_withDensity_realDensity_iff
    (measurable_connesSobolevWeight δ) (connesSobolevWeight_pos δ)).mp hf

/-- Continuity of translation on `L²_δ` for a continuous compactly supported vector. -/
theorem connes_translation_tendsto_of_compactSupport (δ : ℝ) {g : ℝ → ℂ}
    (hg : Continuous g) (hsupp : HasCompactSupport g) :
    Tendsto (fun v : ℝ => eLpNorm (fun u => g (u - v) - g u) 2 (connesSobolevMeasure δ))
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hg
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  obtain ⟨R, hR⟩ := (hsupp.isBounded).subset_closedBall (0 : ℝ)
  set K : Set ℝ := Metric.closedBall (0 : ℝ) (R + 1) with hK
  have hKcomp : IsCompact K := isCompact_closedBall _ _
  have hKmeas : MeasurableSet K := hKcomp.measurableSet
  set bound : ℝ → ℝ≥0∞ := Set.indicator K (fun _ => ENNReal.ofReal ((2 * C) ^ 2)) with hbound
  -- the dominating function has finite mass
  have hfin : ∫⁻ u, bound u ∂(connesSobolevMeasure δ) ≠ ∞ := by
    rw [hbound, lintegral_indicator hKmeas, setLIntegral_const]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKcomp.measure_lt_top).ne
  -- the lower integrals tend to zero
  have hlint : Tendsto (fun v : ℝ => ∫⁻ u, ‖g (u - v) - g u‖ₑ ^ 2 ∂(connesSobolevMeasure δ))
      (𝓝 0) (𝓝 0) := by
    have hzero : (0 : ℝ≥0∞) = ∫⁻ _u : ℝ, (0 : ℝ≥0∞) ∂(connesSobolevMeasure δ) := by simp
    rw [hzero]
    refine tendsto_lintegral_filter_of_dominated_convergence bound ?_ ?_ hfin ?_
    · filter_upwards with v
      have hcont : Continuous fun u : ℝ => ‖g (u - v) - g u‖ₑ :=
        ((hg.comp (continuous_id.sub continuous_const)).sub hg).enorm
      exact hcont.measurable.pow_const 2
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with v hv
      filter_upwards with u
      have hv1 : |v| < 1 := by simpa [Real.dist_eq] using hv
      by_cases hu : u ∈ K
      · rw [hbound, Set.indicator_of_mem hu]
        have hle : ‖g (u - v) - g u‖ ≤ 2 * C := by
          calc ‖g (u - v) - g u‖ ≤ ‖g (u - v)‖ + ‖g u‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add (hC _) (hC _)
            _ = 2 * C := by ring
        have h2 : ‖g (u - v) - g u‖ₑ ≤ ENNReal.ofReal (2 * C) := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hle
        calc ‖g (u - v) - g u‖ₑ ^ 2 ≤ (ENNReal.ofReal (2 * C)) ^ 2 := by
              exact pow_le_pow_left' h2 2
          _ = ENNReal.ofReal ((2 * C) ^ 2) := by
              rw [← ENNReal.ofReal_pow (by positivity)]
      · rw [hbound, Set.indicator_of_notMem hu]
        have hmemK : ∀ y : ℝ, y ∈ tsupport g → |y| ≤ R := by
          intro y hy
          have := hR hy
          rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
          exact this
        have hunotK : ¬ |u| ≤ R + 1 := by
          intro hle
          exact hu (by rw [hK, Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hle)
        have hgu : g u = 0 := by
          by_contra hne
          exact hunotK (le_trans (hmemK u (subset_tsupport g hne)) (by linarith))
        have hguv : g (u - v) = 0 := by
          by_contra hne
          have hmem := hmemK (u - v) (subset_tsupport g hne)
          have : |u| ≤ |u - v| + |v| := by
            have := abs_sub_abs_le_abs_sub u v
            have h2 : |u| - |v| ≤ |u - v| := by
              have := abs_sub_abs_le_abs_sub u v
              linarith [abs_nonneg v]
            linarith
          exact hunotK (by linarith)
        rw [hgu, hguv]
        simp
    · filter_upwards with u
      have hcont : Tendsto (fun v : ℝ => g (u - v) - g u) (𝓝 0) (𝓝 (g (u - 0) - g u)) :=
        ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const).continuousAt
      rw [sub_zero, sub_self] at hcont
      have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp
        (continuous_enorm.continuousAt.tendsto.comp hcont)
      simpa [Function.comp_def] using this
  -- take square roots
  have hsq : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    have h0 : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    have := hc.continuousAt (x := (0 : ℝ≥0∞))
    rw [ContinuousAt, h0] at this
    exact this
  have := hsq.comp hlint
  refine this.congr fun v => ?_
  rw [Function.comp_apply, connes_eLpNorm_two_sq]

/-- The uniform bound of the translation operators on the unit interval. -/
theorem connes_eLpNorm_translate_le_uniform {δ : ℝ} (hδ : 0 ≤ δ) {ξ : ℝ → ℂ}
    (hξ : AEStronglyMeasurable ξ volume) {v : ℝ} (hv : |v| ≤ 1) :
    eLpNorm (fun u => ξ (u - v)) 2 (connesSobolevMeasure δ)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (δ / 2)) * eLpNorm ξ 2 (connesSobolevMeasure δ) := by
  refine le_trans (connes_eLpNorm_translate_le hδ hξ v) ?_
  refine mul_le_mul' ?_ (le_refl _)
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (δ / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hle : 2 ^ (δ / 2) * connesSobolevWeight δ v ≤ 2 ^ (δ / 2) * 2 ^ (δ / 2) :=
    mul_le_mul_of_nonneg_left (connesSobolevWeight_le_of_abs_le_one hδ hv) hpow.le
  calc Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v)
      ≤ Real.sqrt (2 ^ (δ / 2) * 2 ^ (δ / 2)) := Real.sqrt_le_sqrt hle
    _ = 2 ^ (δ / 2) := Real.sqrt_mul_self hpow.le

/-- **Appendix I, continuity of translation on `L²_δ(ℝ)`.**  For every vector of the Sobolev
space the translates converge to the vector as the shift tends to zero. -/
theorem connes_translation_tendsto {δ : ℝ} (hδ : 0 ≤ δ) {ξ : ℝ → ℂ}
    (hξ : MemLp ξ 2 (connesSobolevMeasure δ)) :
    Tendsto (fun v : ℝ => eLpNorm (fun u => ξ (u - v) - ξ u) 2 (connesSobolevMeasure δ))
      (𝓝 0) (𝓝 0) := by
  have hξvol : AEStronglyMeasurable ξ volume := connes_aestronglyMeasurable_volume hξ.1
  set Cδ : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (δ / 2)) with hCδ
  have hCδtop : Cδ ≠ ∞ := ENNReal.ofReal_ne_top
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set D : ℝ≥0∞ := Cδ + 2 with hD
  have hDtop : D ≠ ∞ := by
    rw [hD]
    exact ENNReal.add_ne_top.mpr ⟨hCδtop, by norm_num⟩
  have hD0 : D ≠ 0 := by
    rw [hD]
    have h2 : (0 : ℝ≥0∞) < 2 := by norm_num
    exact (lt_of_lt_of_le h2 le_add_self).ne'
  set η : ℝ≥0∞ := ε / D with hη
  have hη0 : η ≠ 0 := by
    rw [hη]
    exact (ENNReal.div_ne_zero).mpr ⟨hε.ne', hDtop⟩
  have hDη : D * η = ε := by
    rw [hη, ENNReal.mul_div_cancel hD0 hDtop]
  obtain ⟨g, hgsupp, hgclose, hgcont, hgmem⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le (μ := connesSobolevMeasure δ)
      (by norm_num) hξ hη0
  have hgvol : AEStronglyMeasurable g volume := hgcont.aestronglyMeasurable
  have hdiffvol : AEStronglyMeasurable (fun u => ξ u - g u) volume := hξvol.sub hgvol
  have hsub : eLpNorm (fun u => ξ u - g u) 2 (connesSobolevMeasure δ) ≤ η := by
    refine le_trans (le_of_eq ?_) hgclose
    rfl
  have hgtend := connes_translation_tendsto_of_compactSupport δ hgcont hgsupp
  rw [ENNReal.tendsto_nhds_zero] at hgtend
  filter_upwards [hgtend η hη0.bot_lt, Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with v hgv hv
  have hv1 : |v| ≤ 1 := by simpa [Real.dist_eq] using hv
  have hsplit : (fun u => ξ (u - v) - ξ u)
      = (fun u => (ξ (u - v) - g (u - v)) + ((g (u - v) - g u) + (g u - ξ u))) := by
    funext u; ring
  have hA : AEStronglyMeasurable (fun u => ξ (u - v) - g (u - v)) (connesSobolevMeasure δ) :=
    connes_aestronglyMeasurable_sobolev (aestronglyMeasurable_translate hdiffvol v)
  have hB : AEStronglyMeasurable (fun u => g (u - v) - g u) (connesSobolevMeasure δ) :=
    connes_aestronglyMeasurable_sobolev
      ((aestronglyMeasurable_translate hgvol v).sub hgvol)
  have hC : AEStronglyMeasurable (fun u => g u - ξ u) (connesSobolevMeasure δ) :=
    connes_aestronglyMeasurable_sobolev (hgvol.sub hξvol)
  have hBC : AEStronglyMeasurable
      (fun u => (g (u - v) - g u) + (g u - ξ u)) (connesSobolevMeasure δ) := hB.add hC
  have htri : eLpNorm (fun u => ξ (u - v) - ξ u) 2 (connesSobolevMeasure δ)
      ≤ eLpNorm (fun u => ξ (u - v) - g (u - v)) 2 (connesSobolevMeasure δ)
        + (eLpNorm (fun u => g (u - v) - g u) 2 (connesSobolevMeasure δ)
          + eLpNorm (fun u => g u - ξ u) 2 (connesSobolevMeasure δ)) := by
    rw [hsplit]
    have hone : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have hstep1 : eLpNorm (fun u => (ξ (u - v) - g (u - v))
          + ((g (u - v) - g u) + (g u - ξ u))) 2 (connesSobolevMeasure δ)
        ≤ eLpNorm (fun u => ξ (u - v) - g (u - v)) 2 (connesSobolevMeasure δ)
          + eLpNorm (fun u => (g (u - v) - g u) + (g u - ξ u)) 2 (connesSobolevMeasure δ) :=
      eLpNorm_add_le hA hBC hone
    have hstep2 : eLpNorm (fun u => (g (u - v) - g u) + (g u - ξ u)) 2 (connesSobolevMeasure δ)
        ≤ eLpNorm (fun u => g (u - v) - g u) 2 (connesSobolevMeasure δ)
          + eLpNorm (fun u => g u - ξ u) 2 (connesSobolevMeasure δ) :=
      eLpNorm_add_le hB hC hone
    exact le_trans hstep1 (add_le_add (le_refl _) hstep2)
  have hAle : eLpNorm (fun u => ξ (u - v) - g (u - v)) 2 (connesSobolevMeasure δ) ≤ Cδ * η := by
    refine le_trans (connes_eLpNorm_translate_le_uniform hδ hdiffvol hv1) ?_
    exact mul_le_mul' (le_refl _) hsub
  have hCle : eLpNorm (fun u => g u - ξ u) 2 (connesSobolevMeasure δ) ≤ η := by
    have heq : eLpNorm (ξ - g) 2 (connesSobolevMeasure δ)
        = eLpNorm (g - ξ) 2 (connesSobolevMeasure δ) := eLpNorm_sub_comm _ _ _ _
    exact heq ▸ hgclose
  calc eLpNorm (fun u => ξ (u - v) - ξ u) 2 (connesSobolevMeasure δ)
      ≤ Cδ * η + (η + η) := le_trans htri (add_le_add hAle (add_le_add hgv hCle))
    _ = D * η := by rw [hD]; ring
    _ = ε := hDη

end
end GaloisForLFunctions.RHTower
