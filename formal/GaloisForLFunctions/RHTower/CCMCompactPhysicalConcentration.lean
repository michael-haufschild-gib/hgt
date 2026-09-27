import GaloisForLFunctions.RHTower.CCMArchimedeanHilbertFormDomain
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform physical nonconcentration of the compact Gamma embedding

A compact family in physical L² carries uniformly little mass on sets of
small measure. Applied to the actual CCM form embedding, this controls the
operator norm of restriction to every small measurable set, independently
of the geometry or number of connected components of that set.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RHTower

private theorem cutoff_norm_le (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    ‖indicatorCutoff s hs f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖indicatorCutoff s hs‖ * ‖f‖ := (indicatorCutoff s hs).le_opNorm f
    _ ≤ 1 * ‖f‖ := by
      gcongr
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact Submodule.starProjection_norm_le _
    _ = _ := one_mul _

/-- Compact physical families are uniformly absolutely continuous in L² norm. -/
theorem exists_smallSet_cutoff_norm_le_of_isCompact
    (K : Set SoninL2) (hK : IsCompact K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ) (hs : MeasurableSet s),
      volume s ≤ ENNReal.ofReal delta → ∀ f ∈ K,
        ‖indicatorCutoff s hs f‖ ≤ epsilon := by
  obtain ⟨T, _, hT, hcover⟩ := hK.finite_cover_balls (half_pos hepsilon)
  letI : Fintype T := hT.fintype
  have hui : UnifIntegrable (fun f : T => (f.1 : ℝ → ℂ)) 2 volume :=
    unifIntegrable_finite (by norm_num) (by norm_num) (fun f => Lp.memLp f.1)
  obtain ⟨delta, hdelta, hsmall⟩ := hui (half_pos hepsilon)
  refine ⟨delta, hdelta, fun s hs hvol f hf => ?_⟩
  obtain ⟨g, hgT, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  have hg : ‖indicatorCutoff s hs g‖ ≤ epsilon / 2 := by
    rw [Lp.norm_def, eLpNorm_congr_ae (indicatorCutoff_ae s hs g)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hsmall ⟨g, hgT⟩ s hs hvol)).trans_eq
        (ENNReal.toReal_ofReal (half_pos hepsilon).le)
  have hdist : ‖f - g‖ < epsilon / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hfg
  calc
    ‖indicatorCutoff s hs f‖ ≤
        ‖indicatorCutoff s hs (f - g)‖ + ‖indicatorCutoff s hs g‖ := by
      rw [map_sub]
      exact norm_le_norm_sub_add _ _
    _ ≤ ‖f - g‖ + epsilon / 2 := add_le_add (cutoff_norm_le s hs _) hg
    _ ≤ epsilon := by linarith

/-- The actual compact Gamma form embedding has small norm on every small-measure set. -/
theorem exists_ccmSmallSet_restriction_norm_le
    (a : SuzukiPositiveAperture) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ) (hs : MeasurableSet s),
      volume s ≤ ENNReal.ofReal delta →
        ‖(indicatorCutoff s hs).comp (ccmArchimedeanFormEmbedding a)‖ ≤ epsilon := by
  obtain ⟨K, hK, hball⟩ :=
    (isCompactOperator_ccmArchimedeanFormEmbedding a).image_closedBall_subset_compact 1
  obtain ⟨delta, hdelta, hsmall⟩ :=
    exists_smallSet_cutoff_norm_le_of_isCompact K hK epsilon hepsilon
  refine ⟨delta, hdelta, fun s hs hvol => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hepsilon.le
  intro u hu
  exact hsmall s hs hvol _ (hball ⟨u, by simp only [Metric.mem_closedBall, dist_zero_right, hu, le_refl], rfl⟩)

/-- Uniform small-set control in squared mass, with any requested positive coefficient. -/
theorem exists_ccmSmallSet_mass_le
    (a : SuzukiPositiveAperture) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ) (hs : MeasurableSet s),
      volume s ≤ ENNReal.ofReal delta → ∀ u : CCMArchimedeanFormDomain a,
        ‖indicatorCutoff s hs (ccmArchimedeanFormEmbedding a u)‖ ^ 2 ≤ eta * ‖u‖ ^ 2 := by
  obtain ⟨delta, hdelta, hsmall⟩ :=
    exists_ccmSmallSet_restriction_norm_le a (Real.sqrt eta) (Real.sqrt_pos.mpr heta)
  refine ⟨delta, hdelta, fun s hs hvol u => ?_⟩
  have hb := ((indicatorCutoff s hs).comp (ccmArchimedeanFormEmbedding a)).le_of_opNorm_le
    (hsmall s hs hvol) u
  change ‖indicatorCutoff s hs (ccmArchimedeanFormEmbedding a u)‖ ≤ Real.sqrt eta * ‖u‖ at hb
  calc
    _ ≤ (Real.sqrt eta * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = eta * ‖u‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt heta.le]

end RHTower
