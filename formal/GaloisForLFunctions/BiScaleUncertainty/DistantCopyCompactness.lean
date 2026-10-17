import GaloisForLFunctions.BiScaleUncertainty.DistantCopyEnergyTopology
import GaloisForLFunctions.BiScaleUncertainty.SignedGridTraceCompactness

/-!
# Compactness classification for escaping copies

All amplitudes share one energy ceiling. Compact closure and uniform signed-grid
tail control are both equivalent to decay of the mixing coefficient.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def levyCopySeed (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hR : 0 < autocorr f 0) (D : ℝ) : LevyEnergySource (copyEnergyCeiling f D) where
  source := f
  smooth := hf
  mass_pos := hR
  energy_le := normalizedArchEnergy_le_copyEnergyCeiling hR D

def levyDistantCopy (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hR : 0 < autocorr f 0) {D T : ℝ}
    (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    LevyEnergySource (copyEnergyCeiling f D) where
  source := ⟨⟨subtractCopy f a T, continuous_subtractCopy f.continuous a T⟩,
    hasCompactSupport_subtractCopy f.hasCompactSupport a T⟩
  smooth := contDiff_subtractCopy hf a T
  mass_pos := autocorr_subtractCopy_zero_pos f.continuous f.hasCompactSupport hR hs (by linarith) a
  energy_le := normalizedArchEnergy_subtractCopy_le_copyEnergyCeiling hf f.hasCompactSupport hR hs hT a

/-- The exact distance in the global supremum norm equals the absolute mixing coefficient. -/
theorem levyDistantCopy_dist_seed (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hR : 0 < autocorr f 0) {D T : ℝ} (hD : 0 < D)
    (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    dist (levyDistantCopy f hf hR hs hT a).complexCorrelation
      (levyCopySeed f hf hR D).complexCorrelation = |copyMixingCoefficient a| := by
  have hsep : D < T := by linarith
  apply le_antisymm
  · apply (BoundedContinuousFunction.dist_le (abs_nonneg _)).mpr
    intro x
    simp only [LevyEnergySource.complexCorrelation_apply, Complex.isometry_ofReal.dist_eq,
      Real.dist_eq]
    exact normalizedSourceCorrelation_subtractCopy_error_le f.continuous f.hasCompactSupport hR hs hsep a x
  · have hb := BoundedContinuousFunction.dist_coe_le_dist
      (f := (levyDistantCopy f hf hR hs hT a).complexCorrelation)
      (g := (levyCopySeed f hf hR D).complexCorrelation) T
    simp only [LevyEnergySource.complexCorrelation_apply, Complex.isometry_ofReal.dist_eq,
      Real.dist_eq] at hb
    change |normalizedSourceCorrelation (subtractCopy f a T) T - normalizedSourceCorrelation f T| ≤ _ at hb
    rwa [normalizedSourceCorrelation_subtractCopy_error_at_center
      (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport hR hD hs hsep] at hb

/-- Escaping copies form a relatively compact correlation family exactly when their mixing decays. -/
theorem isCompact_closure_distantCopies_iff (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hR : 0 < autocorr f 0) {D : ℝ} (hD : 0 < D)
    (hs : ∀ x, D < |x| → autocorr f x = 0) (a T : ℕ → ℝ)
    (hsep : ∀ n, D + 1 ≤ T n) (hT : Tendsto T atTop atTop) :
    IsCompact (closure (LevyEnergySource.complexCorrelation ''
      range (fun n => levyDistantCopy f hf hR hs (hsep n) (a n)))) ↔
    Tendsto (fun n => copyMixingCoefficient (a n)) atTop (𝓝 0) := by
  let F := levyCopySeed f hf hR D
  let G := fun n => levyDistantCopy f hf hR hs (hsep n) (a n)
  constructor
  · intro hc
    have ht := uniformCorrelationTail_of_isCompact_closure hc
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨A, _, hA⟩ := ht ε hε
    filter_upwards [hT.eventually (eventually_ge_atTop A)] with n hn
    have hb := hA (G n) (mem_range_self n) (T n) (hn.trans (le_abs_self _))
    change |normalizedSourceCorrelation (subtractCopy f (a n) (T n)) (T n)| < ε at hb
    rw [normalizedSourceCorrelation_subtractCopy_center (f := (f : ℝ → ℝ)) (T := T n)
      f.continuous f.hasCompactSupport hR hD hs (by linarith [hsep n]), abs_neg] at hb
    simpa only [Real.dist_eq, sub_zero] using hb
  · intro hb
    have hg : Tendsto (fun n => (G n).complexCorrelation) atTop (𝓝 F.complexCorrelation) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [Metric.tendsto_nhds.mp hb ε hε] with n hn
      rw [levyDistantCopy_dist_seed f hf hR hD hs (hsep n)]
      simpa only [Real.dist_eq, sub_zero] using hn
    have heq : LevyEnergySource.complexCorrelation '' range G =
        range (fun n => (G n).complexCorrelation) := by
      ext z
      constructor
      · rintro ⟨g, ⟨n, rfl⟩, rfl⟩
        exact mem_range_self n
      · rintro ⟨n, rfl⟩
        exact ⟨G n, mem_range_self n, rfl⟩
    change IsCompact (closure (LevyEnergySource.complexCorrelation '' range G))
    rw [heq]
    exact hg.isCompact_insert_range.of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ hz => mem_insert_of_mem _ hz) hg.isCompact_insert_range.isClosed)

/-- Uniform signed-grid tail decay has the same exact mixing-coefficient criterion. -/
theorem uniformSignedGridTail_distantCopies_iff (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hR : 0 < autocorr f 0) {D : ℝ} (hD : 0 < D)
    (hs : ∀ x, D < |x| → autocorr f x = 0) (a T : ℕ → ℝ)
    (hsep : ∀ n, D + 1 ≤ T n) (hT : Tendsto T atTop atTop) :
    UniformSignedGridTail (range (fun n => levyDistantCopy f hf hR hs (hsep n) (a n))) ↔
      Tendsto (fun n => copyMixingCoefficient (a n)) atTop (𝓝 0) :=
  (isCompact_closure_signed_correlations_iff_gridTail _).symm.trans
    (isCompact_closure_distantCopies_iff f hf hR hD hs a T hsep hT)

/-- Every fixed bounded window is eventually exactly unchanged, regardless of amplitudes. -/
theorem eventually_subtractCopy_correlation_eq_on_window {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {D : ℝ}
    (hs : ∀ x, D < |x| → autocorr f x = 0) (a T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x| ≤ A →
      normalizedSourceCorrelation (subtractCopy f (a n) (T n)) x = normalizedSourceCorrelation f x := by
  filter_upwards [hT.eventually (eventually_gt_atTop (D + A))] with n hn x hx
  exact normalized_autocorr_subtractCopy_local hf hfc hA hs hn hx (a n)

end

end GaloisForLFunctions.BiScaleUncertainty
