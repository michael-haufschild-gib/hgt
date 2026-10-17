import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainEnergy
import GaloisForLFunctions.BiScaleUncertainty.SignedGridTraceCompactness

/-!
# Exact compactness criterion with arbitrary growing train data

The same peak controls global uniform convergence, compact correlation closure,
and uniform signed logarithmic traces. Packet counts and integer sites may vary.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem integer_center_abs_ge {S : ℝ} (hS : 0 ≤ S) {k : ℤ} (hk : k ≠ 0) :
    S ≤ |(k : ℝ) * S| := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hb : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have hm := mul_le_mul_of_nonneg_right hb hS
    exact (by nlinarith only [hm] : S ≤ -((k : ℝ) * S)).trans (neg_le_abs _)
  · have hb : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hb hS
    have hm' : S ≤ (k : ℝ) * S := by simpa only [one_mul] using hm
    exact hm'.trans (le_abs_self _)

theorem levyIntegerTrain_dist_seed (d : IntegerPacketTrain) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hR : 0 < autocorr f 0) {D S : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D + 2 ≤ S) :
    dist (levyIntegerTrain d f hf hR hD hs hS).complexCorrelation
      (levyIntegerTrainSeed f hf hR).complexCorrelation = d.peak := by
  have hsep : 2 * D < S := by linarith only [hS]
  apply le_antisymm
  · apply (BoundedContinuousFunction.dist_le d.peak_nonneg).mpr
    intro x
    simp only [LevyEnergySource.complexCorrelation_apply, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    exact d.normalized_source_error_le_peak f.continuous f.hasCompactSupport hR hD hs hsep x
  · rcases d.peak_attained with hz | ⟨k, hk, hk0, hp⟩
    · rw [hz]
      exact dist_nonneg
    · have hb := BoundedContinuousFunction.dist_coe_le_dist
        (f := (levyIntegerTrain d f hf hR hD hs hS).complexCorrelation)
        (g := (levyIntegerTrainSeed f hf hR).complexCorrelation) ((k : ℝ) * S)
      simp only [LevyEnergySource.complexCorrelation_apply, Complex.isometry_ofReal.dist_eq,
        Real.dist_eq] at hb
      change |normalizedSourceCorrelation (d.source f S) ((k : ℝ) * S) -
        normalizedSourceCorrelation f ((k : ℝ) * S)| ≤ _ at hb
      rwa [d.normalized_source_error_at_lag (f := (f : ℝ → ℝ)) f.continuous
        f.hasCompactSupport hR hD hs hsep hk hk0, ← hp] at hb

theorem tendstoUniformly_integerTrains_iff_peak {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (d : ℕ → IntegerPacketTrain) (S : ℕ → ℝ) (hsep : ∀ n, 2 * D < S n) :
    TendstoUniformly (fun n => normalizedSourceCorrelation ((d n).source f (S n)))
      (normalizedSourceCorrelation f) atTop ↔ Tendsto (fun n => (d n).peak) atTop (𝓝 0) := by
  constructor
  · intro hu
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (d n).peak_nonneg]
    rcases (d n).peak_attained with hz | ⟨k, hk, hk0, hp⟩
    · simpa only [hz] using hε
    · have hb := hn ((k : ℝ) * S n)
      rw [Real.dist_eq, abs_sub_comm,
        (d n).normalized_source_error_at_lag hf hfc hR hD hs (hsep n) hk hk0, ← hp] at hb
      exact hb
  · intro hp
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp hp).2 ε hε] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact ((d n).normalized_source_error_le_peak hf hfc hR hD hs (hsep n) x).trans_lt hn

/-- Compactness is exactly peak decay, even for arbitrary growing coefficient data. -/
theorem isCompact_closure_integerTrains_iff_peak (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hR : 0 < autocorr f 0) {D : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (d : ℕ → IntegerPacketTrain) (S : ℕ → ℝ)
    (hsep : ∀ n, 2 * D + 2 ≤ S n) (hS : Tendsto S atTop atTop) :
    IsCompact (closure (LevyEnergySource.complexCorrelation ''
      range (fun n => levyIntegerTrain (d n) f hf hR hD hs (hsep n)))) ↔
      Tendsto (fun n => (d n).peak) atTop (𝓝 0) := by
  let F := levyIntegerTrainSeed f hf hR
  let G := fun n => levyIntegerTrain (d n) f hf hR hD hs (hsep n)
  constructor
  · intro hc
    have ht := uniformCorrelationTail_of_isCompact_closure hc
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨A, _, hA⟩ := ht ε hε
    filter_upwards [hS.eventually (eventually_ge_atTop A)] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (d n).peak_nonneg]
    rcases (d n).peak_attained with hz | ⟨k, hk, hk0, hp⟩
    · simpa only [hz] using hε
    · have hSn : 0 ≤ S n := by have hh := hsep n; linarith only [hD, hh]
      have hb := hA (G n) (mem_range_self n) ((k : ℝ) * S n)
        (hn.trans (integer_center_abs_ge hSn hk0))
      change |normalizedSourceCorrelation ((d n).source f (S n)) ((k : ℝ) * S n)| < ε at hb
      rw [(d n).normalized_source_at_lag (f := (f : ℝ → ℝ)) (S := S n) f.continuous
        f.hasCompactSupport hR hD hs (by have hh := hsep n; linarith only [hh]) hk,
        abs_div, abs_of_pos (d n).mass_pos, ← hp] at hb
      exact hb
  · intro hp
    have hg : Tendsto (fun n => (G n).complexCorrelation) atTop (𝓝 F.complexCorrelation) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [(tendsto_order.mp hp).2 ε hε] with n hn
      rw [levyIntegerTrain_dist_seed (d n) f hf hR hD hs (hsep n)]
      exact hn
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

theorem uniformSignedGridTail_integerTrains_iff_peak (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hR : 0 < autocorr f 0) {D : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (d : ℕ → IntegerPacketTrain) (S : ℕ → ℝ)
    (hsep : ∀ n, 2 * D + 2 ≤ S n) (hS : Tendsto S atTop atTop) :
    UniformSignedGridTail (range (fun n => levyIntegerTrain (d n) f hf hR hD hs (hsep n))) ↔
      Tendsto (fun n => (d n).peak) atTop (𝓝 0) :=
  (isCompact_closure_signed_correlations_iff_gridTail _).symm.trans
    (isCompact_closure_integerTrains_iff_peak f hf hR hD hs d S hsep hS)

end
end GaloisForLFunctions.BiScaleUncertainty
