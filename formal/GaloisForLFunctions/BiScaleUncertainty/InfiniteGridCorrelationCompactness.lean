import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridUniformTail
import GaloisForLFunctions.HTGeometry.BoundedContinuousUniformTailCompactness
import Mathlib.Topology.Sequences

/-!
# Compactness of bounded-energy infinite-grid correlations

Actual compact C² sources of bounded normalized energy give a relatively compact family
of normalized correlations in the global supremum norm. Every uniform limit retains
normalization, evenness, the complete logarithmic grid, and vanishing at both infinities.
The compactness argument concerns correlations and does not assert a source for the limit.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- The actual source domain at a fixed normalized energy ceiling. -/
structure InfiniteGridEnergySource (K : ℝ) where
  source : C_c(ℝ, ℝ)
  smooth : ContDiff ℝ 2 (source : ℝ → ℝ)
  mass_pos : 0 < autocorr source 0
  energy_le : normalizedArchEnergy source ≤ K
  grid_zero : ∀ n : ℕ, 2 ≤ n → autocorr source (Real.log (n : ℝ)) = 0

variable {K : ℝ}

/-- The normalized real correlation of an actual source. -/
def InfiniteGridEnergySource.correlation (f : InfiniteGridEnergySource K) (x : ℝ) : ℝ :=
  autocorr f.source x / autocorr f.source 0

theorem InfiniteGridEnergySource.continuous_correlation (f : InfiniteGridEnergySource K) :
    Continuous f.correlation :=
  (continuous_autocorr f.smooth f.source.hasCompactSupport).div_const _

theorem InfiniteGridEnergySource.abs_correlation_le_one (f : InfiniteGridEnergySource K)
    (x : ℝ) : |f.correlation x| ≤ 1 := by
  rw [correlation, abs_div, abs_of_pos f.mass_pos]
  exact (div_le_one f.mass_pos).mpr
    (abs_autocorr_le_zero f.source.hasCompactSupport f.source.continuous x)

@[simp]
theorem InfiniteGridEnergySource.correlation_zero (f : InfiniteGridEnergySource K) :
    f.correlation 0 = 1 := div_self f.mass_pos.ne'

@[simp]
theorem InfiniteGridEnergySource.correlation_neg (f : InfiniteGridEnergySource K)
    (x : ℝ) : f.correlation (-x) = f.correlation x := by
  simp only [correlation, autocorr_neg]

theorem InfiniteGridEnergySource.correlation_log_nat (f : InfiniteGridEnergySource K)
    {n : ℕ} (hn : 2 ≤ n) : f.correlation (Real.log (n : ℝ)) = 0 := by
  simp only [correlation, f.grid_zero n hn, zero_div]

/-- Isometric complexification permits use of the general bounded-function compactness theorem. -/
def InfiniteGridEnergySource.complexCorrelation (f : InfiniteGridEnergySource K) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (f.correlation x : ℂ))
    (Complex.continuous_ofReal.comp f.continuous_correlation) 1
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using f.abs_correlation_le_one x)

@[simp]
theorem InfiniteGridEnergySource.complexCorrelation_apply (f : InfiniteGridEnergySource K)
    (x : ℝ) : f.complexCorrelation x = (f.correlation x : ℂ) := rfl

/-- Bounded normalized energy and the complete grid give compact closure in the global norm. -/
theorem isCompact_closure_infiniteGrid_correlations (hK : 0 ≤ K) :
    IsCompact (closure (range (InfiniteGridEnergySource.complexCorrelation (K := K)))) := by
  apply HTGeometry.isCompact_closure_bcf_of_uniform_tails (M := 1)
  · rintro g ⟨f, rfl⟩ x
    simpa only [InfiniteGridEnergySource.complexCorrelation_apply, Complex.norm_real,
      Real.norm_eq_abs] using f.abs_correlation_le_one x
  · intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hm⟩ := exists_uniform_autocorr_continuity_radius hK hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy g
    rcases g.property with ⟨f, hf⟩
    rw [← hf]
    simp only [InfiniteGridEnergySource.complexCorrelation_apply,
      Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    apply hm f.source f.smooth f.source.hasCompactSupport f.mass_pos f.energy_le x y
    simpa only [Real.dist_eq, abs_sub_comm] using hy
  · intro ε hε
    obtain ⟨A, _, ht⟩ := exists_uniform_infinite_grid_tail_radius hK hε
    refine ⟨A, ?_⟩
    rintro g ⟨f, rfl⟩ x hx
    simpa only [InfiniteGridEnergySource.complexCorrelation_apply, Complex.norm_real,
      Real.norm_eq_abs, InfiniteGridEnergySource.correlation] using
      (ht f.source f.smooth f.source.hasCompactSupport f.mass_pos f.energy_le f.grid_zero x hx).le

/-- Every sequence of actual sources has a subsequence converging uniformly on the entire line. -/
theorem exists_uniform_limit_infiniteGrid_correlations (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) :
    ∃ (φ : ℕ → ℕ) (H : ℝ → ℝ), StrictMono φ ∧ Continuous H ∧
      TendstoUniformly (fun n => (f (φ n)).correlation) H atTop := by
  obtain ⟨g, _, φ, hφ, hg⟩ := (isCompact_closure_infiniteGrid_correlations hK).tendsto_subseq
    (x := fun n => (f n).complexCorrelation) (fun n => subset_closure (mem_range_self _))
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hg
  have hr := Complex.uniformContinuous_re.comp_tendstoUniformly hu
  refine ⟨φ, fun x => (g x).re, hφ, Complex.continuous_re.comp g.continuous, ?_⟩
  simpa only [Function.comp_def, InfiniteGridEnergySource.complexCorrelation_apply,
    Complex.ofReal_re] using hr

/-- Pointwise closed geometric constraints and uniform tails survive every uniform limit. -/
theorem infiniteGrid_uniform_limit_geometry (hK : 0 ≤ K)
    (f : ℕ → InfiniteGridEnergySource K) {H : ℝ → ℝ}
    (h : TendstoUniformly (fun n => (f n).correlation) H atTop) :
    Continuous H ∧ H 0 = 1 ∧ Function.Even H ∧ (∀ x, |H x| ≤ 1) ∧
      (∀ n : ℕ, 2 ≤ n → H (Real.log (n : ℝ)) = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A ≤ |x| → |H x| < ε := by
  refine ⟨h.continuous (Eventually.of_forall fun n => (f n).continuous_correlation).frequently,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h0 := h.tendsto_at 0
    simp only [InfiniteGridEnergySource.correlation_zero] at h0
    exact tendsto_nhds_unique h0 tendsto_const_nhds
  · intro x
    have hn := h.tendsto_at (-x)
    simp only [InfiniteGridEnergySource.correlation_neg] at hn
    exact tendsto_nhds_unique hn (h.tendsto_at x)
  · intro x
    exact le_of_tendsto' (h.tendsto_at x).abs fun n => (f n).abs_correlation_le_one x
  · intro n hn
    have hz := h.tendsto_at (Real.log (n : ℝ))
    simp only [InfiniteGridEnergySource.correlation_log_nat _ hn] at hz
    exact tendsto_nhds_unique hz tendsto_const_nhds
  · intro ε hε
    obtain ⟨A, hA, ht⟩ := exists_uniform_infinite_grid_tail_radius hK (half_pos hε)
    refine ⟨A, hA, ?_⟩
    intro x hx
    have hb : |H x| ≤ ε / 2 := le_of_tendsto' (h.tendsto_at x).abs fun n =>
      (ht (f n).source (f n).smooth (f n).source.hasCompactSupport (f n).mass_pos
        (f n).energy_le (f n).grid_zero x hx).le
    linarith

end

end GaloisForLFunctions.BiScaleUncertainty
