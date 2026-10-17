import GaloisForLFunctions.BiScaleUncertainty.SignedGridTailEquivalence
import GaloisForLFunctions.HTGeometry.BoundedContinuousUniformTailCompactness
import Mathlib.Topology.Sequences

/-!
# Exact compactness criterion from signed logarithmic traces

A family of actual normalized correlations at one energy ceiling has compact
closure in the global supremum norm exactly when its signed logarithmic traces
vanish uniformly at infinity. Finite nets use centers from the actual source family.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {K : ℝ}

private theorem finite_family_zero_radius (t : Set (ℝ →ᵇ ℂ)) (ht : t.Finite)
    (hz : ∀ g ∈ t, ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A ≤ |x| → g x = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ g ∈ t, ∀ x : ℝ, A ≤ |x| → g x = 0 := by
  induction t, ht using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha hs ih =>
    obtain ⟨A, hA, hAz⟩ := hz a (mem_insert a s)
    obtain ⟨B, _, hBz⟩ := ih (fun g hg => hz g (mem_insert_of_mem a hg))
    refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
    intro g hg x hx
    rcases mem_insert_iff.mp hg with rfl | hg
    · exact hAz x ((le_max_left _ _).trans hx)
    · exact hBz g hg x ((le_max_right _ _).trans hx)

/-- Energy-controlled local equicontinuity and full tails give compact global closure. -/
theorem isCompact_closure_signed_correlations_of_tail {S : Set (LevyEnergySource K)}
    (h : UniformCorrelationTail S) :
    IsCompact (closure (LevyEnergySource.complexCorrelation '' S)) := by
  apply HTGeometry.isCompact_closure_bcf_of_uniform_tails (M := 1)
  · rintro g ⟨f, _, rfl⟩ x
    simpa only [LevyEnergySource.complexCorrelation_apply, Complex.norm_real,
      Real.norm_eq_abs] using f.abs_correlation_le_one x
  · intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hm⟩ := exists_uniform_autocorr_continuity_radius (le_max_right K 0) hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy g
    rcases g.property with ⟨f, _, hf⟩
    rw [← hf]
    simp only [LevyEnergySource.complexCorrelation_apply,
      Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    apply hm f.source f.smooth f.source.hasCompactSupport f.mass_pos
      (f.energy_le.trans (le_max_left K 0)) x y
    simpa only [Real.dist_eq, abs_sub_comm] using hy
  · intro ε hε
    obtain ⟨A, _, ht⟩ := h ε hε
    refine ⟨A, ?_⟩
    rintro g ⟨f, hf, rfl⟩ x hx
    simpa only [LevyEnergySource.complexCorrelation_apply, Complex.norm_real,
      Real.norm_eq_abs] using (ht f hf x hx).le

/-- Compact closure forces uniform tails because finite nets have actual compact-source centers. -/
theorem uniformCorrelationTail_of_isCompact_closure {S : Set (LevyEnergySource K)}
    (h : IsCompact (closure (LevyEnergySource.complexCorrelation '' S))) :
    UniformCorrelationTail S := by
  intro ε hε
  obtain ⟨t, hts, ht, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure h (half_pos hε)
  have hz : ∀ g ∈ t, ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A ≤ |x| → g x = 0 := by
    intro g hg
    obtain ⟨f, _, rfl⟩ := hts hg
    obtain ⟨A, hA, hf⟩ := f.exists_correlation_zero_radius
    refine ⟨A, hA, ?_⟩
    intro x hx
    change (f.correlation x : ℂ) = 0
    exact congrArg (fun r : ℝ => (r : ℂ)) (hf x hx)
  obtain ⟨A, hA, hzero⟩ := finite_family_zero_radius t ht hz
  refine ⟨A, hA, ?_⟩
  intro f hf x hx
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover ⟨f, hf, rfl⟩)
  have hdist : dist f.complexCorrelation g < ε / 2 := hfg
  have he := BoundedContinuousFunction.dist_coe_le_dist
    (f := f.complexCorrelation) (g := g) x
  rw [hzero g hg x hx, dist_zero_right] at he
  have hnear := he.trans_lt hdist
  have hsmall : |f.correlation x| < ε / 2 := by
    simpa only [LevyEnergySource.complexCorrelation_apply, Complex.norm_real,
      Real.norm_eq_abs] using hnear
  linarith only [hsmall, hε]

/-- Global compactness is equivalent to continuum tail tightness on the actual source domain. -/
theorem isCompact_closure_signed_correlations_iff_tail (S : Set (LevyEnergySource K)) :
    IsCompact (closure (LevyEnergySource.complexCorrelation '' S)) ↔ UniformCorrelationTail S :=
  ⟨uniformCorrelationTail_of_isCompact_closure, isCompact_closure_signed_correlations_of_tail⟩

/-- Exact signed-grid compactness criterion, with no zero-grid or polar premise. -/
theorem isCompact_closure_signed_correlations_iff_gridTail (S : Set (LevyEnergySource K)) :
    IsCompact (closure (LevyEnergySource.complexCorrelation '' S)) ↔ UniformSignedGridTail S :=
  (isCompact_closure_signed_correlations_iff_tail S).trans
    (uniformSignedGridTail_iff_correlationTail S).symm

/-- Signed trace tightness produces a global uniform correlation subsequence. -/
theorem exists_uniform_limit_of_signedGridTail (f : ℕ → LevyEnergySource K)
    (h : UniformSignedGridTail (range f)) :
    ∃ (φ : ℕ → ℕ) (H : ℝ → ℝ), StrictMono φ ∧ Continuous H ∧
      TendstoUniformly (fun n => (f (φ n)).correlation) H atTop := by
  have hc := (isCompact_closure_signed_correlations_iff_gridTail (range f)).mpr h
  obtain ⟨g, _, φ, hφ, hg⟩ := hc.tendsto_subseq
    (x := fun n => (f n).complexCorrelation)
    (fun n => subset_closure ⟨f n, mem_range_self n, rfl⟩)
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hg
  have hr := Complex.uniformContinuous_re.comp_tendstoUniformly hu
  refine ⟨φ, fun x => (g x).re, hφ, Complex.continuous_re.comp g.continuous, ?_⟩
  simpa only [Function.comp_def, LevyEnergySource.complexCorrelation_apply,
    Complex.ofReal_re] using hr

end

end GaloisForLFunctions.BiScaleUncertainty
