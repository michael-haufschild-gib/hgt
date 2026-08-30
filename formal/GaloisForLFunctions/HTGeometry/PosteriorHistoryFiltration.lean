import GaloisForLFunctions.HTGeometry.OrthogonalHistoryDecomposition
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Observation towers and the orthogonal history of a source observable

A decreasing filtration of sub-σ-algebras starting at the full one is an observation tower.  Its
`L²` subspaces form a decreasing chain of orthogonally complemented subspaces, the stagewise
projection is the conditional expectation, and the abstract orthogonal history decomposition
applies verbatim: source energy splits exactly into observed endpoint energy plus the energies of
the vertical currents, and the analysis map is an isometry.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Ω : Type*}

theorem hasOrthogonalProjection_lpMeas {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ : Measure Ω) : (lpMeas ℝ ℝ m 2 μ).HasOrthogonalProjection := by
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  infer_instance

theorem lpMeas_mono {m₁ m₂ m0 : MeasurableSpace Ω} (h : m₁ ≤ m₂) (μ : Measure Ω) :
    lpMeas ℝ ℝ m₁ 2 μ ≤ lpMeas ℝ ℝ m₂ 2 μ := by
  intro f hf
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  exact hf.mono h

theorem lpMeas_top {m0 : MeasurableSpace Ω} (μ : Measure Ω) : lpMeas ℝ ℝ m0 2 μ = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun f => ?_
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact Lp.aestronglyMeasurable f

/-- `(PMP.16)`, `(PMP.22)`  The `L²` subspaces of an observation tower. -/
def historySpace {m0 : MeasurableSpace Ω} (μ : Measure Ω) (m : ℕ → MeasurableSpace Ω) (k : ℕ) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  lpMeas ℝ ℝ (m k) 2 μ

theorem antitone_historySpace {m0 : MeasurableSpace Ω} {m : ℕ → MeasurableSpace Ω}
    (hm : Antitone m) (μ : Measure Ω) : Antitone (historySpace μ m) :=
  fun _ _ h => lpMeas_mono (hm h) μ

theorem historySpace_zero {m0 : MeasurableSpace Ω} {m : ℕ → MeasurableSpace Ω} (h0 : m 0 = m0)
    (μ : Measure Ω) : historySpace μ m 0 = ⊤ := by
  rw [historySpace, h0, lpMeas_top]

theorem hasOrthogonalProjection_historySpace {m0 : MeasurableSpace Ω}
    {m : ℕ → MeasurableSpace Ω} (hle : ∀ k, m k ≤ m0) (μ : Measure Ω) (k : ℕ) :
    (historySpace μ m k).HasOrthogonalProjection :=
  hasOrthogonalProjection_lpMeas (hle k) μ

/-! ## The orthogonal history of a source observable -/

variable {m0 : MeasurableSpace Ω} {m : ℕ → MeasurableSpace Ω}

/-- `(PMP.23)`  The stagewise projection of the tower is the conditional expectation. -/
theorem historyStage_eq_condExpL2 (hle : ∀ k, m k ≤ m0) (μ : Measure Ω) (f : Lp ℝ 2 μ) (k : ℕ) :
    letI : ∀ j, (historySpace μ m j).HasOrthogonalProjection :=
      hasOrthogonalProjection_historySpace hle μ
    historyStage (historySpace μ m) f k = (condExpL2 ℝ ℝ (hle k) f : Lp ℝ 2 μ) := rfl

/-- **Theorem 5.1, `(PMP.18)`.**  The observed endpoint plus the vertical currents reconstruct
the source observable. -/
theorem eq_condExpL2_add_sum (hle : ∀ k, m k ≤ m0) (_hmhm : Antitone m) (h0 : m 0 = m0)
    (μ : Measure Ω) (f : Lp ℝ 2 μ) (n : ℕ) :
    f = (condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ)
      + ∑ k ∈ Finset.range n,
        ((condExpL2 ℝ ℝ (hle k) f : Lp ℝ 2 μ) - (condExpL2 ℝ ℝ (hle (k + 1)) f : Lp ℝ 2 μ)) := by
  letI : ∀ j, (historySpace μ m j).HasOrthogonalProjection :=
    hasOrthogonalProjection_historySpace hle μ
  exact eq_historyStage_add_sum_residual (historySpace_zero h0 μ) f n

/-- **Theorem 5.1, `(PMP.19)`.**  The exact energy split of a finite observation history. -/
theorem norm_sq_eq_condExpL2_add_sum (hle : ∀ k, m k ≤ m0) (hm : Antitone m) (h0 : m 0 = m0)
    (μ : Measure Ω) (f : Lp ℝ 2 μ) (n : ℕ) :
    ‖f‖ ^ 2 = ‖(condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ)‖ ^ 2
      + ∑ k ∈ Finset.range n,
        ‖(condExpL2 ℝ ℝ (hle k) f : Lp ℝ 2 μ)
          - (condExpL2 ℝ ℝ (hle (k + 1)) f : Lp ℝ 2 μ)‖ ^ 2 := by
  letI : ∀ j, (historySpace μ m j).HasOrthogonalProjection :=
    hasOrthogonalProjection_historySpace hle μ
  exact norm_sq_eq_historyStage_add_sum (antitone_historySpace hm μ) (historySpace_zero h0 μ) f n

/-- `(PMP.23)`  The tail limit of the conditional expectations along the tower. -/
def tailProjection (hle : ∀ k, m k ≤ m0) (μ : Measure Ω) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  letI : ∀ j, (historySpace μ m j).HasOrthogonalProjection :=
    hasOrthogonalProjection_historySpace hle μ
  historyLimit (historySpace μ m) f

/-- **Theorem 6.1, `(PMP.24)`.**  The exact energy split of an infinite observation history. -/
theorem norm_sq_eq_tailProjection_add_tsum (hle : ∀ k, m k ≤ m0) (hm : Antitone m)
    (h0 : m 0 = m0) (μ : Measure Ω) (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ‖tailProjection hle μ f‖ ^ 2
      + ∑' k, ‖(condExpL2 ℝ ℝ (hle k) f : Lp ℝ 2 μ)
          - (condExpL2 ℝ ℝ (hle (k + 1)) f : Lp ℝ 2 μ)‖ ^ 2 := by
  letI : ∀ j, (historySpace μ m j).HasOrthogonalProjection :=
    hasOrthogonalProjection_historySpace hle μ
  exact norm_sq_eq_historyLimit_add_tsum (antitone_historySpace hm μ)
    (historySpace_zero h0 μ) f

/-- **Corollary 6.2, `(PMP.28)`.**  A source observable vanishes exactly when its tail component
and every vertical current vanish. -/
theorem eq_zero_iff_tailProjection_and_residuals (hle : ∀ k, m k ≤ m0) (hm : Antitone m)
    (h0 : m 0 = m0) (μ : Measure Ω) (f : Lp ℝ 2 μ) :
    f = 0 ↔ tailProjection hle μ f = 0 ∧ ∀ k, (condExpL2 ℝ ℝ (hle k) f : Lp ℝ 2 μ)
        - (condExpL2 ℝ ℝ (hle (k + 1)) f : Lp ℝ 2 μ) = 0 := by
  constructor
  · rintro rfl
    refine ⟨?_, fun k => by simp⟩
    letI : ∀ j, (historySpace μ m j).HasOrthogonalProjection :=
      hasOrthogonalProjection_historySpace hle μ
    have hz : Filter.Tendsto (fun n => historyStage (historySpace μ m) (0 : Lp ℝ 2 μ) n)
        Filter.atTop (nhds 0) := by
      simp only [historyStage, map_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (tendsto_historyStage (antitone_historySpace hm μ)
      (historySpace_zero h0 μ) 0) hz
  · rintro ⟨h1, h2⟩
    have h := norm_sq_eq_tailProjection_add_tsum hle hm h0 μ f
    rw [h1, norm_zero] at h
    have hz : ∀ k, ‖(condExpL2 ℝ ℝ (hle k) f : Lp ℝ 2 μ)
        - (condExpL2 ℝ ℝ (hle (k + 1)) f : Lp ℝ 2 μ)‖ ^ 2 = 0 := by
      intro k; rw [h2 k]; simp
    rw [tsum_congr hz] at h
    simp only [tsum_zero, add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] at h
    simpa [pow_eq_zero_iff] using h

/-! ## Fisher tangent law -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- `(PMP.30)`  The observed part of a convergent family converges to the observed part of the
limit. -/
theorem tendsto_starProjection {ι : Type*} {l : Filter ι} (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {u : ι → E} {T : E} (h : Filter.Tendsto u l (nhds T)) :
    Filter.Tendsto (fun i => U.starProjection (u i)) l (nhds (U.starProjection T)) :=
  (U.starProjection.continuous.tendsto T).comp h

omit [CompleteSpace E] in
/-- `(PMP.31)`  The limiting energy splits exactly into observed and vertical parts. -/
theorem tendsto_norm_sq_split {ι : Type*} {l : Filter ι} (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {u : ι → E} {T : E} (h : Filter.Tendsto u l (nhds T)) :
    Filter.Tendsto (fun i => ‖u i‖ ^ 2) l
      (nhds (‖U.starProjection T‖ ^ 2 + ‖T - U.starProjection T‖ ^ 2)) := by
  have hsplit : ‖T‖ ^ 2 = ‖U.starProjection T‖ ^ 2 + ‖T - U.starProjection T‖ ^ 2 := by
    have horth : inner 𝕜 (U.starProjection T) (T - U.starProjection T) = 0 := by
      have h0' := Submodule.starProjection_inner_eq_zero (K := U) T _
        (Submodule.starProjection_apply_mem U T)
      rw [← inner_conj_symm, h0', map_zero]
    have hsum : T = U.starProjection T + (T - U.starProjection T) := by abel
    calc ‖T‖ ^ 2 = ‖U.starProjection T + (T - U.starProjection T)‖ ^ 2 := by rw [← hsum]
      _ = ‖U.starProjection T‖ ^ 2 + ‖T - U.starProjection T‖ ^ 2 := by
          simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
            (U.starProjection T) (T - U.starProjection T) horth
  rw [← hsplit]
  exact (h.norm).pow 2

end

end GaloisForLFunctions.HTGeometry
