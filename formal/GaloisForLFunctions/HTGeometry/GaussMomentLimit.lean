import GaloisForLFunctions.HTGeometry.GaussTightness
import GaloisForLFunctions.HTGeometry.MomentLimitBound

/-!
# Moments of a weak limit of the Gauss measures

Combining the two halves: the Gauss measures have explicitly computable even moments, and the
portmanteau inequality carries a uniform bound on those moments to any weak limit point.  The
conclusion is that every limit point of the Gauss family has even moments bounded by the moment
sequence itself.

The bound is only available once the level is large enough for the quadrature to reach order `2k`,
which is why the limit lemma is stated with an eventual hypothesis: `liminf` ignores any finite
initial segment, so nothing is lost.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Lower integration against a finite weighted Dirac family. -/
theorem lintegral_finsetWeightedDirac (t : Finset ℝ) (w : ℝ → ℝ) (f : ℝ → ENNReal) :
    ∫⁻ x, f x ∂(∑ y ∈ t, ENNReal.ofReal (w y) • Measure.dirac y)
      = ∑ y ∈ t, ENNReal.ofReal (w y) * f y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lintegral_add_measure,
        lintegral_smul_measure, lintegral_dirac, ih, smul_eq_mul]

theorem lintegral_gaussMeasure (s : ℕ → ℝ) (n : ℕ) (f : ℝ → ENNReal) :
    ∫⁻ x, f x ∂(gaussMeasure s n)
      = ∑ ξ ∈ gaussNodes s n, ENNReal.ofReal (christoffel s n ξ) * f ξ := by
  rw [gaussMeasure]
  exact lintegral_finsetWeightedDirac _ _ f

/-- The even moments of the Gauss measure, as lower integrals. -/
theorem lintegral_even_pow_gaussMeasure (h : PositiveMomentForm s) (n k : ℕ)
    (hk : 2 * k ≤ 2 * n + 1) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(gaussMeasure s n) = ENNReal.ofReal (s (2 * k)) := by
  classical
  rw [lintegral_gaussMeasure s n]
  have hterm : ∀ ξ ∈ gaussNodes s n,
      ENNReal.ofReal (christoffel s n ξ) * ENNReal.ofReal (ξ ^ (2 * k))
        = ENNReal.ofReal (christoffel s n ξ * ξ ^ (2 * k)) := by
    intro ξ _
    rw [← ENNReal.ofReal_mul (christoffel_pos h n ξ).le]
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg fun ξ _ =>
      mul_nonneg (christoffel_pos h n ξ).le (pow_two_mul_nonneg k ξ),
    gaussSum_pow h n (2 * k) hk]

/-- The even moments of the normalised Gauss measure. -/
theorem lintegral_even_pow_gaussProb (h : PositiveMomentForm s) (n k : ℕ)
    (hk : 2 * k ≤ 2 * n + 1) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(gaussProb s n)
      = (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) := by
  rw [gaussProb, lintegral_smul_measure, lintegral_even_pow_gaussMeasure h n k hk, smul_eq_mul]

/-- **Every weak limit point of the Gauss family has bounded even moments.**  The hypothesis is the
portmanteau open-set inequality, so this applies to any limit point of the family, however obtained
— in particular to the cluster point supplied by Prokhorov. -/
theorem lintegral_even_pow_limit_le (h : PositiveMomentForm s) (k : ℕ) {μ : Measure ℝ}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => gaussProb s (i + 1) G) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂μ
      ≤ (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) := by
  refine lintegral_even_pow_le_of_forall_isOpen_le_liminf k h_opens ?_
  refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
  exact le_of_eq (lintegral_even_pow_gaussProb h (i + 1) k (by omega))

/-! ## Extracting a weak limit -/

/-- **A convergent subsequence exists.**  The weak topology on `ProbabilityMeasure ℝ` is metrizable,
so the compact closure supplied by Prokhorov is sequentially compact. -/
theorem exists_subseq_tendsto_gaussProbMeasure (h : PositiveMomentForm s) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => gaussProbMeasure h (φ i + 1)) atTop (nhds μ) := by
  have hK := isCompact_closure_gaussProbMeasure h
  have hmem : ∀ n : ℕ, gaussProbMeasure h (n + 1)
      ∈ closure (Set.range fun n : ℕ => gaussProbMeasure h (n + 1)) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨μ, φ, hφ, hlim⟩

/-- The moment bound along a subsequence. -/
theorem lintegral_even_pow_limit_le_subseq (h : PositiveMomentForm s) (k : ℕ) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {μ : Measure ℝ}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => gaussProb s (φ i + 1) G) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂μ
      ≤ (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) := by
  refine lintegral_even_pow_le_of_forall_isOpen_le_liminf k h_opens ?_
  refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
  have hle : i ≤ φ i := hφ.le_apply
  exact le_of_eq (lintegral_even_pow_gaussProb h (φ i + 1) k (by omega))

/-- **Hamburger existence, moment-bound form.**  From positivity of the moment form alone there is a
probability measure on `ℝ` whose even moments are all finite and bounded by the moment sequence. -/
theorem exists_probabilityMeasure_even_moment_le (h : PositiveMomentForm s) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ k : ℕ,
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μ : Measure ℝ)
        ≤ (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_gaussProbMeasure h
  refine ⟨μ, fun k => ?_⟩
  refine lintegral_even_pow_limit_le_subseq h k hφ ?_
  intro G hG
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG

/-! ## Tail decay of the limit measure

The bound on the second moment controls the tails by Chebyshev's inequality.  This is one of the two
estimates a truncation argument needs in order to upgrade weak convergence to convergence of the
moments themselves; the other is the corresponding bound along the approximating family, which is
`gaussProb_compl_Icc_le'`. -/

/-- **Chebyshev for the second moment.** -/
theorem measure_compl_Icc_le_of_lintegral_sq_le {μ : Measure ℝ} {C : ENNReal}
    (hC : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ ≤ C) {R : ℝ} (hR : 0 < R) :
    μ ((Set.Icc (-R) R)ᶜ) ≤ C / ENNReal.ofReal (R ^ 2) := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) μ :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).aemeasurable
  have hsub : (Set.Icc (-R) R)ᶜ
      ⊆ {x : ℝ | ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le] at hx
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_abs x, abs_nonneg x])
  have hne : ENNReal.ofReal (R ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  calc μ ((Set.Icc (-R) R)ᶜ)
      ≤ μ {x : ℝ | ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ) / ENNReal.ofReal (R ^ 2) :=
        meas_ge_le_lintegral_div hmeas hne ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal (R ^ 2) := ENNReal.div_le_div_right hC _

/-- **The limit measure has decaying tails**, at the rate the moment sequence dictates. -/
theorem exists_probabilityMeasure_tail_le (h : PositiveMomentForm s) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ R : ℝ, 0 < R →
      (μ : Measure ℝ) ((Set.Icc (-R) R)ᶜ)
        ≤ ((ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s 2)) / ENNReal.ofReal (R ^ 2) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_even_moment_le h
  refine ⟨μ, fun R hR => ?_⟩
  have h1 := hμ 1
  norm_num at h1
  exact measure_compl_Icc_le_of_lintegral_sq_le h1 hR

end HTGeometry
