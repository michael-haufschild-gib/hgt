import GaloisForLFunctions.HTGeometry.MomentBochnerBridge
import GaloisForLFunctions.HTGeometry.HamburgerBoundaryKernel

/-!
# Existence of a representing measure

A moment sequence whose associated bilinear form is positive definite is represented by a measure.
The measure is not assumed: it is built from the sequence, through orthogonal polynomials, their
roots as quadrature nodes, the Christoffel weights, tightness of the resulting discrete measures,
Prokhorov compactness, and a weak limit along a subsequence.

The normalisation is the one this construction produces: the limit is a probability measure, so its
moments are those of `s` divided by `s₀`.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The moments of a weak limit of the Gauss family.**  Stated for an arbitrary limit point
together with the data witnessing it, so that callers keep the subsequence and the portmanteau
inequality rather than having them discarded. -/
theorem hasMoments_of_tendsto (h : PositiveMomentForm s) {μ : ProbabilityMeasure ℝ}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => gaussProb s (φ i + 1) G)
    (hlim : Tendsto (fun i => gaussProbMeasure h (φ i + 1)) atTop (nhds μ)) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
      ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k := by
  have hs0 : 0 < s 0 := moment_zero_pos h
  have hs2k : 0 < s (2 * k) := moment_even_pos h k
  set C : ENNReal := (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) with hCdef
  have hCtop : C ≠ ⊤ := by
    rw [hCdef]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ?_) ENNReal.ofReal_ne_top
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hs0
  have hCreal : C.toReal = (s 0)⁻¹ * s (2 * k) := by
    rw [hCdef, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofReal hs2k.le]
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μ : Measure ℝ) ≤ C :=
    lintegral_even_pow_limit_le_subseq h k hφ hopen
  have hmeas : Measurable fun x : ℝ => x ^ (2 * k) := measurable_id.pow_const _
  have hnn : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := pow_two_mul_nonneg k
  have hint2 : Integrable (fun x : ℝ => x ^ (2 * k)) (μ : Measure ℝ) :=
    integrable_of_lintegral_ofReal_lt_top hmeas hnn
      (lt_of_le_of_lt hlint (lt_top_iff_ne_top.mpr hCtop))
  have hMmu : ∫ x, x ^ (2 * k) ∂(μ : Measure ℝ) ≤ C.toReal :=
    integral_le_toReal_of_lintegral_le hmeas hnn hCtop hlint
  have hintk : Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) :=
    integrable_pow_of_integrable_even k hint2
  refine ⟨hintk, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ∫ x : ℝ, x ^ 0 ∂(μ : Measure ℝ) = 1 := by simp
    rw [h0, inv_mul_cancel₀ hs0.ne']
  have hMnu : ∀ᶠ i in atTop, ∫ x, x ^ (2 * k) ∂(gaussProb s (φ i + 1)) ≤ C.toReal := by
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    refine le_of_eq ?_
    rw [integral_even_pow_gaussProb_le h k hφ hi, hCreal]
  have hmain := tendsto_integral_pow_of_uniform_even_moment
    (μ := (μ : Measure ℝ)) (νs := fun i => gaussProb s (φ i + 1)) hk
    (fun f => tendsto_integral_gaussProb h hlim f)
    hMnu hMmu
    (fun i => integrable_gaussProb h _ _)
    (fun i => integrable_gaussProb h _ _)
    (fun R _ i => integrable_gaussProb h _ _)
    hintk hint2
    (fun R hR => integrable_truncPow hR k)
  have hconst : (fun _ : ℕ => (s 0)⁻¹ * s k)
      =ᶠ[atTop] fun i => ∫ x, x ^ k ∂(gaussProb s (φ i + 1)) := by
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    have hle : i ≤ φ i := hφ.le_apply
    exact (integral_pow_gaussProb h (φ i + 1) k (by omega)).symm
  have htc : Tendsto (fun i => ∫ x, x ^ k ∂(gaussProb s (φ i + 1))) atTop
      (nhds ((s 0)⁻¹ * s k)) :=
    Tendsto.congr' hconst tendsto_const_nhds
  exact tendsto_nhds_unique hmain htc

/-- **Existence of a representing measure.**  For a positive definite moment form there is a
probability measure on `ℝ` integrating every power, with `k`-th moment `s_k / s₀`. -/
theorem exists_probabilityMeasure_hasMoments (h : PositiveMomentForm s) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ k : ℕ,
      Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_gaussProbMeasure h
  exact ⟨μ, fun k => hasMoments_of_tendsto h hφ
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG) hlim k⟩

/-- The constructed measure represents the normalised moment sequence, in the project's own
`HasHamburgerMoments` form. -/
theorem exists_hasHamburgerMoments (h : PositiveMomentForm s) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (fun k => (s 0)⁻¹ * s k)
        (μ : Measure ℝ) := by
  obtain ⟨μ, hmu⟩ := exists_probabilityMeasure_hasMoments h
  exact ⟨μ, fun n => hmu n⟩

/-- **A finite measure representing the sequence exactly.**  Rescaling the probability measure by
`s₀` removes the normalisation, so a positive definite moment form is represented on the nose. -/
theorem exists_finiteMeasure_hasHamburgerMoments (h : PositiveMomentForm s) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν := by
  obtain ⟨μ, hmu⟩ := exists_probabilityMeasure_hasMoments h
  have hs0 : 0 < s 0 := moment_zero_pos h
  have hne : ENNReal.ofReal (s 0) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨ENNReal.ofReal (s 0) • (μ : Measure ℝ), ?_, fun k => ?_⟩
  · constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · refine ⟨((hmu k).1).smul_measure hne, ?_⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal hs0.le, smul_eq_mul, (hmu k).2]
    field_simp

/-- For a normalised sequence the probability measure represents it directly. -/
theorem exists_hasHamburgerMoments_of_moment_zero_eq_one (h : PositiveMomentForm s)
    (h0 : s 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
  obtain ⟨μ, hmu⟩ := exists_probabilityMeasure_hasMoments h
  refine ⟨μ, fun k => ⟨(hmu k).1, ?_⟩⟩
  rw [(hmu k).2, h0, inv_one, one_mul]

end HTGeometry
