import GaloisForLFunctions.HTGeometry.LimitCarrier

/-!
# Bounded nodes force determinacy

If every level's Gauss nodes lie in a fixed compact interval, every Gauss measure vanishes off
it, so
the weak limit does too.  The limit is a representing measure, so the sequence has a compactly
supported representative — and by `measure_eq_of_moments_eq_of_one_carried` it is then determinate.

Contrapositively, an indeterminate sequence has nodes escaping every compact interval.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Bounded nodes give a compactly carried representative.** -/
theorem exists_carried_representative_of_nodes_bounded (h : PositiveMomentForm s) {B : ℝ}
    (hbdd : ∀ n : ℕ, ∀ xi ∈ gaussNodes s n, xi ∈ Set.Icc (-B) B) :
    ∃ μ : ProbabilityMeasure ℝ,
      (μ : Measure ℝ) (Set.Icc (-B) B)ᶜ = 0 ∧
        ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
          ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_gaussProbMeasure h
  have hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => gaussProb s (φ i + 1) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  refine ⟨μ, ?_, fun k => hasMoments_of_tendsto h hφ hopen hlim k⟩
  refine measure_eq_zero_of_isOpen_le_liminf hopen (isOpen_compl_iff.mpr isClosed_Icc) ?_
  intro i
  exact gaussProb_compl_eq_zero_of_nodes_mem hbdd (φ i + 1)

/-- **Bounded nodes force determinacy.**  Any two representatives of the normalised sequence
agree. -/
theorem determinate_of_nodes_bounded (h : PositiveMomentForm s) {B : ℝ} (hB : 0 < B)
    (hbdd : ∀ n : ℕ, ∀ xi ∈ gaussNodes s n, xi ∈ Set.Icc (-B) B)
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    (hsnu : ∀ k, (s 0)⁻¹ * s k = ∫ x, (x : ℝ) ^ k ∂nu)
    (hintnu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) = nu := by
  obtain ⟨μ, hcar, hmom⟩ := exists_carried_representative_of_nodes_bounded h hbdd
  refine ⟨μ, ?_⟩
  have hIcc : Set.Icc (-B) B = Set.Icc (0 - B) (0 + B) := by norm_num
  rw [hIcc] at hcar
  exact measure_eq_of_moments_eq_of_one_carried hB hcar
    (fun k => (hmom k).2.symm) (fun k => (hmom k).1) hsnu hintnu

/-- **Bounded nodes give uniqueness outright.**  Any two finite measures with the normalised moments
coincide, both being equal to the carried representative. -/
theorem measure_eq_of_nodes_bounded (h : PositiveMomentForm s) {B : ℝ} (hB : 0 < B)
    (hbdd : ∀ n : ℕ, ∀ xi ∈ gaussNodes s n, xi ∈ Set.Icc (-B) B)
    {nu1 nu2 : Measure ℝ} [IsFiniteMeasure nu1] [IsFiniteMeasure nu2]
    (hs1 : ∀ k, (s 0)⁻¹ * s k = ∫ x, (x : ℝ) ^ k ∂nu1)
    (hi1 : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu1)
    (hs2 : ∀ k, (s 0)⁻¹ * s k = ∫ x, (x : ℝ) ^ k ∂nu2)
    (hi2 : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu2) :
    nu1 = nu2 := by
  obtain ⟨μ, hcar, hmom⟩ := exists_carried_representative_of_nodes_bounded h hbdd
  have hIcc : Set.Icc (-B) B = Set.Icc (0 - B) (0 + B) := by norm_num
  rw [hIcc] at hcar
  have e1 : (μ : Measure ℝ) = nu1 :=
    measure_eq_of_moments_eq_of_one_carried hB hcar
      (fun k => (hmom k).2.symm) (fun k => (hmom k).1) hs1 hi1
  have e2 : (μ : Measure ℝ) = nu2 :=
    measure_eq_of_moments_eq_of_one_carried hB hcar
      (fun k => (hmom k).2.symm) (fun k => (hmom k).1) hs2 hi2
  rw [← e1, e2]

/-- **Two distinct representatives force unbounded nodes.**  The contrapositive, in the form a
concrete indeterminate sequence would use. -/
theorem exists_node_outside_of_measure_ne (h : PositiveMomentForm s) {B : ℝ} (hB : 0 < B)
    {nu1 nu2 : Measure ℝ} [IsFiniteMeasure nu1] [IsFiniteMeasure nu2]
    (hs1 : ∀ k, (s 0)⁻¹ * s k = ∫ x, (x : ℝ) ^ k ∂nu1)
    (hi1 : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu1)
    (hs2 : ∀ k, (s 0)⁻¹ * s k = ∫ x, (x : ℝ) ^ k ∂nu2)
    (hi2 : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu2)
    (hne : nu1 ≠ nu2) :
    ∃ n : ℕ, ∃ xi ∈ gaussNodes s n, xi ∉ Set.Icc (-B) B := by
  by_contra hcon
  refine hne (measure_eq_of_nodes_bounded h hB ?_ hs1 hi1 hs2 hi2)
  intro n xi hxi
  by_contra hmem
  exact hcon ⟨n, xi, hxi, hmem⟩

end HTGeometry
