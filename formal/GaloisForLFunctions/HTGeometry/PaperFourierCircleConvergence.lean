import GaloisForLFunctions.HTGeometry.PaperFourierCircleTransport
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.PaperMain

/-! # Full Fourier convergence for native circle boundary spaces

The completed paper theorem applies to every actual L² boundary input. One null
set works for a countable family and for its entire complex finite span.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Topology FourierLLogL
open scoped BigOperators ENNReal

variable (T : ℝ) [Fact (0 < T)]

def paperCircleFourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x

/-- All symmetric cutoffs converge to the actual L² representative off a measurable null set. -/
theorem paperCircleLp_fourier_convergence
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, Tendsto (fun N => paperCircleFourierPartialSum T f N x) atTop (𝓝 (f x)) := by
  let e := paperCircleRescale (2 * Real.pi) T
  obtain ⟨E, hm, hz, hc⟩ := almost_everywhere_fourier_convergence
    (fun x => f (e x)) (paperCircle_rescaled_memLLogL T f)
  refine ⟨e '' E, e.measurableEmbedding.measurableSet_image.mpr hm, ?_, ?_⟩
  · have h := (paperCircleRescale_measurePreserving (2 * Real.pi) T).measure_preimage_emb
      e.measurableEmbedding (e '' E)
    rw [e.injective.preimage_image] at h
    exact h.symm.trans hz
  · intro x hx
    have he : e.symm x ∉ E := fun h => hx ⟨e.symm x, h, e.apply_symm_apply x⟩
    have h := hc (e.symm x) he
    simpa only [symmetricPartialSum, fourierPartialSum_paperCircleRescale,
      e, Homeomorph.apply_symm_apply, paperCircleFourierPartialSum] using h

/-- A countable family has a single exceptional set, selected before the member. -/
theorem paperCircleLp_common_fourier_convergence {κ : Type*} [Countable κ]
    (f : κ → Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ j, Tendsto (fun N => paperCircleFourierPartialSum T (f j) N x)
        atTop (𝓝 (f j x)) := by
  classical
  choose E hm hz hc using fun j => paperCircleLp_fourier_convergence T (f j)
  refine ⟨⋃ j, E j, MeasurableSet.iUnion hm, measure_iUnion_null hz, ?_⟩
  intro x hx j
  exact hc j x (fun h => hx (Set.mem_iUnion.mpr ⟨j, h⟩))

/-- Finite linear combinations commute with every literal symmetric cutoff. -/
theorem paperCircleLp_fourierPartialSum_span {κ : Type*}
    (f : κ → Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (S : Finset κ) (c : κ → ℂ)
    (N : ℕ) (x : AddCircle T) :
    paperCircleFourierPartialSum T (fun y => ∑ j ∈ S, c j * f j y) N x =
      ∑ j ∈ S, c j * paperCircleFourierPartialSum T (f j) N x := by
  classical
  have hi (j : κ) : Integrable (fun y => c j * f j y) AddCircle.haarAddCircle :=
    ((Lp.memLp (f j)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul (c j)
  have hc (k : ℤ) : fourierCoeff (fun y => ∑ j ∈ S, c j * f j y) k =
      ∑ j ∈ S, c j * fourierCoeff (f j) k := by
    have h := congrFun (fourierCoeff.sum S (fun j y => c j * f j y) (fun j _ => hi j)) k
    have he : (∑ j ∈ S, fun y => c j * f j y) = (fun y => ∑ j ∈ S, c j * f j y) := by
      funext y
      rw [Finset.sum_apply]
    rw [he] at h
    simpa only [Finset.sum_apply, fourierCoeff.const_mul] using h
  simp only [paperCircleFourierPartialSum, hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The same set works for uncountably many coefficient choices in the finite span. -/
theorem paperCircleLp_common_span_convergence {κ : Type*} [Countable κ]
    (f : κ → Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => paperCircleFourierPartialSum T
          (fun y => ∑ j ∈ S, c j * f j y) N x) atTop (𝓝 (∑ j ∈ S, c j * f j x)) := by
  classical
  obtain ⟨E, hm, hz, hc⟩ := paperCircleLp_common_fourier_convergence T f
  refine ⟨E, hm, hz, fun x hx S c => ?_⟩
  simp only [paperCircleLp_fourierPartialSum_span]
  exact tendsto_finsetSum S (fun j _ => (hc x hx j).const_mul (c j))

end
end GaloisForLFunctions.HTGeometry
