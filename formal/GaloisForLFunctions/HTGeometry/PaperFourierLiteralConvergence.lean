import GaloisForLFunctions.HTGeometry.PaperFourierCircleConvergence
import GaloisForLFunctions.HTGeometry.UnitIntervalFourierProjection

/-! # Literal circle and interval representatives in the Fourier endpoint

All exceptional sets are chosen before a countable family member and before every
complex finite combination. The interval transfer identifies the existing literal
unit-interval coefficients and partial sums, including nonperiodic endpoints.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal

private theorem common_span_of_ae (T : ℝ) [Fact (0 < T)] {κ : Type*} [Countable κ]
    (f : κ → Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (g : κ → AddCircle T → ℂ)
    (he : ∀ j, f j =ᵐ[AddCircle.haarAddCircle] g j) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => paperCircleFourierPartialSum T
          (fun y => ∑ j ∈ S, c j * g j y) N x) atTop (𝓝 (∑ j ∈ S, c j * g j x)) := by
  classical
  have hAll : ∀ᵐ x ∂AddCircle.haarAddCircle, ∀ j, f j x = g j x := ae_all_iff.mpr he
  obtain ⟨D, hsub, hDm, hDz⟩ := exists_measurable_superset_of_null (ae_iff.mp hAll)
  have hD : ∀ x ∉ D, ∀ j, f j x = g j x := by
    intro x hx
    by_contra h
    exact hx (hsub h)
  obtain ⟨E, hEm, hEz, hE⟩ := paperCircleLp_common_span_convergence T f
  refine ⟨E ∪ D, hEm.union hDm, measure_union_null hEz hDz, ?_⟩
  intro x hx S c
  have hxE : x ∉ E := fun h => hx (Or.inl h)
  have hxD : x ∉ D := fun h => hx (Or.inr h)
  have hc : fourierCoeff (fun y => ∑ j ∈ S, c j * f j y) =
      fourierCoeff (fun y => ∑ j ∈ S, c j * g j y) :=
    fourierCoeff_congr_ae (hAll.mono (fun y hy =>
      Finset.sum_congr rfl (fun j _ => congrArg (c j * ·) (hy j))))
  have ht := hE x hxE S c
  simpa only [paperCircleFourierPartialSum, hc, hD x hxD] using ht

/-- The actual continuous representatives share one null set for their entire finite span. -/
theorem paperCircleContinuous_common_span_convergence (T : ℝ) [Fact (0 < T)]
    {κ : Type*} [Countable κ] (f : κ → C(AddCircle T, ℂ)) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => paperCircleFourierPartialSum T
          (fun y => ∑ j ∈ S, c j * f j y) N x) atTop (𝓝 (∑ j ∈ S, c j * f j x)) :=
  common_span_of_ae T (fun j => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (f j))
    (fun j => f j) (fun j => ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (f j))

theorem paperCircleContinuous_common_convergence (T : ℝ) [Fact (0 < T)]
    {κ : Type*} [Countable κ] (f : κ → C(AddCircle T, ℂ)) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ j, Tendsto (fun N => paperCircleFourierPartialSum T (f j) N x)
        atTop (𝓝 (f j x)) := by
  classical
  obtain ⟨E, hm, hz, hc⟩ := paperCircleContinuous_common_span_convergence T f
  exact ⟨E, hm, hz, fun x hx j => by simpa using hc x hx {j} (fun _ => 1)⟩

theorem paperCircleContinuous_fourier_convergence (T : ℝ) [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) :
    ∃ E : Set (AddCircle T), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, Tendsto (fun N => paperCircleFourierPartialSum T f N x) atTop (𝓝 (f x)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperCircleContinuous_common_convergence T (fun _ : Unit => f)
  exact ⟨E, hm, hz, fun x hx => hc x hx ()⟩

/-- The circle cutoff is exactly the existing interval cutoff, with identical coefficients. -/
theorem paperUnitInterval_partialSum_lift (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    paperCircleFourierPartialSum 1 (AddCircle.liftIoc 1 0 f) N (x : AddCircle (1 : ℝ)) =
      fourierPartialSum f N x := by
  unfold paperCircleFourierPartialSum fourierPartialSum
  apply Finset.sum_congr rfl
  intro n _
  rw [fourierCoeff_liftIoc_eq]
  have hc : fourierCoeffOn (lt_add_of_pos_right 0 (by norm_num : (0 : ℝ) < 1)) f n =
      l2Pair (fourierChar n) f := by simpa only [zero_add] using fourierCoeffOn_eq_l2Pair f n
  rw [hc]
  congr 1
  rw [fourier_coe_apply, fourierChar]
  congr 1
  push_cast
  ring

private theorem unit_common_span {κ : Type*} [Countable κ] (f : κ → ℝ → ℂ)
    (hf : ∀ j, MemLp (f j) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => fourierPartialSum (fun y => ∑ j ∈ S, c j * f j y) N x)
          atTop (𝓝 (∑ j ∈ S, c j * f j x)) := by
  classical
  let g (j : κ) := AddCircle.liftIoc 1 0 (f j)
  have hg (j : κ) : MemLp (g j) 2 AddCircle.haarAddCircle := by
    have h : MemLp (f j) 2 (volume.restrict (Ioc (0 : ℝ) (0+1))) := by simpa using hf j
    exact h.memLp_liftIoc.haarAddCircle
  obtain ⟨D, hm, hz, hc⟩ := common_span_of_ae 1 (fun j => (hg j).toLp (g j)) g
    (fun j => (hg j).coeFn_toLp)
  let E := ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' D
  have hE : MeasurableSet E := AddCircle.measurable_mk' hm
  have hp : MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Ioc (0 : ℝ) 1)) AddCircle.haarAddCircle := by
    simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle,
      ENNReal.ofReal_one, one_smul] using AddCircle.measurePreserving_mk (1 : ℝ) 0
  refine ⟨E ∩ Ioc 0 1, hE.inter measurableSet_Ioc, ?_, ?_⟩
  · have h := hp.preimage_null hz
    rwa [Measure.restrict_apply hE] at h
  · intro x hx hbad S c
    have hxE : (x : AddCircle (1 : ℝ)) ∉ D := fun h => hbad ⟨h, hx⟩
    have ht := hc (x : AddCircle (1 : ℝ)) hxE S c
    have hsum : (fun y => ∑ j ∈ S, c j * g j y) =
        AddCircle.liftIoc 1 0 (fun y => ∑ j ∈ S, c j * f j y) := rfl
    rw [hsum] at ht
    have hx' : x ∈ Ioc (0 : ℝ) (0 + 1) := by simpa only [zero_add] using hx
    simpa only [paperUnitInterval_partialSum_lift, g, AddCircle.liftIoc_coe_apply hx'] using ht

/-- Every actual unit-interval L² family has full-sequence convergence on one common set. -/
theorem paperUnitIntervalLp_common_span_convergence {κ : Type*} [Countable κ]
    (f : κ → Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => fourierPartialSum (fun y => ∑ j ∈ S, c j * f j y) N x)
          atTop (𝓝 (∑ j ∈ S, c j * f j x)) :=
  unit_common_span (fun j => f j) (fun j => Lp.memLp (f j))

/-- Local continuity pays all interval integrability obligations, including endpoint jumps. -/
theorem paperUnitIntervalContinuous_common_span_convergence {κ : Type*} [Countable κ]
    (f : κ → C(ℝ, ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => fourierPartialSum (fun y => ∑ j ∈ S, c j * f j y) N x)
          atTop (𝓝 (∑ j ∈ S, c j * f j x)) := by
  apply unit_common_span (fun j => f j)
  intro j
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (f j).continuous.continuousOn
  exact MemLp.of_bound (f j).continuous.aestronglyMeasurable B
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hB x ⟨hx.1.le, hx.2⟩))

theorem paperUnitIntervalContinuous_common_convergence {κ : Type*} [Countable κ]
    (f : κ → C(ℝ, ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ j,
        Tendsto (fun N => fourierPartialSum (f j) N x) atTop (𝓝 (f j x)) := by
  classical
  obtain ⟨E, hm, hz, hc⟩ := paperUnitIntervalContinuous_common_span_convergence f
  exact ⟨E, hm, hz, fun x hx he j => by simpa using hc x hx he {j} (fun _ => 1)⟩

end
end GaloisForLFunctions.HTGeometry
