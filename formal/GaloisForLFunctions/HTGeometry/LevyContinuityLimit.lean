import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Lévy's continuity theorem, existence form

If the characteristic functions of a sequence of probability measures on `ℝ` converge pointwise to
a function `f` continuous at the origin, then `f` is the characteristic function of a probability
measure `ν` and the sequence converges weakly to `ν`.  Tightness comes from the convergence of the
characteristic functions, Prokhorov's theorem supplies a cluster point along an ultrafilter, and
continuity of characteristic functions for weak convergence identifies its characteristic
function with `f`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Characteristic functions are continuous for weak convergence along any filter. -/
theorem tendsto_charFun_of_tendsto {ι : Type*} {F : Filter ι} {μ : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} (h : Tendsto μ F (𝓝 ν)) (t : ℝ) :
    Tendsto (fun i => charFun (μ i : Measure ℝ) t) F (𝓝 (charFun (ν : Measure ℝ) t)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h
  simp_rw [charFun_eq_integral_innerProbChar]
  exact h (BoundedContinuousFunction.innerProbChar t)

/-- **Lévy's continuity theorem, existence form.**  Pointwise convergence of characteristic
functions to a function continuous at `0` produces a weak limit whose characteristic function is
that function. -/
theorem exists_tendsto_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure ℝ} {f : ℝ → ℂ}
    (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n => charFun (μ n : Measure ℝ) t) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ t, charFun (ν : Measure ℝ) t = f t) ∧ Tendsto μ atTop (𝓝 ν) := by
  have htight : IsTightMeasureSet (Set.range fun n => (μ n : Measure ℝ)) :=
    isTightMeasureSet_of_tendsto_charFun hf h
  have hcomp : IsCompact (closure (Set.range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext ρ
    simp
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨ν, -, hν⟩ := hcomp.ultrafilter_le_nhds (U.map μ) (by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact mem_map.mpr (Eventually.of_forall fun n => subset_closure (Set.mem_range_self n)))
  have hνU : Tendsto μ U (𝓝 ν) := by
    rw [Tendsto, ← Ultrafilter.coe_map]
    exact hν
  have hchar : ∀ t, charFun (ν : Measure ℝ) t = f t := fun t =>
    tendsto_nhds_unique (tendsto_charFun_of_tendsto hνU t) ((h t).mono_left hU)
  refine ⟨ν, hchar, ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_⟩
  rw [hchar t]
  exact h t

end GaloisForLFunctions.HTGeometry
