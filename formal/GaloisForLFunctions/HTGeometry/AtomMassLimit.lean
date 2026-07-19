import GaloisForLFunctions.HTGeometry.AtomMassKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The scaled kernel integral converges to the atom mass

Against a finite measure the scaled Poisson kernel integrates to the mass of the node in the limit:
it is bounded by one, so the constant function dominates, and it converges pointwise to the
indicator of the node.

For a node that is not an atom the limit is zero, which is the vanishing the Krein index computation
needs on the measure part of the Pick kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory

noncomputable section

/-- For nonzero height the kernel is continuous in the base point. -/
theorem continuous_atomKernel {a y : ℝ} (hy : y ≠ 0) :
    Continuous fun t : ℝ => atomKernel a y t := by
  apply Continuous.div continuous_const
  · exact ((continuous_id.sub continuous_const).pow 2).add continuous_const
  · intro t
    have : (0 : ℝ) < (t - a) ^ 2 + y ^ 2 := by positivity
    exact ne_of_gt this

/-- The kernel converges pointwise to the indicator of the node. -/
theorem tendsto_atomKernel_indicator (a t : ℝ) :
    Tendsto (fun y : ℝ => atomKernel a y t) (𝓝[≠] 0)
      (𝓝 (Set.indicator {a} (fun _ => (1 : ℝ)) t)) := by
  by_cases hta : t = a
  · subst hta
    have hval : Set.indicator {t} (fun _ => (1 : ℝ)) t = 1 := by
      simp [Set.indicator_of_mem]
    rw [hval]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (atomKernel_self t hy).symm
  · have hval : Set.indicator {a} (fun _ => (1 : ℝ)) t = 0 := by
      simp [Set.indicator_of_notMem, hta]
    rw [hval]
    exact (tendsto_atomKernel_of_ne a t hta).mono_left nhdsWithin_le_nhds

/-- **The scaled kernel integral converges to the atom mass.**  Against a finite measure, the
integral of the scaled Poisson kernel tends to the measure of the node. -/
theorem tendsto_integral_atomKernel (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    Tendsto (fun y : ℝ => ∫ t, atomKernel a y t ∂ν) (𝓝[≠] 0)
      (𝓝 (ν {a}).toReal) := by
  have hlim : Tendsto (fun y : ℝ => ∫ t, atomKernel a y t ∂ν) (𝓝[≠] 0)
      (𝓝 (∫ t, Set.indicator {a} (fun _ => (1 : ℝ)) t ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (continuous_atomKernel hy).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with y hy
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (atomKernel_nonneg a t)]
      exact atomKernel_le_one a t hy
    · filter_upwards with t
      exact tendsto_atomKernel_indicator a t
  have hval : ∫ t, Set.indicator {a} (fun _ => (1 : ℝ)) t ∂ν = (ν {a}).toReal := by
    rw [integral_indicator_const _ (measurableSet_singleton a)]
    simp [measureReal_def]
  rwa [hval] at hlim

/-- **The measure part vanishes at a non-atom.**  This is the vanishing consumed by the Krein index
limit: at a node carrying no mass the scaled kernel integral tends to zero. -/
theorem tendsto_integral_atomKernel_of_notAtom
    (ν : Measure ℝ) [IsFiniteMeasure ν] {a : ℝ} (ha : ν {a} = 0) :
    Tendsto (fun y : ℝ => ∫ t, atomKernel a y t ∂ν) (𝓝[≠] 0) (𝓝 0) := by
  have h := tendsto_integral_atomKernel ν a
  rwa [ha, ENNReal.toReal_zero] at h

end

end GaloisForLFunctions.HTGeometry
