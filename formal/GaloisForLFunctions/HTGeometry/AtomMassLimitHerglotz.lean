import GaloisForLFunctions.HTGeometry.AtomKernelDominant
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The atom limit for an infinite Herglotz measure

With the height-independent dominant in hand the atom limit no longer needs the measure to be
finite.  Dominated convergence applies verbatim: the scaled kernel converges pointwise to the
indicator of the node and is bounded by the dominant for every height at most one.

At a node carrying no mass the limit is zero, which is the vanishing of the measure part in the
Krein index computation.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory

noncomputable section

/-- Heights near zero are eventually small enough for the dominating bound. -/
theorem eventually_sq_le_one : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), y ^ 2 ≤ 1 := by
  have hmem : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y ^ 2 ≤ 1 := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) one_pos) ?_
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    nlinarith [abs_nonneg y, sq_abs y]
  exact hmem.filter_mono nhdsWithin_le_nhds

/-- **The atom limit against an infinite Herglotz measure.**  Whenever the height-independent
dominant is integrable, the scaled kernel integral tends to the mass of the node. -/
theorem tendsto_integral_atomKernel_of_integrable_dominant
    (ν : Measure ℝ) (a R : ℝ) (hR : 0 < R)
    (hdom : Integrable (atomDominant a R) ν) :
    Tendsto (fun y : ℝ => ∫ t, atomKernel a y t ∂ν) (𝓝[≠] 0)
      (𝓝 (ν {a}).toReal) := by
  have hlim : Tendsto (fun y : ℝ => ∫ t, atomKernel a y t ∂ν) (𝓝[≠] 0)
      (𝓝 (∫ t, Set.indicator {a} (fun _ => (1 : ℝ)) t ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (atomDominant a R) ?_ ?_ hdom ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (continuous_atomKernel hy).aestronglyMeasurable
    · filter_upwards [eventually_sq_le_one] with y hy
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (atomKernel_nonneg a t)]
      exact atomKernel_le_atomDominant hR hy t
    · filter_upwards with t
      exact tendsto_atomKernel_indicator a t
  have hval : ∫ t, Set.indicator {a} (fun _ => (1 : ℝ)) t ∂ν = (ν {a}).toReal := by
    rw [integral_indicator_const _ (measurableSet_singleton a)]
    simp [measureReal_def]
  rwa [hval] at hlim

/-- **The measure part vanishes at a non-atom, infinite measure allowed.**  This is the card's (M4):
at a node carrying no mass the scaled kernel integral tends to zero, with no finiteness of the
measure, only integrability of the Herglotz dominant. -/
theorem tendsto_integral_atomKernel_of_notAtom_herglotz
    (ν : Measure ℝ) {a : ℝ} (R : ℝ) (hR : 0 < R)
    (hdom : Integrable (atomDominant a R) ν) (ha : ν {a} = 0) :
    Tendsto (fun y : ℝ => ∫ t, atomKernel a y t ∂ν) (𝓝[≠] 0) (𝓝 0) := by
  have h := tendsto_integral_atomKernel_of_integrable_dominant ν a R hR hdom
  rwa [ha, ENNReal.toReal_zero] at h

end

end GaloisForLFunctions.HTGeometry
