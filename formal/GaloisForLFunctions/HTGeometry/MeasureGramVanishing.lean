import GaloisForLFunctions.HTGeometry.TotalGramLimits

/-!
# The measure part vanishes at non-atoms

The Herglotz dominant makes the atom kernel integrable at every small height, and the atom law makes
its integral vanish at a node carrying no mass.  So the measure diagonal vanishes, and with the
Cauchy-Schwarz bound so does the measure off-diagonal.

Integrability is available only at small heights, since the constant bound is useless for an infinite
measure at large ones, so the statements are in eventual form.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory

noncomputable section

/-- **The dominant makes the atom kernel integrable at small heights.** -/
theorem integrable_atomKernel_of_dominant (ν : Measure ℝ) (a R : ℝ) (hR : 0 < R)
    (hdom : Integrable (atomDominant a R) ν) {y : ℝ} (hy : y ≠ 0) (hy1 : y ^ 2 ≤ 1) :
    Integrable (fun t : ℝ => atomKernel a y t) ν := by
  refine hdom.mono' ((continuous_atomKernel hy).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (atomKernel_nonneg a t)]
  exact atomKernel_le_atomDominant hR hy1 t

/-- The atom kernel is eventually integrable as the height tends to zero. -/
theorem eventually_integrable_atomKernel (ν : Measure ℝ) (a R : ℝ) (hR : 0 < R)
    (hdom : Integrable (atomDominant a R) ν) :
    ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), Integrable (fun t : ℝ => atomKernel a y t) ν := by
  filter_upwards [self_mem_nhdsWithin, eventually_sq_le_one] with y hy hy1
  exact integrable_atomKernel_of_dominant ν a R hR hdom hy hy1

/-- **The measure diagonal vanishes at a non-atom.**  Eventual-integrability form, which is what the
Herglotz dominant supplies. -/
theorem tendsto_measureGram_diagonal_of_dominant {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ)
    (l : Fin d) (R : ℝ) (hR : 0 < R)
    (hdom : Integrable (atomDominant (a l) R) ν) (hatom : ν {a l} = 0) :
    Tendsto (fun y : ℝ => measureGram ν a y l l) (𝓝[≠] 0) (𝓝 0) := by
  have hlim := tendsto_integral_atomKernel_of_notAtom_herglotz ν R hR hdom hatom
  have heq : (fun y : ℝ => measureGram ν a y l l) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun y : ℝ => ((∫ t, atomKernel (a l) y t ∂ν : ℝ) : ℂ)) := by
    filter_upwards [eventually_integrable_atomKernel ν (a l) R hR hdom] with y hy
    exact measureGram_diagonal ν a y l hy
  refine Tendsto.congr' heq.symm ?_
  have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hlim
  simpa using hc

end

end GaloisForLFunctions.HTGeometry
