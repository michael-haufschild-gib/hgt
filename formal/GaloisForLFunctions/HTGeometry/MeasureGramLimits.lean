import GaloisForLFunctions.HTGeometry.AtomicGramLimits

/-!
# The measure Gram entries converge

The measure diagonal is the atom kernel integral, so it inherits the atom limit directly.  The
off-diagonal is controlled by the geometric mean of two diagonals, so it vanishes once they do —
after passing through a square root, since the Cauchy-Schwarz bound is on the squared modulus.

Isolating that square-root step keeps the off-diagonal argument a squeeze like the others.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory

noncomputable section

/-- **A vanishing squared norm gives a vanishing norm.**  The square-root step of the off-diagonal
argument. -/
theorem tendsto_norm_of_tendsto_sq {α E : Type*} [NormedAddCommGroup E]
    {l : Filter α} {f : α → E} (h : Tendsto (fun i => ‖f i‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ‖f i‖) l (𝓝 0) := by
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun i => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- A vanishing norm gives a vanishing family. -/
theorem tendsto_zero_of_tendsto_norm {α E : Type*} [NormedAddCommGroup E]
    {l : Filter α} {f : α → E} (h : Tendsto (fun i => ‖f i‖) l (𝓝 0)) :
    Tendsto f l (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.2 h

/-- **The measure diagonal converges to the atom mass.**  At a node carrying no mass it converges to
zero. -/
theorem tendsto_measureGram_diagonal {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (l : Fin d)
    (hint : ∀ y : ℝ, y ≠ 0 → Integrable (fun t : ℝ => atomKernel (a l) y t) ν)
    (hlim : Tendsto (fun y : ℝ => ∫ t, atomKernel (a l) y t ∂ν) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun y : ℝ => measureGram ν a y l l) (𝓝[≠] 0) (𝓝 0) := by
  have heq : (fun y : ℝ => measureGram ν a y l l) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun y : ℝ => ((∫ t, atomKernel (a l) y t ∂ν : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact measureGram_diagonal ν a y l (hint y hy)
  refine Tendsto.congr' heq.symm ?_
  have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hlim
  rw [show (fun y : ℝ => ((∫ t, atomKernel (a l) y t ∂ν : ℝ) : ℂ)) =
      Complex.ofReal ∘ fun y => ∫ t, atomKernel (a l) y t ∂ν by
    funext y
    rfl]
  exact hc

/-- **The measure off-diagonal converges to zero.**  Its squared modulus is squeezed by the product
of the two diagonal integrals, and the square-root step finishes. -/
theorem tendsto_measureGram_offdiag {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (l m : Fin d)
    (hbound : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ),
      ‖measureGram ν a y l m‖ ^ 2 ≤
        (∫ t, atomKernel (a l) y t ∂ν) * (∫ t, atomKernel (a m) y t ∂ν))
    (hl : Tendsto (fun y : ℝ => ∫ t, atomKernel (a l) y t ∂ν) (𝓝[≠] 0) (𝓝 0))
    (hm : Tendsto (fun y : ℝ => ∫ t, atomKernel (a m) y t ∂ν) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun y : ℝ => measureGram ν a y l m) (𝓝[≠] 0) (𝓝 0) := by
  have hprod : Tendsto (fun y : ℝ =>
      (∫ t, atomKernel (a l) y t ∂ν) * (∫ t, atomKernel (a m) y t ∂ν)) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hl.mul hm
  have hsq : Tendsto (fun y : ℝ => ‖measureGram ν a y l m‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero' ?_ hbound hprod
    filter_upwards with y
    positivity
  exact tendsto_zero_of_tendsto_norm (tendsto_norm_of_tendsto_sq hsq)

end

end GaloisForLFunctions.HTGeometry
