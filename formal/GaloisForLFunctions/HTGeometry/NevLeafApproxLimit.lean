import GaloisForLFunctions.HTGeometry.NevLeafFunction

/-!
# The quadrature family converges to the leaf itself

The construction of the leaf chose a weak limit of quasi-orthogonal quadrature measures, and the
atom identification pins that limit: any such limit is the fiber measure carrying the Christoffel
limits, which is the leaf.  So the approximating family converges to the leaf on the nose, and
every weakly continuous functional of the leaf may be computed from the quadrature levels.
-/

open scoped BigOperators
open MeasureTheory Filter Topology OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The quadrature levels converge to the leaf.** -/
theorem exists_tendsto_quasiProbMeasure_nevLeaf (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (tau : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)))
        atTop (𝓝 (nevLeaf h h0b h0 (tau : OnePoint ℝ))) := by
  obtain ⟨μ, φ, hφ, hlim, hmom, hcar⟩ := exists_leaf_approx h h0b tau
  have hmom' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
    intro k
    refine ⟨(hmom k).1, ?_⟩
    simpa [h0] using (hmom k).2
  have hset : ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ
      = {x : ℝ | nevBrealInf s x * tau - nevDrealInf s x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
      nevMatrixDataInf]
  have hcar' : (μ : Measure ℝ) ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 := by
    rw [hset]; exact hcar
  have hatoms : ∀ ξ ∈ (nevMatrixDataInf h h0b).finiteDenominatorFiber tau,
      (μ : Measure ℝ) {ξ} = ENNReal.ofReal (christoffelLimit s ξ) := by
    intro ξ hξmem
    have hξ : nevBrealInf s ξ * tau - nevDrealInf s ξ = 0 := hξmem
    refine le_antisymm (measure_singleton_le_ofReal_christoffelLimit h hmom' ξ) ?_
    exact ofReal_christoffelLimit_le_leaf_singleton h h0b h0 hφ hlim hξ
  have hfiber : (μ : Measure ℝ)
      = fiberMeasure (fun x => christoffelLimit s x)
          ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) := by
    have hbase := measure_eq_fiberMeasure_of_carried (μ : Measure ℝ)
      (countable_finiteDenominatorFiber h h0b tau)
      (isClosed_finiteDenominatorFiber h h0b tau).measurableSet hcar'
    rw [hbase, fiberMeasure, fiberMeasure]
    refine congrArg Measure.sum (funext fun p => ?_)
    rw [hatoms p p.2, ENNReal.toReal_ofReal (christoffelLimit_nonneg h _)]
  have heq : μ = nevLeaf h h0b h0 (tau : OnePoint ℝ) := by
    refine MeasureTheory.ProbabilityMeasure.toMeasure_injective ?_
    rw [hfiber, nevLeaf_eq_fiberMeasure h h0b h0 tau]
  exact ⟨φ, hφ, heq ▸ hlim⟩

end HTGeometry
