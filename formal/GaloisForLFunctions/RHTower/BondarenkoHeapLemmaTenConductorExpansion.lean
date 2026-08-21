/-
# Bondarenko--Heap Lemma 10: enlarged primitive-conductor zero boxes

The primitive-conductor aggregation in Bondarenko--Heap Lemma 10 must remain
valid after the slight rectangle enlargements used in zero-detection and
spacing arguments.  This module transports that exact source aggregation
through the closed Dirichlet-L zero-box enlargement mechanism.

No RH, GRH, exceptional-zero, zero-density, or counting premise is used.
-/

import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenConductorAggregation
import GaloisForLFunctions.RHTower.DirichletLZeroDensityBoxExpansion

noncomputable section

namespace RHTower

/-- The exact primitive-conductor zero-density aggregation from
Bondarenko--Heap Lemma 10 is monotone under every closed zero-box enlargement. -/
theorem completedLFunction_primitiveDivisor_zeroDensityBoxCount_le_expand
    (q : ℕ) (σ H : ℝ) (δ : NNReal) :
    completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ H ≤
      completedLFunctionPrimitiveDivisorZeroDensityBoxCount q
        (cglZeroDensityExpandedAbscissa σ δ)
        (cglZeroDensityExpandedHeight H δ) := by
  unfold completedLFunctionPrimitiveDivisorZeroDensityBoxCount
  exact Finset.sum_le_sum (fun d _ =>
    completedLFunction_primitiveFamily_zeroDensityBoxCount_le_expand (d - 1) σ H δ)

end RHTower
