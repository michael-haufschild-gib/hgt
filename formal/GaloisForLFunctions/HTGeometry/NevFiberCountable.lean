import GaloisForLFunctions.HTGeometry.NevanlinnaRealMatrix

/-!
# The denominator fibers are closed, discrete and countable

A set of reals every point of which has a punctured neighbourhood missing the set carries the
discrete topology as a subspace.  `ℝ` is second countable, so that subspace is separable, and a
separable discrete space is countable.

Applied to the denominator fibers this says the N-extremal support of every parameter is a countable
closed discrete set — the shape a `countableWeightedDirac` leaf needs.
-/

open scoped BigOperators
open Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A set of reals with no accumulation point in itself is countable.** -/
theorem countable_of_eventually_notMem {A : Set ℝ}
    (hA : ∀ x ∈ A, ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∉ A) : A.Countable := by
  haveI hd : DiscreteTopology ↥A :=
    discreteTopology_subtype_iff.mpr fun x hx => Filter.inf_principal_eq_bot.mpr (hA x hx)
  exact Set.countable_coe_iff.mp (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- **The N-extremal support of a finite parameter is countable.** -/
theorem countable_finiteDenominatorFiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℝ) : ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau).Countable :=
  countable_of_eventually_notMem fun x _ =>
    eventually_notMem_finiteDenominatorFiber h h0b tau x

/-- **The N-extremal support of the parameter at infinity is countable.** -/
theorem countable_infinityDenominatorFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    (nevMatrixDataInf h h0b).infinityDenominatorFiber.Countable :=
  countable_of_eventually_notMem fun x _ =>
    eventually_notMem_infinityDenominatorFiber h h0b x

/-- The finite denominator fiber is closed: it is a level set of a continuous function. -/
theorem isClosed_finiteDenominatorFiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℝ) : IsClosed ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) := by
  have hcont : Continuous fun x : ℝ => nevBrealInf s x * tau - nevDrealInf s x :=
    ((continuous_nevBrealInf h h0b).mul continuous_const).sub (continuous_nevDrealInf h h0b)
  exact isClosed_singleton.preimage hcont

/-- The infinity denominator fiber is closed. -/
theorem isClosed_infinityDenominatorFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    IsClosed (nevMatrixDataInf h h0b).infinityDenominatorFiber :=
  isClosed_singleton.preimage (continuous_nevBrealInf h h0b)

end HTGeometry
