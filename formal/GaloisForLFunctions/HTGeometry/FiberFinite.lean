import GaloisForLFunctions.HTGeometry.NevFiberCountable

/-!
# The fiber meets a compact set finitely

The denominator fibers are closed and discrete, so their intersection with a compact set is compact
and discrete, hence finite.  This is what turns an integral against a leaf into a finite sum when the
test function has compact support.
-/

open scoped BigOperators
open Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A set of reals with no accumulation point in itself is discrete. -/
theorem isDiscrete_of_eventually_notMem {A : Set ℝ}
    (hA : ∀ x, ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∉ A) : IsDiscrete A :=
  isDiscrete_iff_nhdsNE.mpr fun x _ => Filter.inf_principal_eq_bot.mpr (hA x)

/-- A subset of a set with no accumulation point in itself is discrete. -/
theorem isDiscrete_inter_of_eventually_notMem {A : Set ℝ}
    (hA : ∀ x, ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∉ A) (K : Set ℝ) : IsDiscrete (A ∩ K) := by
  refine isDiscrete_iff_nhdsNE.mpr fun x _ => ?_
  refine le_bot_iff.mp ?_
  refine le_trans (inf_le_inf_left _ (Filter.principal_mono.mpr Set.inter_subset_left)) ?_
  exact le_of_eq (Filter.inf_principal_eq_bot.mpr (hA x))

/-- **A finite-parameter fiber meets a compact set finitely.** -/
theorem finite_finiteDenominatorFiber_inter (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (tau : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    (((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) ∩ K).Finite := by
  have hcompact : IsCompact
      (((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) ∩ K) :=
    hK.inter_left (isClosed_finiteDenominatorFiber h h0b tau)
  exact hcompact.finite (isDiscrete_inter_of_eventually_notMem
    (fun x => eventually_notMem_finiteDenominatorFiber h h0b tau x) K)

/-- **The infinity fiber meets a compact set finitely.** -/
theorem finite_infinityDenominatorFiber_inter (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {K : Set ℝ} (hK : IsCompact K) :
    ((nevMatrixDataInf h h0b).infinityDenominatorFiber ∩ K).Finite := by
  have hcompact : IsCompact ((nevMatrixDataInf h h0b).infinityDenominatorFiber ∩ K) :=
    hK.inter_left (isClosed_infinityDenominatorFiber h h0b)
  exact hcompact.finite (isDiscrete_inter_of_eventually_notMem
    (fun x => eventually_notMem_infinityDenominatorFiber h h0b x) K)

end HTGeometry
