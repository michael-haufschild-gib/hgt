import GaloisForLFunctions.HTGeometry.RecurrenceSwapInteractionReconstructionLaw

/-!
# Universal recurrence swaps exist

A mask is a universal recurrence symmetry when partially swapping two configurations along it
leaves the total energy of the pair unchanged.  The two extreme masks are symmetries of every
energy at all, since they either do nothing or exchange the two configurations outright.

The substantive realization is the additively separable energy: a sum of one-site terms is
invariant under *every* partial swap, and is additively separable across every cut.  So the
reconstruction law — which turns the dynamical swap symmetry into additive separability — has an
exhaustive supply of instances, and its two hypotheses are simultaneously satisfiable.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [DecidableEq V] {A : V → Type*}

/-- The energy assembled from one-site terms. -/
def siteEnergy [Fintype V] (f : ∀ v, A v → ℝ) (x : ∀ v, A v) : ℝ := ∑ v, f v (x v)

/-- **Every additively separable energy is invariant under every partial swap.**  Swapping a mask
permutes the one-site terms of the pair without changing their multiset. -/
theorem isUniversalRecurrenceSwap_siteEnergy [Fintype V] (f : ∀ v, A v → ℝ)
    (mask : Finset V) :
    IsUniversalRecurrenceSwap (siteEnergy f) mask := by
  intro x y
  rw [siteEnergy, siteEnergy, siteEnergy, siteEnergy, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v ∈ mask
  · simp [dependentPartialSwapFirst, dependentPartialSwapSecond, dependentUpdateOnFinset, hv,
      add_comm]
  · simp [dependentPartialSwapFirst, dependentPartialSwapSecond, dependentUpdateOnFinset, hv]

/-- **Every additively separable energy is additively separable across every cut.** -/
theorem isAdditivelySeparableAcross_siteEnergy [Fintype V] (f : ∀ v, A v → ℝ)
    (base : ∀ v, A v) (mask : Finset V) :
    IsAdditivelySeparableAcross (siteEnergy f) base mask := by
  intro x
  rw [siteEnergy, siteEnergy, siteEnergy, siteEnergy, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v ∈ mask
  · simp [dependentUpdateOnFinset, hv, add_comm]
  · simp [dependentUpdateOnFinset, hv, add_comm]

/-- Both hypotheses of the reconstruction law hold simultaneously on an additively separable
energy, for every cut and every basepoint. -/
theorem isUniversalRecurrenceSwap_and_isAdditivelySeparableAcross_siteEnergy [Fintype V]
    (f : ∀ v, A v → ℝ) (base : ∀ v, A v) (mask : Finset V) :
    IsUniversalRecurrenceSwap (siteEnergy f) mask ∧
      IsAdditivelySeparableAcross (siteEnergy f) base mask :=
  ⟨isUniversalRecurrenceSwap_siteEnergy f mask,
    isAdditivelySeparableAcross_siteEnergy f base mask⟩

end

end GaloisForLFunctions.HTGeometry
