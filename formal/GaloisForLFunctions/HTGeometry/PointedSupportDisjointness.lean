import GaloisForLFunctions.HTGeometry.PrimeResidueInteractionSpectrum

/-!
# Disjoint pointed supports

The superselection theorems compare two configurations through disjointness of their pointed
supports, and that hypothesis was consumed with no named producer — it appears inside one proof
discharged by `simp`, which hides the general fact.

Disjointness is a pointwise condition: two configurations have disjoint pointed supports exactly
when at every site at least one of them is unpointed.  In particular the unit configuration has
empty pointed support, so it is disjoint from everything.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, DecidableEq (A i)] [∀ i, One (A i)]

@[simp] theorem mem_pointedSupport (x : ∀ i, A i) (i : ι) :
    i ∈ pointedSupport A x ↔ x i ≠ 1 := by
  simp [pointedSupport]

/-- **Disjointness is pointwise.**  Two configurations have disjoint pointed supports exactly when
at every site at least one of them is unpointed. -/
theorem disjoint_pointedSupport_iff (z w : ∀ i, A i) :
    Disjoint (pointedSupport A z) (pointedSupport A w) ↔ ∀ i, z i = 1 ∨ w i = 1 := by
  rw [Finset.disjoint_left]
  constructor
  · intro h i
    by_cases hz : z i = 1
    · exact Or.inl hz
    · refine Or.inr ?_
      by_contra hw
      exact h ((mem_pointedSupport z i).mpr hz) ((mem_pointedSupport w i).mpr hw)
  · intro h i hi hj
    rcases h i with hz | hw
    · exact ((mem_pointedSupport z i).mp hi) hz
    · exact ((mem_pointedSupport w i).mp hj) hw

/-- The unit configuration is disjoint from every configuration, so the superselection hypothesis
is always available against it. -/
theorem disjoint_pointedSupport_one (z : ∀ i, A i) :
    Disjoint (pointedSupport A z) (pointedSupport A (fun i => (1 : A i))) := by
  rw [disjoint_pointedSupport_iff]
  intro i
  exact Or.inr rfl

/-- Symmetrically. -/
theorem disjoint_one_pointedSupport (z : ∀ i, A i) :
    Disjoint (pointedSupport A (fun i => (1 : A i))) (pointedSupport A z) :=
  (disjoint_pointedSupport_one z).symm

end GaloisForLFunctions.HTGeometry
