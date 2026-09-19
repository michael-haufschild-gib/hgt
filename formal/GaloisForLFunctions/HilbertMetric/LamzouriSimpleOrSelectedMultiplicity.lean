import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity

/-!
# Simple-or-selected finite multiplicity packets

This is the finite union-count layer behind Lamzouri's "simple or real"
bookkeeping.  A selected point contributes its full multiplicity, while an
unselected point contributes exactly when it is simple.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Multiplicity mass carried by points that are simple or satisfy a selected
geometric predicate. -/
def finiteSimpleOrSelectedMultiplicityMass
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    (P : ι → Prop) [DecidablePred P] : ℝ :=
  ∑ i ∈ s, if m i = 1 ∨ P i then (m i : ℝ) else 0

/-- Multiplicity mass carried by selected points that are not simple. -/
def finiteSelectedNonsimpleMultiplicityMass
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    (P : ι → Prop) [DecidablePred P] : ℝ :=
  ∑ i ∈ s, if m i ≠ 1 ∧ P i then (m i : ℝ) else 0

/-- Exact disjoint decomposition of the simple-or-selected mass. -/
theorem finiteSimpleOrSelectedMultiplicityMass_eq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    (P : ι → Prop) [DecidablePred P] :
    finiteSimpleOrSelectedMultiplicityMass s m P =
      ((finiteSimpleMultiplicitySupport s m).card : ℝ) +
        finiteSelectedNonsimpleMultiplicityMass s m P := by
  unfold finiteSimpleOrSelectedMultiplicityMass
    finiteSelectedNonsimpleMultiplicityMass finiteSimpleMultiplicitySupport
  rw [show ((s.filter fun i => m i = 1).card : ℝ) =
      ∑ i ∈ s, if m i = 1 then (1 : ℝ) else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hs : m i = 1
  · simp [hs]
  · by_cases hP : P i
    · simp [hs, hP]
    · simp [hs, hP]

/-- Lamzouri's baseline simple-or-selected inequality.  Beyond Montgomery's
simple-point term, every selected non-simple multiplicity copy is recovered
without loss. -/
theorem finiteSimpleOrSelectedMultiplicityMass_lower
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    (P : ι → Prop) [DecidablePred P] :
    2 * finiteMultiplicityMass s m - finiteMultiplicityCollisionMass s m +
        finiteSelectedNonsimpleMultiplicityMass s m P ≤
      finiteSimpleOrSelectedMultiplicityMass s m P := by
  rw [finiteSimpleOrSelectedMultiplicityMass_eq]
  have h := finiteSimpleMultiplicitySupport_lower s m
  linarith

end

end GaloisForLFunctions.HilbertMetric
