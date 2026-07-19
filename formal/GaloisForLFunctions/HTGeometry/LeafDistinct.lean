import GaloisForLFunctions.HTGeometry.DenominatorFiberDisjoint

/-!
# Distinct parameters give distinct leaves

Each leaf is a probability measure whose fiber carries all the mass, so the fiber has measure at
least `1`.  Disjointness of the fibers puts the second fiber inside the complement of the first,
which is null for the first leaf.  If the two leaves were the same measure, that measure would give
its own fiber both `≥ 1` and `0`.

Only monotonicity and subadditivity of a measure are used, so no measurability of the fibers is
needed — the structure does not provide it.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

open GaloisForLFunctions.HTGeometry

variable {s : ℕ → ℝ}

/-- A leaf gives its own fiber full mass. -/
theorem one_le_leaf_fiber (F : ClassicalNevanlinnaExtremalFamily s) (tau : ℝ) :
    1 ≤ (F.leaf (tau : OnePoint ℝ) : Measure ℝ) (F.matrix.finiteDenominatorFiber tau) := by
  have hsplit : (F.leaf (tau : OnePoint ℝ) : Measure ℝ) Set.univ
      ≤ (F.leaf (tau : OnePoint ℝ) : Measure ℝ) (F.matrix.finiteDenominatorFiber tau)
        + (F.leaf (tau : OnePoint ℝ) : Measure ℝ) (F.matrix.finiteDenominatorFiber tau)ᶜ := by
    rw [← Set.union_compl_self (F.matrix.finiteDenominatorFiber tau)]
    exact measure_union_le _ _
  rw [F.finite_carried tau, add_zero, measure_univ] at hsplit
  exact hsplit

/-- **Distinct finite parameters give distinct leaves.** -/
theorem leaf_ne_of_ne (F : ClassicalNevanlinnaExtremalFamily s) {t1 t2 : ℝ} (hne : t1 ≠ t2) :
    (F.leaf (t1 : OnePoint ℝ) : Measure ℝ) ≠ (F.leaf (t2 : OnePoint ℝ) : Measure ℝ) := by
  intro heq
  have hsub : F.matrix.finiteDenominatorFiber t2 ⊆ (F.matrix.finiteDenominatorFiber t1)ᶜ :=
    fun x hx => Set.disjoint_right.mp (disjoint_finiteDenominatorFiber F.matrix hne) hx
  have hle : (F.leaf (t1 : OnePoint ℝ) : Measure ℝ) (F.matrix.finiteDenominatorFiber t2)
      ≤ (F.leaf (t1 : OnePoint ℝ) : Measure ℝ) (F.matrix.finiteDenominatorFiber t1)ᶜ :=
    measure_mono hsub
  rw [F.finite_carried t1] at hle
  have hone := one_le_leaf_fiber F t2
  rw [← heq] at hone
  have hbad : (1 : ENNReal) ≤ 0 := le_trans hone hle
  simp at hbad

/-- **Nodes of an indeterminate family diverge.**  An extremal family with two distinct finite
parameters has Gauss nodes outside every compact interval.

`PositiveMomentForm s` is an explicit hypothesis rather than a consequence: the family's fields give
carriers, continuity and moments, but nothing forces a leaf to have infinite support, which is what
`positiveMomentForm_iff_exists_representing` would need. -/
theorem exists_node_outside_of_extremalFamily (h : PositiveMomentForm s)
    (F : ClassicalNevanlinnaExtremalFamily s) {t1 t2 : ℝ} (hne : t1 ≠ t2)
    {B : ℝ} (hB : 0 < B) :
    ∃ n : ℕ, ∃ xi ∈ gaussNodes s n, xi ∉ Set.Icc (-B) B := by
  haveI h1 : IsFiniteMeasure (F.leaf (t1 : OnePoint ℝ) : Measure ℝ) := inferInstance
  haveI h2 : IsFiniteMeasure (F.leaf (t2 : OnePoint ℝ) : Measure ℝ) := inferInstance
  exact exists_node_outside_of_hasMoments_ne h hB
    (F.leaf_moments (t1 : OnePoint ℝ)) (F.leaf_moments (t2 : OnePoint ℝ))
    (leaf_ne_of_ne F hne)

end HTGeometry
