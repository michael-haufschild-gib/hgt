import Mathlib.Analysis.Complex.Basic

/-!
# Support--escape descent law

This file isolates the elementary functional-analytic obstruction shared by
source-to-target descent problems.  If one target coordinate becomes
arbitrarily large on a source family of uniformly bounded capacity, then a
bounded weighted descent must erase that coordinate.  Hence a pointwise
faithful weight can coexist with bounded descent only when every charge that
forces such escape vanishes.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Coordinate `i` escapes source capacity: one fixed-capacity source family
has arbitrarily large `i`-th evaluation. -/
def CapacityEscapesAt {S I : Type*}
    (capacity : S → ℝ) (evaluation : I → S → ℂ) (i : I) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, ∃ u : S,
    capacity u ≤ C ∧ M < ‖evaluation i u‖

/-- A diagonal weight admits a uniform source bound for every coordinate. -/
def WeightedDescentBounded {S I : Type*}
    (capacity : S → ℝ) (evaluation : I → S → ℂ)
    (weight : I → ℂ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : S) (i : I),
    ‖evaluation i u * weight i‖ ≤ K * capacity u

/-- **Support--escape law.**  A bounded weighted descent vanishes at every
coordinate that escapes bounded source capacity. -/
theorem weight_eq_zero_of_capacityEscapesAt
    {S I : Type*} {capacity : S → ℝ} {evaluation : I → S → ℂ}
    {weight : I → ℂ} (hbounded : WeightedDescentBounded capacity evaluation weight)
    {i : I} (hescape : CapacityEscapesAt capacity evaluation i) :
    weight i = 0 := by
  obtain ⟨K, hK, hbound⟩ := hbounded
  obtain ⟨C, hC, hescape⟩ := hescape
  by_contra hw
  have hwnorm : 0 < ‖weight i‖ := norm_pos_iff.mpr hw
  obtain ⟨u, hcapacity, heval⟩ := hescape (K * C / ‖weight i‖)
  have hlower : K * C < ‖evaluation i u * weight i‖ := by
    rw [norm_mul]
    calc
      K * C = (K * C / ‖weight i‖) * ‖weight i‖ := by
        exact (div_mul_cancel₀ (K * C) (ne_of_gt hwnorm)).symm
      _ < ‖evaluation i u‖ * ‖weight i‖ :=
        mul_lt_mul_of_pos_right heval hwnorm
  have hupper : ‖evaluation i u * weight i‖ ≤ K * C :=
    (hbound u i).trans (mul_le_mul_of_nonneg_left hcapacity hK)
  exact (not_lt_of_ge hupper) hlower

/-- The support of every bounded diagonal descent is contained in the
non-escape locus. -/
theorem support_weight_subset_nonEscape
    {S I : Type*} {capacity : S → ℝ} {evaluation : I → S → ℂ}
    {weight : I → ℂ} (hbounded : WeightedDescentBounded capacity evaluation weight) :
    Function.support weight ⊆ {i | ¬ CapacityEscapesAt capacity evaluation i} := by
  intro i hi hescape
  exact hi (weight_eq_zero_of_capacityEscapesAt hbounded hescape)

/-- If nonzero charge forces capacity escape, then any bounded weighted
descent is supported on the neutral-charge locus. -/
theorem charge_eq_zero_on_boundedDescent_support
    {S I : Type*} {capacity : S → ℝ} {evaluation : I → S → ℂ}
    {weight : I → ℂ} {charge : I → ℝ}
    (hescape : ∀ i, charge i ≠ 0 → CapacityEscapesAt capacity evaluation i)
    (hbounded : WeightedDescentBounded capacity evaluation weight)
    {i : I} (hi : weight i ≠ 0) :
    charge i = 0 := by
  by_contra hcharge
  exact hi (weight_eq_zero_of_capacityEscapesAt hbounded (hescape i hcharge))

/-- A pointwise faithful bounded descent forces every escape-detecting charge
to vanish. -/
theorem charge_eq_zero_of_faithful_boundedDescent
    {S I : Type*} {capacity : S → ℝ} {evaluation : I → S → ℂ}
    {weight : I → ℂ} {charge : I → ℝ}
    (hescape : ∀ i, charge i ≠ 0 → CapacityEscapesAt capacity evaluation i)
    (hfaithful : ∀ i, weight i ≠ 0)
    (hbounded : WeightedDescentBounded capacity evaluation weight) :
    ∀ i, charge i = 0 := by
  intro i
  exact charge_eq_zero_on_boundedDescent_support hescape hbounded (hfaithful i)

end GaloisForLFunctions.HTGeometry
