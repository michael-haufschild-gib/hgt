import GaloisForLFunctions.HTGeometry.NormalCrossingCriticalBaseChange

/-!
# The normal-crossing constraint Hodge diamond

A codimension-`q` face of an `N`-direction normal-crossing source has `q` independent exterior
critical base-change directions.  Its internal degree-`p` multiplicity is therefore `q.choose p`,
and there are `N.choose q` such faces.  The resulting bidegree multiplicity is

`N.choose q * q.choose p`.

This file records three structural consequences:

* the diamond is supported on the constraint cone `0 <= p <= q <= N`;
* exterior duality reflects `p` to `q-p` inside each source face;
* the total labelled capacity is `3^N`, not `2^N`: every source direction is absent,
  source-only, or source-plus-derived-excess.

The two degrees are intrinsic to the source-face/critical-base-change diagram.  They are not a
one-parameter clock grading, and an additive scalar totalization cannot retain them faithfully.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- The normal-crossing multiplicity in internal excess degree `p` and source-face degree `q`. -/
def normalCrossingConstraintMultiplicity (N p q : ℕ) : ℕ :=
  N.choose q * q.choose p

/-- There is no internal excess above source depth. -/
theorem normalCrossingConstraintMultiplicity_eq_zero_of_source_lt_excess
    (N p q : ℕ) (h : q < p) :
    normalCrossingConstraintMultiplicity N p q = 0 := by
  simp [normalCrossingConstraintMultiplicity, Nat.choose_eq_zero_of_lt h]

/-- There are no source faces beyond the number of structural directions. -/
theorem normalCrossingConstraintMultiplicity_eq_zero_of_rank_lt_source
    (N p q : ℕ) (h : N < q) :
    normalCrossingConstraintMultiplicity N p q = 0 := by
  simp [normalCrossingConstraintMultiplicity, Nat.choose_eq_zero_of_lt h]

/-- Exterior Poincare duality reflects internal degree `p` to `q-p` at fixed source depth. -/
theorem normalCrossingConstraintMultiplicity_duality
    (N p q : ℕ) (hpq : p ≤ q) :
    normalCrossingConstraintMultiplicity N (q - p) q =
      normalCrossingConstraintMultiplicity N p q := by
  simp only [normalCrossingConstraintMultiplicity]
  rw [Nat.choose_symm hpq]

/-- **Three-state capacity law.** Summing the complete constraint Hodge diamond gives `3^N`:
each structural direction is absent, belongs to the source face only, or belongs to both the
source face and its derived exterior excess. -/
theorem sum_normalCrossingConstraintMultiplicity (N : ℕ) :
    (∑ q ∈ range (N + 1), ∑ p ∈ range (q + 1),
      normalCrossingConstraintMultiplicity N p q) = 3 ^ N := by
  calc
    _ = ∑ q ∈ range (N + 1), N.choose q * 2 ^ q := by
      apply sum_congr rfl
      intro q hq
      rw [← Nat.sum_range_choose q, Finset.mul_sum]
      rfl
    _ = 3 ^ N := by
      have h := add_pow (2 : ℕ) 1 N
      norm_num at h ⊢
      simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm

/-- A source face together with a derived-excess subface.  The containment is the exact
constraint-cone condition: an internal excess direction cannot occur before its source direction
is present. -/
structure NormalCrossingConstraintLabel (N : ℕ) where
  source : Finset (Fin N)
  excess : Finset (Fin N)
  excess_subset_source : excess ⊆ source

namespace NormalCrossingConstraintLabel

/-- Source-face degree. -/
def sourceDepth {N : ℕ} (c : NormalCrossingConstraintLabel N) : ℕ :=
  c.source.card

/-- Internal derived-excess degree. -/
def excessDegree {N : ℕ} (c : NormalCrossingConstraintLabel N) : ℕ :=
  c.excess.card

/-- **Constraint-cone theorem.** Internal derived excess never exceeds source depth. -/
theorem excessDegree_le_sourceDepth {N : ℕ} (c : NormalCrossingConstraintLabel N) :
    c.excessDegree ≤ c.sourceDepth :=
  Finset.card_le_card c.excess_subset_source

/-- Exterior Poincare duality within one fixed source face. -/
def dual {N : ℕ} (c : NormalCrossingConstraintLabel N) :
    NormalCrossingConstraintLabel N where
  source := c.source
  excess := c.source \ c.excess
  excess_subset_source := Finset.sdiff_subset

@[simp]
theorem dual_source {N : ℕ} (c : NormalCrossingConstraintLabel N) :
    c.dual.source = c.source := rfl

@[simp]
theorem dual_excess {N : ℕ} (c : NormalCrossingConstraintLabel N) :
    c.dual.excess = c.source \ c.excess := rfl

/-- Constraint duality is an involution. -/
@[simp]
theorem dual_dual {N : ℕ} (c : NormalCrossingConstraintLabel N) :
    c.dual.dual = c := by
  cases c with
  | mk source excess h =>
      simp [dual, Finset.sdiff_sdiff_eq_self h]

/-- Duality preserves source depth and complements the internal degree inside it. -/
theorem dual_excessDegree {N : ℕ} (c : NormalCrossingConstraintLabel N) :
    c.dual.excessDegree = c.sourceDepth - c.excessDegree := by
  simp [excessDegree, sourceDepth, dual, Finset.card_sdiff,
    Finset.inter_eq_left.2 c.excess_subset_source]

end NormalCrossingConstraintLabel

end GaloisForLFunctions.HTGeometry
